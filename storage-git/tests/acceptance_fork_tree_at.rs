//! Acceptance tests for `tree_at(n)` on a log resumed from a seal (a fork),
//! from `docs/specs/storage-git.md` §4.3 (SG20) alone, narrowed by the merge
//! re-gate's own directive (`storage-git-regate-2.md`, RT20 [1]): hasher
//! evidence must be required only where reconstructing `n` actually invokes
//! the hasher -- never for `n == current size`, and never for a target
//! frontier of zero or one peak. A fold is only ever needed to combine two
//! or more peaks; a lone peak is promoted to itself (`bag_peaks`'s own
//! documented behavior), and an empty frontier has no algorithm root to
//! fold at all.
//!
//! A fork's resumed frontier is opaque (SG10/SG11): the coordinate a
//! resumed peak was sealed at is addressable, but nothing strictly beneath
//! it is (this crate's own documented Departure 3) -- that is a pre-existing,
//! separate limitation this file's genesis/current-size assertions never
//! exercise, and the below-the-fork case is asserted here only to pin down
//! which error a query into it must surface once hasher-evidence validation
//! no longer masks it.

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::NaryMerkleLog;
use spine::{Hasher, Subtree};
use storage_git::GitStorage;
use support::{FixtureHasher, bare_repo, new_log};

/// Same-width, different-function hasher, isolating a wrong *function*
/// registration from a wrong *width* one (mirrors `acceptance_roots_hasher.rs`
/// and `acceptance_opacity.rs`'s own independent copies of this fixture).
#[derive(Debug, Clone)]
struct WrongFunctionHasher {
    inner: FixtureHasher,
}

impl WrongFunctionHasher {
    fn new(width: usize) -> Self {
        Self {
            inner: FixtureHasher::new(width),
        }
    }
}

impl Hasher for WrongFunctionHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        self.hash(data)
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut buf = Vec::new();
        for c in children {
            buf.extend_from_slice(c);
        }
        self.hash(&buf)
    }

    fn empty(&self) -> Vec<u8> {
        self.hash(b"")
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        let mut bytes = self.inner.hash(data);
        bytes.reverse();
        bytes
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

/// Seal a flat log of `n` leaves at arity 2 -- `n` a power of 2, so both `n`
/// and `n/2` land on a single-peak frontier size -- and resume it onto a
/// fresh ref with the correct hasher registered. `tree_at(n)`, the current
/// size, must be served as the staging tip itself (the fast path never
/// touches the hasher). `tree_at(0)`, the empty frontier, must succeed too:
/// no algorithm's root has ever been folded at size 0, so `roots/` there
/// carries no entry and no hasher evidence is needed either. Neither call
/// may be refused for lack of hasher evidence -- registering the correct
/// hasher must never make a fork harder to read than an unregistered one.
#[test]
fn tree_at_serves_genesis_and_current_size_for_a_fork_at_a_single_peak_size() {
    smol::block_on(async {
        for n in [4u64, 8] {
            let dir_src = tempfile::tempdir().unwrap();
            let staging_src = format!("refs/eml/storage/fork-tree-at-src-{n}/staging");
            let repo_src = bare_repo(dir_src.path(), gix::hash::Kind::Sha256);
            let real = FixtureHasher::new(32);
            let mut log = new_log(&repo_src, &staging_src, 2, real.clone()).await;
            for i in 0..n {
                log.append_leaf(format!("leaf-{i}").as_bytes())
                    .await
                    .unwrap();
            }
            let sealed = log.seal().await.unwrap();

            let dir_dst = tempfile::tempdir().unwrap();
            let staging_dst = format!("refs/eml/storage/fork-tree-at-dst-{n}/staging");
            let repo_dst = bare_repo(dir_dst.path(), gix::hash::Kind::Sha256);
            let mut storage_dst =
                GitStorage::new(repo_dst.clone(), &staging_dst, 2).expect("open a fresh ref");
            storage_dst.register_hasher(0, Box::new(real.clone()));
            let resumed =
                NaryMerkleLog::resume(&sealed, storage_dst, vec![(0, Box::new(real.clone()))])
                    .await
                    .expect("resume onto a fresh ref with the correct hasher registered");

            let local_dst = repo_dst.to_thread_local();
            let written_at_n = support::ref_target(&local_dst, &staging_dst)
                .expect("resume commits exactly one checkpoint, at size n");

            // tree_at(n) at the current size must be served as the staging
            // tip itself.
            let at_n = resumed.storage().tree_at(n).unwrap_or_else(|e| {
                panic!(
                    "n={n}: tree_at({n}) with the correct hasher registered must succeed (n == \
                     current size never needs a fold): {e}"
                )
            });
            assert_eq!(
                at_n, written_at_n,
                "n={n}: tree_at(n) must equal the tree resume actually wrote at size {n}"
            );

            // tree_at(0): the frontier is empty, so roots/ carries no entry
            // and no hasher evidence is needed.
            let at_0 = resumed.storage().tree_at(0).unwrap_or_else(|e| {
                panic!(
                    "n={n}: tree_at(0) with the correct hasher registered must succeed (an empty \
                     frontier has no root to fold): {e}"
                )
            });
            let roots_0 = support::find_entry(&local_dst, at_0, "roots")
                .expect("n={n}: C(0) must still carry a roots/ tree")
                .oid;
            assert!(
                support::read_tree(&local_dst, roots_0).is_empty(),
                "n={n}: C(0)'s roots/ must carry no entry -- no algorithm's root has ever been \
                 computed at size 0"
            );

            // tree_at(n/2) targets a coordinate strictly beneath the fork's
            // single inherited opaque peak. That peak carries no
            // `hex(c,2)` children at all (SG10/SG11), so this coordinate
            // has never been anything but unreconstructable -- this crate's
            // own documented Departure 3, unrelated to hasher evidence.
            // Once hasher-evidence validation no longer runs where no fold
            // is needed, this must surface as exactly that pre-existing
            // refusal, never the hasher-evidence one.
            let n_half = n / 2;
            match resumed.storage().tree_at(n_half) {
                Ok(id) => panic!(
                    "n={n}: tree_at({n_half}) returned Ok({id}); a coordinate strictly beneath \
                     the fork's single inherited opaque peak has no materialized substructure to \
                     reconstruct from and must still be refused"
                ),
                Err(e) => {
                    let msg = e.to_string();
                    assert!(
                        !msg.contains("cannot be checked against any stored evidence"),
                        "n={n}: tree_at({n_half}) must never be blocked by hasher-evidence \
                         validation -- a target frontier of one peak needs no fold at all; got: \
                         {msg}"
                    );
                    assert!(
                        msg.contains("sealed opaque"),
                        "n={n}: tree_at({n_half}) must fail for the pre-existing, documented \
                         reason (a coordinate beneath the fork's inherited opaque peak is not \
                         reconstructable), not some other error; got: {msg}"
                    );
                },
            }
        }
    });
}

/// Once a fork gains a second peak -- one more append past a single-peak
/// resumed size -- reconstructing the live tree's `roots/` genuinely needs
/// to fold two peaks together. A wrong same-width hasher registered there
/// must still be refused: narrowing hasher-evidence validation to skip
/// zero/one-peak targets must never also skip the case a fold is actually
/// needed.
#[test]
fn tree_at_wrong_hasher_still_refused_once_the_fork_has_two_peaks() {
    smol::block_on(async {
        let dir_src = tempfile::tempdir().unwrap();
        let staging_src = "refs/eml/storage/fork-two-peaks-src/staging";
        let repo_src = bare_repo(dir_src.path(), gix::hash::Kind::Sha256);
        let real = FixtureHasher::new(32);
        let mut log = new_log(&repo_src, staging_src, 2, real.clone()).await;
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = log.seal().await.unwrap();

        let dir_dst = tempfile::tempdir().unwrap();
        let staging_dst = "refs/eml/storage/fork-two-peaks-dst/staging";
        let repo_dst = bare_repo(dir_dst.path(), gix::hash::Kind::Sha256);
        let mut storage_dst = GitStorage::new(repo_dst.clone(), staging_dst, 2).expect("open");
        storage_dst.register_hasher(0, Box::new(real.clone()));
        let mut resumed =
            NaryMerkleLog::resume(&sealed, storage_dst, vec![(0, Box::new(real.clone()))])
                .await
                .expect("resume onto a fresh ref");
        resumed
            .append_subtree(&Subtree::Leaf(b"fwd-0".to_vec()))
            .await
            .unwrap();
        let n = resumed.count();
        assert_eq!(
            spine::frontier_for_size(n, 2).len(),
            2,
            "fixture sanity: one more append past a single-peak fork must give two peaks"
        );

        // Sanity: the correct hasher still succeeds for the live tree.
        resumed
            .storage()
            .tree_at(n)
            .unwrap_or_else(|e| panic!("tree_at({n}) with the correct hasher: {e}"));
        drop(resumed);

        let mut wrong_storage =
            GitStorage::new(support::reopen_repo(dir_dst.path()), staging_dst, 2).expect("reopen");
        wrong_storage.register_hasher(0, Box::new(WrongFunctionHasher::new(32)));
        if let Ok(id) = wrong_storage.tree_at(n) {
            panic!(
                "tree_at({n}) returned Ok({id}) with a wrong same-width hasher once the fork has \
                 two peaks -- folding them together is exactly where hasher evidence is needed, \
                 and a wrong function must still be refused"
            );
        }
    });
}
