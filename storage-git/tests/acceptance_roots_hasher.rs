//! Acceptance tests guarding `tree_at`'s historical `roots/` reconstruction
//! against a missing or wrong hasher (SG14, SG20's amendment, and GB44's
//! resolution in `.ledger/state/2026-09-14-the-git-backend-in-three-layers.md`,
//! closing SGG12 from the merge gate at
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-merge-gate.md`).
//!
//! Written from `docs/specs/storage-git.md` alone, against `storage-git`'s
//! public API (`GitStorage`, `GitStorageError`). Not derived from
//! `storage-git`'s private modules (`historical.rs`, ...) or from its
//! existing test suite -- including not reusing that suite's fixture
//! module's `new_log` helper, which registers a hasher unconditionally and
//! so cannot exercise the "no hasher registered" path these tests check
//! (the merge gate's own SGG13 finding).

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::{NaryMerkleLog, TreeConfig};
use spine::Hasher;
use storage_git::GitStorage;
use support::FixtureHasher;

const ARITY: u64 = 2;
const REAL_WIDTH: usize = 32;

fn real_hasher() -> FixtureHasher {
    FixtureHasher::new(REAL_WIDTH)
}

/// A `Hasher` of the SAME digest width as [`real_hasher`] but a genuinely
/// different function (the real hasher's digest with its bytes reversed),
/// so a "wrong function" registration cannot be mistaken for a "wrong
/// width" one in the case that needs to isolate it.
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

/// **`tree_at` with no hasher registered for an algorithm active at `n`
/// (SG20's amendment, GB44).** It MUST return an error naming that
/// algorithm, for every historical `n` the algorithm is active at. It MUST
/// NEVER return `Ok`.
#[test]
fn tree_at_without_registered_hasher_names_the_missing_algorithm() {
    const NAMED_ALG: u64 = 42;

    let result: Result<(), String> = smol::block_on(async {
        let dir = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
        let staging_ref = "refs/eml/storage/tree-at-no-hasher/staging";
        let repo = support::bare_repo(dir.path(), gix::hash::Kind::Sha1);

        let mut storage =
            GitStorage::new(repo, staging_ref, ARITY).map_err(|e| format!("open: {e}"))?;
        // Algorithm 0's fold is registered; NAMED_ALG's never is -- isolating
        // exactly the "no hasher for an active algorithm" gap.
        storage.register_hasher(0, Box::new(real_hasher()));
        let mut log = NaryMerkleLog::new(
            storage,
            Box::new(real_hasher()),
            TreeConfig { arity: ARITY },
        )
        .await
        .map_err(|e| format!("new: {e:?}"))?;

        log.add_algorithm(NAMED_ALG, Box::new(real_hasher()))
            .await
            .map_err(|e| format!("add_algorithm({NAMED_ALG}): {e:?}"))?;
        for i in 0..4u8 {
            log.append_leaf(&[i])
                .await
                .map_err(|e| format!("append {i}: {e:?}"))?;
        }

        // Every n in 1..current is historical and NAMED_ALG is active
        // throughout (registered before any append).
        for n in 1..log.count() {
            match log.storage().tree_at(n) {
                Ok(id) => {
                    return Err(format!(
                        "tree_at({n}) returned Ok({id}) with no hasher registered for algorithm \
                         {NAMED_ALG}, active at every appended n -- SG20's amendment and GB44 \
                         both require an error naming the algorithm, never Ok"
                    ));
                },
                Err(e) => {
                    let msg = e.to_string();
                    if !msg.contains(&NAMED_ALG.to_string()) {
                        return Err(format!(
                            "tree_at({n}) errored ({msg}) but did not name the algorithm \
                             ({NAMED_ALG}) with no registered hasher"
                        ));
                    }
                },
            }
        }
        Ok(())
    });

    if let Err(msg) = result {
        panic!("{msg}");
    }
}

/// **`tree_at` rejects a hasher that does not reproduce the stored current
/// root, before any historical root is trusted (SG20's amendment, GB44).**
/// Neither a wrong-width nor a wrong-function registered hasher for an
/// algorithm that DOES have real, correctly-computed digests already
/// stored may be silently accepted.
#[test]
fn tree_at_rejects_a_hasher_that_does_not_reproduce_the_stored_root() {
    let result: Result<(), String> = smol::block_on(async {
        let dir = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
        let staging_ref = "refs/eml/storage/tree-at-wrong-hasher/staging";
        let repo = support::bare_repo(dir.path(), gix::hash::Kind::Sha1);

        // Build the real log with the real (width-32) hasher, no hasher
        // registered on the storage yet.
        let storage =
            GitStorage::new(repo, staging_ref, ARITY).map_err(|e| format!("open: {e}"))?;
        let mut log = NaryMerkleLog::new(
            storage,
            Box::new(real_hasher()),
            TreeConfig { arity: ARITY },
        )
        .await
        .map_err(|e| format!("new: {e:?}"))?;
        for i in 0..4u8 {
            log.append_leaf(&[i])
                .await
                .map_err(|e| format!("append {i}: {e:?}"))?;
        }
        drop(log);

        // Case A: same function, wrong width.
        let mut wrong_width_storage =
            GitStorage::new(support::reopen_repo(dir.path()), staging_ref, ARITY)
                .map_err(|e| format!("reopen (wrong width): {e}"))?;
        wrong_width_storage.register_hasher(0, Box::new(FixtureHasher::new(16)));
        if let Ok(id) = wrong_width_storage.tree_at(1) {
            return Err(format!(
                "tree_at(1) returned Ok({id}) with a wrong-width hasher registered for algorithm \
                 0, whose real digests are {REAL_WIDTH} bytes wide"
            ));
        }

        // Case B: same width, wrong function.
        let mut wrong_fn_storage =
            GitStorage::new(support::reopen_repo(dir.path()), staging_ref, ARITY)
                .map_err(|e| format!("reopen (wrong function): {e}"))?;
        wrong_fn_storage.register_hasher(0, Box::new(WrongFunctionHasher::new(REAL_WIDTH)));
        if let Ok(id) = wrong_fn_storage.tree_at(1) {
            return Err(format!(
                "tree_at(1) returned Ok({id}) with a same-width hasher that does not reproduce \
                 algorithm 0's real digest function"
            ));
        }

        Ok(())
    });

    if let Err(msg) = result {
        panic!("{msg}");
    }
}
