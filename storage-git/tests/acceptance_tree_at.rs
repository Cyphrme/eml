//! Acceptance test for §4.3's `tree_at(n)` (SG20), from
//! `docs/specs/storage-git.md` alone.

#[path = "acceptance_support/mod.rs"]
mod support;

use support::{FixtureHasher, bare_repo, new_log};

/// [SG20] `tree_at(n)` MUST return `C(n)`'s object id for any `n` from `0`
/// to the instance's current size, inclusive, and it MUST be
/// byte-identical to the checkpoint tree the layout actually wrote at size
/// `n` -- including after further appends have moved the log well past
/// `n`. Record each size's tree id as it is written, then compare against
/// `tree_at` for every size, after every further append.
#[test]
fn sg20_tree_at_matches_the_checkpoint_written_at_each_size() {
    smol::block_on(async {
        for k in [2u64, 3, 4] {
            let dir = tempfile::tempdir().unwrap();
            let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
            let staging = format!("refs/eml/storage/sg20-k{k}/staging");
            let mut log = new_log(&repo, &staging, k, FixtureHasher::new(32)).await;

            // Record the tree id written at every size 0..=20, as it is
            // written -- straight from the staging ref, never from
            // `tree_at` itself, so the recorded oracle is independent of
            // the function under test.
            let n_max = 20u64;
            let mut written_at: Vec<gix::ObjectId> = Vec::with_capacity(n_max as usize + 1);
            written_at.push(
                support::ref_target(&repo.to_thread_local(), &staging)
                    .expect("size 0 already has a checkpoint (alg 0 registered)"),
            );
            for i in 0..n_max {
                log.append_leaf(format!("leaf-{i}").as_bytes())
                    .await
                    .unwrap();
                written_at.push(support::ref_target(&repo.to_thread_local(), &staging).unwrap());
            }

            // tree_at(n) for every recorded size must match immediately...
            for n in 0..=n_max {
                let got = log.storage().tree_at(n).unwrap();
                assert_eq!(
                    got, written_at[n as usize],
                    "k={k}: tree_at({n}) must equal the checkpoint written at size {n}"
                );
            }

            // ...and must keep matching after further appends move the log
            // well past every one of those sizes (SG20: "never a stale
            // intermediate one" -- but also never anything other than
            // exactly what was written at that historical size).
            for i in n_max..(n_max + 10) {
                log.append_leaf(format!("leaf-{i}").as_bytes())
                    .await
                    .unwrap();
            }
            for n in 0..=n_max {
                let got = log.storage().tree_at(n).unwrap();
                assert_eq!(
                    got, written_at[n as usize],
                    "k={k}: tree_at({n}) must still equal the size-{n} checkpoint after further \
                     appends"
                );
            }

            // tree_at(current size) must equal the staging ref's own target.
            let current_tip = support::ref_target(&repo.to_thread_local(), &staging).unwrap();
            assert_eq!(log.storage().tree_at(n_max + 10).unwrap(), current_tip);

            // tree_at(n) for n beyond the current size must be an error, not
            // a fabricated value.
            assert!(
                log.storage().tree_at(n_max + 11).is_err(),
                "tree_at beyond the current size must error, not fabricate a value"
            );
        }
    });
}

/// Isolates the exact cause of the failure above: [SG20] requires
/// `tree_at(n)`'s object to be the checkpoint the layout actually wrote at
/// size `n`, and [SG14]/§3.3 require `roots/` to carry an entry for every
/// algorithm active at that size. The tree *actually written* live at n=1
/// carries `roots/hex(0,16)` (algorithm 0 is active). Once the log has
/// moved past n=1 and `tree_at(1)` must *reconstruct* C(1), the
/// reconstruction comes back with an empty `roots/` instead -- dropping the
/// entry SG14 requires and producing a different object than SG20 requires.
#[test]
fn sg20_reconstructed_roots_disagree_with_the_roots_actually_written() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg20-roots/staging";
        let mut log = new_log(&repo, staging, 2, FixtureHasher::new(32)).await;
        log.append_leaf(b"leaf-0").await.unwrap();

        let local = repo.to_thread_local();
        let written_at_1 = support::ref_target(&local, staging).unwrap();
        let roots_written = support::find_entry(&local, written_at_1, "roots")
            .unwrap()
            .oid;
        let roots_written_entries = support::read_tree(&local, roots_written);
        assert_eq!(
            roots_written_entries.len(),
            1,
            "the tree actually written live at n=1 must carry roots/hex(0,16) (alg 0 is active, \
             SG14)"
        );

        for i in 1..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let reconstructed_1 = log.storage().tree_at(1).unwrap();
        let roots_reconstructed = support::find_entry(&local, reconstructed_1, "roots")
            .unwrap()
            .oid;
        let roots_reconstructed_entries = support::read_tree(&local, roots_reconstructed);
        assert_eq!(
            roots_reconstructed_entries.len(),
            1,
            "tree_at(1)'s roots/ must carry the same active-algorithm entry the tree written live \
             at n=1 carried (SG14/SG20)"
        );
        assert_eq!(
            reconstructed_1, written_at_1,
            "tree_at(1) must be byte-identical to the checkpoint actually written at n=1 (SG20)"
        );
    });
}
