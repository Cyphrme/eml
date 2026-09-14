//! Acceptance tests for §4.2's staging ref and compare-and-swap writes
//! (SG17, SG18, SG19) and §5's crash-safety claim about the staging ref
//! (SG25), from `docs/specs/storage-git.md` alone.

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::Storage;
use support::{FixtureHasher, bare_repo, new_log, object_kind, ref_target, reopen_repo};

/// [SG17] The staging ref's target MUST always be a tree object, `C(n)` for
/// the instance's current `n`; it MUST NOT be a commit.
#[test]
fn sg17_staging_ref_targets_a_tree_never_a_commit() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg17/staging";
        let mut log = new_log(&repo, staging, 2, FixtureHasher::new(32)).await;
        let local = repo.to_thread_local();

        for i in 0..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
            let target = ref_target(&local, staging).unwrap();
            assert_eq!(
                object_kind(&local, target),
                gix::objs::Kind::Tree,
                "the staging ref must always target a tree, never a commit"
            );
        }
    });
}

/// [SG19] If the compare-and-swap precondition fails, the write MUST fail
/// as a whole, MUST NOT move the ref, and MUST return a distinguished
/// tip-moved error. [SG25] There is no partial-batch state a reader can
/// observe through the staging ref: after any write attempt (successful or
/// not), the ref is at exactly one of the two values a writer could
/// legitimately have left it at -- never a third state.
#[test]
fn sg19_sg25_concurrent_writer_gets_tip_moved_and_ref_never_moves_on_failure() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg19/staging";
        let local = repo.to_thread_local();

        // Two independent writer instances against the same ref, as two
        // racing processes would be -- both currently observe "no ref yet"
        // (genesis).
        let mut writer_a =
            storage_git::GitStorage::new(repo.clone(), staging, 10).expect("open writer A");
        let mut writer_b =
            storage_git::GitStorage::new(repo.clone(), staging, 10).expect("open writer B");

        assert!(
            ref_target(&local, staging).is_none(),
            "sanity: no ref yet before either writer commits"
        );

        // Writer A wins the genesis race.
        writer_a
            .store_leaf(0, b"from-a")
            .await
            .expect("writer A's genesis write must succeed");
        let tip_after_a = ref_target(&local, staging).expect("ref must exist after A's write");

        // Writer B, still holding the pre-A observation (no ref), now
        // attempts its own genesis write and must lose.
        let result_b = writer_b.store_leaf(0, b"from-b").await;
        let err = result_b.expect_err(
            "writer B's stale genesis write must fail, not silently overwrite A's data",
        );
        assert!(
            err.is_tip_moved(),
            "the CAS failure must surface as the distinguished tip-moved variant, not a generic \
             error"
        );

        let tip_after_failed_b = ref_target(&local, staging).expect("ref must still exist");
        assert_eq!(
            tip_after_failed_b, tip_after_a,
            "a failed CAS must never move the ref away from the winning writer's value"
        );

        // The failed attempt's own object may exist unreferenced, but the
        // ref itself must never be observed anywhere but A's tip or (were
        // this a real crash) the value it held immediately before -- there
        // is no ref state that is neither.
        assert!(
            ref_target(&local, staging) == Some(tip_after_a),
            "SG25: after the failed write, the ref must be observed at exactly the value a \
             legitimate writer left it at"
        );

        // Per SG19, the caller reloads and retries: a fresh instance built
        // against the ref's *current* value succeeds.
        let mut writer_b_retry = storage_git::GitStorage::new(reopen_repo(dir.path()), staging, 10)
            .expect("reopen for retry");
        writer_b_retry
            .store_leaf(1, b"from-b-retry")
            .await
            .expect("a reloaded writer must be able to append next");
        let tip_after_retry = ref_target(&local, staging).unwrap();
        assert_ne!(
            tip_after_retry, tip_after_a,
            "the successful retry must move the ref forward"
        );
    });
}

/// [SG18d] Every non-batched mutating method (here, a second `store_leaf`
/// through the same stale instance) goes through the identical
/// compare-and-swap path as `write_batch` -- it must not bypass CAS
/// protection just because it is not literally routed through
/// `write_batch` at the call site.
#[test]
fn sg18d_standalone_methods_share_the_same_cas_path() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg18d/staging";
        let local = repo.to_thread_local();

        let mut writer_a =
            storage_git::GitStorage::new(repo.clone(), staging, 10).expect("open writer A");
        let mut writer_b =
            storage_git::GitStorage::new(repo.clone(), staging, 10).expect("open writer B");

        writer_a.store_leaf(0, b"a0").await.unwrap();
        writer_a.store_leaf(1, b"a1").await.unwrap();
        let tip_after_a = ref_target(&local, staging).unwrap();

        // writer_b is stale from before either of A's writes; its next
        // standalone store_algorithm_meta call must also be CAS-protected.
        let result = writer_b.store_algorithm_meta(0, &[(0, u64::MAX)]).await;
        assert!(
            result.is_err_and(|e| e.is_tip_moved()),
            "a standalone store_algorithm_meta must go through the same CAS path as write_batch"
        );
        assert_eq!(
            ref_target(&local, staging).unwrap(),
            tip_after_a,
            "the rejected standalone write must not move the ref"
        );
    });
}
