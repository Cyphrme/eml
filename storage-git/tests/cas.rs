//! Staging-ref and compare-and-swap tests: SG17, SG18, SG19, SG25.

mod common;

use common::init_repo;
use gix::hash::Kind as HashKind;
use polydigest::Storage;
use storage_git::GitStorage;

const STAGING: &str = "refs/eml/storage/cas/staging";

/// SG17: the staging ref's target is a tree object, never a commit.
#[test]
fn sg17_staging_ref_points_at_a_tree() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage = GitStorage::new(repo.clone(), STAGING, 2).unwrap();
        storage.store_leaf(0, b"leaf0").await.unwrap();

        let local = repo.to_thread_local();
        let r = local.find_reference(STAGING).unwrap();
        let id = r.target().id().to_owned();
        let header = local.find_header(id).unwrap();
        assert_eq!(header.kind(), gix::objs::Kind::Tree);
    });
}

/// SG18/SG19/SG25: a second instance whose observed tip has gone stale
/// (another writer moved the ref) gets the distinguished tip-moved error on
/// its own write, and the ref is left exactly at the first writer's value --
/// never moved by the failed attempt, never left in a third, partial state.
///
/// Arity 8 keeps every index used here below the first carry reduction
/// (`reduction_count` stays 0 through index 6), so a bare `store_leaf` call
/// -- which, unlike `write_batch`, carries no digest for a merge it can't
/// compute without a hasher -- never needs one; the CAS behavior under test
/// is orthogonal to that.
#[test]
fn sg19_stale_writer_gets_tip_moved_and_ref_is_unmoved() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);

        let mut writer_a = GitStorage::new(repo.clone(), STAGING, 8).unwrap();
        writer_a.store_leaf(0, b"a0").await.unwrap();

        // writer_b opens the ref at the same point writer_a started from,
        // then writer_a advances again before writer_b's own write lands.
        let mut writer_b = GitStorage::new(repo.clone(), STAGING, 8).unwrap();
        writer_a.store_leaf(1, b"a1").await.unwrap();

        let local = repo.to_thread_local();
        let tip_after_a = local
            .find_reference(STAGING)
            .unwrap()
            .target()
            .id()
            .to_owned();

        let result = writer_b.store_leaf(1, b"b1-conflicting").await;
        assert!(result.is_err(), "stale writer's CAS must fail");
        assert!(
            result.unwrap_err().is_tip_moved(),
            "failure must be the distinguished tip-moved variant"
        );

        let tip_after_failed_b = local
            .find_reference(STAGING)
            .unwrap()
            .target()
            .id()
            .to_owned();
        assert_eq!(
            tip_after_a, tip_after_failed_b,
            "a failed compare-and-swap must never move the ref (SG19/SG25)"
        );

        // The object writer_b attempted to write is simply unreferenced
        // garbage now; a fresh read through the ref must still see writer_a's
        // committed value, not writer_b's.
        let reader = GitStorage::new(repo, STAGING, 8).unwrap();
        assert_eq!(reader.get_leaf(1).await.unwrap(), b"a1");
    });
}

/// A fresh instance's genesis write uses `MustNotExist`; a second instance
/// racing the very first write also gets tip-moved, not some other error
/// shape, confirming the CAS discipline holds at genesis too.
#[test]
fn sg19_genesis_race_is_also_tip_moved() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut first = GitStorage::new(repo.clone(), STAGING, 2).unwrap();
        let mut racer = GitStorage::new(repo, STAGING, 2).unwrap();

        first.store_leaf(0, b"first").await.unwrap();
        let result = racer.store_leaf(0, b"racer").await;
        assert!(result.is_err());
        assert!(result.unwrap_err().is_tip_moved());
    });
}
