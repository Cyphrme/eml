//! Kind derivation and non-optional log metadata (head's ruling,
//! 2026-09-17, requirements A and B), on [`GitStorage`]. `polydigest`'s own
//! `tests/kind_and_meta.rs` carries the identical claim over `MemoryStorage`;
//! `storage-fjall`'s own copy carries it over `FjallStorage`. See that
//! file's doc comment for the full derivation this pins.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, LogError, LogKind, NaryMerkleLog, Storage, Subtree, TreeConfig};
use storage_git::GitStorage;

fn hashers(ids: impl IntoIterator<Item = u64>) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.into_iter()
        .map(|id| (id, Box::new(WideHasher) as Box<dyn Hasher>))
        .collect()
}

/// [KIND DERIVATION] A flat log reopens as `LogKind::Flat` from a `GitStorage`
/// alone -- `len() > 0` is the flat signal, never a stored byte.
#[test]
fn flat_log_reopens_as_flat() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/flat/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_root = log.root();
        drop(log);

        let storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert!(storage.len().await.unwrap() > 0);
        let mut reopened = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        assert_eq!(reopened.kind(), LogKind::Flat);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);

        let err = reopened
            .append_subtree(&Subtree::Leaf(b"x".to_vec()))
            .await
            .unwrap_err();
        assert!(matches!(err, LogError::CorruptedMetadata { .. }));
    });
}

/// [KIND DERIVATION] A subtree-appended-from-genesis log reopens as
/// `LogKind::Subtree` -- a nonzero append count with `len() == 0`.
#[test]
fn subtree_from_genesis_log_reopens_as_subtree() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/subtree/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..4u32 {
            log.append_subtree(&Subtree::Leaf(format!("s-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_root = log.root();
        drop(log);

        let storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(storage.len().await.unwrap(), 0);
        assert!(storage.append_count().await.unwrap() > 0);
        let mut reopened = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        assert_eq!(reopened.kind(), LogKind::Subtree);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);

        let err = reopened.append_leaf(b"x").await.unwrap_err();
        assert!(matches!(err, LogError::CorruptedMetadata { .. }));
    });
}

/// [KIND DERIVATION] A log resumed onto fresh `GitStorage` reopens as
/// `LogKind::Subtree`: the inherited prefix and any forward subtree appends
/// never populate the leaf keyspace.
#[test]
fn resumed_log_reopens_as_subtree() {
    smol::block_on(async {
        let (_dir_src, repo_src) = init_repo(HashKind::Sha1);
        let mut src = NaryMerkleLog::new(
            GitStorage::new(repo_src, "refs/eml/storage/kind-meta/src/staging", 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            src.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = src.seal().await.unwrap();

        let (dir_dst, repo_dst) = init_repo(HashKind::Sha1);
        let staging_dst = "refs/eml/storage/kind-meta/resumed/staging";
        let mut resumed = NaryMerkleLog::resume(
            &sealed,
            GitStorage::new(repo_dst, staging_dst, 2).unwrap(),
            hashers([0]),
        )
        .await
        .unwrap();
        for i in 0..2u32 {
            resumed
                .append_subtree(&Subtree::Leaf(format!("fwd-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = resumed.count();
        let expected_root = resumed.root();
        drop(resumed);

        let storage = GitStorage::open(dir_dst.path(), staging_dst, 2).unwrap();
        assert_eq!(storage.len().await.unwrap(), 0);
        let reopened = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        assert_eq!(reopened.kind(), LogKind::Subtree);
        assert_eq!(reopened.count(), expected_count);
        assert_eq!(reopened.root(), expected_root);
    });
}

/// [KIND DERIVATION] An empty log (`append_count == 0`) accepts either
/// append kind on reopen, same as a freshly constructed one.
#[test]
fn empty_log_reopens_accepting_either_append() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/empty/staging";
        let src = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        drop(src);

        let storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(storage.append_count().await.unwrap(), 0);
        let mut flat_leg = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        flat_leg.append_leaf(b"a").await.unwrap();
        assert_eq!(flat_leg.kind(), LogKind::Flat);

        let storage2 = GitStorage::open(dir.path(), staging, 2).unwrap();
        let mut subtree_leg = NaryMerkleLog::from_storage(storage2, hashers([0]))
            .await
            .unwrap();
        subtree_leg
            .append_subtree(&Subtree::Leaf(b"b".to_vec()))
            .await
            .unwrap();
        assert_eq!(subtree_leg.kind(), LogKind::Subtree);
    });
}

/// [NON-OPTIONAL META] `append_count` is authoritative after every one of
/// the five operations and after a reopen from disk.
#[test]
fn append_count_is_authoritative_after_every_operation_and_reopen() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/append-count/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 0);

        log.append_leaf(b"a").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.append_leaf(b"b").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 2);

        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 3);
        drop(log);

        let reopened_storage = GitStorage::open(dir.path(), staging, 2).unwrap();
        assert_eq!(reopened_storage.append_count().await.unwrap(), 3);
        let reopened = NaryMerkleLog::from_storage(reopened_storage, hashers([0, 1]))
            .await
            .unwrap();
        assert_eq!(reopened.count(), 3);
    });
}

/// [METADATA ACCESSOR] `GitStorage::metadata()` reports the live instance's
/// own `(count, kind)`, matching the polydigest-level `NaryMerkleLog`
/// accessors driving it -- so a caller (e.g. the checkpoint layer) never
/// needs to decode `meta`'s bytes or re-derive kind itself.
#[test]
fn git_storage_metadata_accessor_matches_the_live_log() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/accessor/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }

        let meta = log.storage().metadata();
        assert_eq!(meta.count, log.count());
        assert_eq!(meta.kind, log.kind());
    });
}

/// [METADATA ACCESSOR] `GitReadOnlyView::metadata()` reports the checkpoint
/// tree's own `(count, kind)` -- the read-only-view peer of
/// `GitStorage::metadata`, independent of the live instance that produced
/// the tree.
#[test]
fn git_read_only_view_metadata_accessor_matches_the_checkpoint() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kind-meta/accessor-view/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo, staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            log.append_subtree(&Subtree::Leaf(format!("s-{i}").into_bytes()))
                .await
                .unwrap();
        }
        let expected_count = log.count();
        let expected_kind = log.kind();
        let tip = log.storage().tip_tree().unwrap();

        let view = log.storage().open_at(tip).unwrap();
        let meta = view.metadata();
        assert_eq!(meta.count, expected_count);
        assert_eq!(meta.kind, expected_kind);
    });
}
