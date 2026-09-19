//! Kind derivation and non-optional log metadata (head's ruling,
//! 2026-09-17, requirements A and B), on [`FjallStorage`]. `polydigest`'s own
//! `tests/kind_and_meta.rs` carries the identical claim over `MemoryStorage`;
//! `storage-git`'s own copy carries it over `GitStorage`. See that file's
//! doc comment for the full derivation this pins.

use polydigest::{Hasher, LogError, LogKind, NaryMerkleLog, Storage, Subtree, TreeConfig};
use sha2::{Digest, Sha256};
use storage_fjall::FjallStorage;
use tempfile::tempdir;

#[derive(Debug, Clone)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

fn hashers(ids: impl IntoIterator<Item = u64>) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.into_iter()
        .map(|id| (id, Box::new(Sha256Hasher) as Box<dyn Hasher>))
        .collect()
}

/// [KIND DERIVATION] A flat log reopens as `LogKind::Flat` from a
/// `FjallStorage` alone.
#[test]
fn flat_log_reopens_as_flat() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut log = NaryMerkleLog::new(
            FjallStorage::open(dir.path()).unwrap(),
            Box::new(Sha256Hasher),
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

        let storage = FjallStorage::open(dir.path()).unwrap();
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
/// `LogKind::Subtree`.
#[test]
fn subtree_from_genesis_log_reopens_as_subtree() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut log = NaryMerkleLog::new(
            FjallStorage::open(dir.path()).unwrap(),
            Box::new(Sha256Hasher),
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

        let storage = FjallStorage::open(dir.path()).unwrap();
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

/// [KIND DERIVATION] A log resumed onto fresh `FjallStorage` reopens as
/// `LogKind::Subtree`.
#[test]
fn resumed_log_reopens_as_subtree() {
    smol::block_on(async {
        let src_dir = tempdir().unwrap();
        let mut src = NaryMerkleLog::new(
            FjallStorage::open(src_dir.path()).unwrap(),
            Box::new(Sha256Hasher),
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

        let dst_dir = tempdir().unwrap();
        let mut resumed = NaryMerkleLog::resume(
            &sealed,
            FjallStorage::open(dst_dir.path()).unwrap(),
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

        let storage = FjallStorage::open(dst_dir.path()).unwrap();
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
/// append kind on reopen.
#[test]
fn empty_log_reopens_accepting_either_append() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let src = NaryMerkleLog::new(
            FjallStorage::open(dir.path()).unwrap(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        drop(src);

        let storage = FjallStorage::open(dir.path()).unwrap();
        assert_eq!(storage.append_count().await.unwrap(), 0);
        let mut flat_leg = NaryMerkleLog::from_storage(storage, hashers([0]))
            .await
            .unwrap();
        flat_leg.append_leaf(b"a").await.unwrap();
        assert_eq!(flat_leg.kind(), LogKind::Flat);
    });
}

/// [NON-OPTIONAL META] `append_count` is authoritative after every one of
/// the five operations and after a reopen from disk.
#[test]
fn append_count_is_authoritative_after_every_operation_and_reopen() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut log = NaryMerkleLog::new(
            FjallStorage::open(dir.path()).unwrap(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 0);

        log.append_leaf(b"a").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 1);

        log.append_leaf(b"b").await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 2);

        log.remove_algorithm(1).await.unwrap();
        log.append_leaf(b"c").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        assert_eq!(log.storage().append_count().await.unwrap(), 3);
        drop(log);

        let reopened_storage = FjallStorage::open(dir.path()).unwrap();
        assert_eq!(reopened_storage.append_count().await.unwrap(), 3);
        let reopened = NaryMerkleLog::from_storage(reopened_storage, hashers([0, 1]))
            .await
            .unwrap();
        assert_eq!(reopened.count(), 3);
    });
}
