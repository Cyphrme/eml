use eml_log::{Hasher, NaryMerkleLog, Storage, TreeConfig};
use neml_storage_fjall::FjallStorage;
use sha2::{Digest, Sha256};
use tempfile::tempdir;

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children {
            h.update(child);
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
        Box::new(Sha256Hasher)
    }
}

#[test]
fn test_fjall_storage_basic_ops() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut storage = FjallStorage::open(dir.path()).unwrap();

        // Init
        assert_eq!(storage.len().await.unwrap(), 0);

        // Leaf ops
        storage.store_leaf(0, b"leaf0").await.unwrap();
        storage.store_leaf(1, b"leaf1").await.unwrap();
        assert_eq!(storage.len().await.unwrap(), 2);
        assert_eq!(storage.get_leaf(0).await.unwrap(), b"leaf0");
        assert_eq!(storage.get_leaf(1).await.unwrap(), b"leaf1");

        // Node ops
        storage.store_node(0, 100, 0, b"hash100").await.unwrap();
        assert_eq!(
            storage.get_node(0, 100, 0).await.unwrap().unwrap(),
            b"hash100"
        );
        assert!(storage.get_node(0, 999, 0).await.unwrap().is_none());

        // Metadata ops
        let epochs = vec![(0, 10), (15, 20)];
        storage.store_algorithm_meta(0, &epochs).await.unwrap();
        let loaded = storage.load_algorithm_metas().await.unwrap();
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].0, 0);
        assert_eq!(loaded[0].1, epochs);
    });
}

#[test]
fn test_fjall_log_integration_and_recovery() {
    smol::block_on(async {
        let dir = tempdir().unwrap();

        // Step 1: Build a log and write elements
        let root0;
        let root1;
        {
            let storage = FjallStorage::open(dir.path()).unwrap();
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();

            log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

            log.append_leaf(b"hello").await.unwrap();
            log.append_leaf(b"world").await.unwrap();

            log.remove_algorithm(1).await.unwrap();

            log.append_leaf(b"rust").await.unwrap();

            root0 = log.root_for(0).unwrap();
            root1 = log.root_for(1).unwrap();

            assert_eq!(log.size(), 3);
        }

        // Step 2: Open a new log with the same storage and check recovery
        {
            let storage = FjallStorage::open(dir.path()).unwrap();
            let reconstructed = NaryMerkleLog::from_storage(
                storage,
                vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
            )
            .await
            .unwrap();

            assert_eq!(reconstructed.size(), 3);
            assert_eq!(reconstructed.root_for(0).unwrap(), root0);
            assert_eq!(reconstructed.root_for(1).unwrap(), root1);
        }
    });
}

#[test]
fn test_fjall_metadata_corruption() {
    smol::block_on(async {
        let dir = tempdir().unwrap();

        // 1. Write corrupted key length (< 8 bytes)
        {
            let db = fjall::Database::builder(dir.path()).open().unwrap();
            let metadata = db
                .keyspace("neml_metadata", fjall::KeyspaceCreateOptions::default)
                .unwrap();
            metadata.insert(b"short", [0; 16]).unwrap();
        }

        let storage = FjallStorage::open(dir.path()).unwrap();
        let metas_res = storage.load_algorithm_metas().await;
        assert!(metas_res.is_err());

        // Try from_storage
        let log_res = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))]).await;
        assert!(log_res.is_err());
    });

    smol::block_on(async {
        let dir = tempdir().unwrap();

        // 2. Write corrupted value length (not a multiple of 16)
        {
            let db = fjall::Database::builder(dir.path()).open().unwrap();
            let metadata = db
                .keyspace("neml_metadata", fjall::KeyspaceCreateOptions::default)
                .unwrap();
            metadata.insert(0u64.to_be_bytes(), [0; 15]).unwrap();
        }

        let storage = FjallStorage::open(dir.path()).unwrap();
        let metas_res = storage.load_algorithm_metas().await;
        assert!(metas_res.is_err());

        // Try from_storage
        let log_res = NaryMerkleLog::from_storage(storage, vec![(0, Box::new(Sha256Hasher))]).await;
        assert!(log_res.is_err());
    });
}

// FjallStorage is intentionally not Clone; single-writer ownership is
// enforced at compile time.  The concurrent-clone race test that existed
// here was testing the unsound behaviour we eliminated; it is removed.

#[test]
fn test_fjall_out_of_order_and_sparse() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let mut storage = FjallStorage::open(dir.path()).unwrap();

        // Store index 10 first
        storage.store_leaf(10, b"index10").await.unwrap();

        // len() should return 11 (highest key + 1)
        assert_eq!(storage.len().await.unwrap(), 11);

        // index 10 should be found
        assert_eq!(storage.get_leaf(10).await.unwrap(), b"index10");

        // indices 0..10 should return NotFound
        for i in 0..10 {
            assert!(storage.get_leaf(i).await.is_err());
        }

        // Store index 5
        storage.store_leaf(5, b"index5").await.unwrap();

        // len() should still be 11
        assert_eq!(storage.len().await.unwrap(), 11);

        // index 5 should be found
        assert_eq!(storage.get_leaf(5).await.unwrap(), b"index5");

        // index 10 should still be found
        assert_eq!(storage.get_leaf(10).await.unwrap(), b"index10");
    });
}
