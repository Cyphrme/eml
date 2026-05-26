use eml::{Hasher, Log, Storage, verify_inclusion};
use eml_storage_fjall::FjallStorage;
use sha2::{Digest, Sha256};
use tempfile::tempdir;

#[derive(Debug, Clone)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

#[tokio::test]
async fn test_low_level_storage_api() {
    let dir = tempdir().unwrap();
    let mut storage = FjallStorage::open(dir.path()).unwrap();

    // 1. Test len on empty database
    assert_eq!(storage.len().await, 0);

    // 2. Test leaves read/write
    storage.store_leaf(0, b"leaf0").await.unwrap();
    storage.store_leaf(1, b"leaf1").await.unwrap();
    assert_eq!(storage.len().await, 2);
    assert_eq!(storage.get_leaf(0).await.unwrap(), b"leaf0");
    assert_eq!(storage.get_leaf(1).await.unwrap(), b"leaf1");

    // 3. Test leaf not found
    let err = storage.get_leaf(2).await;
    assert!(err.is_err());

    // 4. Test nodes read/write
    let alg_id = 42u64;
    storage.store_node(alg_id, 0, 1, b"hash_0_1").await.unwrap();
    storage.store_node(alg_id, 2, 2, b"hash_2_2").await.unwrap();

    assert_eq!(
        storage.get_node(alg_id, 0, 1).await.unwrap().unwrap(),
        b"hash_0_1"
    );
    assert_eq!(
        storage.get_node(alg_id, 2, 2).await.unwrap().unwrap(),
        b"hash_2_2"
    );
    assert!(storage.get_node(alg_id, 0, 2).await.unwrap().is_none());

    // 5. Test algorithm metadata read/write
    let epochs_a = vec![(0, 100), (200, 300)];
    let epochs_b = vec![(10, 50)];
    storage.store_algorithm_meta(1, &epochs_a).await.unwrap();
    storage.store_algorithm_meta(2, &epochs_b).await.unwrap();

    let mut metas = storage.load_algorithm_metas().await.unwrap();
    metas.sort_by_key(|&(id, _)| id);
    assert_eq!(metas.len(), 2);
    assert_eq!(metas[0], (1, epochs_a));
    assert_eq!(metas[1], (2, epochs_b));
}

#[tokio::test]
async fn test_write_batch() {
    let dir = tempdir().unwrap();
    let mut storage = FjallStorage::open(dir.path()).unwrap();

    let leaves = vec![(0, b"data0".as_slice()), (1, b"data1".as_slice())];
    let nodes = vec![
        (1, 0, 1, b"node0".as_slice()),
        (1, 2, 2, b"node1".as_slice()),
    ];

    storage.write_batch(&leaves, &nodes).await.unwrap();

    assert_eq!(storage.len().await, 2);
    assert_eq!(storage.get_leaf(0).await.unwrap(), b"data0");
    assert_eq!(storage.get_leaf(1).await.unwrap(), b"data1");
    assert_eq!(storage.get_node(1, 0, 1).await.unwrap().unwrap(), b"node0");
    assert_eq!(storage.get_node(1, 2, 2).await.unwrap().unwrap(), b"node1");
}

#[tokio::test]
async fn test_eml_log_integration_and_cold_start() {
    let dir = tempdir().unwrap();
    let db_path = dir.path().to_path_buf();
    let hasher_id = 99u64;

    // Phase 1: Initialize log, add algorithm, append entries
    {
        let storage = FjallStorage::open(&db_path).unwrap();
        let mut log = Log::new(storage);

        log.add_algorithm(hasher_id, Box::new(Sha256Hasher))
            .await
            .unwrap();
        log.append(b"apple").await.unwrap();
        log.append(b"banana").await.unwrap();
        log.append(b"cherry").await.unwrap();

        assert_eq!(log.size().await, 3);

        // Get root and check proof
        let root = log.root(hasher_id).unwrap();
        let proof = log.inclusion_proof(hasher_id, 1).await.unwrap();

        let leaf_hash = Sha256Hasher.leaf(b"banana");
        let verified = verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root);
        assert!(verified);
    }

    // Phase 2: Close log and reconstruct from storage (Cold Start)
    {
        let storage = FjallStorage::open(&db_path).unwrap();
        let hashers: Vec<(u64, Box<dyn Hasher>)> = vec![(hasher_id, Box::new(Sha256Hasher))];
        let mut log = Log::from_storage(storage, hashers).await.unwrap();

        // Check if state was correctly reconstructed
        assert_eq!(log.size().await, 3);

        let root = log.root(hasher_id).unwrap();
        let proof = log.inclusion_proof(hasher_id, 1).await.unwrap();

        let leaf_hash = Sha256Hasher.leaf(b"banana");
        let verified = verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root);
        assert!(verified);

        // Phase 3: Continue appends on reconstructed log
        log.append(b"date").await.unwrap();
        assert_eq!(log.size().await, 4);

        let new_root = log.root(hasher_id).unwrap();
        assert_ne!(root, new_root);
    }
}

#[tokio::test]
async fn test_concurrency_and_race_conditions() {
    use std::sync::Arc;

    use tokio::sync::Barrier;

    let dir = tempdir().unwrap();
    let storage = FjallStorage::open(dir.path()).unwrap();

    let num_tasks = 20;
    let barrier = Arc::new(Barrier::new(num_tasks));
    let mut handles = Vec::new();

    for i in 0..num_tasks {
        let mut local_storage = storage.clone(); // Clone is cheap, shares keyspace handle
        let barrier_clone = barrier.clone();

        let handle = tokio::spawn(async move {
            // Wait for all threads to align
            barrier_clone.wait().await;

            // 1. Perform concurrent write
            local_storage
                .store_leaf(i as u64, format!("leaf_payload_{i}").as_bytes())
                .await
                .unwrap();

            // 2. Perform concurrent read of our own write
            let data = local_storage.get_leaf(i as u64).await.unwrap();
            assert_eq!(data, format!("leaf_payload_{i}").as_bytes());

            // 3. Perform concurrent node operations
            local_storage
                .store_node(100, i as u64, 2, format!("node_hash_{i}").as_bytes())
                .await
                .unwrap();

            let node_data = local_storage
                .get_node(100, i as u64, 2)
                .await
                .unwrap()
                .unwrap();
            assert_eq!(node_data, format!("node_hash_{i}").as_bytes());
        });

        handles.push(handle);
    }

    // Wait for all concurrent tasks to complete
    for handle in handles {
        handle.await.unwrap();
    }

    // Verify all keys were successfully persisted
    assert_eq!(storage.len().await, num_tasks as u64);
    for i in 0..num_tasks {
        let data = storage.get_leaf(i as u64).await.unwrap();
        assert_eq!(data, format!("leaf_payload_{i}").as_bytes());
    }
}

#[tokio::test]
async fn test_double_open_locking() {
    let dir = tempdir().unwrap();
    // Open first storage driver instance
    let _storage1 = FjallStorage::open(dir.path()).unwrap();
    // Opening a second instance pointing to the same path should fail due to process-level locking
    let storage2 = FjallStorage::open(dir.path());
    assert!(storage2.is_err());
}
