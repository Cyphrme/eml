//! Fault injection crash-recovery tests for neml.

use std::sync::{Arc, Mutex};
use neml::{
    Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig,
};
use sha2::{Digest, Sha256};

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

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(Sha256Hasher)
    }
}

#[derive(Debug, Clone)]
struct FaultInjectingStorage {
    inner: MemoryStorage,
    fail_after_writes: Arc<Mutex<Option<usize>>>,
    write_count: Arc<Mutex<usize>>,
}

impl FaultInjectingStorage {
    fn new(inner: MemoryStorage) -> Self {
        Self {
            inner,
            fail_after_writes: Arc::new(Mutex::new(None)),
            write_count: Arc::new(Mutex::new(0)),
        }
    }

    fn set_fail_after_writes(&self, count: Option<usize>) {
        *self.fail_after_writes.lock().unwrap() = count;
        *self.write_count.lock().unwrap() = 0;
    }
}

#[derive(Debug)]
pub enum FaultError {
    Injected,
    Storage,
}

impl std::fmt::Display for FaultError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for FaultError {}

impl Storage for FaultInjectingStorage {
    type Error = FaultError;

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        let should_fail = {
            let mut count = self.write_count.lock().unwrap();
            let limit = self.fail_after_writes.lock().unwrap();
            if let Some(limit) = *limit {
                if *count >= limit {
                    true
                } else {
                    *count += 1;
                    false
                }
            } else {
                *count += 1;
                false
            }
        };

        if should_fail {
            return Err(FaultError::Injected);
        }

        self.inner
            .store_leaf(index, data)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.inner
            .get_leaf(index)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn len(&self) -> u64 {
        self.inner.len().await
    }

    async fn store_node(&mut self, alg_id: u64, node_id: u64, hash: &[u8]) -> Result<(), Self::Error> {
        let should_fail = {
            let mut count = self.write_count.lock().unwrap();
            let limit = self.fail_after_writes.lock().unwrap();
            if let Some(limit) = *limit {
                if *count >= limit {
                    true
                } else {
                    *count += 1;
                    false
                }
            } else {
                *count += 1;
                false
            }
        };

        if should_fail {
            return Err(FaultError::Injected);
        }

        self.inner
            .store_node(alg_id, node_id, hash)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn get_node(&self, alg_id: u64, node_id: u64) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner
            .get_node(alg_id, node_id)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn store_algorithm_meta(&mut self, alg_id: u64, epochs: &[(u64, u64)]) -> Result<(), Self::Error> {
        self.inner
            .store_algorithm_meta(alg_id, epochs)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn load_algorithm_metas(&self) -> Result<neml::AlgorithmMetas, Self::Error> {
        self.inner
            .load_algorithm_metas()
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, &[u8])],
    ) -> Result<(), Self::Error> {
        let backup = self.inner.clone();

        for &(index, data) in leaves {
            if let Err(e) = self.store_leaf(index, data).await {
                self.inner = backup;
                return Err(e);
            }
        }

        for &(alg_id, node_id, hash) in nodes {
            if let Err(e) = self.store_node(alg_id, node_id, hash).await {
                self.inner = backup;
                return Err(e);
            }
        }

        Ok(())
    }
}

#[test]
fn test_mid_batch_failure_recovery() {
    smol::block_on(async {
        let storage = FaultInjectingStorage::new(MemoryStorage::new());
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage.clone(), Box::new(Sha256Hasher), config).await;

        for i in 0..10 {
            log.append_leaf(&[i]).await.unwrap();
        }

        let root_before = log.root();
        let size_before = log.size();
        assert_eq!(size_before, 10);

        storage.set_fail_after_writes(Some(1));

        let append_res = log.append_leaf(&[10]).await;
        assert!(append_res.is_err());

        let final_storage = log.into_storage();
        let reconstructed = NaryMerkleLog::from_storage(
            final_storage,
            vec![(0, Box::new(Sha256Hasher))],
        )
        .await
        .unwrap();

        assert_eq!(reconstructed.size(), size_before);
        assert_eq!(reconstructed.root(), root_before);

        storage.set_fail_after_writes(None);
        let mut reconstructed = reconstructed;
        reconstructed.append_leaf(&[10]).await.unwrap();
        assert_eq!(reconstructed.size(), 11);
    });
}

#[test]
fn test_verify_non_divergence_tamper_detection() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

        // Populate log
        for i in 0..15u8 {
            log.append_leaf(&[i]).await.unwrap();
        }
        
        // Assert clean state passes
        assert!(log.verify_non_divergence(None, &[]).await.unwrap());

        // 1. Leaf data tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Mutate leaf 7 payload
            tampered_storage.leaves[7] = vec![0xFF; 16];
            let tampered_log = NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))]).await.unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered leaf data"
            );
        }

        // 2. Internal node hash tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Find an internal node and tamper it
            let key = (0, 3); // (alg_id, node_id)
            if let std::collections::hash_map::Entry::Occupied(mut e) = tampered_storage.nodes.entry(key) {
                e.insert(vec![0x00; 32]);
                let tampered_log = NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))]).await.unwrap();
                assert!(
                    !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                    "Failed to detect tampered internal node hash"
                );
            }
        }

        // 3. Epoch metadata tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Shorten the active epoch interval for algorithm 0
            if let Some(epochs) = tampered_storage.algorithm_metas.get_mut(&0) {
                if !epochs.is_empty() {
                    epochs[0].1 = 10; // set arbitrary frozen boundary where it should be active (u64::MAX)
                }
            }
            let tampered_log = NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))]).await.unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered epoch metadata"
            );
        }
    });
}

#[test]
fn test_verify_non_divergence_legitimate_frozen() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

        // Add alg 1
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        // Append 5 leaves
        for i in 0..5 {
            log.append_leaf(&[i]).await.unwrap();
        }

        // Deactivate alg 1 at size 5
        log.remove_algorithm(1).await.unwrap();

        // Append 5 more leaves (so global size is 10, but alg 1 is frozen at 5)
        for i in 5..10 {
            log.append_leaf(&[i]).await.unwrap();
        }

        // Verify clean log: verify_non_divergence should return Ok(true)
        let metas = vec![
            (0, Box::new(Sha256Hasher) as Box<dyn Hasher>),
            (1, Box::new(Sha256Hasher) as Box<dyn Hasher>),
        ];
        let reconstructed = NaryMerkleLog::from_storage(log.storage().clone(), metas).await.unwrap();
        assert!(
            reconstructed.verify_non_divergence(None, &[]).await.unwrap(),
            "Legitimate frozen algorithm failed non-divergence verification"
        );

        // Tamper test: Modify alg 1's frozen deactivation boundary from 5 to 3
        {
            let mut tampered_storage = log.storage().clone();
            if let Some(epochs) = tampered_storage.algorithm_metas.get_mut(&1) {
                epochs[0].1 = 3;
            }
            let metas = vec![
                (0, Box::new(Sha256Hasher) as Box<dyn Hasher>),
                (1, Box::new(Sha256Hasher) as Box<dyn Hasher>),
            ];
            let tampered_log = NaryMerkleLog::from_storage(tampered_storage, metas).await.unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered epoch metadata for frozen algorithm"
            );
        }
    });
}


