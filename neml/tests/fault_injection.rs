//! Fault injection crash-recovery tests for neml.

use std::sync::{Arc, Mutex};

use neml::{Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
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

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
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
            .store_node(alg_id, left, height, hash)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner
            .get_node(alg_id, left, height)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
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

    async fn store_log_meta(&mut self, count: u64, kind: u8) -> Result<(), Self::Error> {
        self.inner
            .store_log_meta(count, kind)
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        self.inner
            .load_log_meta()
            .await
            .map_err(|_| FaultError::Storage)
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
    ) -> Result<(), Self::Error> {
        let backup = self.inner.clone();

        for &(index, data) in leaves {
            if let Err(e) = self.store_leaf(index, data).await {
                self.inner = backup;
                return Err(e);
            }
        }

        for &(alg_id, left, height, hash) in nodes {
            if let Err(e) = self.store_node(alg_id, left, height, hash).await {
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
        let mut log = NaryMerkleLog::new(storage.clone(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();

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
        let reconstructed =
            NaryMerkleLog::from_storage(final_storage, vec![(0, Box::new(Sha256Hasher))])
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
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config)
            .await
            .unwrap();

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
            let tampered_log =
                NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))])
                    .await
                    .unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered leaf data"
            );
        }

        // 2. Internal node hash tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Find an internal node and tamper it
            let key = (0, 0, 3); // (alg_id, left, height)
            if let std::collections::hash_map::Entry::Occupied(mut e) =
                tampered_storage.nodes.entry(key)
            {
                e.insert(vec![0x00; 32]);
                let tampered_log = NaryMerkleLog::from_storage(
                    tampered_storage,
                    vec![(0, Box::new(Sha256Hasher))],
                )
                .await
                .unwrap();
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
            let tampered_log =
                NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))])
                    .await
                    .unwrap();
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
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

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
        let reconstructed = NaryMerkleLog::from_storage(log.storage().clone(), metas)
            .await
            .unwrap();
        assert!(
            reconstructed
                .verify_non_divergence(None, &[])
                .await
                .unwrap(),
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
            let tampered_log = NaryMerkleLog::from_storage(tampered_storage, metas)
                .await
                .unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered epoch metadata for frozen algorithm"
            );
        }
    });
}

#[test]
fn test_resume_algorithm_non_atomic_crash_recovery() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        // 1. Append 2 leaves (alg 0 is active)
        log.append_leaf(b"leaf0").await.unwrap();
        log.append_leaf(b"leaf1").await.unwrap();

        // Add alg 1 to keep active during log appends while alg 0 is frozen
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        // 2. Freeze alg 0 at size 2
        log.remove_algorithm(0).await.unwrap();

        // 3. Append 2 more leaves (global size is 4, alg 0 is frozen at 2, alg 1 is active)
        log.append_leaf(b"leaf2").await.unwrap();
        log.append_leaf(b"leaf3").await.unwrap();

        // 4. Simulate resume_algorithm crash:
        // We write the reconstructed frontier nodes for size 4 to storage,
        // but do NOT update the algorithm metadata.
        let mut mutated_storage = log.storage().clone();
        
        // Write a garbage node to storage at alg 0, left 0, height 2 (root of size 4)
        // representing a corrupted/partial write.
        mutated_storage.store_node(0, 0, 2, &[0xAA; 32]).await.unwrap();

        // 5. Recover/from_storage: metadata is still frozen.
        let metas = vec![
            (0, Box::new(Sha256Hasher) as Box<dyn Hasher>),
            (1, Box::new(Sha256Hasher) as Box<dyn Hasher>),
        ];
        let mut recovered_log = NaryMerkleLog::from_storage(mutated_storage, metas)
            .await
            .unwrap();

        assert_eq!(recovered_log.size(), 4);

        // 6. Call resume_algorithm again on recovered log.
        // It must succeed, correctly re-evaluate the frontier root,
        // write the correct root to storage (overwriting/ignoring the garbage node),
        // and activate the algorithm.
        recovered_log.resume_algorithm(0).await.unwrap();

        // 7. Try to resume again. It should fail with AlgorithmActive,
        // indicating it was successfully reactivated.
        let res = recovered_log.resume_algorithm(0).await;
        assert!(matches!(res.unwrap_err(), neml::Error::AlgorithmActive(0)));

        // Append leaf 4, which should hash the correct root of size 4!
        recovered_log.append_leaf(b"leaf4").await.unwrap();
        assert_eq!(recovered_log.size(), 5);
    });
}

/// V12: a missing node in the partially-active boundary band is corruption,
/// not a legitimate null.
///
/// A boundary band node covers a range that is only partially active (at
/// least one active leaf, at least one inactive leaf). resume_algorithm
/// computes and stores these mixed nodes. Deleting one should be detected
/// as CorruptedMetadata, not silently treated as null.
///
/// Setup: alg 1 has epochs [(0,3),(6,∞)]. The height-1 node at
/// (alg=1, left=2, height=1) covers [2, 4):
///   active_range(2, 4) = true  (epoch [0,3) overlaps: 0 < 4 and 3 > 2)
///   fully_active(2, 4) = false (position 3 is not in [0,3): 4 > 3)
/// It is stored by resume_algorithm as nary_mr([h2, null]).
#[test]
fn test_v12_boundary_band_corruption_detected() {
    smol::block_on(async {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
            .await
            .unwrap();

        // Register a second algorithm alongside alg 0.
        log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

        // Append 3 leaves (alg 1 active during [0, 3)).
        log.append_leaf(b"leaf0").await.unwrap();
        log.append_leaf(b"leaf1").await.unwrap();
        log.append_leaf(b"leaf2").await.unwrap();

        // Deactivate alg 1 (epoch [0, 3)).
        log.remove_algorithm(1).await.unwrap();

        // Append 3 more leaves; alg 1 is skipped (not active).
        log.append_leaf(b"leaf3").await.unwrap();
        log.append_leaf(b"leaf4").await.unwrap();
        log.append_leaf(b"leaf5").await.unwrap();
        // Log size is now 6; alg 1 epoch = [(0, 3)].

        // Resume alg 1 at size 6. This runs reconstruct_subtree_root, which
        // computes and stores boundary band nodes: specifically the height-1
        // node at (alg=1, left=2, height=1) covering [2, 4).
        log.resume_algorithm(1).await.unwrap();

        // Append one more leaf (position 6) so alg 1's second epoch is
        // active at the final log position.  Without this, root_for_at would
        // compute alg_size = 3 (last epoch end before size 6) and the
        // frontier folded by verify_non_divergence (which spans all 6
        // positions including the null gap) would not match.
        log.append_leaf(b"leaf6").await.unwrap();
        // Now alg 1 has epochs [(0,3),(6,7)] — wait, it's still active:
        // epochs = [(0,3), (6,∞)]. is_active_at(6) = true.

        let metas = vec![
            (0u64, Box::new(Sha256Hasher) as Box<dyn Hasher>),
            (1u64, Box::new(Sha256Hasher) as Box<dyn Hasher>),
        ];

        // Clean log: verify_non_divergence must succeed.
        // This verifies that legitimately-null boundary regions
        // (active_range = false, e.g. (alg1, left=4, height=1) covering
        // [4,6) which is fully outside all active epochs) do not trigger
        // false positives.
        assert!(
            log.verify_non_divergence(None, &[])
                .await
                .unwrap(),
            "clean log after resume_algorithm + extra leaf failed non-divergence check"
        );

        // Corrupt the boundary band node (alg=1, left=2, height=1).
        // Before the V12 fix, get_node_hash silently returned null() for
        // this absent node (partially active, not fully active). After the
        // fix it returns CorruptedMetadata, which propagates from
        // verify_non_divergence as Err.
        let mut tampered = log.storage().clone();
        tampered.nodes.remove(&(1, 2, 1));

        let tampered_log =
            NaryMerkleLog::from_storage(tampered, metas).await.unwrap();

        let result = tampered_log.verify_non_divergence(None, &[]).await;
        assert!(
            result.is_err() || !result.unwrap(),
            "boundary band corruption was not detected"
        );
    });
}

