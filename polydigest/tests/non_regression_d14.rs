//! D14 non-regression: the decomposition into `polydigest(cml × N)` must keep **one
//! shared data substrate** with a **per-algorithm frontier only**, and the
//! multi-tree append must stay **atomic** — no data duplication, no per-algorithm
//! cost or complexity increase.
//!
//! These checks inspect the combinator's storage directly. The behavioral half
//! of D14 (root + inclusion byte-identity with the pre-MMR fold; the consistency
//! proof is upgraded to the MMR prefix-form) is anchored by the Lean corpus and
//! the durability property tests; this file is the structural half the IBC
//! names: shared-substrate + atomic-append.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
use sha2::{Digest, Sha256};

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

/// A second, domain-separated hasher modelling a distinct algorithm.
#[derive(Debug, Clone)]
struct PrefixedSha256Hasher;
impl Hasher for PrefixedSha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update(b"ALG1:");
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update(b"ALG1:");
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update(b"ALG1:");
        h.finalize().to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update(b"ALG1:");
        h.update(data);
        h.finalize().to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

// D14 (b): ONE shared data substrate, per-algorithm frontier only.
//
// With N algorithms active over `n` flat appends, the raw leaf payloads must be
// stored EXACTLY ONCE — `n` entries total, never `N × n`. The per-algorithm
// state is the node digests (alg-keyed) and the frontier, never a second copy of
// the leaf data. This is the trap the IBC names: `polydigest` driving N independent
// logs would give N× data.
#[test]
fn leaf_data_is_stored_once_not_per_algorithm() {
    smol::block_on(async {
        let n = 16u64;
        for num_algs in [1u64, 2, 3] {
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                TreeConfig { arity: 2 },
            )
            .await
            .unwrap();
            // Activate the extra algorithms from genesis.
            for alg in 1..num_algs {
                log.add_algorithm(alg, Box::new(PrefixedSha256Hasher))
                    .await
                    .unwrap();
            }
            for i in 0..n {
                log.append_leaf(format!("leaf-{i}").as_bytes())
                    .await
                    .unwrap();
            }

            let storage = log.into_storage();
            // (a) The leaf payloads live ONCE — exactly `n`, independent of N.
            assert_eq!(
                storage.leaves.len() as u64,
                n,
                "leaf data must be stored once, not per-algorithm (num_algs={num_algs})"
            );
            assert_eq!(
                storage.len().await.unwrap(),
                n,
                "the substrate's leaf count is the global size, never N×n (num_algs={num_algs})"
            );

            // Every persisted node key carries its algorithm id; the node store is
            // the per-algorithm state, distinct from the one leaf array.
            let alg_ids: std::collections::HashSet<u64> =
                storage.nodes.keys().map(|&(alg, ..)| alg).collect();
            assert!(
                alg_ids.len() as u64 <= num_algs,
                "node keys are alg-scoped per-algorithm state (num_algs={num_algs})"
            );
        }
    });
}

/// A `Storage` decorator that counts how many `write_batch` calls happen and the
/// max number of distinct algorithms touched in any single batch. Wraps
/// `MemoryStorage` and forwards everything.
struct CountingStorage {
    inner: MemoryStorage,
    batch_calls: AtomicU64,
    max_algs_in_a_batch: AtomicUsize,
}

impl CountingStorage {
    fn new() -> Self {
        Self {
            inner: MemoryStorage::new(),
            batch_calls: AtomicU64::new(0),
            max_algs_in_a_batch: AtomicUsize::new(0),
        }
    }
}

impl Storage for CountingStorage {
    type Error = <MemoryStorage as Storage>::Error;

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        self.inner.store_leaf(index, data).await
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.inner.get_leaf(index).await
    }

    async fn len(&self) -> Result<u64, Self::Error> {
        self.inner.len().await
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.inner.store_node(alg_id, left, height, hash).await
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner.get_node(alg_id, left, height).await
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        self.inner.store_algorithm_meta(alg_id, epochs).await
    }

    async fn load_algorithm_metas(&self) -> Result<polydigest::AlgorithmMetas, Self::Error> {
        self.inner.load_algorithm_metas().await
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        self.inner.load_log_meta().await
    }

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        self.inner.load_checkpoint_roots().await
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
        algorithm_metas: &[(u64, &[(u64, u64)])],
        log_meta: Option<(u64, u8)>,
        checkpoint_roots: &[(u64, &[u8])],
    ) -> Result<(), Self::Error> {
        self.batch_calls.fetch_add(1, Ordering::Relaxed);
        // Distinct algorithms touched in this single atomic batch: the union of
        // the algorithms appearing across node + checkpoint updates.
        let mut algs: std::collections::HashSet<u64> = nodes.iter().map(|&(a, ..)| a).collect();
        algs.extend(checkpoint_roots.iter().map(|&(a, _)| a));
        self.max_algs_in_a_batch
            .fetch_max(algs.len(), Ordering::Relaxed);
        self.inner
            .write_batch(leaves, nodes, algorithm_metas, log_meta, checkpoint_roots)
            .await
    }
}

// D14 (a): the multi-tree append is ATOMIC — one append is exactly one write
// batch, and that single batch carries ALL active algorithms' updates. The
// binding root forms over a consistent multi-tree snapshot; no algorithm has a
// committed state independent of the others.
#[test]
fn one_append_is_one_atomic_batch_touching_all_algorithms() {
    smol::block_on(async {
        let mut log = NaryMerkleLog::new(
            CountingStorage::new(),
            Box::new(Sha256Hasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();
        log.add_algorithm(1, Box::new(PrefixedSha256Hasher))
            .await
            .unwrap();

        // Reset the counter after registration so we measure only appends.
        log.storage().batch_calls.store(0, Ordering::Relaxed);
        log.storage()
            .max_algs_in_a_batch
            .store(0, Ordering::Relaxed);

        let appends = 8u64;
        for i in 0..appends {
            log.append_leaf(&i.to_be_bytes()).await.unwrap();
        }

        let storage = log.into_storage();
        // Exactly one atomic write batch per append — never one-per-algorithm.
        assert_eq!(
            storage.batch_calls.load(Ordering::Relaxed),
            appends,
            "each append must commit in exactly one atomic write batch"
        );
        // At least one append (any append that seals nodes for both algorithms)
        // must have touched BOTH algorithms in the same batch — proof the
        // multi-tree commit is atomic, not serialized per algorithm.
        assert_eq!(
            storage.max_algs_in_a_batch.load(Ordering::Relaxed),
            2,
            "a single atomic batch must carry both algorithms' updates together"
        );
    });
}
