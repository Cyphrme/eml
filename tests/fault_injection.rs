//! Fault injection tests for EML.
//!
//! Verifies that storage-layer corruption (bit flips, missing nodes) is
//! always detected — either as a verification failure (wrong root / proof
//! mismatch) or as an explicit error. Silent acceptance of corrupted data
//! would be a critical security defect.

mod common;

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use common::Sha256Hasher;
use eml::{AlgorithmMetas, Hasher, Log, Storage, verify_inclusion};

// ============================================================================
// CorruptingStorage — fault injection wrapper
// ============================================================================

/// Fault injection mode for [`CorruptingStorage`].
#[derive(Debug, Clone, Copy, Default)]
enum FaultMode {
    /// All operations pass through cleanly.
    #[default]
    Clean,
    /// Flip one bit in every `get_node` return value.
    BitFlip {
        /// Byte offset within the hash to flip (mod hash length).
        byte_offset: usize,
        /// Bit position within the byte (0..7).
        bit: u8,
    },
    /// Return `None` for stored nodes, simulating data loss.
    Drop,
}

/// Handle for controlling fault injection from outside `Log`.
///
/// `CorruptingStorage` and `FaultHandle` share the same thread-safe state,
/// allowing the test to toggle faults after the storage has been consumed
/// by `Log::new`.
#[derive(Debug, Clone)]
struct FaultHandle {
    mode: Arc<Mutex<FaultMode>>,
    /// Number of `get_node` calls where corruption was actually applied.
    corruptions: Arc<AtomicU64>,
}

impl FaultHandle {
    /// Enable bit-flip fault injection on subsequent `get_node` calls.
    fn enable_bit_flip(&self, byte_offset: usize, bit: u8) {
        self.corruptions.store(0, Ordering::SeqCst);
        let mut m = self.mode.lock().unwrap();
        *m = FaultMode::BitFlip {
            byte_offset,
            bit: bit % 8,
        };
    }

    /// Enable data-loss fault injection: `get_node` returns `None`.
    fn enable_drop(&self) {
        self.corruptions.store(0, Ordering::SeqCst);
        let mut m = self.mode.lock().unwrap();
        *m = FaultMode::Drop;
    }

    /// Disable fault injection.
    #[allow(dead_code)]
    fn disable(&self) {
        let mut m = self.mode.lock().unwrap();
        *m = FaultMode::Clean;
    }

    /// How many `get_node` calls actually returned corrupted data.
    fn corruptions_applied(&self) -> u64 {
        self.corruptions.load(Ordering::SeqCst)
    }
}

/// Storage wrapper that delegates to in-memory collections but can inject
/// faults on `get_node` reads.
///
/// Fault mode is controlled via a shared thread-safe state — the
/// [`FaultHandle`] holds a clone, allowing external control after the
/// storage has been moved into `Log`.
#[derive(Debug)]
struct CorruptingStorage {
    leaves: Vec<Vec<u8>>,
    nodes: HashMap<(u64, u64, usize), Vec<u8>>,
    algorithm_metas: HashMap<u64, Vec<(u64, u64)>>,
    mode: Arc<Mutex<FaultMode>>,
    corruptions: Arc<AtomicU64>,
}

/// Error type — same as MemoryStorage.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CorruptingStorageError {
    index: u64,
    stored: u64,
}

impl std::fmt::Display for CorruptingStorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "leaf {} not found (storage has {} leaves)",
            self.index, self.stored
        )
    }
}

impl std::error::Error for CorruptingStorageError {}

impl CorruptingStorage {
    /// Create a new corrupting storage and its control handle.
    fn new() -> (Self, FaultHandle) {
        let mode = Arc::new(Mutex::new(FaultMode::Clean));
        let corruptions = Arc::new(AtomicU64::new(0u64));
        let handle = FaultHandle {
            mode: mode.clone(),
            corruptions: corruptions.clone(),
        };
        let storage = Self {
            leaves: Vec::new(),
            nodes: HashMap::new(),
            algorithm_metas: HashMap::new(),
            mode,
            corruptions,
        };
        (storage, handle)
    }
}

impl Storage for CorruptingStorage {
    type Error = CorruptingStorageError;

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        debug_assert_eq!(index, self.leaves.len() as u64);
        self.leaves.push(data.to_vec());
        Ok(())
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        let val = self.leaves.get(index as usize).cloned();
        let stored = self.leaves.len() as u64;
        val.ok_or(CorruptingStorageError { index, stored })
    }

    async fn len(&self) -> u64 {
        self.leaves.len() as u64
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: usize,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.nodes.insert((alg_id, left, height), hash.to_vec());
        Ok(())
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: usize,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        let mode = *self.mode.lock().unwrap();
        let val = self.nodes.get(&(alg_id, left, height)).cloned();
        let has_key = self.nodes.contains_key(&(alg_id, left, height));
        let corruptions = self.corruptions.clone();
        match mode {
            FaultMode::Clean => Ok(val),
            FaultMode::BitFlip { byte_offset, bit } => Ok(val.map(|hash| {
                let mut corrupted = hash.clone();
                if !corrupted.is_empty() {
                    let idx = byte_offset % corrupted.len();
                    corrupted[idx] ^= 1 << bit;
                    corruptions.fetch_add(1, Ordering::SeqCst);
                }
                corrupted
            })),
            FaultMode::Drop => {
                if has_key {
                    corruptions.fetch_add(1, Ordering::SeqCst);
                }
                Ok(None)
            },
        }
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        self.algorithm_metas.insert(alg_id, epochs.to_vec());
        Ok(())
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        Ok(self
            .algorithm_metas
            .iter()
            .map(|(&id, e)| (id, e.clone()))
            .collect())
    }
}

// ============================================================================
// Helper: build a log with CorruptingStorage
// ============================================================================

async fn build_log(leaf_count: u64) -> (Log<CorruptingStorage>, FaultHandle) {
    let (storage, handle) = CorruptingStorage::new();
    let mut log = Log::new(storage);
    log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();
    for i in 0..leaf_count {
        log.append(&i.to_le_bytes()).await.unwrap();
    }
    (log, handle)
}

// ============================================================================
// Tests: bit-flip corruption
// ============================================================================

/// A bit flip in stored nodes must cause proof verification failure.
///
/// Strategy: build a correct log, capture the root, enable bit-flip mode,
/// generate a proof (which reads corrupted nodes), verify against the
/// correct root — must fail.
#[test]
fn bit_flip_corrupts_inclusion_proof() {
    smol::block_on(async {
        for n in [4, 7, 8, 16, 31, 32, 64, 100] {
            let (log, handle) = build_log(n).await;
            let root = log.root(0).unwrap();

            // Enable bit-flip on all subsequent get_node calls.
            handle.enable_bit_flip(0, 0);

            // For trees where proof generation touches stored nodes
            // (size > 2), the corrupted sibling hashes should cause
            // verification to fail.
            for leaf_idx in [0, n / 2, n - 1] {
                let proof = log.inclusion_proof(0, leaf_idx).await.unwrap();
                let leaf_hash = Sha256Hasher.leaf(&leaf_idx.to_le_bytes());

                // The proof was generated with corrupted nodes —
                // it must NOT verify against the correct root.
                if !proof.path.is_empty() {
                    assert!(
                        !verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root),
                        "bit-flipped proof should NOT verify: n={n}, leaf={leaf_idx}"
                    );
                }
            }
        }
    });
}

/// Different bit positions produce different (all invalid) proof paths.
#[test]
fn bit_flip_all_positions() {
    smol::block_on(async {
        let (log, handle) = build_log(16).await;
        let root = log.root(0).unwrap();
        let leaf_idx = 5u64;
        let leaf_hash = Sha256Hasher.leaf(&leaf_idx.to_le_bytes());

        for byte in 0..32 {
            for bit in 0..8u8 {
                handle.enable_bit_flip(byte, bit);
                let proof = log.inclusion_proof(0, leaf_idx).await.unwrap();

                assert!(
                    !verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root),
                    "bit flip at byte={byte} bit={bit} should invalidate proof"
                );
            }
        }
    });
}

// ============================================================================
// Tests: data loss (node drop)
// ============================================================================

/// Missing nodes force subtree_root into recursive decomposition.
///
/// With all nodes dropped, subtree_root recomputes from leaf data. The
/// proof should still verify because the leaf data is intact — this
/// tests graceful degradation, not corruption.
#[test]
fn drop_mode_forces_recomputation() {
    smol::block_on(async {
        for n in [4, 8, 16, 32] {
            let (log, handle) = build_log(n).await;
            let root = log.root(0).unwrap();

            // Drop all node lookups — forces full recursive recomputation.
            handle.enable_drop();

            for leaf_idx in [0, n / 2, n - 1] {
                let proof = log.inclusion_proof(0, leaf_idx).await.unwrap();
                let leaf_hash = Sha256Hasher.leaf(&leaf_idx.to_le_bytes());

                // Proof should STILL verify — subtree_root falls back to
                // recursive computation from intact leaf data.
                assert!(
                    verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root),
                    "drop mode should not corrupt proofs (recomputation fallback): n={n}, \
                     leaf={leaf_idx}"
                );
            }
        }
    });
}

/// Root extraction is unaffected by node drops (uses in-memory stack).
#[test]
fn drop_mode_root_unaffected() {
    smol::block_on(async {
        let (log, handle) = build_log(32).await;
        let root_before = log.root(0).unwrap();

        handle.enable_drop();
        let root_after = log.root(0).unwrap();

        assert_eq!(root_before, root_after, "root uses stack, not stored nodes");
    });
}

// ============================================================================
// Tests: consistency proof corruption
// ============================================================================

/// Bit-flip corruption invalidates consistency proofs.
#[test]
fn bit_flip_corrupts_consistency_proof() {
    smol::block_on(async {
        let (log, handle) = build_log(32).await;
        let root = log.root(0).unwrap();

        // Build old root from a separate clean log.
        let (old_log, _) = build_log(16).await;
        let old_root = old_log.root(0).unwrap();

        // Enable corruption.
        handle.enable_bit_flip(0, 0);

        let proof = log.consistency_proof(0, 16).await.unwrap();

        assert!(
            !eml::verify_consistency(&Sha256Hasher, &proof, &old_root, &root),
            "bit-flipped consistency proof should NOT verify"
        );
    });
}

// ============================================================================
// Proptest-driven fault injection
// ============================================================================

#[cfg(test)]
mod proptests {
    use proptest::prelude::*;

    use super::*;

    proptest! {
        /// For random tree sizes, leaf indices, and corruption parameters,
        /// a bit-flipped proof must never verify against the correct root.
        #[test]
        fn bit_flip_never_verifies(
            n in 3u64..=128,
            leaf_frac in 0.0..1.0f64,
            flip_byte in 0usize..32,
            flip_bit in 0u8..8,
        ) {
            smol::block_on(async {
                let (log, handle) = build_log(n).await;
                let root = log.root(0).unwrap();
                let leaf_idx = ((n as f64 * leaf_frac) as u64).min(n - 1);
                let leaf_hash = Sha256Hasher.leaf(&leaf_idx.to_le_bytes());

                handle.enable_bit_flip(flip_byte, flip_bit);
                let proof = log.inclusion_proof(0, leaf_idx).await.unwrap();

                // Only assert corruption when get_node was actually called and
                // returned a corrupted value. For small trees, subtree_root
                // resolves siblings entirely from leaf data (get_leaf), so
                // get_node corruption has no effect.
                if handle.corruptions_applied() > 0 {
                    prop_assert!(
                        !verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root),
                        "corrupted proof verified for n={}, leaf={}", n, leaf_idx
                    );
                }
                Ok::<(), proptest::test_runner::TestCaseError>(())
            })?;
        }

        /// Drop mode preserves proof validity (graceful degradation).
        #[test]
        fn drop_mode_preserves_validity(
            n in 2u64..=64,
            leaf_frac in 0.0..1.0f64,
        ) {
            smol::block_on(async {
                let (log, handle) = build_log(n).await;
                let root = log.root(0).unwrap();
                let leaf_idx = ((n as f64 * leaf_frac) as u64).min(n - 1);
                let leaf_hash = Sha256Hasher.leaf(&leaf_idx.to_le_bytes());

                handle.enable_drop();
                let proof = log.inclusion_proof(0, leaf_idx).await.unwrap();

                prop_assert!(
                    verify_inclusion(&Sha256Hasher, &leaf_hash, &proof, &root),
                    "drop mode should not corrupt proofs for n={}, leaf={}", n, leaf_idx
                );
                Ok::<(), proptest::test_runner::TestCaseError>(())
            })?;
        }
    }
}
