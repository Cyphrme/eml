//! Empirical computational complexity regression tests.
//!
//! Verifies that TSML proof generation and root extraction maintain the
//! O(log n) performance bounds stated in the formal model (§Performance
//! Bounds). Uses `bigoish` curve-fitting to assert that `Log(N)` is the
//! best-fit model across tree sizes spanning multiple orders of magnitude.
//!
//! # Running
//!
//! These tests are gated behind release profile (no debug assertions):
//!
//! ```text
//! cargo test --release --test complexity
//! ```
//!
//! They will be silently skipped under `cargo test` (dev profile).

#![cfg(not(debug_assertions))]

use std::sync::Arc;

use bigoish::{Log as LogModel, N, assert_best_fit, growing_inputs};
use sha2::{Digest, Sha256};
use tsml::{Hasher, Log, MemoryStorage};

// ---------------------------------------------------------------------------
// Test hasher — domain-separated SHA-256 per the Hasher trait contract.
// ---------------------------------------------------------------------------

#[derive(Debug)]
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

    fn digest_len(&self) -> usize {
        32
    }
}

// ---------------------------------------------------------------------------
// Input factory — builds a log of `n` leaves with a single algorithm,
// wrapped in Arc for cheap cloning (bigoish calls `Fn(T) -> R` with
// `T: Clone`; Log is not Clone, but Arc<Log> is).
// ---------------------------------------------------------------------------

/// Build a log with one algorithm (id 0) and `n` appended leaves.
fn make_log(n: usize) -> Arc<Log<MemoryStorage>> {
    let mut log = Log::new(MemoryStorage::new());
    log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
    for i in 0..n {
        // Deterministic leaf payload — value doesn't affect complexity.
        log.append(&(i as u64).to_le_bytes()).unwrap();
    }
    Arc::new(log)
}

// ---------------------------------------------------------------------------
// Complexity assertions
// ---------------------------------------------------------------------------

/// Inclusion proof generation must be O(log n).
///
/// Queries the midpoint leaf to exercise the maximal binary-split
/// depth at every level of the proof path.
#[test]
fn complexity_inclusion_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            let ts = log.tree_size(0).unwrap();
            log.inclusion_proof(0, ts / 2).unwrap()
        },
        growing_inputs(100, make_log, 25),
    );
}

/// Consistency proof generation must be O(log n).
///
/// Uses old_size = current_size / 2 to exercise the consistency
/// decomposition across the widest split.
#[test]
fn complexity_consistency_proof_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| {
            let ts = log.tree_size(0).unwrap();
            log.consistency_proof(0, ts / 2).unwrap()
        },
        growing_inputs(100, make_log, 25),
    );
}

/// Root extraction must be O(log n).
///
/// Root computation folds the frontier stack, which has O(popcount(n))
/// entries — O(log n) worst case.
#[test]
fn complexity_root_extraction_log_n() {
    assert_best_fit(
        LogModel(N),
        |log: Arc<Log<MemoryStorage>>| log.root(0).unwrap(),
        growing_inputs(100, make_log, 25),
    );
}
