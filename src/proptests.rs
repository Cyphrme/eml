//! Property-based tests for TSML equational laws.
//!
//! Each test maps to a named law from `docs/models/temporally-sparse-merkle-log.md`.
//! Properties are universally quantified over tree sizes, activation points,
//! and leaf data — proptest explores the input space adversarially.

use proptest::prelude::*;
use sha2::{Digest, Sha256};

use crate::Log;
use crate::hasher::Hasher;
use crate::proof;
use crate::storage::MemoryStorage;

// ============================================================================
// Test hasher
// ============================================================================

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

// ============================================================================
// Helpers
// ============================================================================

/// Build a Log with algorithm 0 activated at `activation`, append
/// `size` leaves, and return it.
///
/// When `activation > 0`, a bootstrap algorithm (id=99) is active from
/// genesis so the log can accept appends before the test algorithm activates.
fn build_log(size: usize, activation: usize) -> Log<MemoryStorage> {
    let mut log = Log::new(MemoryStorage::new());

    if activation == 0 {
        // Algorithm under test is active from genesis.
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
    } else {
        // Bootstrap: need something active for pre-activation appends.
        log.add_algorithm(99, Box::new(Sha256Hasher)).unwrap();
    }

    for i in 0..size {
        if i == activation && activation > 0 {
            log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        }
        log.append(&[i as u8]).unwrap();
    }

    log
}

// ============================================================================
// A-EQUIV-TSML: incremental root == batch root over projection
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn a_equiv_tsml(size in 1usize..128, act_frac in 0.0f64..1.0) {
        let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let incremental = log.root(0).unwrap();
        let projected = log.project(0).unwrap();
        let batch = proof::mth(&Sha256Hasher, &projected);

        prop_assert!(
            incremental == batch,
            "A-EQUIV-TSML failed: size={}, activation={}", size, activation
        );
    }
}

// ============================================================================
// A-STACK-TSML: popcount invariant (indirect via A-EQUIV)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn a_stack_tsml(size in 1usize..128) {
        let log = build_log(size, 0);

        // A-EQUIV is the structural consequence of correct stack operations.
        // If the frontier stack had the wrong number of peaks (not popcount(n)),
        // the fold would produce a wrong root. So A-EQUIV at every size is a
        // sufficient indirect check of A-STACK.
        let incremental = log.root(0).unwrap();
        let projected = log.project(0).unwrap();
        let batch = proof::mth(&Sha256Hasher, &projected);

        prop_assert!(
            incremental == batch,
            "A-STACK (via A-EQUIV) violated at size={}", size
        );

        let ts = log.tree_size(0).unwrap();
        prop_assert!(ts == size as u64, "tree_size mismatch at size={}", size);
    }
}

// ============================================================================
// I-SOUND-TSML: inclusion proof soundness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn i_sound_tsml(
        size in 2usize..64,
        act_frac in 0.0f64..1.0,
        idx_frac in 0.0f64..1.0,
    ) {
        let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let ts = log.tree_size(0).unwrap() as usize;
        if ts == 0 { return Ok(()); }
        let index = ((idx_frac * ts as f64) as usize).min(ts - 1);

        let root = log.root(0).unwrap();
        let projected = log.project(0).unwrap();
        let proof = log.inclusion_proof(0, index as u64).unwrap();

        prop_assert!(
            crate::verify_inclusion(&Sha256Hasher, &projected[index], &proof, &root),
            "I-SOUND-TSML failed: size={}, activation={}, index={}", size, activation, index
        );

        // Wrong leaf must NOT verify (soundness, not just completeness).
        let wrong = Sha256Hasher.leaf(b"WRONG_LEAF_DATA_FOR_PROPTEST");
        prop_assert!(
            !crate::verify_inclusion(&Sha256Hasher, &wrong, &proof, &root),
            "I-SOUND-TSML false positive: size={}, activation={}, index={}", size, activation, index
        );
    }
}

// ============================================================================
// K-SOUND-TSML: consistency proof soundness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn k_sound_tsml(
        size in 3usize..64,
        old_frac in 0.0f64..1.0,
    ) {
        // Algorithm active from genesis for simplicity.
        let log = build_log(size, 0);

        let ts = log.tree_size(0).unwrap();
        // old_size ∈ [1, ts-1].
        let old_size = ((old_frac * (ts - 1) as f64) as u64).max(1).min(ts - 1);

        // Compute old_root by building a separate log of old_size leaves.
        let old_log = build_log(old_size as usize, 0);
        let old_root = old_log.root(0).unwrap();
        let new_root = log.root(0).unwrap();

        let proof = log.consistency_proof(0, old_size).unwrap();

        prop_assert!(
            crate::verify_consistency(&Sha256Hasher, &proof, &old_root, &new_root),
            "K-SOUND-TSML failed: size={}, old_size={}", size, old_size
        );
    }
}

// ============================================================================
// T-BOUND: temporal binding — no payload verifies at null position
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn t_bound(
        size in 2usize..64,
        act_frac in 0.01f64..1.0,  // activation > 0 to ensure null prefix exists
        payload in proptest::collection::vec(any::<u8>(), 1..32),
    ) {
        let activation = ((act_frac * size as f64) as usize).max(1).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let root = log.root(0).unwrap();

        // Pick a null-prefix position (index < activation).
        let null_idx = activation.saturating_sub(1);

        // Forge a leaf hash from arbitrary payload.
        let forged = Sha256Hasher.leaf(&payload);

        let proof = log.inclusion_proof(0, null_idx as u64).unwrap();

        // Forged leaf at a null position must NOT verify.
        prop_assert!(
            !crate::verify_inclusion(&Sha256Hasher, &forged, &proof, &root),
            "T-BOUND violated: forged leaf at null position {}, activation={}, size={}",
            null_idx, activation, size
        );
    }
}

// ============================================================================
// D-SEP: domain separation — leaf ≠ null, leaf ≠ node
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    #[test]
    fn d_sep_leaf_vs_null(data in proptest::collection::vec(any::<u8>(), 0..64)) {
        let leaf = Sha256Hasher.leaf(&data);
        let null = Sha256Hasher.null();
        prop_assert!(leaf != null, "D-SEP violated: leaf == null");
    }

    #[test]
    fn d_sep_leaf_vs_node(
        data in proptest::collection::vec(any::<u8>(), 0..64),
        left in proptest::collection::vec(any::<u8>(), 32..=32),
        right in proptest::collection::vec(any::<u8>(), 32..=32),
    ) {
        let leaf = Sha256Hasher.leaf(&data);
        let node = Sha256Hasher.node(&left, &right);
        prop_assert!(leaf != node, "D-SEP violated: leaf == node");
    }
}

// ============================================================================
// ELIDE-ROUNDTRIP: elide(proof) → rehydrate → original proof
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn elide_roundtrip(
        size in 4usize..64,
        act_frac in 0.01f64..0.99,
        idx_frac in 0.0f64..1.0,
    ) {
        let activation = ((act_frac * size as f64) as usize).max(1).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let ts = log.tree_size(0).unwrap() as usize;
        if ts == 0 { return Ok(()); }

        // Pick an index in the active range (>= activation).
        let active_range = ts.saturating_sub(activation);
        if active_range == 0 { return Ok(()); }
        let index = activation + ((idx_frac * active_range as f64) as usize).min(active_range - 1);

        let root = log.root(0).unwrap();
        let projected = log.project(0).unwrap();
        let full_proof = log.inclusion_proof(0, index as u64).unwrap();

        // Sanity: full proof verifies.
        prop_assert!(
            crate::verify_inclusion(&Sha256Hasher, &projected[index], &full_proof, &root),
            "full proof failed before elision: size={}, activation={}, index={}",
            size, activation, index
        );

        // Elide → rehydrate.
        let elided = crate::elide_inclusion_proof(&full_proof, &[(activation as u64, None)]);
        let rehydrated = crate::rehydrate_inclusion_proof(&elided, &Sha256Hasher);

        // Rehydrated must equal original.
        prop_assert!(
            rehydrated == full_proof,
            "elide roundtrip mismatch: size={}, activation={}, index={}",
            size, activation, index
        );

        // And verify.
        prop_assert!(
            crate::verify_inclusion(&Sha256Hasher, &projected[index], &rehydrated, &root),
            "rehydrated proof failed: size={}, activation={}, index={}",
            size, activation, index
        );
    }
}

// ============================================================================
// PROJ-VALID: projection yields valid malt tree
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn proj_valid(size in 1usize..128, act_frac in 0.0f64..1.0) {
        let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let projected = log.project(0).unwrap();
        let ts = log.tree_size(0).unwrap() as usize;

        // Projected sequence length must equal tree_size.
        prop_assert!(
            projected.len() == ts,
            "PROJ-VALID: projected length {} != tree_size {}", projected.len(), ts
        );

        // Batch root over projection must match incremental root.
        let batch = proof::mth(&Sha256Hasher, &projected);
        let incremental = log.root(0).unwrap();
        prop_assert!(
            batch == incremental,
            "PROJ-VALID: batch root != incremental at size={}, activation={}", size, activation
        );

        // Every leaf in the projection must be either a real leaf hash or null.
        let null_leaf = Sha256Hasher.null();
        for (i, leaf_hash) in projected.iter().enumerate() {
            if i < activation {
                // Pre-activation: must be null.
                prop_assert!(
                    leaf_hash == &null_leaf,
                    "PROJ-VALID: position {} should be null (activation={})", i, activation
                );
            } else {
                // Post-activation: must be real leaf hash.
                let expected = Sha256Hasher.leaf(&[i as u8]);
                prop_assert!(
                    leaf_hash == &expected,
                    "PROJ-VALID: position {} should be real leaf (activation={})", i, activation
                );
            }
        }
    }
}

// ============================================================================
// CR-MANIFEST: algorithms() snapshot consistency (Definition 13)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn cr_manifest_consistency(size in 1usize..64, act_frac in 0.0f64..1.0) {
        let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let infos = log.algorithms();

        // When activation > 0, there's a bootstrap algorithm (99) + test algorithm (0).
        if activation == 0 {
            prop_assert!(infos.len() == 1, "expected 1 algorithm, got {}", infos.len());
        } else {
            prop_assert!(infos.len() == 2, "expected 2 algorithms, got {}", infos.len());
        }

        // Validate algorithm 0's manifest entry.
        let info = infos.iter().find(|a| a.id == 0).expect("algorithm 0 missing from manifest");
        let expected_root = log.root(0).unwrap();
        let expected_ts = log.tree_size(0).unwrap();
        let expected_act = log.activation_index(0).unwrap();
        let expected_deact = log.deactivation_index(0).unwrap();

        prop_assert!(info.root == expected_root, "manifest root mismatch");
        prop_assert!(info.tree_size == expected_ts, "manifest tree_size mismatch");
        prop_assert!(info.activation_index == expected_act, "manifest activation mismatch");
        prop_assert!(info.deactivation_index == expected_deact, "manifest deactivation mismatch");
    }
}
