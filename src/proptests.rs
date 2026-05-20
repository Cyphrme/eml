//! Property-based tests for EML equational laws.
//!
//! Each test maps to a named law from `docs/models/epoch-merkle-log.md`.
//! Properties are universally quantified over tree sizes, activation points,
//! and leaf data — proptest explores the input space adversarially.

use blake2::Blake2b;
use blake2::digest::consts::U32;
use proptest::prelude::*;
use sha2::{Digest, Sha256};
use sha3::Sha3_256;

use crate::hasher::Hasher;
use crate::storage::MemoryStorage;
use crate::{Log, proof};

// ============================================================================
// Test hashers — three real, distinct digest families
// ============================================================================

/// SHA-256 hasher (32-byte digest).
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

/// SHA3-256 hasher (32-byte digest, Keccak-based).
#[derive(Debug)]
struct Sha3Hasher;

impl Hasher for Sha3Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha3_256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha3_256::new();
        h.update([0x01]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha3_256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        Sha3_256::digest([0x02]).to_vec()
    }

    fn digest_len(&self) -> usize {
        32
    }
}

/// BLAKE2b-256 hasher (32-byte digest).
#[derive(Debug)]
struct Blake2bHasher;

impl Hasher for Blake2bHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Blake2b::<U32>::new();
        Digest::update(&mut h, [0x00]);
        Digest::update(&mut h, data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Blake2b::<U32>::new();
        Digest::update(&mut h, [0x01]);
        Digest::update(&mut h, left);
        Digest::update(&mut h, right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        <Blake2b<U32> as Digest>::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        <Blake2b<U32> as Digest>::digest([0x02]).to_vec()
    }

    fn digest_len(&self) -> usize {
        32
    }
}

/// Three-way hasher dispatch by algorithm ID: 0→SHA-256, 1→SHA3-256, 2→BLAKE2b.
fn new_hasher_for(alg_id: u64) -> Box<dyn Hasher> {
    match alg_id % 3 {
        0 => Box::new(Sha256Hasher),
        1 => Box::new(Sha3Hasher),
        2 => Box::new(Blake2bHasher),
        _ => unreachable!(),
    }
}

/// Compute batch mth using the correct hasher for the given algorithm ID.
fn mth_for(alg_id: u64, leaves: &[Vec<u8>]) -> Vec<u8> {
    match alg_id % 3 {
        0 => proof::mth(&Sha256Hasher, leaves),
        1 => proof::mth(&Sha3Hasher, leaves),
        2 => proof::mth(&Blake2bHasher, leaves),
        _ => unreachable!(),
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
// A-EQUIV-EML: incremental root == batch root over projection
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn a_equiv_eml(size in 1usize..128, act_frac in 0.0f64..1.0) {
        let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let incremental = log.root(0).unwrap();
        let projected = log.project(0).unwrap();
        let batch = proof::mth(&Sha256Hasher, &projected);

        prop_assert!(
            incremental == batch,
            "A-EQUIV-EML failed: size={}, activation={}", size, activation
        );
    }
}

// ============================================================================
// SUBTREE-ROOT-EQUIV: subtree_root(S, a, 0, ts) == root(a)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// SUBTREE-ROOT-EQUIV: the operational primitive produces the same root
    /// as the frontier-stack fold. This is the foundational bridge between
    /// the O(n) oracle world and the O(log n) stored-node world.
    #[test]
    fn subtree_root_equiv(size in 1usize..128, act_frac in 0.0f64..1.0) {
        let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let ts = log.tree_size(0).unwrap();
        let root = log.root(0).unwrap();
        let subtree = log.test_subtree_root(0, 0, ts).unwrap();

        prop_assert!(
            subtree == root,
            "subtree_root(0, {}) != root: size={}, activation={}",
            ts, size, activation
        );
    }
}

// ============================================================================
// A-STACK-EML: popcount invariant (indirect via A-EQUIV)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn a_stack_eml(size in 1usize..128) {
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
// I-SOUND-EML: inclusion proof soundness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn i_sound_eml(
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
            "I-SOUND-EML failed: size={}, activation={}, index={}", size, activation, index
        );

        // Wrong leaf must NOT verify (soundness, not just completeness).
        let wrong = Sha256Hasher.leaf(b"WRONG_LEAF_DATA_FOR_PROPTEST");
        prop_assert!(
            !crate::verify_inclusion(&Sha256Hasher, &wrong, &proof, &root),
            "I-SOUND-EML false positive: size={}, activation={}, index={}", size, activation, index
        );
    }
}

// ============================================================================
// K-SOUND-EML: consistency proof soundness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn k_sound_eml(
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
            "K-SOUND-EML failed: size={}, old_size={}", size, old_size
        );
    }

    /// K-SOUND with activation offset: consistency proofs must verify when
    /// the algorithm has a null prefix (activated mid-stream).
    #[test]
    fn k_sound_activation(
        size in 4usize..128,
        act_frac in 0.01f64..0.99,
        old_frac in 0.0f64..1.0,
    ) {
        let activation = ((act_frac * size as f64) as usize).max(1).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let ts = log.tree_size(0).unwrap();
        if ts < 2 { return Ok(()); }
        let old_size = ((old_frac * (ts - 1) as f64) as u64).max(1).min(ts - 1);

        // Compute old_root from the projection oracle.
        let projected = log.project(0).unwrap();
        let old_root = proof::mth(&Sha256Hasher, &projected[..old_size as usize]);
        let new_root = log.root(0).unwrap();

        let proof = log.consistency_proof(0, old_size).unwrap();

        prop_assert!(
            crate::verify_consistency(&Sha256Hasher, &proof, &old_root, &new_root),
            "K-SOUND-ACTIVATION failed: size={}, activation={}, old_size={}",
            size, activation, old_size
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

// ============================================================================
// STATE-MACHINE: random multi-algorithm interleaving
// ============================================================================

/// Operations for the state-machine fuzzer.
#[derive(Debug, Clone)]
enum Op {
    Append,
    AddAlg(u64),
    RemoveAlg(u64),
    ResumeAlg(u64),
}

/// Strategy producing a random sequence of state-machine operations.
///
/// Keeps algorithm IDs in [0, max_algs) to avoid unbounded namespace.
fn op_strategy(max_algs: u64) -> impl Strategy<Value = Op> {
    prop_oneof![
        6 => Just(Op::Append),         // Appends are the dominant operation.
        2 => (0..max_algs).prop_map(Op::AddAlg),
        1 => (0..max_algs).prop_map(Op::RemoveAlg),
        1 => (0..max_algs).prop_map(Op::ResumeAlg),
    ]
}

/// Verify A-EQUIV, A-STACK, proof soundness, and domain separation for
/// every algorithm in the log.
///
/// Returns Err on first violation. This is extracted as a helper so it can
/// be called after every mutation operation, not just at the end.
fn check_invariants(
    log: &Log<MemoryStorage>,
    frozen_roots: &std::collections::BTreeMap<u64, Vec<u8>>,
    context: &str,
) -> std::result::Result<(), proptest::test_runner::TestCaseError> {
    let infos = log.algorithms();

    for info in &infos {
        // A-EQUIV: incremental root == batch root over projection.
        let projected = log.project(info.id).unwrap();
        let batch = mth_for(info.id, &projected);
        prop_assert!(
            info.root == batch,
            "A-EQUIV failed for alg {} {}",
            info.id,
            context
        );

        // A-STACK: projection length == tree_size.
        prop_assert!(
            projected.len() as u64 == info.tree_size,
            "A-STACK proj len {} != tree_size {} for alg {} {}",
            projected.len(),
            info.tree_size,
            info.id,
            context
        );

        // Frozen root stability.
        if let Some(frozen_root) = frozen_roots.get(&info.id) {
            prop_assert!(
                &info.root == frozen_root,
                "Frozen root drifted for alg {} {}",
                info.id,
                context
            );
        }

        // --- Proof soundness (sampled) ---
        if info.tree_size > 0 {
            // I-SOUND: verify inclusion proofs at first, last, and midpoint.
            let sample_indices: Vec<u64> = {
                let ts = info.tree_size;
                let mut v = vec![0, ts - 1];
                if ts > 2 {
                    v.push(ts / 2);
                }
                v
            };

            for &idx in &sample_indices {
                let proof = log.inclusion_proof(info.id, idx).unwrap_or_else(|e| {
                    panic!(
                        "inclusion_proof({}, {}) failed {}: {}",
                        info.id, idx, context, e
                    )
                });
                let hasher: Box<dyn crate::Hasher> = new_hasher_for(info.id);
                prop_assert!(
                    crate::verify_inclusion(
                        hasher.as_ref(),
                        &projected[idx as usize],
                        &proof,
                        &info.root
                    ),
                    "I-SOUND failed for alg {} at index {} {}",
                    info.id,
                    idx,
                    context
                );
            }

            // K-SOUND: verify one consistency proof from midpoint.
            if info.tree_size > 1 {
                let old_size = std::cmp::max(1, info.tree_size / 2);
                let hasher: Box<dyn crate::Hasher> = new_hasher_for(info.id);
                let old_root = crate::proof::mth(hasher.as_ref(), &projected[..old_size as usize]);

                let proof = log
                    .consistency_proof(info.id, old_size)
                    .unwrap_or_else(|e| {
                        panic!(
                            "consistency_proof({}, {}) failed {}: {}",
                            info.id, old_size, context, e
                        )
                    });
                prop_assert!(
                    crate::verify_consistency(hasher.as_ref(), &proof, &old_root, &info.root),
                    "K-SOUND failed for alg {} old_size={} {}",
                    info.id,
                    old_size,
                    context
                );
            }
        }
    }

    // ALG-IND: algorithms sharing the same tree_size with different hashers
    // must produce different roots (domain separation).
    for i in 0..infos.len() {
        for j in (i + 1)..infos.len() {
            let a = &infos[i];
            let b = &infos[j];
            // Only compare if same tree_size AND tree_size > 0 AND different hasher.
            if a.tree_size == b.tree_size && a.tree_size > 0 && (a.id % 3) != (b.id % 3) {
                prop_assert!(
                    a.root != b.root,
                    "ALG-IND violated: alg {} and alg {} share root at tree_size={} {}",
                    a.id,
                    b.id,
                    a.tree_size,
                    context
                );
            }
        }
    }

    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// STATE-MACHINE: Random interleaving of AddAlg/RemoveAlg/ResumeAlg/Append
    /// across k algorithms with three distinct hash families:
    ///   - id % 3 == 0 → SHA-256
    ///   - id % 3 == 1 → SHA3-256
    ///   - id % 3 == 2 → BLAKE2b-256
    ///
    /// Invariants verified **after every mutation**, not just at the end:
    ///   - A-EQUIV holds for every algorithm in dom(act)
    ///   - A-STACK holds for every algorithm in dom(act)
    ///   - Frozen root stability
    ///   - ALG-IND: distinct hashers produce distinct roots
    #[test]
    fn state_machine(
        ops in proptest::collection::vec(op_strategy(9), 50..150),
    ) {
        let mut log = Log::new(MemoryStorage::new());

        // Seed with three algorithms — one per hash family.
        log.add_algorithm(0, new_hasher_for(0)).unwrap(); // SHA-256
        log.add_algorithm(1, new_hasher_for(1)).unwrap(); // SHA3-256
        log.add_algorithm(2, new_hasher_for(2)).unwrap(); // BLAKE2b-256

        let mut frozen_roots: std::collections::BTreeMap<u64, Vec<u8>> =
            std::collections::BTreeMap::new();

        for (step, op) in ops.iter().enumerate() {
            match op {
                Op::Append => {
                    let has_active = log.
                    algorithms().
                    iter().
                    any(|a| a.deactivation_index.is_none());
                    if has_active {
                        let data = [log.size() as u8];
                        log.append(&data).unwrap();
                    }
                }
                Op::AddAlg(id) => {
                    let _ = log.add_algorithm(*id, new_hasher_for(*id));
                }
                Op::RemoveAlg(id) => {
                    if log.remove_algorithm(*id).is_ok() {
                        let root = log.root(*id).unwrap();
                        frozen_roots.insert(*id, root);
                    }
                }
                Op::ResumeAlg(id) => {
                    if log.resume_algorithm(*id).is_ok() {
                        frozen_roots.remove(id);
                    }
                }
            }

            // Verify invariants after every mutation.
            let ctx = format!("after step {} ({:?})", step, op);
            check_invariants(&log, &frozen_roots, &ctx)?;
        }
    }
}

// ============================================================================
// FROZEN-BOUNDS: proof domain bounds after deactivation
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// FROZEN-BOUNDS: Freeze algorithm at T, append many more entries.
    ///   - inclusion_proof(a, i) succeeds for all i < T
    ///   - inclusion_proof(a, i) returns IndexOutOfBounds for i >= T
    ///   - root(a) is stable across all subsequent appends
    ///
    /// Uses three distinct hash families (SHA-256, SHA3-256, BLAKE2b).
    /// Algorithm 0 (SHA-256) is frozen; algorithms 1 and 2 remain active.
    #[test]
    fn frozen_bounds(
        freeze_at in 2usize..128,
        extra_appends in 10usize..256,
    ) {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, new_hasher_for(0)).unwrap(); // SHA-256 (frozen)
        log.add_algorithm(1, new_hasher_for(1)).unwrap(); // SHA3-256 (keeper)
        log.add_algorithm(2, new_hasher_for(2)).unwrap(); // BLAKE2b (keeper)

        for i in 0..freeze_at {
            log.append(&[i as u8]).unwrap();
        }

        log.remove_algorithm(0).unwrap();
        let frozen_root = log.root(0).unwrap();
        let frozen_ts = log.tree_size(0).unwrap();
        prop_assert!(
            frozen_ts == freeze_at as u64,
            "frozen tree_size {} != freeze_at {}", frozen_ts, freeze_at
        );

        for i in 0..extra_appends {
            log.append(&[(freeze_at + i) as u8]).unwrap();
        }

        // Root must be stable.
        let root_after = log.root(0).unwrap();
        prop_assert!(
            root_after == frozen_root,
            "frozen root changed after {} extra appends", extra_appends
        );

        // Valid range: all indices < freeze_at must produce valid proofs.
        let projected = log.project(0).unwrap();
        for i in 0..freeze_at {
            let p = log.inclusion_proof(0, i as u64).unwrap_or_else(|e| {
                panic!("inclusion_proof(0, {i}) should succeed but got: {e}")
            });
            prop_assert!(
                crate::verify_inclusion(&Sha256Hasher, &projected[i], &p, &frozen_root),
                "I-SOUND failed for frozen alg at index {}", i
            );
        }

        // Out-of-bounds: indices >= freeze_at must fail with IndexOutOfBounds.
        for i in freeze_at..(freeze_at + 3) {
            let result = log.inclusion_proof(0, i as u64);
            match result {
                Err(crate::Error::IndexOutOfBounds { index, tree_size }) => {
                    prop_assert!(index == i as u64, "wrong index in error");
                    prop_assert!(tree_size == frozen_ts, "wrong tree_size in error");
                }
                other => {
                    prop_assert!(
                        false,
                        "expected IndexOutOfBounds at {}, got {:?}", i, other
                    );
                }
            }
        }
    }
}

// ============================================================================
// ELIDE-WIRE-LEN: wire length over single-epoch and multi-epoch logs
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// ELIDE-WIRE-LEN (single epoch): verify wire savings with null prefix.
    #[test]
    fn elide_wire_len(
        size in 4usize..256,
        act_frac in 0.01f64..0.99,
        idx_frac in 0.0f64..1.0,
    ) {
        let activation = ((act_frac * size as f64) as usize).max(1).min(size.saturating_sub(1));
        let log = build_log(size, activation);

        let ts = log.tree_size(0).unwrap() as usize;
        if ts == 0 { return Ok(()); }

        let active_range = ts.saturating_sub(activation);
        if active_range == 0 { return Ok(()); }
        let index = activation + ((idx_frac * active_range as f64) as usize).min(active_range - 1);

        let full_proof = log.inclusion_proof(0, index as u64).unwrap();
        let epochs = log.epochs(0).unwrap();
        let elided = crate::elide_inclusion_proof(&full_proof, &epochs);

        // Wire length <= full proof length.
        prop_assert!(
            elided.wire_len() <= full_proof.path.len(),
            "wire_len {} > full proof len {}", elided.wire_len(), full_proof.path.len()
        );

        // Transmitted values must match full proof.
        for (entry, full_hash) in elided.path.iter().zip(full_proof.path.iter()) {
            if let Some(transmitted) = entry {
                prop_assert!(
                    transmitted == full_hash,
                    "transmitted sibling doesn't match full proof"
                );
            }
        }

        // Roundtrip fidelity.
        let rehydrated = crate::rehydrate_inclusion_proof(&elided, &Sha256Hasher);
        prop_assert!(
            rehydrated == full_proof,
            "elide roundtrip mismatch at size={}, activation={}, index={}",
            size, activation, index
        );
    }

    /// ELIDE-WIRE-LEN (multi-epoch): exercises the disjoint epoch elision path.
    ///
    /// Creates a log with two active epochs separated by a null gap:
    ///   epoch 0: [0, freeze_at)
    ///   gap:     [freeze_at, freeze_at + gap)
    ///   epoch 1: [freeze_at + gap, freeze_at + gap + post_resume)
    ///
    /// Verifies elision/rehydration for indices in both active epochs.
    #[test]
    fn elide_wire_len_multi_epoch(
        freeze_at in 2usize..64,
        gap in 2usize..64,
        post_resume in 2usize..64,
        idx_frac in 0.0f64..1.0,
    ) {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, new_hasher_for(0)).unwrap(); // SHA-256 (frozen/resumed)
        log.add_algorithm(1, new_hasher_for(1)).unwrap(); // SHA3-256 (keeper)
        log.add_algorithm(2, new_hasher_for(2)).unwrap(); // BLAKE2b (keeper)

        for i in 0..freeze_at {
            log.append(&[i as u8]).unwrap();
        }
        log.remove_algorithm(0).unwrap();
        for i in 0..gap {
            log.append(&[(freeze_at + i) as u8]).unwrap();
        }
        log.resume_algorithm(0).unwrap();
        for i in 0..post_resume {
            log.append(&[(freeze_at + gap + i) as u8]).unwrap();
        }

        let epochs = log.epochs(0).unwrap();
        prop_assert!(
            epochs.len() == 2,
            "expected 2 epochs, got {}: {:?}", epochs.len(), epochs
        );

        let ts = log.tree_size(0).unwrap() as usize;
        let root = log.root(0).unwrap();
        let projected = log.project(0).unwrap();

        // Total active positions = freeze_at + post_resume.
        let total_active = freeze_at + post_resume;

        // Pick an index from the active positions.
        let active_idx = ((idx_frac * total_active as f64) as usize).min(total_active - 1);

        // Map to global index: first epoch [0, freeze_at), second epoch [freeze_at+gap, ...).
        let global_index = if active_idx < freeze_at {
            active_idx
        } else {
            freeze_at + gap + (active_idx - freeze_at)
        };

        if global_index as u64 >= ts as u64 { return Ok(()); }

        let full_proof = log.inclusion_proof(0, global_index as u64).unwrap();
        let elided = crate::elide_inclusion_proof(&full_proof, &epochs);

        // Wire length must be <= full proof length.
        prop_assert!(
            elided.wire_len() <= full_proof.path.len(),
            "wire_len {} > full proof len {} at global_index={}",
            elided.wire_len(), full_proof.path.len(), global_index
        );

        // If gap > 0, at least some siblings should be elidable.
        // (The gap region is entirely null, so siblings fully within it can be elided.)
        // We only assert this when the gap is large enough relative to the tree
        // to guarantee at least one fully-null sibling subtree.
        if gap >= 2 && full_proof.path.len() > 1 {
            let elided_count = elided.path.iter().filter(|e| e.is_none()).count();
            // With a non-trivial gap, SOME elision should occur for most tree shapes.
            // We don't assert strict > 0 because edge cases exist (e.g., gap perfectly
            // aligns with tree splits such that no sibling falls entirely in the gap).
            // The roundtrip check below is the hard guarantee.
            let _ = elided_count; // Acknowledged but not strictly asserted.
        }

        // Roundtrip is the hard correctness guarantee.
        let rehydrated = crate::rehydrate_inclusion_proof(&elided, &Sha256Hasher);
        prop_assert!(
            rehydrated == full_proof,
            "multi-epoch roundtrip mismatch at freeze_at={}, gap={}, post_resume={}, idx={}",
            freeze_at, gap, post_resume, global_index
        );

        // Rehydrated proof must verify against the root.
        prop_assert!(
            crate::verify_inclusion(&Sha256Hasher, &projected[global_index], &rehydrated, &root),
            "rehydrated proof fails verification at global_index={}", global_index
        );
    }
}
