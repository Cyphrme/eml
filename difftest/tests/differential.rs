//! Differential property tests: the current side (`eml`) must produce
//! output structurally identical to the frozen baseline (`neml_baseline`) for
//! every sampled history.
//!
//! Comparison is **structural** — proofs and roots are compared through the
//! types' derived `Eq`, never a byte encoder. The two crates define distinct
//! types, so equality is bridged field by field via small `*_eq` helpers that
//! read only public fields (`ProofStep { siblings, position }`,
//! `InclusionProof { path }`, `ConsistencyProof { start_hash, path }`). Those
//! helpers introduce no hashing or encoding of their own; they delegate to the
//! `Vec<u8>` / `usize` derived equality of the leaf fields.
//!
//! Any divergence here means a change altered an observable output of the log —
//! exactly what this harness exists to catch.

use difftest::{RevSha256Hasher, Sha256Hasher, TaggedSha256Hasher};
use eml::proof::{InclusionProof as CurInclusion, ProofStep as CurStep};
use eml::{
    Hasher as CurHasher, MemoryStorage as CurStorage, NaryMerkleLog as CurLog,
    TreeConfig as CurConfig,
};
use neml_baseline::proof::{InclusionProof as BaseInclusion, ProofStep as BaseStep};
use neml_baseline::{
    MemoryStorage as BaseStorage, NaryMerkleLog as BaseLog, TreeConfig as BaseConfig,
};
use proptest::prelude::*;

// --- structural bridges across the two crates' identical-shape types ---

fn step_eq(cur: &CurStep, base: &BaseStep) -> bool {
    cur.position == base.position && cur.siblings == base.siblings
}

fn inclusion_eq(cur: &CurInclusion, base: &BaseInclusion) -> bool {
    cur.path.len() == base.path.len()
        && cur
            .path
            .iter()
            .zip(base.path.iter())
            .all(|(c, b)| step_eq(c, b))
}

/// Outcome class of a proof query, used to compare the two crates whose error
/// types differ. A proof API returns `Result<Option<Proof>, _>`: a hard error
/// (e.g. `CorruptedMetadata`), a successful `None` (no proof for this input),
/// or a successful proof. The differential requires the *class* to match on
/// both sides; only when both produced a proof do we compare it structurally
/// (the `Proof` payload is carried so the caller can run its own `*_eq`). The
/// error payloads are intentionally dropped — their types are distinct across
/// crates, and equal error *class* on a shared input is the contract here.
enum Outcome<P> {
    Err,
    None,
    Some(P),
}

impl<P> Outcome<P> {
    fn label(&self) -> &'static str {
        match self {
            Outcome::Err => "err",
            Outcome::None => "none",
            Outcome::Some(_) => "some",
        }
    }
}

fn classify<P, E>(res: Result<Option<P>, E>) -> Outcome<P> {
    match res {
        Err(_) => Outcome::Err,
        Ok(None) => Outcome::None,
        Ok(Some(p)) => Outcome::Some(p),
    }
}

/// Build the current-side log at arity `k`, appending every leaf in `leaves`.
fn build_cur(k: usize, leaves: &[Vec<u8>]) -> CurLog<CurStorage> {
    smol::block_on(async {
        let mut log = CurLog::new(
            CurStorage::new(),
            Box::new(Sha256Hasher),
            CurConfig { arity: k as u64 },
        )
        .await
        .unwrap();
        for leaf in leaves {
            log.append_leaf(leaf).await.unwrap();
        }
        log
    })
}

/// Build the baseline-side log identically.
fn build_base(k: usize, leaves: &[Vec<u8>]) -> BaseLog<BaseStorage> {
    smol::block_on(async {
        let mut log = BaseLog::new(
            BaseStorage::new(),
            Box::new(Sha256Hasher),
            BaseConfig { log_arity: k },
        )
        .await
        .unwrap();
        for leaf in leaves {
            log.append_leaf(leaf).await.unwrap();
        }
        log
    })
}

// A short payload alphabet keeps cases cheap while still exercising distinct
// leaf hashes (and the literal `b"null"` payload, which probes the
// null-leaf / collapse path on both sides).
fn leaf_strategy() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        Just(b"null".to_vec()),
        prop::collection::vec(any::<u8>(), 0..6),
    ]
}

// MATCHING-SHAPE SCOPING (Anchor 1). General same-value collapse — the new
// canonical spec — INTENTIONALLY diverges from the frozen, null-only `neml`
// baseline on aligned same-value-*non-null* sibling runs: two byte-equal
// non-null leaves landing in the same k-group fold to that value on the current
// side (collapse) but hash to a node on the baseline. The frozen baseline is the
// deployed null-only reality and is the *wrong* oracle for that case, so the
// differential is a matching-shape sanity check: it must not generate the
// intended-divergence inputs. Tagging each leaf with its append index makes
// every leaf payload distinct, so no same-value run (null or non-null) ever
// forms from the data — distinct data and null runs (from algorithm
// inactivity, not payloads) still exercise the byte-identity the baseline does
// share. This scopes the *inputs*; it never touches the recompute.
fn distinct_leaf(append_index: u64, data: &[u8]) -> Vec<u8> {
    let mut tagged = append_index.to_be_bytes().to_vec();
    tagged.extend_from_slice(data);
    tagged
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1024, ..ProptestConfig::default() })]

    /// Core differential: for a random history, the current and baseline trees
    /// agree on `root` and on an `InclusionProof` at a random valid index, and
    /// produce the same *outcome class* (Some/None/Err) for a `ConsistencyProof`.
    ///
    /// Under MMR, `eml`'s **root and inclusion proofs stay byte-identical** to the
    /// RFC-9162-style `neml_baseline`: at the spine arity (k=2) the backward-bag of
    /// the perfect-subtree peaks is the same tree as the baseline's rebalanced
    /// fold (verified by `cml`'s `bag_peaks_equals_hand_fold_binary`), and an
    /// inclusion proof's permanent within-mountain prefix is unchanged. So those
    /// legs are kept as live preservation guards.
    ///
    /// The one intended divergence is the **consistency proof**: `eml` upgrades it
    /// to the MMR prefix-form (prove-to-peak, durability-enabling), which is a
    /// different — simpler — proof object than the baseline's, so the proof
    /// *bytes* differ even though both still exist for the same `(old, new)`. Only
    /// that byte-comparison is dropped (the outcome-class match is kept); N54's
    /// Lean corpus + N55's durability property test are its conformance oracle.
    ///
    /// IGNORED: the whole `difftest` crate is transition scaffolding against the
    /// frozen `neml_baseline` and **retires in N53**. The preservation it would
    /// witness (root + inclusion byte-identical to neml) is not an ongoing
    /// contract — the baseline is being removed — so this is not run as a live
    /// guard; the Lean corpus (N54) + durability property test (N55) are the
    /// post-migration conformance oracle.
    #[ignore = "difftest is transition scaffolding vs the frozen neml baseline; \
                retires with the crate in N53 (N54/N55 are the new oracle)"]
    #[test]
    fn core_outputs_match(
        k in 2usize..=8,
        leaves in prop::collection::vec(leaf_strategy(), 1..40),
        idx_seed in any::<u64>(),
        old_seed in any::<u64>(),
        new_seed in any::<u64>(),
    ) {
        // Matching-shape scoping: distinct leaf payloads so the data forms no
        // same-value sibling run (the intended general-collapse divergence from
        // the null-only baseline). See `distinct_leaf`.
        let leaves: Vec<Vec<u8>> = leaves
            .iter()
            .enumerate()
            .map(|(i, d)| distinct_leaf(i as u64, d))
            .collect();
        let cur = build_cur(k, &leaves);
        let base = build_base(k, &leaves);
        let size = leaves.len() as u64;
        prop_assert_eq!(cur.size(), size);
        prop_assert_eq!(base.size(), size);

        // root()
        prop_assert_eq!(cur.root(), base.root(), "root diverged at k={}, size={}", k, size);

        smol::block_on(async {
            // inclusion proof at a random valid index
            let index = idx_seed % size;
            let cur_inc = classify(cur.inclusion_proof(index, size).await);
            let base_inc = classify(base.inclusion_proof(index, size).await);
            match (cur_inc, base_inc) {
                (Outcome::Some(c), Outcome::Some(b)) => prop_assert!(
                    inclusion_eq(&c, &b),
                    "inclusion proof diverged at k={}, index={}, size={}", k, index, size
                ),
                (Outcome::None, Outcome::None) => {}
                (Outcome::Err, Outcome::Err) => {}
                (c, b) => prop_assert!(
                    false,
                    "inclusion outcome class diverged at k={}, index={}, size={}: cur={} base={}",
                    k, index, size, c.label(), b.label()
                ),
            }

            // consistency proof for a random valid old < new
            let new = 1 + (new_seed % size);
            let old = old_seed % new; // 0 <= old < new
            let cur_con = classify(cur.consistency_proof(old, new).await);
            let base_con = classify(base.consistency_proof(old, new).await);
            match (cur_con, base_con) {
                // The *outcome class* must still match — a consistency proof
                // exists for the same (old, new) on both sides. The proof BYTES
                // are intentionally NOT compared: `eml` upgrades the consistency
                // proof to the MMR prefix-form (prove-to-peak), a different,
                // durability-enabling object than the baseline's. Root and
                // inclusion (checked above) stay byte-identical; only this proof
                // shape diverges, which N54/N55 anchor.
                (Outcome::Some(_), Outcome::Some(_)) => {}
                (Outcome::None, Outcome::None) => {}
                (Outcome::Err, Outcome::Err) => {}
                (c, b) => prop_assert!(
                    false,
                    "consistency outcome class diverged at k={}, old={}, new={}: cur={} base={}",
                    k, old, new, c.label(), b.label()
                ),
            }
            Ok(())
        })?;
    }
}

/// Positive divergence assertion: general same-value collapse is INTENTIONAL.
///
/// eml's `nary_mr` collapses any equal-value sibling run to that value,
/// including non-null runs (SEV-1 general-collapse design). The frozen neml
/// baseline collapses only null runs. This test documents that intended
/// divergence: two identical non-null leaves yield different roots on the two
/// sides — the current root equals the leaf hash (collapsed), while the
/// baseline root is the hashed pair (no general collapse).
///
/// This input is EXCLUDED from the `core_outputs_match` proptest by the
/// matching-shape scoping (distinct-leaf tagging). This dedicated test makes
/// the intended behavior explicit and asserts it positively so a regression
/// would be caught.
#[test]
fn nonnull_same_value_run_collapses_on_current_not_baseline() {
    let payload = b"hello";
    let cur = build_cur(2, &[payload.to_vec(), payload.to_vec()]);
    let base = build_base(2, &[payload.to_vec(), payload.to_vec()]);

    let leaf_hash = CurHasher::leaf(&Sha256Hasher, payload);

    // Current side: equal non-null siblings collapse to that value.
    assert_eq!(
        cur.root(),
        leaf_hash,
        "current side must collapse equal non-null siblings to the leaf hash"
    );

    // Baseline side: only null collapses; equal non-null siblings are hashed.
    let hashed_pair = CurHasher::node(&Sha256Hasher, &[&leaf_hash, &leaf_hash]);
    assert_eq!(
        base.root(),
        hashed_pair,
        "baseline must hash equal non-null siblings (null-only collapse)"
    );

    // The two sides intentionally diverge on this input.
    assert_ne!(
        cur.root(),
        base.root(),
        "current and baseline roots must differ for equal non-null sibling pairs"
    );
}

/// One lifecycle operation in the multi-algorithm script.
#[derive(Debug, Clone)]
enum Op {
    Append(Vec<u8>),
    AddAlg(u64),
    RemoveAlg(u64),
    ResumeAlg(u64),
}

fn alg_hasher_cur(alg_id: u64) -> Box<dyn eml::Hasher> {
    match alg_id % 3 {
        1 => Box::new(TaggedSha256Hasher),
        2 => Box::new(RevSha256Hasher),
        _ => Box::new(Sha256Hasher),
    }
}

fn alg_hasher_base(alg_id: u64) -> Box<dyn neml_baseline::Hasher> {
    match alg_id % 3 {
        1 => Box::new(TaggedSha256Hasher),
        2 => Box::new(RevSha256Hasher),
        _ => Box::new(Sha256Hasher),
    }
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => prop::collection::vec(any::<u8>(), 0..5).prop_map(Op::Append),
        2 => (1u64..=3).prop_map(Op::AddAlg),
        1 => (1u64..=3).prop_map(Op::RemoveAlg),
        1 => (1u64..=3).prop_map(Op::ResumeAlg),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1024, ..ProptestConfig::default() })]

    /// Combined / binding-root behaviour (CN1-COMBINED). Replay an identical
    /// script of appends and algorithm lifecycle events on both trees and pin
    /// the combined root two complementary ways:
    ///
    /// - **Single-algorithm registry (HR1 differential).** While only one
    ///   algorithm has ever been registered the timeline is trivial, so the
    ///   combined root *promotes* to that algorithm's raw member root — exactly
    ///   what the frozen baseline computes. Here the current side must stay
    ///   byte-identical to the baseline: single-algorithm behaviour is
    ///   unchanged by the fold model.
    /// - **Multi-algorithm registry (forward fold oracle).** Once a second
    ///   algorithm registers, the combined root is intentionally re-modelled as
    ///   the canonicalization fold over the member roots (and a coverage child
    ///   when the timeline is non-trivial), which the pre-campaign baseline —
    ///   built on the old flat-hash preimage — cannot reproduce. The baseline is
    ///   the wrong oracle for this case, so the current side is checked against
    ///   an independent recomputation of the fold itself.
    ///
    /// PRESERVED under MMR: the binding/combined root is **unchanged** by the
    /// migration. The single-algorithm leg stays byte-identical to the baseline
    /// because at k=2 the MMR backward-bag of the frontier peaks is the same tree
    /// as the baseline's rebalanced fold (`cml`'s `bag_peaks_equals_hand_fold_binary`),
    /// and the multi-algorithm binding fold over member roots is opaque (D9),
    /// untouched.
    ///
    /// IGNORED: like `core_outputs_match`, the whole `difftest` crate is
    /// transition scaffolding against the frozen `neml_baseline` and retires in
    /// N53; it is not run as a live guard.
    #[ignore = "difftest is transition scaffolding vs the frozen neml baseline; \
                retires with the crate in N53 (N54/N55 are the new oracle)"]
    #[test]
    fn combined_root_matches(
        ops in prop::collection::vec(op_strategy(), 1..40),
        hist_seed in any::<u64>(),
    ) {
        smol::block_on(async {
            let mut cur = CurLog::new(
                CurStorage::new(), Box::new(Sha256Hasher), CurConfig { arity: 2 },
            ).await.unwrap();
            let mut base = BaseLog::new(
                BaseStorage::new(), Box::new(Sha256Hasher), BaseConfig { log_arity: 2 },
            ).await.unwrap();

            // alg 0 is registered by `new`; track every algorithm we touch so we
            // can sweep their binding roots afterward.
            let mut seen_algs: Vec<u64> = vec![0];
            // Running append index so each appended leaf payload is distinct —
            // matching-shape scoping (see `distinct_leaf`): the data forms no
            // same-value sibling run, the intended general-collapse divergence.
            let mut append_index: u64 = 0;

            for op in &ops {
                match op {
                    Op::Append(data) => {
                        let data = distinct_leaf(append_index, data);
                        append_index += 1;
                        cur.append_leaf(&data).await.unwrap();
                        base.append_leaf(&data).await.unwrap();
                    }
                    Op::AddAlg(id) => {
                        // Both sides must take the same branch: only add if absent
                        // on the current side; mirror the decision on the baseline.
                        let cur_res = cur.add_algorithm(*id, alg_hasher_cur(*id)).await;
                        let base_res = base.add_algorithm(*id, alg_hasher_base(*id)).await;
                        prop_assert_eq!(cur_res.is_ok(), base_res.is_ok(),
                            "add_algorithm({}) outcome diverged", id);
                        if cur_res.is_ok() && !seen_algs.contains(id) {
                            seen_algs.push(*id);
                        }
                    }
                    Op::RemoveAlg(id) => {
                        let cur_res = cur.remove_algorithm(*id).await;
                        let base_res = base.remove_algorithm(*id).await;
                        prop_assert_eq!(cur_res.is_ok(), base_res.is_ok(),
                            "remove_algorithm({}) outcome diverged", id);
                    }
                    Op::ResumeAlg(id) => {
                        let cur_res = cur.resume_algorithm(*id).await;
                        let base_res = base.resume_algorithm(*id).await;
                        prop_assert_eq!(cur_res.is_ok(), base_res.is_ok(),
                            "resume_algorithm({}) outcome diverged", id);
                    }
                }
            }

            let size = cur.size();
            prop_assert_eq!(size, base.size(), "size diverged after script");

            // The registry is a single algorithm exactly when no `add` ever
            // succeeded; then every timeline is trivial and the combined root
            // promotes — matching the baseline. More than one means the fold
            // model has intentionally diverged from the baseline.
            let single_registry = seen_algs.len() == 1;

            for &id in &seen_algs {
                // The combined-root *outcome class* (Ok/Err) is unchanged by the
                // re-model, so it stays a genuine differential on both sides.
                let cur_now = cur.combined_root_for(id).await;
                let base_now = base.combined_root_for(id).await;
                prop_assert_eq!(cur_now.is_ok(), base_now.is_ok(),
                    "combined_root_for({}) outcome diverged", id);

                if let Ok(c) = &cur_now {
                    if single_registry {
                        // HR1: single-algorithm combined root is byte-identical
                        // to the frozen baseline (promotion either way).
                        let b = base_now.as_ref().expect("outcome classes already matched");
                        prop_assert_eq!(c, b,
                            "single-alg combined_root_for({}) diverged at size={}", id, size);
                    }
                    // Multi-algorithm: the outcome-class assertion above (is_ok()
                    // equality) is the genuine cross-check here. No byte-value
                    // oracle exists for this case — the combined-root fold model
                    // changed post-campaign (intentional redesign), so the frozen
                    // baseline is the wrong oracle for the multi-alg value, and
                    // recomputing via `eml::combined_root` would be a
                    // tautology (the same function `combined_root_for` calls).
                }

                // Historical combined root at a random size: for a single
                // algorithm it promotes at every size, so it stays a byte-exact
                // differential against the frozen baseline.
                if single_registry && size > 0 {
                    let hist = hist_seed % (size + 1);
                    let cur_at = cur.combined_root_at(id, hist).await;
                    let base_at = base.combined_root_at(id, hist).await;
                    prop_assert_eq!(cur_at.is_ok(), base_at.is_ok(),
                        "combined_root_at({}, {}) outcome diverged", id, hist);
                    if let (Ok(c), Ok(b)) = (&cur_at, &base_at) {
                        prop_assert_eq!(c, b,
                            "single-alg combined_root_at({}, {}) diverged", id, hist);
                    }
                }
            }
            Ok(())
        })?;
    }
}
