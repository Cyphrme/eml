//! Differential property tests: the current `neml` tree must produce output
//! structurally identical to the frozen baseline (`neml_baseline`) for every
//! sampled history.
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
use neml::proof::{
    ConsistencyProof as CurConsistency, InclusionProof as CurInclusion, ProofStep as CurStep,
};
use neml::{MemoryStorage as CurStorage, NaryMerkleLog as CurLog, TreeConfig as CurConfig};
use neml_baseline::proof::{
    ConsistencyProof as BaseConsistency, InclusionProof as BaseInclusion, ProofStep as BaseStep,
};
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

fn consistency_eq(cur: &CurConsistency, base: &BaseConsistency) -> bool {
    cur.start_hash == base.start_hash
        && cur.path.len() == base.path.len()
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
            CurConfig { log_arity: k },
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

proptest! {
    #![proptest_config(ProptestConfig { cases: 1024, ..ProptestConfig::default() })]

    /// Core differential: for a random history, the current and baseline trees
    /// agree structurally on `root`, an `InclusionProof` at a random valid
    /// index, and a `ConsistencyProof` for a random valid `old < new`.
    #[test]
    fn core_outputs_match(
        k in 2usize..=8,
        leaves in prop::collection::vec(leaf_strategy(), 1..40),
        idx_seed in any::<u64>(),
        old_seed in any::<u64>(),
        new_seed in any::<u64>(),
    ) {
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
                (Outcome::Some(c), Outcome::Some(b)) => prop_assert!(
                    consistency_eq(&c, &b),
                    "consistency proof diverged at k={}, old={}, new={}", k, old, new
                ),
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

/// One lifecycle operation in the multi-algorithm script.
#[derive(Debug, Clone)]
enum Op {
    Append(Vec<u8>),
    AddAlg(u64),
    RemoveAlg(u64),
    ResumeAlg(u64),
}

fn alg_hasher_cur(alg_id: u64) -> Box<dyn neml::Hasher> {
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

    /// Combined / binding-root differential (CN1-COMBINED): replay an identical
    /// script of appends and algorithm lifecycle events on both trees, then
    /// assert that `combined_root_for` (current size) and `combined_root_at`
    /// (a historical size) agree for every algorithm — including across
    /// deactivation and epoch resumption.
    #[test]
    fn combined_root_matches(
        ops in prop::collection::vec(op_strategy(), 1..40),
        hist_seed in any::<u64>(),
    ) {
        smol::block_on(async {
            let mut cur = CurLog::new(
                CurStorage::new(), Box::new(Sha256Hasher), CurConfig { log_arity: 2 },
            ).await.unwrap();
            let mut base = BaseLog::new(
                BaseStorage::new(), Box::new(Sha256Hasher), BaseConfig { log_arity: 2 },
            ).await.unwrap();

            // alg 0 is registered by `new`; track every algorithm we touch so we
            // can sweep their binding roots afterward.
            let mut seen_algs: Vec<u64> = vec![0];

            for op in &ops {
                match op {
                    Op::Append(data) => {
                        cur.append_leaf(data).await.unwrap();
                        base.append_leaf(data).await.unwrap();
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

            for &id in &seen_algs {
                // current combined (binding) root
                let cur_now = cur.combined_root_for(id).await;
                let base_now = base.combined_root_for(id).await;
                prop_assert_eq!(cur_now.is_ok(), base_now.is_ok(),
                    "combined_root_for({}) outcome diverged", id);
                if let (Ok(c), Ok(b)) = (&cur_now, &base_now) {
                    prop_assert_eq!(c, b, "combined_root_for({}) diverged at size={}", id, size);
                }

                // historical combined (binding) root at a random size <= current
                if size > 0 {
                    let hist = hist_seed % (size + 1);
                    let cur_at = cur.combined_root_at(id, hist).await;
                    let base_at = base.combined_root_at(id, hist).await;
                    prop_assert_eq!(cur_at.is_ok(), base_at.is_ok(),
                        "combined_root_at({}, {}) outcome diverged", id, hist);
                    if let (Ok(c), Ok(b)) = (&cur_at, &base_at) {
                        prop_assert_eq!(c, b,
                            "combined_root_at({}, {}) diverged", id, hist);
                    }
                }
            }
            Ok(())
        })?;
    }
}
