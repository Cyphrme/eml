//! `pmt` — compatibility facade over the re-layered `spine` + `epoch` crates.
//!
//! The kernel was split into the structural **Merkle Spine** ([`spine`]) and the
//! **`epoch` combinator** ([`epoch`]). The spine owns canonicalization, the proof
//! spine, inclusion/leaf proofs, and the general structural [`spine::Seal`]; the
//! combinator owns the activation timeline, the null-run-extents, the binding
//! root, coupling, the [`epoch::BoundSnapshot`] facet, and the combined [`Sealed`].
//!
//! This crate is a thin **facade** that re-exports the spine and epoch surfaces
//! verbatim — including the combined [`epoch::Sealed`] — so existing consumers
//! keep compiling while they are re-pointed at `spine` / `epoch` directly. It is
//! transitional and carries no logic of its own.

// Structural surface — re-exported verbatim from the spine.
// Epoch surface — re-exported verbatim from the combinator, including the
// combined `Sealed` (the one commitment currency both EMT and the append-only
// log seal into) and the combinator error/result.
pub use epoch::{
    AuditPayload, BindingProof, BoundSnapshot, CouplingProof, Error, NullRun, Result, Sealed,
    TrustedBindingRoot, VerifierConfig, all_null_runs, combined_root, committed_active_algs,
    committed_active_at, null_runs_are_trivial, null_runs_for_alg, serialize_null_runs,
    validate_committed_epochs, verify_inactivity_with_coupling, verify_inclusion_with_coupling,
};
pub use spine::{
    ARITY_RANGE, Hasher, InclusionProof, LeafProof, Meta, ProofStep, RunExtent, SkeletonStep,
    Subtree, constant_time_eq, count_leaves, evaluate, fold_frontier, frontier_for_size,
    inclusion_skeleton, nary_mr, null_digest, reconstruct_inclusion_root, verify_inclusion,
    verify_inclusion_path_structure, within_subtree_path,
};
// Module re-exports preserved for `pmt::mr::…`, `pmt::topology::…`, etc.
pub use spine::{hasher, mr, proof, subtree, topology};
