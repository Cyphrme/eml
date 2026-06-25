//! `epoch` — the epoch combinator.
//!
//! Lifts the structural Merkle Spine ([`spine`]) across **N algorithms over one
//! shared data substrate** by driving **N** single-algorithm CML ([`cml`])
//! engines over it. It is **not** a composition of independent logs (that would
//! duplicate data); the [`NaryMerkleLog`] driver holds the one shared store plus,
//! per algorithm, a `{hasher, frontier}` view, and adds the three epoch concepts
//! the structural core deliberately omits:
//!
//! - the **activation timeline** — the committed epochs that say which algorithm is live where
//!   ([`validate_committed_epochs`], [`committed_active_at`], [`committed_active_algs`]);
//! - the **null-run-extents** — the one logical count, the per-tree-divergent collapse
//!   ([`NullRun`], [`null_runs_for_alg`], [`serialize_null_runs`]);
//! - the **binding root** — the atomic multi-tree commitment ([`combined_root`]), opened by a
//!   [`CouplingProof`] and proven mutually consistent by a [`BindingProof`].
//!
//! The combinator's frozen snapshot is the [`Sealed`] (the [`BoundSnapshot`]
//! epoch facet over a structural [`spine::Seal`]); the structural `Seal` carries
//! no epoch field (D13). The [`fill`] operation and the [`SnapshotProof`] are the
//! trustless verification and aggregate-proof surfaces over a `Sealed`.

pub mod binding_proof;
pub mod evolution;
pub mod filling;
pub mod root;
pub mod seal;
pub mod snapshot;
pub mod snapshot_proof;
pub mod storage;
pub mod tree;

mod log_error;
mod sealed;

pub(crate) mod error;

pub use binding_proof::{BindingProof, TrustedBindingRoot};
// The single-algorithm engine surface re-exported through epoch for the
// `cyphr-log` facade: the log kind, the consistency proof surface, and the spine
// primitives a consumer reaches via the combinator.
pub use cml::LogKind;
pub use cml::proof::{
    ConsistencyProof, InclusionProof, ProofStep, constant_time_eq, reconstruct_consistency_roots,
    reconstruct_inclusion_root, verify_consistency, verify_inclusion,
    verify_inclusion_path_structure,
};
pub use cml::reduction_count;
pub use error::{Error, Result};
pub use evolution::{verify_consistency_with_coupling, verify_epoch_evolution};
pub use filling::{FillError, FillKind, FilledTree, fill};
pub use log_error::{LogError, LogResult};
pub use root::{
    AuditPayload, CouplingProof, NullRun, VerifierConfig, all_null_runs, combined_root,
    committed_active_algs, committed_active_at, null_runs_are_trivial, null_runs_for_alg,
    serialize_null_runs, validate_committed_epochs, verify_inactivity_with_coupling,
    verify_inclusion_with_coupling,
};
pub use sealed::Sealed;
pub use snapshot::BoundSnapshot;
pub use snapshot_proof::{ClaimedLeaf, SnapshotProof};
pub use storage::{AlgorithmMetas, Epochs, MemoryStorage, Storage};
pub use tree::{NaryMerkleLog, TreeConfig};

/// The full proof surface a consumer reaches through `epoch::proof::*` (and so
/// `cyphr_log::proof::*`): the CML engine's append-only consistency + inclusion/
/// leaf proofs, plus the combinator's binding/coupling/audit proofs and the
/// epoch-coupled evolution checks. The originals live in [`cml`] and the
/// combinator modules; this module re-exports them, never a parallel copy.
pub mod proof {
    pub use cml::proof::{
        ConsistencyProof, InclusionProof, ProofStep, constant_time_eq,
        reconstruct_consistency_roots, reconstruct_inclusion_root, verify_consistency,
        verify_inclusion, verify_inclusion_path_structure,
    };

    pub use crate::binding_proof::{BindingProof, TrustedBindingRoot};
    pub use crate::evolution::{verify_consistency_with_coupling, verify_epoch_evolution};
    pub use crate::root::{
        AuditPayload, CouplingProof, NullRun, VerifierConfig, all_null_runs, combined_root,
        committed_active_algs, committed_active_at, null_runs_are_trivial, null_runs_for_alg,
        serialize_null_runs, validate_committed_epochs, verify_inactivity_with_coupling,
        verify_inclusion_with_coupling,
    };
}
pub use spine::{
    Hasher, LeafProof, Meta, RunExtent, Seal, SkeletonStep, Subtree, count_leaves, evaluate,
    frontier_for_size, hasher, inclusion_skeleton, mr, nary_mr, null_digest, subtree, topology,
    within_subtree_path,
};
