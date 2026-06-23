//! `eml_log` — EML, the append-only Merkle log library over the [`pmt`] kernel.
//!
//! EML (Epoch Merkle Log) is the append-only engineering construction layered
//! over the Polymorphic Merkle Tree kernel. The kernel surface (the `Hasher`
//! seam, the proof spine, canonicalization, inclusion, embedding, [`Sealed`],
//! and epoch construction) lives in [`pmt`] and is re-exported here so consumers
//! reach the whole library through `eml_log::*`. This crate owns the
//! append-only mechanism (the frontier carry, the log builder, storage) and the
//! consistency surface ([`proof::ConsistencyProof`], [`proof::verify_epoch_evolution`]).
//!
//! The library is parameterized essentially by the arity `k` alone
//! ([`TreeConfig`]); a concrete instantiation (for example a binary log at
//! `k = 2` with no prefix) is a thin layer on top.

pub mod error;
pub mod filling;
pub mod proof;
pub mod schedule;
pub mod seal;
pub mod snapshot_proof;
pub mod storage;
pub mod tree;

// The kernel surface, re-exported so consumers reach it through `eml_log::*`.
pub use error::{Error, Result};
pub use filling::{FillError, FillKind, FilledTree, fill};
pub use pmt::hasher::{self, Hasher};
pub use pmt::mr::{self, count_leaves, evaluate, nary_mr, within_subtree_path};
pub use pmt::subtree::{self, Subtree};
pub use pmt::topology::{self, SkeletonStep, frontier_for_size, inclusion_skeleton};
pub use pmt::{LeafProof, RunExtent, Sealed, null_digest};
pub use proof::{
    AuditPayload, BindingProof, ConsistencyProof, CouplingProof, InclusionProof, ProofStep,
    TrustedBindingRoot, VerifierConfig, combined_root, committed_active_algs, committed_active_at,
    committed_is_live, reconstruct_consistency_roots, reconstruct_inclusion_root,
    serialize_timeline, timeline_is_trivial, validate_committed_epochs, verify_consistency,
    verify_consistency_with_coupling, verify_epoch_evolution, verify_inactivity_with_coupling,
    verify_inclusion, verify_inclusion_with_coupling,
};
pub use schedule::reduction_count;
pub use snapshot_proof::{ClaimedLeaf, SnapshotProof};
pub use storage::{AlgorithmMetas, Epochs, MemoryStorage, Storage};
pub use tree::{LogKind, NaryMerkleLog, TreeConfig};
