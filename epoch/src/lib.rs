//! `epoch` — the epoch combinator.
//!
//! Lifts the structural Merkle Spine ([`spine`]) across **N algorithms over one
//! shared data substrate**. It is **not** a composition of independent logs
//! (that would duplicate data); it holds the shared structure plus, per
//! algorithm, a `{hasher, frontier}` view, and adds the three epoch concepts the
//! structural core deliberately omits:
//!
//! - the **activation timeline** — the committed epochs that say which algorithm is live where
//!   ([`validate_committed_epochs`], [`committed_active_at`], [`committed_active_algs`]);
//! - the **null-run-extents** — the one logical count, the per-tree-divergent collapse
//!   ([`NullRun`], [`null_runs_for_alg`], [`serialize_null_runs`]);
//! - the **binding root** — the atomic multi-tree commitment ([`combined_root`]), opened by a
//!   [`CouplingProof`] and proven mutually consistent by a [`BindingProof`].
//!
//! The combinator's frozen snapshot is the [`BoundSnapshot`]: a structural
//! [`spine::Seal`] paired with the committed timeline, deriving the binding root.
//! The structural `Seal` carries no epoch field — the epoch facet is this
//! wrapper (D13).

pub mod binding_proof;
pub mod root;
pub mod snapshot;

pub(crate) mod error;

pub use binding_proof::{BindingProof, TrustedBindingRoot};
pub use error::{Error, Result};
pub use root::{
    AuditPayload, CouplingProof, NullRun, VerifierConfig, all_null_runs, combined_root,
    committed_active_algs, committed_active_at, null_runs_are_trivial, null_runs_for_alg,
    serialize_null_runs, validate_committed_epochs, verify_inactivity_with_coupling,
    verify_inclusion_with_coupling,
};
pub use snapshot::BoundSnapshot;
