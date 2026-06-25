//! `cml` — CML, the single-algorithm canonical append log over the [`spine`].
//!
//! CML (Canonical Merkle Log) is the **single-algorithm** append-only engine
//! layered over the structural Merkle Spine. It owns one algorithm's frontier
//! carry (the base-k reduction [`schedule`]), the member-root fold, the
//! append-only [`consistency::ConsistencyProof`], inclusion
//! and leaf proof generation, and the structural snapshot facet — the frontier
//! peaks a [`spine::Seal`] freezes.
//!
//! It is **epoch-free and multi-algorithm-free** (D7): the engine reads one
//! algorithm's view ([`AlgView`]) over a borrowed [`NodeReader`] substrate and
//! never owns the store, so the `polydigest` combinator can drive **N** views over
//! **one** shared data substrate without duplicating leaf data (D14). The
//! activation timeline, the null-run-extents, the binding root, and coupling are
//! the combinator's facet, not CML's.
//!
//! The structural commitment a CML seal produces is the general [`spine::Seal`]
//! (re-exported here); the epoch facet over it is `polydigest::BoundSnapshot`.

pub mod consistency;
pub mod engine;
pub mod mountain;
pub mod schedule;

pub mod error;

// The append-only proof surface: CML's consistency proof plus the spine's
// inclusion/leaf surface re-exported through `cml::proof::*`.
pub mod proof {
    pub use crate::consistency::{
        ConsistencyProof, InclusionProof, ProofStep, constant_time_eq,
        reconstruct_consistency_roots, reconstruct_inclusion_root, verify_consistency,
        verify_inclusion, verify_inclusion_path_structure,
    };
}

pub use consistency::{ConsistencyProof, reconstruct_consistency_roots, verify_consistency};
pub use engine::{
    AlgView, LogKind, NodeReader, carry, compute_root, consistency_proof, frontier_peaks,
    get_node_hash, inclusion_proof, leaf_proof, peak_at, reconstruct_subtree_root,
    reconstruct_view, root_for_at, validate_epochs,
};
pub use error::{Error, Result};
pub use schedule::reduction_count;
// The spine surface a CML consumer needs directly.
pub use spine::{Hasher, Subtree, evaluate, frontier_for_size, nary_mr, null_digest};
// The structural snapshot facet a CML seal freezes is the general spine Seal;
// re-exported so a CML consumer reaches it through `cml::*`.
pub use spine::{RunExtent, Seal};
