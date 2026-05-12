//! # TSML — Temporally-Sparse Merkle Log
//!
//! A single RFC 9162 append-only Merkle tree supporting dynamic sets of hash
//! algorithms over a shared topology. Algorithms activate and deactivate
//! between appends. A new algorithm's view of pre-activation positions
//! consists of deterministic null constants, enabling O(1) algorithm addition
//! without retroactive computation.
//!
//! See `docs/models/temporally-sparse-merkle-log.md` for the formal model.
//!
//! # Architecture
//!
//! TSML is algorithm-agnostic. Callers provide hash implementations via the
//! [`Hasher`] trait. The crate has zero runtime dependencies.
//!
//! # Proofs
//!
//! TSML generates standard RFC 9162 inclusion and consistency proofs per
//! algorithm, operating over the projected leaf sequence. Proofs verify
//! against the standard [`verify_inclusion`] and [`verify_consistency`]
//! functions — no modified verifier is needed (PROJ-VALID).
//!
//! # Usage
//!
//! ```ignore
//! use tsml::{Log, Hasher};
//!
//! // Implement Hasher for your algorithm, then:
//! let mut log = Log::new();
//! log.add_algorithm(0, my_hasher);     // algorithm 0 active from genesis
//! log.append(b"first entry");
//! let root = log.root(0).unwrap();
//! ```

mod error;
mod hasher;
mod log;
mod null;
mod proof;

pub use error::Error;
pub use hasher::Hasher;
pub use log::{AlgorithmInfo, Log};
pub use null::NullTable;
pub use proof::{
    ConsistencyProof, ElidedInclusionProof, InclusionProof, elide_inclusion_proof,
    rehydrate_inclusion_proof, verify_consistency, verify_inclusion,
};

#[cfg(test)]
mod proptests;
