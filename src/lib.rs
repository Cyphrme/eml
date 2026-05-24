//! # EML — Epoch Merkle Log
//!
//! A single RFC 9162 append-only Merkle tree supporting dynamic sets of hash
//! algorithms over a shared topology. Algorithms activate and deactivate
//! between appends. A new algorithm's view of pre-activation positions
//! consists of deterministic null constants, enabling O(log n) algorithm addition
//! without retroactive computation.
//!
//! See `docs/models/epoch-merkle-log.md` for the formal model.
//!
//! # Architecture
//!
//! EML is algorithm-agnostic. Callers provide hash implementations via the
//! [`Hasher`] trait. Leaf storage is decoupled via the [`Storage`] trait.
//! The crate has zero runtime dependencies.
//!
//! # Proofs
//!
//! EML generates standard RFC 9162 inclusion and consistency proofs per
//! algorithm. Proofs verify against the standard [`verify_inclusion`] and
//! [`verify_consistency`] functions — no modified verifier is needed.
//!
//! **Specification vs. implementation.** The formal model (§11) defines
//! `project(S, a)` as an O(n) specification oracle — the conceptual
//! per-algorithm leaf sequence that establishes correctness via equational
//! laws. The implementation does not materialize this sequence. Proof
//! generation instead uses `subtree_root` (§11c), which resolves sibling
//! hashes via O(1) stored-node lookups, achieving O(log n) proof generation.
//! The correctness bridge (§12) proves these produce identical output.
//!
//! # Usage
//!
//! ```ignore
//! use eml::{Log, Hasher, MemoryStorage};
//!
//! // Implement Hasher for your algorithm, then:
//! let mut log = Log::new(MemoryStorage::new());
//! log.add_algorithm(0, my_hasher);     // algorithm 0 active from genesis
//! log.append(b"first entry");
//! let root = log.root(0).unwrap();
//! ```

mod error;
mod hasher;
mod log;
mod null;
mod proof;
mod storage;

#[cfg(test)]
mod test_hashers;

pub use error::{Error, Result};
pub use hasher::Hasher;
pub use log::{AlgorithmInfo, Log};
pub use null::NullTable;
pub use proof::{
    ConsistencyProof, ElidedInclusionProof, InclusionProof, elide_inclusion_proof,
    rehydrate_inclusion_proof, verify_consistency, verify_inclusion,
};
pub use storage::{AlgorithmMetas, Epochs, MemoryStorage, MemoryStorageError, Storage};

#[cfg(test)]
mod proptests;
