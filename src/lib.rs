//! # TSML — Temporally-Sparse Merkle Log
//!
//! A single RFC 9162 append-only Merkle tree supporting dynamic sets of hash
//! algorithms over a shared topology. Algorithms activate and deactivate at
//! commit boundaries. Pre-activation positions are filled with deterministic
//! null constants, enabling O(1) algorithm addition without retroactive
//! computation.
//!
//! See `docs/models/temporally-sparse-merkle-log.md` for the formal model.
//!
//! # Architecture
//!
//! TSML is algorithm-agnostic. Callers provide hash implementations via the
//! [`Hasher`] trait. The crate has zero runtime dependencies.
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

pub use error::Error;
pub use hasher::Hasher;
pub use log::Log;
pub use null::NullTable;
