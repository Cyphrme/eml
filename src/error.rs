//! Error types for the TSML crate.

use std::fmt;

/// Errors that can occur during TSML operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Algorithm not found in the activation map.
    UnknownAlgorithm(u64),

    /// Algorithm is already registered.
    DuplicateAlgorithm(u64),

    /// Algorithm is frozen (deactivated) and cannot be modified.
    FrozenAlgorithm(u64),

    /// No algorithms are active.
    NoActiveAlgorithms,

    /// Leaf index is out of bounds for the given algorithm's projection.
    IndexOutOfBounds {
        /// The requested index.
        index: u64,
        /// The algorithm's tree size.
        tree_size: u64,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownAlgorithm(id) => write!(f, "unknown algorithm: {id}"),
            Self::DuplicateAlgorithm(id) => write!(f, "algorithm already registered: {id}"),
            Self::FrozenAlgorithm(id) => write!(f, "algorithm is frozen: {id}"),
            Self::NoActiveAlgorithms => write!(f, "no active algorithms"),
            Self::IndexOutOfBounds { index, tree_size } => {
                write!(f, "index {index} out of bounds for tree size {tree_size}")
            },
        }
    }
}

impl std::error::Error for Error {}

/// Convenience alias.
pub type Result<T> = std::result::Result<T, Error>;
