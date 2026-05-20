//! Error types for the EML crate.

use std::fmt;

/// Errors that can occur during EML operations.
#[derive(Debug)]
pub enum Error {
    /// Algorithm not found in the activation map.
    UnknownAlgorithm(u64),

    /// Algorithm is already registered.
    DuplicateAlgorithm(u64),

    /// Algorithm is frozen (deactivated) and cannot be modified.
    FrozenAlgorithm(u64),

    /// Algorithm is currently active and cannot be resumed.
    AlgorithmActive(u64),

    /// No algorithms are active.
    NoActiveAlgorithms,

    /// Leaf index is out of bounds for the given algorithm's projection.
    IndexOutOfBounds {
        /// The requested index.
        index: u64,
        /// The algorithm's tree size.
        tree_size: u64,
    },

    /// Storage backend error.
    Storage(Box<dyn std::error::Error + Send + Sync>),

    /// Algorithm metadata exists in storage but no hasher was provided.
    OrphanedMetadata(u64),

    /// Hasher provided for an algorithm with no persisted metadata.
    UnknownMetadata(u64),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownAlgorithm(id) => write!(f, "unknown algorithm: {id}"),
            Self::DuplicateAlgorithm(id) => write!(f, "algorithm already registered: {id}"),
            Self::FrozenAlgorithm(id) => write!(f, "algorithm is frozen: {id}"),
            Self::AlgorithmActive(id) => write!(f, "algorithm is active: {id}"),
            Self::NoActiveAlgorithms => write!(f, "no active algorithms"),
            Self::IndexOutOfBounds { index, tree_size } => {
                write!(f, "index {index} out of bounds for tree size {tree_size}")
            },
            Self::Storage(e) => write!(f, "storage error: {e}"),
            Self::OrphanedMetadata(id) => {
                write!(
                    f,
                    "algorithm {id} in storage metadata but no hasher provided"
                )
            },
            Self::UnknownMetadata(id) => {
                write!(
                    f,
                    "hasher provided for algorithm {id} with no stored metadata"
                )
            },
        }
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::UnknownAlgorithm(a), Self::UnknownAlgorithm(b)) => a == b,
            (Self::DuplicateAlgorithm(a), Self::DuplicateAlgorithm(b)) => a == b,
            (Self::FrozenAlgorithm(a), Self::FrozenAlgorithm(b)) => a == b,
            (Self::AlgorithmActive(a), Self::AlgorithmActive(b)) => a == b,
            (Self::NoActiveAlgorithms, Self::NoActiveAlgorithms) => true,
            (
                Self::IndexOutOfBounds {
                    index: i1,
                    tree_size: t1,
                },
                Self::IndexOutOfBounds {
                    index: i2,
                    tree_size: t2,
                },
            ) => i1 == i2 && t1 == t2,
            (Self::Storage(_), Self::Storage(_)) => false, // opaque; not comparable
            (Self::OrphanedMetadata(a), Self::OrphanedMetadata(b)) => a == b,
            (Self::UnknownMetadata(a), Self::UnknownMetadata(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Error {}

impl std::error::Error for Error {}

/// Convenience alias.
pub type Result<T> = std::result::Result<T, Error>;
