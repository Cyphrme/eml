//! Crate error types.

use std::fmt;

/// Crate-level error type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<E> {
    /// An error wrapper around the storage backend's error type.
    Storage(E),
    /// Algorithm not found.
    UnknownAlgorithm(u64),
    /// Algorithm already registered.
    DuplicateAlgorithm(u64),
    /// Algorithm is frozen (deactivated) and cannot be modified.
    FrozenAlgorithm(u64),
    /// Algorithm is active and cannot be resumed.
    AlgorithmActive(u64),
    /// No algorithms are active.
    NoActiveAlgorithms,
    /// Index out of bounds.
    IndexOutOfBounds {
        /// The requested index.
        index: u64,
        /// The algorithm's tree size.
        tree_size: u64,
    },
    /// Persisted metadata does not match provided hashers on restore.
    OrphanedMetadata(u64),
    /// Provided hasher has no matching persisted metadata on restore.
    UnknownMetadata(u64),
    /// Persistent metadata is corrupted.
    CorruptedMetadata {
        /// The algorithm ID.
        alg_id: u64,
        /// Description of why it is corrupted.
        reason: String,
    },
    /// The kernel rejected the timeline while building a [`pmt::Sealed`] (the
    /// committed epochs are not well-formed at the sealed size).
    MalformedSeal,
}

impl<E: fmt::Display> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Storage(e) => write!(f, "storage error: {}", e),
            Self::UnknownAlgorithm(id) => write!(f, "unknown algorithm: {}", id),
            Self::DuplicateAlgorithm(id) => write!(f, "algorithm already registered: {}", id),
            Self::FrozenAlgorithm(id) => write!(f, "algorithm is frozen: {}", id),
            Self::AlgorithmActive(id) => write!(f, "algorithm is active: {}", id),
            Self::NoActiveAlgorithms => write!(f, "no active algorithms"),
            Self::IndexOutOfBounds { index, tree_size } => {
                write!(
                    f,
                    "index {} out of bounds for tree size {}",
                    index, tree_size
                )
            },
            Self::OrphanedMetadata(id) => {
                write!(
                    f,
                    "algorithm {} in storage metadata but no hasher provided",
                    id
                )
            },
            Self::UnknownMetadata(id) => {
                write!(
                    f,
                    "hasher provided for algorithm {} with no stored metadata",
                    id
                )
            },
            Self::CorruptedMetadata { alg_id, reason } => {
                write!(f, "corrupted metadata for algorithm {}: {}", alg_id, reason)
            },
            Self::MalformedSeal => {
                write!(f, "kernel rejected the timeline while sealing")
            },
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for Error<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Storage(e) => Some(e),
            _ => None,
        }
    }
}

/// A specialized Result alias for the crate.
pub type Result<T, E> = std::result::Result<T, Error<E>>;

impl<E> From<E> for Error<E> {
    fn from(err: E) -> Self {
        Self::Storage(err)
    }
}
