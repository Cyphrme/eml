//! Crate error types.

use std::fmt;

/// Crate-level error type.
#[derive(Debug)]
pub enum Error<E> {
    /// An error wrapper around the storage backend's error type.
    Storage(E),
    /// Persisted metadata does not match provided hashers on restore.
    OrphanedMetadata,
    /// Provided hasher has no matching persisted metadata on restore.
    UnknownMetadata,
}

impl<E: fmt::Display> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Storage(e) => write!(f, "storage error: {}", e),
            Self::OrphanedMetadata => write!(f, "orphaned metadata in storage"),
            Self::UnknownMetadata => write!(f, "unknown metadata"),
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
