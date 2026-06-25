//! Errors raised by the mutable tree's construction and mutation surface.
//!
//! The spine reports proof *verification* with `bool`/`Option`; these errors
//! arise only where the CMT rejects an ill-formed mutation or seal.

use std::fmt;

/// A CMT construction or mutation error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The configured arity is outside the spine's `2..=256` range.
    InvalidArity(u64),
    /// An algorithm ID was registered twice.
    DuplicateAlgorithm(u64),
    /// A `set` at `index` would leave a gap: the tree is dense, so an index may
    /// be at most `len` (which appends).
    IndexGap {
        /// The rejected index.
        index: u64,
        /// The current cell count.
        len: u64,
    },
    /// Sealing an empty tree, which has no root to carry.
    EmptySeal,
    /// The spine rejected the resumable frontier as malformed.
    MalformedSeal,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArity(k) => write!(f, "arity {k} is outside the supported range 2..=256"),
            Self::DuplicateAlgorithm(id) => write!(f, "algorithm {id} is already registered"),
            Self::IndexGap { index, len } => {
                write!(
                    f,
                    "index {index} leaves a gap in a dense tree of length {len} (max settable \
                     index is {len})"
                )
            },
            Self::EmptySeal => write!(f, "cannot seal an empty tree: there is no root to carry"),
            Self::MalformedSeal => {
                write!(f, "the spine rejected the sealed resumable frontier")
            },
        }
    }
}

impl std::error::Error for Error {}

/// A specialized `Result` for the mutable tree.
pub type Result<T> = std::result::Result<T, Error>;
