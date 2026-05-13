//! Storage abstraction for leaf persistence.
//!
//! The [`Storage`] trait decouples the TSML log from its leaf storage
//! strategy. The log retains only frontier stacks in memory (O(log n)
//! per algorithm); raw leaf payloads are persisted through this trait.
//!
//! [`MemoryStorage`] provides an in-memory implementation suitable for
//! testing and small logs.

/// Backend for persisting and retrieving raw leaf payloads.
///
/// # Integrity Contract
///
/// `get_leaf(i)` **must** return exactly the bytes that were passed to
/// `store_leaf(i, data)`, or return an error. Implementations are
/// responsible for ensuring this invariant through whatever mechanism
/// is appropriate for their storage layer (content-addressing,
/// checksums, database constraints, etc.).
///
/// # Implementor Guidance
///
/// - [`MemoryStorage`] satisfies the contract trivially (in-process `Vec`).
/// - Database backends should use integrity constraints or checksums.
/// - Filesystem backends may use content-addressed storage (hash as filename).
///
/// TSML does not prescribe a caching strategy for intermediate node
/// hashes. Implementors who need O(log n) proof generation can maintain
/// their own node cache internally.
pub trait Storage {
    /// Error type for storage operations.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Persist a raw leaf payload at the given index.
    ///
    /// Called exactly once per index, in monotonically increasing order.
    fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error>;

    /// Retrieve the raw leaf payload at the given index.
    ///
    /// Returns the exact bytes previously passed to `store_leaf` for this
    /// index. Returns an error if the index has not been stored or if the
    /// underlying storage detects corruption.
    fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error>;

    /// The number of leaves currently stored.
    fn len(&self) -> u64;

    /// Whether the storage is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// ============================================================================
// In-memory implementation
// ============================================================================

/// In-memory leaf storage backed by a `Vec`.
///
/// Suitable for testing and small logs. The integrity contract is
/// satisfied trivially — in-process memory cannot be corrupted by
/// external actors.
#[derive(Debug, Default)]
pub struct MemoryStorage {
    leaves: Vec<Vec<u8>>,
}

impl MemoryStorage {
    /// Create a new empty in-memory storage.
    #[must_use]
    pub fn new() -> Self {
        Self { leaves: Vec::new() }
    }
}

/// Error type for [`MemoryStorage`] operations.
///
/// In-memory storage can only fail on out-of-bounds reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryStorageError {
    /// The index that was requested.
    pub index: u64,
    /// The number of stored leaves.
    pub stored: u64,
}

impl std::fmt::Display for MemoryStorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "leaf index {} not found (storage contains {} leaves)",
            self.index, self.stored
        )
    }
}

impl std::error::Error for MemoryStorageError {}

impl Storage for MemoryStorage {
    type Error = MemoryStorageError;

    fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        debug_assert_eq!(
            index,
            self.leaves.len() as u64,
            "store_leaf called out of order"
        );
        self.leaves.push(data.to_vec());
        Ok(())
    }

    fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.leaves
            .get(index as usize)
            .cloned()
            .ok_or(MemoryStorageError {
                index,
                stored: self.leaves.len() as u64,
            })
    }

    fn len(&self) -> u64 {
        self.leaves.len() as u64
    }
}
