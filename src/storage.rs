//! Storage abstraction for leaf and node persistence.
//!
//! The [`Storage`] trait decouples the TSML log from its persistence
//! strategy. The log retains only frontier stacks in memory (O(log n)
//! per algorithm); raw leaf payloads and sealed internal node hashes
//! are persisted through this trait.
//!
//! [`MemoryStorage`] provides an in-memory implementation suitable for
//! testing and small logs.

use std::collections::HashMap;

/// Backend for persisting and retrieving raw leaf payloads and sealed
/// internal node hashes.
///
/// # Integrity Contract
///
/// `get_leaf(i)` **must** return exactly the bytes that were passed to
/// `store_leaf(i, data)`, or return an error. Likewise, `get_node`
/// **must** return exactly the bytes passed to `store_node` for the
/// same `(alg_id, left, height)` triple.
///
/// # Node Storage
///
/// Internal node hashes are persisted during CTO merges in `append`.
/// Each entry is keyed by `(alg_id, left_index, height)` and contains
/// the root hash of the subtree covering leaves `[left, left + 2^height)`.
/// This enables O(log n) proof generation without materializing the
/// full projection.
///
/// # Implementor Guidance
///
/// - [`MemoryStorage`] satisfies the contract trivially (in-process collections).
/// - Database backends should use integrity constraints or checksums.
/// - Filesystem backends may use content-addressed storage (hash as filename).
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

    /// Persist a sealed internal node hash.
    ///
    /// Called during CTO merges when a parent node is computed from two
    /// children. The node covers leaves `[left, left + 2^height)`.
    ///
    /// - `alg_id`: the algorithm this node belongs to.
    /// - `left`: the leftmost leaf index of the subtree.
    /// - `height`: the height of this node (1 = parent of two leaves).
    /// - `hash`: the computed node hash.
    fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: usize,
        hash: &[u8],
    ) -> Result<(), Self::Error>;

    /// Retrieve a sealed internal node hash.
    ///
    /// Returns `None` if no node has been stored for this coordinate.
    /// Returns `Err` only on storage corruption or I/O failure.
    fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: usize,
    ) -> Result<Option<Vec<u8>>, Self::Error>;
}

// ============================================================================
// In-memory implementation
// ============================================================================

/// In-memory leaf and node storage backed by collections.
///
/// Suitable for testing and small logs. The integrity contract is
/// satisfied trivially — in-process memory cannot be corrupted by
/// external actors.
#[derive(Debug, Default)]
pub struct MemoryStorage {
    leaves: Vec<Vec<u8>>,
    /// Sealed internal node hashes, keyed by `(alg_id, left_index, height)`.
    ///
    /// `HashMap` for O(1) amortized lookups — this map is point-queried
    /// only (never iterated or range-scanned).
    nodes: HashMap<(u64, u64, usize), Vec<u8>>,
}

impl MemoryStorage {
    /// Create a new empty in-memory storage.
    #[must_use]
    pub fn new() -> Self {
        Self {
            leaves: Vec::new(),
            nodes: HashMap::new(),
        }
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

    fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: usize,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.nodes.insert((alg_id, left, height), hash.to_vec());
        Ok(())
    }

    fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: usize,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(self.nodes.get(&(alg_id, left, height)).cloned())
    }
}
