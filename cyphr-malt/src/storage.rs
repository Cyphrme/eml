//! Storage abstraction for leaf and node persistence.

use std::collections::HashMap;

/// Backend for persisting and retrieving raw leaf payloads and sealed
/// internal node hashes.
pub trait Storage: Send + Sync {
    /// Error type for storage operations.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Persist a raw leaf payload at the given index.
    fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error>;

    /// Retrieve the raw leaf payload at the given index.
    fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error>;

    /// The number of leaves currently stored.
    #[must_use]
    fn len(&self) -> u64;

    /// Whether the storage contains no leaves.
    #[must_use]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Persist a sealed internal node hash.
    fn store_node(
        &mut self,
        alg_id: u64,
        node_id: u64,
        hash: &[u8],
    ) -> Result<(), Self::Error>;

    /// Retrieve a sealed internal node hash.
    fn get_node(
        &self,
        alg_id: u64,
        node_id: u64,
    ) -> Result<Option<Vec<u8>>, Self::Error>;

    /// Persist algorithm metadata (epoch boundaries).
    fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error>;

    /// Load all persisted algorithm metadata.
    fn load_algorithm_metas(&self) -> Result<Vec<(u64, Vec<(u64, u64)>)>, Self::Error>;
}

// ============================================================================
// In-memory implementation
// ============================================================================

/// In-memory leaf and node storage backed by collections.
#[derive(Debug, Default, Clone)]
pub struct MemoryStorage {
    /// Raw leaf payloads.
    pub leaves: Vec<Vec<u8>>,
    /// Sealed internal node hashes, keyed by `(alg_id, node_id)`.
    pub nodes: HashMap<(u64, u64), Vec<u8>>,
    /// Algorithm epoch metadata, keyed by algorithm ID.
    pub algorithm_metas: HashMap<u64, Vec<(u64, u64)>>,
}

impl MemoryStorage {
    /// Create a new empty in-memory storage.
    #[must_use]
    pub fn new() -> Self {
        Self {
            leaves: Vec::new(),
            nodes: HashMap::new(),
            algorithm_metas: HashMap::new(),
        }
    }
}

/// Error type for [`MemoryStorage`] operations.
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
        node_id: u64,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.nodes.insert((alg_id, node_id), hash.to_vec());
        Ok(())
    }

    fn get_node(
        &self,
        alg_id: u64,
        node_id: u64,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(self.nodes.get(&(alg_id, node_id)).cloned())
    }

    fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        self.algorithm_metas.insert(alg_id, epochs.to_vec());
        Ok(())
    }

    fn load_algorithm_metas(&self) -> Result<Vec<(u64, Vec<(u64, u64)>)>, Self::Error> {
        Ok(self
            .algorithm_metas
            .iter()
            .map(|(&id, e)| (id, e.clone()))
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_storage_leaves() {
        let mut storage = MemoryStorage::new();
        assert!(storage.is_empty());
        assert_eq!(storage.len(), 0);

        storage.store_leaf(0, b"leaf0").unwrap();
        assert!(!storage.is_empty());
        assert_eq!(storage.len(), 1);
        assert_eq!(storage.get_leaf(0).unwrap(), b"leaf0");

        // Out of bounds retrieval
        assert!(storage.get_leaf(1).is_err());
    }

    #[test]
    fn test_memory_storage_nodes() {
        let mut storage = MemoryStorage::new();
        assert_eq!(storage.get_node(1, 42).unwrap(), None);

        storage.store_node(1, 42, b"node_hash").unwrap();
        assert_eq!(storage.get_node(1, 42).unwrap(), Some(b"node_hash".to_vec()));
    }
}
