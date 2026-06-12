//! Storage abstraction for leaf and node persistence.

use std::collections::HashMap;

/// Epoch metadata for a registered algorithm: a sequence of half-open `[start, end)` intervals.
pub type Epochs = Vec<(u64, u64)>;

/// Reconstructed metadata for registered algorithms: a list of `(alg_id, epochs)` pairs.
pub type AlgorithmMetas = Vec<(u64, Epochs)>;

/// Backend for persisting and retrieving raw leaf payloads and sealed
/// internal node hashes.
pub trait Storage: Send + Sync {
    /// Error type for storage operations.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Persist a raw leaf payload at the given index.
    fn store_leaf(
        &mut self,
        index: u64,
        data: &[u8],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;

    /// Retrieve the raw leaf payload at the given index.
    fn get_leaf(
        &self,
        index: u64,
    ) -> impl std::future::Future<Output = Result<Vec<u8>, Self::Error>> + Send;

    /// The number of leaves currently stored.
    fn len(&self) -> impl std::future::Future<Output = u64> + Send;

    /// Whether the storage contains no leaves.
    fn is_empty(&self) -> impl std::future::Future<Output = bool> + Send {
        async move { self.len().await == 0 }
    }

    /// Persist a sealed internal node hash.
    fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;

    /// Retrieve a sealed internal node hash.
    fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> impl std::future::Future<Output = Result<Option<Vec<u8>>, Self::Error>> + Send;

    /// Persist algorithm metadata (epoch boundaries).
    fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;

    /// Load all persisted algorithm metadata.
    fn load_algorithm_metas(
        &self,
    ) -> impl std::future::Future<Output = Result<AlgorithmMetas, Self::Error>> + Send;

    /// Persist authoritative log metadata: the total append count and log kind byte.
    ///
    /// Kind byte: `0` = flat leaf log, `1` = subtree log.
    ///
    /// This must be called on every append so that `from_storage` can recover
    /// the authoritative size without probing node storage. V7 (atomic batch)
    /// will fold this write into the append batch; until then it is a separate
    /// call made immediately after `write_batch`.
    fn store_log_meta(
        &mut self,
        count: u64,
        kind: u8,
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;

    /// Load authoritative log metadata written by `store_log_meta`.
    ///
    /// Returns `None` for stores that have never written log metadata (legacy
    /// or newly initialised), triggering the deterministic probe fallback in
    /// `from_storage`.
    fn load_log_meta(
        &self,
    ) -> impl std::future::Future<Output = Result<Option<(u64, u8)>, Self::Error>> + Send;

    /// Perform a batch write of multiple leaves and nodes.
    fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send {
        async move {
            for &(index, data) in leaves {
                self.store_leaf(index, data).await?;
            }
            for &(alg_id, left, height, hash) in nodes {
                self.store_node(alg_id, left, height, hash).await?;
            }
            Ok(())
        }
    }
}

// ============================================================================
// In-memory implementation
// ============================================================================

/// In-memory leaf and node storage backed by collections.
#[derive(Debug, Default, Clone)]
pub struct MemoryStorage {
    /// Raw leaf payloads.
    pub leaves: Vec<Vec<u8>>,
    /// Sealed internal node hashes, keyed by `(alg_id, left, height)`.
    pub nodes: HashMap<(u64, u64, u32), Vec<u8>>,
    /// Algorithm epoch metadata, keyed by algorithm ID.
    pub algorithm_metas: HashMap<u64, Vec<(u64, u64)>>,
    /// Authoritative log metadata: `(total_append_count, kind_byte)`.
    pub log_meta: Option<(u64, u8)>,
}

impl MemoryStorage {
    /// Create a new empty in-memory storage.
    #[must_use]
    pub fn new() -> Self {
        Self {
            leaves: Vec::new(),
            nodes: HashMap::new(),
            algorithm_metas: HashMap::new(),
            log_meta: None,
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

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        debug_assert_eq!(
            index,
            self.leaves.len() as u64,
            "store_leaf called out of order"
        );
        self.leaves.push(data.to_vec());
        Ok(())
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.leaves
            .get(index as usize)
            .cloned()
            .ok_or(MemoryStorageError {
                index,
                stored: self.leaves.len() as u64,
            })
    }

    async fn len(&self) -> u64 {
        self.leaves.len() as u64
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.nodes.insert((alg_id, left, height), hash.to_vec());
        Ok(())
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        Ok(self.nodes.get(&(alg_id, left, height)).cloned())
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        self.algorithm_metas.insert(alg_id, epochs.to_vec());
        Ok(())
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        Ok(self
            .algorithm_metas
            .iter()
            .map(|(&id, e)| (id, e.clone()))
            .collect())
    }

    async fn store_log_meta(&mut self, count: u64, kind: u8) -> Result<(), Self::Error> {
        self.log_meta = Some((count, kind));
        Ok(())
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        Ok(self.log_meta)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_storage_leaves() {
        smol::block_on(async {
            let mut storage = MemoryStorage::new();
            assert!(storage.is_empty().await);
            assert_eq!(storage.len().await, 0);

            storage.store_leaf(0, b"leaf0").await.unwrap();
            assert!(!storage.is_empty().await);
            assert_eq!(storage.len().await, 1);
            assert_eq!(storage.get_leaf(0).await.unwrap(), b"leaf0");

            // Out of bounds retrieval
            assert!(storage.get_leaf(1).await.is_err());
        });
    }

    #[test]
    fn test_memory_storage_nodes() {
        smol::block_on(async {
            let mut storage = MemoryStorage::new();
            assert_eq!(storage.get_node(1, 42, 0).await.unwrap(), None);

            storage.store_node(1, 42, 0, b"node_hash").await.unwrap();
            assert_eq!(
                storage.get_node(1, 42, 0).await.unwrap(),
                Some(b"node_hash".to_vec())
            );
        });
    }
}
