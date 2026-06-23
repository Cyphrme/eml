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

    /// The number of leaves currently stored, or an error if storage is
    /// unreadable.  Never returns 0 on error; a storage failure must be
    /// propagated so callers can distinguish "empty log" from "broken store".
    fn len(&self) -> impl std::future::Future<Output = Result<u64, Self::Error>> + Send;

    /// Whether the storage contains no leaves.
    fn is_empty(&self) -> impl std::future::Future<Output = Result<bool, Self::Error>> + Send {
        async move { self.len().await.map(|n| n == 0) }
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

    /// Persist algorithm metadata (epoch boundaries) for add/remove operations.
    ///
    /// Use `write_batch` when algorithm metadata must be committed atomically
    /// alongside node data (e.g. during `resume_algorithm`).
    fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;

    /// Load all persisted algorithm metadata.
    fn load_algorithm_metas(
        &self,
    ) -> impl std::future::Future<Output = Result<AlgorithmMetas, Self::Error>> + Send;

    /// Load authoritative log metadata written by `write_batch`.
    ///
    /// Returns `None` for stores that have never written log metadata (legacy
    /// or newly initialised), triggering the deterministic probe fallback in
    /// `from_storage`.
    fn load_log_meta(
        &self,
    ) -> impl std::future::Future<Output = Result<Option<(u64, u8)>, Self::Error>> + Send;

    /// Load per-algorithm checkpoint roots last written by `write_batch`.
    ///
    /// Used by `from_storage` to verify frontier integrity: the root
    /// recomputed from the loaded frontier must match the stored checkpoint.
    /// Returns an empty list for stores that have never written checkpoint
    /// roots (legacy or newly initialised).
    fn load_checkpoint_roots(
        &self,
    ) -> impl std::future::Future<Output = Result<Vec<(u64, Vec<u8>)>, Self::Error>> + Send;

    /// Atomically commit leaves, nodes, algorithm epoch updates, log
    /// metadata, and per-algorithm checkpoint roots in a single durable
    /// transaction.
    ///
    /// All fields are optional (pass empty slices / `None`) but the
    /// implementation MUST guarantee all-or-nothing semantics: a crash
    /// between any two writes within the batch must leave no partial state.
    ///
    /// `algorithm_metas` carries epoch updates for algorithms whose epoch
    /// list changes as part of this operation (e.g. `resume_algorithm`).
    ///
    /// `log_meta` is `Some((count, kind_byte))` on every leaf/subtree
    /// append; `None` for operations that don't change the global count.
    ///
    /// `checkpoint_roots` is a list of `(alg_id, root_hash)` pairs to store
    /// alongside the batch so `from_storage` can verify frontier integrity.
    fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
        algorithm_metas: &[(u64, &[(u64, u64)])],
        log_meta: Option<(u64, u8)>,
        checkpoint_roots: &[(u64, &[u8])],
    ) -> impl std::future::Future<Output = Result<(), Self::Error>> + Send;
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
    /// Per-algorithm checkpoint roots: the root hash at the last append.
    pub checkpoint_roots: HashMap<u64, Vec<u8>>,
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
            checkpoint_roots: HashMap::new(),
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

    async fn len(&self) -> Result<u64, Self::Error> {
        Ok(self.leaves.len() as u64)
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

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        Ok(self.log_meta)
    }

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        Ok(self
            .checkpoint_roots
            .iter()
            .map(|(&id, r)| (id, r.clone()))
            .collect())
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
        algorithm_metas: &[(u64, &[(u64, u64)])],
        log_meta: Option<(u64, u8)>,
        checkpoint_roots: &[(u64, &[u8])],
    ) -> Result<(), Self::Error> {
        for &(index, data) in leaves {
            debug_assert_eq!(
                index,
                self.leaves.len() as u64,
                "write_batch leaf out of order"
            );
            self.leaves.push(data.to_vec());
        }
        for &(alg_id, left, height, hash) in nodes {
            self.nodes.insert((alg_id, left, height), hash.to_vec());
        }
        for &(alg_id, epochs) in algorithm_metas {
            self.algorithm_metas.insert(alg_id, epochs.to_vec());
        }
        if let Some((count, kind)) = log_meta {
            self.log_meta = Some((count, kind));
        }
        for &(alg_id, root) in checkpoint_roots {
            self.checkpoint_roots.insert(alg_id, root.to_vec());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_storage_leaves() {
        smol::block_on(async {
            let mut storage = MemoryStorage::new();
            assert!(storage.is_empty().await.unwrap());
            assert_eq!(storage.len().await.unwrap(), 0);

            storage.store_leaf(0, b"leaf0").await.unwrap();
            assert!(!storage.is_empty().await.unwrap());
            assert_eq!(storage.len().await.unwrap(), 1);
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
