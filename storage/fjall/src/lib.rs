//! Fjall-backed persistence implementation for the Epoch Merkle Log (EML).
//!
//! This crate provides [`FjallStorage`], a production-grade implementation of the EML
//! [`Storage`] trait. It stores leaves, internal node hashes, and algorithm metadata
//! in dedicated Fjall partitions inside a shared keyspace.
//!
//! # Architecture
//!
//! `FjallStorage` manages three distinct partitions:
//! - `"eml_leaves"`: Maps leaf index (`u64`) to raw payload bytes.
//! - `"eml_nodes"`: Maps tree node coordinates `(alg_id, left, height)` to hash digests.
//! - `"eml_metadata"`: Maps algorithm ID (`u64`) to serialized active epoch ranges.

use std::path::Path;

use eml::{AlgorithmMetas, Epochs, Storage};
use fjall::{Config, Keyspace, PartitionCreateOptions, PartitionHandle};

/// Error type for [`FjallStorage`] operations.
#[derive(Debug, thiserror::Error)]
pub enum FjallStorageError {
    /// An error occurred in the underlying Fjall engine.
    #[error("Fjall database error: {0}")]
    Fjall(#[from] fjall::Error),

    /// An I/O error occurred.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// Serialized epoch data is malformed or corrupted.
    #[error("Epoch metadata corruption: {0}")]
    MetadataCorruption(String),
}

/// A production-grade EML storage backend backed by a Fjall keyspace.
///
/// Clones of `FjallStorage` share the same underlying database handle.
#[derive(Clone)]
pub struct FjallStorage {
    keyspace: Keyspace,
    leaves: PartitionHandle,
    nodes: PartitionHandle,
    metadata: PartitionHandle,
}

impl FjallStorage {
    /// Open or create a new EML storage keyspace at the specified directory path.
    ///
    /// # Errors
    ///
    /// Returns a [`FjallStorageError`] if the directory cannot be created or the database
    /// keyspace fails to initialize.
    pub fn open(path: &Path) -> Result<Self, FjallStorageError> {
        let keyspace = Config::new(path).open()?;
        Self::with_keyspace(keyspace)
    }

    /// Initialize EML storage partitions using an existing, shared Fjall keyspace.
    ///
    /// This constructor allows reuse of a single keyspace instance (e.g., sharing it
    /// with a concurrent content-addressed blob store).
    ///
    /// # Errors
    ///
    /// Returns a [`FjallStorageError`] if partition initialization fails.
    pub fn with_keyspace(keyspace: Keyspace) -> Result<Self, FjallStorageError> {
        let leaves = keyspace.open_partition("eml_leaves", PartitionCreateOptions::default())?;
        let nodes = keyspace.open_partition("eml_nodes", PartitionCreateOptions::default())?;
        let metadata =
            keyspace.open_partition("eml_metadata", PartitionCreateOptions::default())?;

        Ok(Self {
            keyspace,
            leaves,
            nodes,
            metadata,
        })
    }
}

impl Storage for FjallStorage {
    type Error = FjallStorageError;

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        let key = index.to_be_bytes();
        self.leaves.insert(key, data)?;
        Ok(())
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        let key = index.to_be_bytes();
        let value = self.leaves.get(key)?;
        match value {
            Some(bytes) => Ok(bytes.to_vec()),
            None => Err(FjallStorageError::Io(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("leaf index {index} not found"),
            ))),
        }
    }

    async fn len(&self) -> u64 {
        // len() returns the number of leaves currently stored.
        // We retrieve the count of keys stored in the leaves partition.
        // Fjall's len() provides the partition key count as a Result.
        self.leaves.len().map(|len| len as u64).unwrap_or(0)
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: usize,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        let mut key = [0u8; 24];
        key[0..8].copy_from_slice(&alg_id.to_be_bytes());
        key[8..16].copy_from_slice(&left.to_be_bytes());
        key[16..24].copy_from_slice(&(height as u64).to_be_bytes());

        self.nodes.insert(key, hash)?;
        Ok(())
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: usize,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        let mut key = [0u8; 24];
        key[0..8].copy_from_slice(&alg_id.to_be_bytes());
        key[8..16].copy_from_slice(&left.to_be_bytes());
        key[16..24].copy_from_slice(&(height as u64).to_be_bytes());

        let value = self.nodes.get(key)?;
        Ok(value.map(|bytes| bytes.to_vec()))
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        let key = alg_id.to_be_bytes();
        let value = serialize_epochs(epochs);
        self.metadata.insert(key, value)?;
        Ok(())
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        let mut metas = Vec::new();
        // Iterate through all entries in the metadata partition.
        for result in self.metadata.iter() {
            let (key_bytes, value_bytes) = result?;

            let alg_id = u64::from_be_bytes(key_bytes.as_ref().try_into().map_err(|_| {
                FjallStorageError::MetadataCorruption("Invalid key length".to_string())
            })?);

            let epochs =
                deserialize_epochs(&value_bytes).map_err(FjallStorageError::MetadataCorruption)?;

            metas.push((alg_id, epochs));
        }
        Ok(metas)
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, usize, &[u8])],
    ) -> Result<(), Self::Error> {
        // Implement atomic batch write across both leaf and node partitions
        let mut batch = self.keyspace.batch();

        for &(index, data) in leaves {
            let key = index.to_be_bytes();
            batch.insert(&self.leaves, key, data);
        }

        for &(alg_id, left, height, hash) in nodes {
            let mut key = [0u8; 24];
            key[0..8].copy_from_slice(&alg_id.to_be_bytes());
            key[8..16].copy_from_slice(&left.to_be_bytes());
            key[16..24].copy_from_slice(&(height as u64).to_be_bytes());
            batch.insert(&self.nodes, key, hash);
        }

        // Commit the batch atomically
        batch.commit()?;
        Ok(())
    }
}

/// Helper to serialize active algorithm epochs into bytes.
fn serialize_epochs(epochs: &[(u64, u64)]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(epochs.len() * 16);
    for &(start, end) in epochs {
        bytes.extend_from_slice(&start.to_be_bytes());
        bytes.extend_from_slice(&end.to_be_bytes());
    }
    bytes
}

/// Helper to deserialize active algorithm epochs from bytes.
fn deserialize_epochs(bytes: &[u8]) -> Result<Epochs, String> {
    if bytes.len() % 16 != 0 {
        return Err(format!("Invalid metadata length: {}", bytes.len()));
    }
    let mut epochs = Vec::with_capacity(bytes.len() / 16);
    for chunk in bytes.chunks_exact(16) {
        let start = u64::from_be_bytes(chunk[0..8].try_into().unwrap());
        let end = u64::from_be_bytes(chunk[8..16].try_into().unwrap());
        epochs.push((start, end));
    }
    Ok(epochs)
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[tokio::test]
    async fn test_atomic_batch_abort() {
        let dir = tempdir().unwrap();
        let storage = FjallStorage::open(dir.path()).unwrap();

        // Verify initial state is empty
        assert_eq!(storage.len().await, 0);

        // Open a batch, perform inserts, then drop the batch without committing
        {
            let mut batch = storage.keyspace.batch();
            batch.insert(&storage.leaves, 0u64.to_be_bytes(), b"should_not_exist");
            let mut node_key = [0u8; 24];
            node_key[0..8].copy_from_slice(&99u64.to_be_bytes());
            batch.insert(&storage.nodes, node_key, b"should_not_exist_node");
            // batch is dropped here
        }

        // Verify partitions remain empty
        assert_eq!(storage.len().await, 0);
        assert!(storage.get_leaf(0).await.is_err());
        assert!(storage.get_node(99, 0, 0).await.unwrap().is_none());
    }
}
