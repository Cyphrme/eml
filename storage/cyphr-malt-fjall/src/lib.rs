//! Fjall-backed persistence implementation for cyphr-malt.

use std::path::Path;

use cyphr_malt::{AlgorithmMetas, Storage};
use fjall::{Database, Keyspace, KeyspaceCreateOptions};

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

/// A production-grade cyphr-malt storage backend backed by a Fjall database.
///
/// Clones of `FjallStorage` share the same underlying database handle.
#[derive(Clone)]
pub struct FjallStorage {
    db: Database,
    leaves: Keyspace,
    nodes: Keyspace,
    metadata: Keyspace,
}

impl FjallStorage {
    /// Open or create a new Merkle log storage database at the specified directory path.
    ///
    /// # Errors
    ///
    /// Returns a [`FjallStorageError`] if the directory cannot be created or the database
    /// fails to initialize.
    pub fn open(path: &Path) -> Result<Self, FjallStorageError> {
        let db = Database::builder(path).open()?;
        Self::with_database(db)
    }

    /// Initialize storage keyspaces using an existing, shared Fjall database.
    ///
    /// # Errors
    ///
    /// Returns a [`FjallStorageError`] if keyspace initialization fails.
    pub fn with_database(db: Database) -> Result<Self, FjallStorageError> {
        let leaves = db.keyspace("cyphr_malt_leaves", KeyspaceCreateOptions::default)?;
        let nodes = db.keyspace("cyphr_malt_nodes", KeyspaceCreateOptions::default)?;
        let metadata = db.keyspace("cyphr_malt_metadata", KeyspaceCreateOptions::default)?;

        Ok(Self {
            db,
            leaves,
            nodes,
            metadata,
        })
    }
}

impl Storage for FjallStorage {
    type Error = FjallStorageError;

    fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        let key = index.to_be_bytes();
        self.leaves.insert(key, data)?;
        Ok(())
    }

    fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
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

    fn len(&self) -> u64 {
        if let Some(guard) = self.leaves.iter().next_back() {
            if let Ok(key_bytes) = guard.key() {
                if let Ok(arr) = key_bytes.as_ref().try_into() {
                    return u64::from_be_bytes(arr) + 1;
                }
            }
        }
        0
    }

    fn store_node(&mut self, alg_id: u64, node_id: u64, hash: &[u8]) -> Result<(), Self::Error> {
        let mut key = [0u8; 16];
        key[0..8].copy_from_slice(&alg_id.to_be_bytes());
        key[8..16].copy_from_slice(&node_id.to_be_bytes());

        self.nodes.insert(key, hash)?;
        Ok(())
    }

    fn get_node(&self, alg_id: u64, node_id: u64) -> Result<Option<Vec<u8>>, Self::Error> {
        let mut key = [0u8; 16];
        key[0..8].copy_from_slice(&alg_id.to_be_bytes());
        key[8..16].copy_from_slice(&node_id.to_be_bytes());

        let value = self.nodes.get(key)?;
        Ok(value.map(|bytes| bytes.to_vec()))
    }

    fn store_algorithm_meta(&mut self, alg_id: u64, epochs: &[(u64, u64)]) -> Result<(), Self::Error> {
        let key = alg_id.to_be_bytes();
        let mut bytes = Vec::with_capacity(epochs.len() * 16);
        for &(start, end) in epochs {
            bytes.extend_from_slice(&start.to_be_bytes());
            bytes.extend_from_slice(&end.to_be_bytes());
        }
        self.metadata.insert(key, bytes)?;
        Ok(())
    }

    fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        let mut metas = Vec::new();
        for item in self.metadata.iter() {
            let (key_bytes, val_bytes) = item.into_inner()?;
            let alg_id = {
                let arr: [u8; 8] = key_bytes.as_ref().try_into().map_err(|_| {
                    FjallStorageError::MetadataCorruption("invalid key length".to_string())
                })?;
                u64::from_be_bytes(arr)
            };

            if val_bytes.len() % 16 != 0 {
                return Err(FjallStorageError::MetadataCorruption(
                    "metadata value length is not a multiple of 16".to_string(),
                ));
            }

            let mut epochs = Vec::with_capacity(val_bytes.len() / 16);
            for chunk in val_bytes.chunks_exact(16) {
                let start_bytes = chunk[0..8]
                    .try_into()
                    .map_err(|e: std::array::TryFromSliceError| {
                        FjallStorageError::MetadataCorruption(e.to_string())
                    })?;
                let end_bytes = chunk[8..16]
                    .try_into()
                    .map_err(|e: std::array::TryFromSliceError| {
                        FjallStorageError::MetadataCorruption(e.to_string())
                    })?;
                let start = u64::from_be_bytes(start_bytes);
                let end = u64::from_be_bytes(end_bytes);
                epochs.push((start, end));
            }
            metas.push((alg_id, epochs));
        }
        Ok(metas)
    }
}
