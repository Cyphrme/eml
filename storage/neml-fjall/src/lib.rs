//! Fjall-backed persistence implementation for neml.

use std::path::Path;

use fjall::{Database, Keyspace, KeyspaceCreateOptions};
use neml::{AlgorithmMetas, Storage};

/// Reserved 9-byte key for log metadata in the `neml_metadata` keyspace.
///
/// All algorithm-epoch keys are exactly 8 bytes (alg_id as big-endian u64), so
/// this 9-byte key never collides with any valid algorithm entry.
const LOG_META_KEY: [u8; 9] = [b'_', b'l', b'o', b'g', b'm', b'e', b't', b'a', b'_'];

/// Error type for [`FjallStorage`] operations.
#[derive(Debug, thiserror::Error)]
pub enum FjallStorageError {
    /// An error occurred in the underlying database engine.
    #[error("Database error: {0}")]
    Database(String),

    /// An I/O error occurred.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// Serialized epoch data is malformed or corrupted.
    #[error("Epoch metadata corruption: {0}")]
    MetadataCorruption(String),
}

/// A production-grade neml storage backend backed by a Fjall database.
///
/// Not `Clone` — enforces single-writer ownership so the tree-level
/// read-count→write-at-count window cannot race across aliased handles.
pub struct FjallStorage {
    #[allow(dead_code)]
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
        let db = Database::builder(path)
            .open()
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Self::with_database(db)
    }

    /// Initialize storage keyspaces using an existing, shared Fjall database.
    pub(crate) fn with_database(db: Database) -> Result<Self, FjallStorageError> {
        let leaves = db
            .keyspace("neml_leaves", KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        let nodes = db
            .keyspace("neml_nodes", KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        let metadata = db
            .keyspace("neml_metadata", KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;

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

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        let key = index.to_be_bytes();
        self.leaves
            .insert(key, data)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(())
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        let key = index.to_be_bytes();
        let value = self
            .leaves
            .get(key)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        match value {
            Some(bytes) => Ok(bytes.to_vec()),
            None => Err(FjallStorageError::Io(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("leaf index {index} not found"),
            ))),
        }
    }

    async fn len(&self) -> u64 {
        if let Some(guard) = self.leaves.iter().next_back() {
            if let Ok(key_bytes) = guard.key() {
                if let Ok(arr) = key_bytes.as_ref().try_into() {
                    return u64::from_be_bytes(arr) + 1;
                }
            }
        }
        0
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        let mut key = [0u8; 20];
        key[0..8].copy_from_slice(&alg_id.to_be_bytes());
        key[8..16].copy_from_slice(&left.to_be_bytes());
        key[16..20].copy_from_slice(&height.to_be_bytes());

        self.nodes
            .insert(key, hash)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(())
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        let mut key = [0u8; 20];
        key[0..8].copy_from_slice(&alg_id.to_be_bytes());
        key[8..16].copy_from_slice(&left.to_be_bytes());
        key[16..20].copy_from_slice(&height.to_be_bytes());

        let value = self
            .nodes
            .get(key)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(value.map(|bytes| bytes.to_vec()))
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        let key = alg_id.to_be_bytes();
        let mut bytes = Vec::with_capacity(epochs.len() * 16);
        for &(start, end) in epochs {
            bytes.extend_from_slice(&start.to_be_bytes());
            bytes.extend_from_slice(&end.to_be_bytes());
        }
        self.metadata
            .insert(key, bytes)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(())
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        let mut metas = Vec::new();
        for item in self.metadata.iter() {
            let (key_bytes, val_bytes) = item
                .into_inner()
                .map_err(|e| FjallStorageError::Database(e.to_string()))?;
            // Skip the reserved log-metadata entry (9 bytes, not a valid alg key).
            if key_bytes.as_ref() == LOG_META_KEY {
                continue;
            }
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
                let start_bytes =
                    chunk[0..8]
                        .try_into()
                        .map_err(|e: std::array::TryFromSliceError| {
                            FjallStorageError::MetadataCorruption(e.to_string())
                        })?;
                let end_bytes =
                    chunk[8..16]
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

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
    ) -> Result<(), Self::Error> {
        let mut batch = self.db.batch();

        for &(index, data) in leaves {
            let key = index.to_be_bytes();
            batch.insert(&self.leaves, key, data);
        }

        for &(alg_id, left, height, hash) in nodes {
            let mut key = [0u8; 20];
            key[0..8].copy_from_slice(&alg_id.to_be_bytes());
            key[8..16].copy_from_slice(&left.to_be_bytes());
            key[16..20].copy_from_slice(&height.to_be_bytes());
            batch.insert(&self.nodes, key, hash);
        }

        batch
            .commit()
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(())
    }

    async fn store_log_meta(&mut self, count: u64, kind: u8) -> Result<(), Self::Error> {
        let mut value = [0u8; 9];
        value[0..8].copy_from_slice(&count.to_be_bytes());
        value[8] = kind;
        self.metadata
            .insert(LOG_META_KEY, value)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(())
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        let value = self
            .metadata
            .get(LOG_META_KEY)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        match value {
            None => Ok(None),
            Some(bytes) => {
                if bytes.len() != 9 {
                    return Err(FjallStorageError::MetadataCorruption(
                        "log_meta value must be 9 bytes".to_string(),
                    ));
                }
                let count = u64::from_be_bytes(bytes[0..8].try_into().unwrap());
                let kind = bytes[8];
                Ok(Some((count, kind)))
            }
        }
    }
}
