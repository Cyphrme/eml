//! Fjall-backed persistence backend for the EML append-only library.
//!
//! Implements the library's generic `Storage` trait, so it serves any EML
//! instantiation (cyphr-log, CT, …) rather than a specific one.

use std::path::Path;

use epoch::{AlgorithmMetas, Storage};
use fjall::{Database, Keyspace, KeyspaceCreateOptions, PersistMode};

/// Reserved 9-byte key for log metadata in the `neml_metadata` keyspace.
///
/// All algorithm-epoch keys are exactly 8 bytes (alg_id as big-endian u64), so
/// this 9-byte key never collides with any valid algorithm entry.
const LOG_META_KEY: [u8; 9] = *b"_logmeta_";

/// 10-byte key prefix for per-algorithm checkpoint roots in `neml_metadata`.
///
/// Format: `[b'r', b'o', alg_id_be_bytes[0..8]]` — does not collide with the
/// 8-byte epoch keys or the 9-byte LOG_META_KEY.
fn checkpoint_root_key(alg_id: u64) -> [u8; 10] {
    let mut key = [0u8; 10];
    key[0] = b'r';
    key[1] = b'o';
    key[2..10].copy_from_slice(&alg_id.to_be_bytes());
    key
}

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

    async fn len(&self) -> Result<u64, Self::Error> {
        match self.leaves.iter().next_back() {
            None => Ok(0),
            Some(guard) => {
                let key = guard
                    .key()
                    .map_err(|e| FjallStorageError::Database(e.to_string()))?;
                let arr: [u8; 8] = key.as_ref().try_into().map_err(|_| {
                    FjallStorageError::MetadataCorruption("leaf key has wrong length".to_string())
                })?;
                Ok(u64::from_be_bytes(arr) + 1)
            },
        }
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
            // Skip reserved entries: log-metadata (9 bytes) and checkpoint roots (10 bytes).
            let key_ref = key_bytes.as_ref();
            if key_ref == LOG_META_KEY
                || (key_ref.len() == 10 && key_ref[0] == b'r' && key_ref[1] == b'o')
            {
                continue;
            }
            let alg_id = {
                let arr: [u8; 8] = key_ref.try_into().map_err(|_| {
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
            },
        }
    }

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        let mut roots = Vec::new();
        for item in self.metadata.iter() {
            let (key_bytes, val_bytes) = item
                .into_inner()
                .map_err(|e| FjallStorageError::Database(e.to_string()))?;
            let key_ref = key_bytes.as_ref();
            if key_ref.len() == 10 && key_ref[0] == b'r' && key_ref[1] == b'o' {
                let arr: [u8; 8] = key_ref[2..10].try_into().map_err(|_| {
                    FjallStorageError::MetadataCorruption(
                        "checkpoint root key has wrong alg_id length".to_string(),
                    )
                })?;
                let alg_id = u64::from_be_bytes(arr);
                roots.push((alg_id, val_bytes.to_vec()));
            }
        }
        Ok(roots)
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
        algorithm_metas: &[(u64, &[(u64, u64)])],
        log_meta: Option<(u64, u8)>,
        checkpoint_roots: &[(u64, &[u8])],
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

        for &(alg_id, epochs) in algorithm_metas {
            let key = alg_id.to_be_bytes();
            let mut bytes = Vec::with_capacity(epochs.len() * 16);
            for &(start, end) in epochs {
                bytes.extend_from_slice(&start.to_be_bytes());
                bytes.extend_from_slice(&end.to_be_bytes());
            }
            batch.insert(&self.metadata, key, bytes);
        }

        if let Some((count, kind)) = log_meta {
            let mut value = [0u8; 9];
            value[0..8].copy_from_slice(&count.to_be_bytes());
            value[8] = kind;
            batch.insert(&self.metadata, LOG_META_KEY, value);
        }

        for &(alg_id, root) in checkpoint_roots {
            let key = checkpoint_root_key(alg_id);
            batch.insert(&self.metadata, key, root);
        }

        batch
            .durability(Some(PersistMode::SyncAll))
            .commit()
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;

        Ok(())
    }
}
