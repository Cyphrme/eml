//! Fjall-backed persistence backend for the EML append-only library.
//!
//! Implements the library's generic `Storage` trait, so it serves any EML
//! instantiation (eml, emt, …) rather than a specific one.

use std::path::Path;

use fjall::{Database, Keyspace, KeyspaceCreateOptions};
use polydigest::{AlgorithmMetas, Storage, WriteOp};

/// Reserved 9-byte key for log metadata in the `eml_metadata` keyspace.
///
/// All algorithm-epoch keys are exactly 8 bytes (alg_id as big-endian u64), so
/// this 9-byte key never collides with any valid algorithm entry. The
/// trailing byte was the now-dropped kind byte (a log's kind is derived,
/// never persisted); [`FjallStorage::append_count`] reads only the leading
/// 8 bytes.
const LOG_META_KEY: [u8; 9] = *b"_logmeta_";

/// 10-byte key prefix for per-algorithm checkpoint roots in `eml_metadata`.
///
/// Format: `[b'r', b'o', alg_id_be_bytes[0..8]]` — does not collide with the
/// 8-byte epoch keys or the 9-byte LOG_META_KEY.
#[allow(
    dead_code,
    reason = "unreachable from the crate's own (stubbed) apply() until it lands; the key scheme \
              itself is unchanged by the operation-enum redesign"
)]
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

    /// The supplied keyspace-scoping prefix is invalid.
    #[error("invalid keyspace prefix: {0:?}")]
    InvalidPrefix(String),
}

/// A production-grade EML storage backend backed by a Fjall database.
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
    ///
    /// Lets a caller that owns its own [`Database`] (e.g. to share one
    /// physical database — one WAL, atomic cross-keyspace batches — with
    /// other partitions it manages) hand it to this storage backend instead
    /// of having [`Self::open`] create a dedicated one.
    pub fn with_database(db: Database) -> Result<Self, FjallStorageError> {
        let leaves = db
            .keyspace("eml_leaves", KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        let nodes = db
            .keyspace("eml_nodes", KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        let metadata = db
            .keyspace("eml_metadata", KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;

        Ok(Self {
            db,
            leaves,
            nodes,
            metadata,
        })
    }

    /// Initialize storage keyspaces under a caller-supplied scope, using an
    /// existing, shared Fjall database.
    ///
    /// [`Self::with_database`] opens fixed keyspace names
    /// (`eml_leaves`/`eml_nodes`/`eml_metadata`), so two [`FjallStorage`]
    /// instances sharing one physical [`Database`] would read and write the
    /// same keyspaces. That's fine for content-addressed data, but EML's
    /// leaf/node keys are positional (leaf index; alg_id+left+height), so
    /// two unrelated logical logs' "leaf 0" would collide at the identical
    /// key. This constructor opens `{prefix}_eml_leaves` /
    /// `{prefix}_eml_nodes` / `{prefix}_eml_metadata` instead, so distinct
    /// prefixes give each logical log (e.g. each Cyphr principal) its own
    /// isolated triplet within the same database.
    ///
    /// # Errors
    ///
    /// Returns [`FjallStorageError::InvalidPrefix`] if `prefix` is empty,
    /// contains characters outside fjall's documented keyspace-name charset
    /// (alphanumeric, `_`, `-`, `.`, `#`, `$`), or would produce a keyspace
    /// name exceeding fjall's 255-byte limit. Returns
    /// [`FjallStorageError::Database`] if the underlying keyspaces fail to
    /// open.
    pub fn with_database_scoped(db: Database, prefix: &str) -> Result<Self, FjallStorageError> {
        if prefix.is_empty()
            || !prefix
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.' | '#' | '$'))
        {
            return Err(FjallStorageError::InvalidPrefix(prefix.to_string()));
        }

        let leaves_name = format!("{prefix}_eml_leaves");
        let nodes_name = format!("{prefix}_eml_nodes");
        let metadata_name = format!("{prefix}_eml_metadata");

        // metadata_name is always the longest of the three suffixes, so
        // bounding it bounds the other two.
        if metadata_name.len() > 255 {
            return Err(FjallStorageError::InvalidPrefix(prefix.to_string()));
        }

        let leaves = db
            .keyspace(&leaves_name, KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        let nodes = db
            .keyspace(&nodes_name, KeyspaceCreateOptions::default)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        let metadata = db
            .keyspace(&metadata_name, KeyspaceCreateOptions::default)
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

    async fn append_count(&self) -> Result<u64, Self::Error> {
        let value = self
            .metadata
            .get(LOG_META_KEY)
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        match value {
            None => Ok(0),
            Some(bytes) => {
                if bytes.len() != 9 {
                    return Err(FjallStorageError::MetadataCorruption(
                        "log_meta value must be 9 bytes".to_string(),
                    ));
                }
                Ok(u64::from_be_bytes(bytes[0..8].try_into().unwrap()))
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

    async fn apply(&mut self, _ops: &[WriteOp<'_>]) -> Result<(), Self::Error> {
        // Deliberately unimplemented: the operation-enum write path (head's
        // ruling 2026-09-17) has no landed implementation on this backend
        // yet. The previous five-parameter `write_batch` assembly this file
        // held is gone with it rather than left as dead code nothing calls
        // -- see `git log` for that version if it is useful as a starting
        // point.
        unimplemented!("FjallStorage::apply: the operation-enum write path is not implemented yet")
    }
}
