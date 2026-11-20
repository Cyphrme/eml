//! Fjall-backed persistence backend for the EML append-only library.
//!
//! Implements the library's generic `Storage` trait, so it serves any EML
//! instantiation (eml, emt, …) rather than a specific one.
//!
//! # Scoping
//!
//! Many logical logs (e.g. one per Cyphr principal) share one fixed
//! keyspace triplet -- `eml_leaves`, `eml_nodes`, `eml_metadata` -- opened
//! once as [`LogKeyspaces`]. A [`FjallStorage`] is a *scope* over them: every
//! key it touches begins with `u16 BE scope length ++ scope bytes`, so one
//! scope's keys can neither equal nor be a byte-prefix of another's, and a
//! prefix scan is confined to its scope. Scope is a key prefix and not a
//! keyspace name because creating a fjall keyspace costs roughly 14 fsyncs
//! under a database-wide lock.

use std::path::Path;

use fjall::{Database, Keyspace, KeyspaceCreateOptions};
use polydigest::{AlgorithmMetas, Storage, WriteOp};

/// Reserved 9-byte key suffix (after the scope prefix) for log metadata in
/// the `eml_metadata` keyspace.
///
/// All algorithm-epoch key suffixes are exactly 8 bytes (alg_id as big-endian u64), so
/// this 9-byte key never collides with any valid algorithm entry. The key
/// itself keeps its historical 9-byte spelling; the VALUE stored under it is
/// the append count alone, 8 bytes, big-endian -- no kind byte, since a
/// log's kind is derived, never persisted.
const LOG_META_KEY: [u8; 9] = *b"_logmeta_";

/// Encode an epoch list as `eml_metadata`'s per-algorithm value: a sequence
/// of `(start, end)` `u64` big-endian pairs, 16 bytes each -- the inverse of
/// [`FjallStorage::load_algorithm_metas`]'s own decoding.
fn encode_epochs(epochs: &[(u64, u64)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(epochs.len() * 16);
    for &(start, end) in epochs {
        out.extend_from_slice(&start.to_be_bytes());
        out.extend_from_slice(&end.to_be_bytes());
    }
    out
}

/// The node key suffix `get_node`/`apply` share: `alg_id` (8 bytes) ++
/// `left` (8 bytes) ++ `height` (4 bytes), all big-endian.
fn node_suffix(alg_id: u64, left: u64, height: u32) -> [u8; 20] {
    let mut key = [0u8; 20];
    key[0..8].copy_from_slice(&alg_id.to_be_bytes());
    key[8..16].copy_from_slice(&left.to_be_bytes());
    key[16..20].copy_from_slice(&height.to_be_bytes());
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

    /// The supplied scope exceeds the 65535-byte limit of its `u16` length
    /// prefix.
    #[error("invalid scope: {0} bytes exceeds the {max}-byte limit", max = u16::MAX)]
    InvalidScope(usize),

    /// A [`WriteOp`] handed to [`Storage::apply`] violated its own
    /// precondition: an append at a position other than the current count,
    /// a duplicate algorithm registration, or a removal/resume naming an
    /// algorithm this store has never registered.
    #[error("invalid apply operation: {0}")]
    InvalidOperation(String),
}

/// The fixed keyspace triplet every scope shares, opened once per database.
///
/// Cheap to clone (fjall handles are reference-counted). Opening it creates
/// the keyspaces if absent -- the only keyspace creation in this crate --
/// so do it once at startup and hand clones, or a reference, to every
/// [`FjallStorage::scoped`] call.
#[derive(Clone)]
pub struct LogKeyspaces {
    db: Database,
    leaves: Keyspace,
    nodes: Keyspace,
    metadata: Keyspace,
}

impl LogKeyspaces {
    /// Open (creating if absent) `eml_leaves`, `eml_nodes` and
    /// `eml_metadata` in `db`.
    ///
    /// Taking the [`Database`] lets a caller share one physical database --
    /// one journal, atomic cross-keyspace batches -- with its other
    /// partitions.
    ///
    /// # Errors
    ///
    /// [`FjallStorageError::Database`] if a keyspace fails to open.
    pub fn open(db: Database) -> Result<Self, FjallStorageError> {
        let open = |name: &str| {
            db.keyspace(name, KeyspaceCreateOptions::default)
                .map_err(|e| FjallStorageError::Database(e.to_string()))
        };
        let leaves = open("eml_leaves")?;
        let nodes = open("eml_nodes")?;
        let metadata = open("eml_metadata")?;
        Ok(Self {
            db,
            leaves,
            nodes,
            metadata,
        })
    }
}

/// A production-grade EML storage backend backed by a Fjall database: one
/// scope over the shared [`LogKeyspaces`].
///
/// Not `Clone` — enforces single-writer ownership so the tree-level
/// read-count→write-at-count window cannot race across aliased handles.
/// Durability policy (journal sync) is the caller's: [`Storage::apply`]
/// commits one batch and never persists.
pub struct FjallStorage {
    ks: LogKeyspaces,
    /// `u16 BE scope length ++ scope`; prepended to every key.
    prefix: Vec<u8>,
}

impl FjallStorage {
    /// Open or create a Merkle log storage database at `path`, as the
    /// empty scope.
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

    /// Use an existing, shared Fjall database as the empty scope.
    ///
    /// Opens [`LogKeyspaces`] itself; callers that need several scopes
    /// should open it once and use [`Self::scoped`].
    pub fn with_database(db: Database) -> Result<Self, FjallStorageError> {
        Self::scoped(&LogKeyspaces::open(db)?, &[])
    }

    /// A storage over `scope` within `keyspaces`.
    ///
    /// Does no IO and creates no keyspace: it clones three handles and
    /// builds the key prefix, so it is free to call on every load. Distinct
    /// scopes -- including one that is a byte-prefix of another -- are fully
    /// isolated: leaves, nodes, metadata, counts and scans. The empty scope
    /// is what [`Self::open`] and [`Self::with_database`] use.
    ///
    /// # Errors
    ///
    /// [`FjallStorageError::InvalidScope`] if `scope` is longer than 65535
    /// bytes.
    pub fn scoped(keyspaces: &LogKeyspaces, scope: &[u8]) -> Result<Self, FjallStorageError> {
        let len =
            u16::try_from(scope.len()).map_err(|_| FjallStorageError::InvalidScope(scope.len()))?;
        let mut prefix = Vec::with_capacity(2 + scope.len());
        prefix.extend_from_slice(&len.to_be_bytes());
        prefix.extend_from_slice(scope);
        Ok(Self {
            ks: keyspaces.clone(),
            prefix,
        })
    }

    /// Delete every key of this scope, in one fjall batch (fjall has no
    /// keyspace range delete, so the scope's keys are scanned and
    /// tombstoned). Not synced. Other scopes are untouched; the scope may be
    /// reused afterwards from position 0.
    ///
    /// Consumes the handle: it describes a log that no longer exists.
    ///
    /// # Errors
    ///
    /// [`FjallStorageError::Database`] on a scan or commit failure; nothing
    /// is deleted in that case.
    pub fn drop_scope(self) -> Result<(), FjallStorageError> {
        let db_err = |e: fjall::Error| FjallStorageError::Database(e.to_string());
        let mut batch = self.ks.db.batch();
        for ks in [&self.ks.leaves, &self.ks.nodes, &self.ks.metadata] {
            for item in ks.prefix(&self.prefix) {
                batch.remove(ks, item.key().map_err(db_err)?);
            }
        }
        batch.commit().map_err(db_err)
    }

    fn key(&self, suffix: &[u8]) -> Vec<u8> {
        let mut key = Vec::with_capacity(self.prefix.len() + suffix.len());
        key.extend_from_slice(&self.prefix);
        key.extend_from_slice(suffix);
        key
    }

    fn node_key(&self, alg_id: u64, left: u64, height: u32) -> Vec<u8> {
        self.key(&node_suffix(alg_id, left, height))
    }
}

impl Storage for FjallStorage {
    type Error = FjallStorageError;

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        let value = self
            .ks
            .leaves
            .get(self.key(&index.to_be_bytes()))
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
        match self.ks.leaves.prefix(&self.prefix).next_back() {
            None => Ok(0),
            Some(guard) => {
                let key = guard
                    .key()
                    .map_err(|e| FjallStorageError::Database(e.to_string()))?;
                let arr: [u8; 8] = key[self.prefix.len()..].try_into().map_err(|_| {
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
        let value = self
            .ks
            .nodes
            .get(self.node_key(alg_id, left, height))
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(value.map(|bytes| bytes.to_vec()))
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        let mut metas = Vec::new();
        for item in self.ks.metadata.prefix(&self.prefix) {
            let (key_bytes, val_bytes) = item
                .into_inner()
                .map_err(|e| FjallStorageError::Database(e.to_string()))?;
            // Skip the reserved log-metadata entry (9 bytes).
            let key_ref = &key_bytes[self.prefix.len()..];
            if key_ref == LOG_META_KEY {
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
            .ks
            .metadata
            .get(self.key(&LOG_META_KEY))
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        match value {
            None => Ok(0),
            Some(bytes) => {
                if bytes.len() != 8 {
                    return Err(FjallStorageError::MetadataCorruption(
                        "log_meta value must be 8 bytes".to_string(),
                    ));
                }
                Ok(u64::from_be_bytes(bytes[0..8].try_into().unwrap()))
            },
        }
    }

    async fn apply(&mut self, ops: &[WriteOp<'_>]) -> Result<(), Self::Error> {
        let mut count = self.append_count().await?;

        // Validate every op's precondition against a running projection of
        // this store's state before building the batch: an append at the
        // wrong position, a duplicate registration, or a removal/resume
        // naming an unregistered algorithm must be refused before anything
        // is queued, so a rejected call leaves the database untouched.
        let mut projected_count = count;
        for op in ops {
            match op {
                WriteOp::AppendLeaf { at, .. } | WriteOp::AppendSubtree { at, .. } => {
                    if *at != projected_count {
                        return Err(FjallStorageError::InvalidOperation(format!(
                            "append at position {at}, expected the current count {projected_count}"
                        )));
                    }
                    projected_count += 1;
                },
                WriteOp::AddAlgorithm { alg_id, .. } => {
                    let known = self
                        .ks
                        .metadata
                        .get(self.key(&alg_id.to_be_bytes()))
                        .map_err(|e| FjallStorageError::Database(e.to_string()))?
                        .is_some();
                    if known {
                        return Err(FjallStorageError::InvalidOperation(format!(
                            "algorithm {alg_id} is already registered"
                        )));
                    }
                },
                WriteOp::RemoveAlgorithm { alg_id, .. }
                | WriteOp::ResumeAlgorithm { alg_id, .. } => {
                    let known = self
                        .ks
                        .metadata
                        .get(self.key(&alg_id.to_be_bytes()))
                        .map_err(|e| FjallStorageError::Database(e.to_string()))?
                        .is_some();
                    if !known {
                        return Err(FjallStorageError::InvalidOperation(format!(
                            "algorithm {alg_id} is not registered"
                        )));
                    }
                },
                WriteOp::SeedFrontier { .. } => {},
            }
        }

        // Every key this batch touches -- across the leaves, nodes and
        // metadata keyspaces -- lands in one atomic `fjall::WriteBatch`, so
        // a crash between any two ops (or between any two of one op's own
        // component writes) leaves no partial state.
        let mut batch = self.ks.db.batch();

        for op in ops {
            match op {
                WriteOp::AppendLeaf { at, data, nodes } => {
                    batch.insert(&self.ks.leaves, self.key(&at.to_be_bytes()), *data);
                    for n in *nodes {
                        batch.insert(
                            &self.ks.nodes,
                            self.node_key(n.alg_id, n.left, n.height),
                            n.hash,
                        );
                    }
                    count += 1;
                },
                WriteOp::AppendSubtree { at: _, nodes } => {
                    for n in *nodes {
                        batch.insert(
                            &self.ks.nodes,
                            self.node_key(n.alg_id, n.left, n.height),
                            n.hash,
                        );
                    }
                    count += 1;
                },
                WriteOp::AddAlgorithm { alg_id, epochs } => {
                    batch.insert(
                        &self.ks.metadata,
                        self.key(&alg_id.to_be_bytes()),
                        encode_epochs(epochs),
                    );
                },
                WriteOp::RemoveAlgorithm { alg_id, epochs } => {
                    batch.insert(
                        &self.ks.metadata,
                        self.key(&alg_id.to_be_bytes()),
                        encode_epochs(epochs),
                    );
                },
                WriteOp::ResumeAlgorithm {
                    alg_id,
                    epochs,
                    nodes,
                } => {
                    batch.insert(
                        &self.ks.metadata,
                        self.key(&alg_id.to_be_bytes()),
                        encode_epochs(epochs),
                    );
                    for n in *nodes {
                        batch.insert(
                            &self.ks.nodes,
                            self.node_key(n.alg_id, n.left, n.height),
                            n.hash,
                        );
                    }
                },
                WriteOp::SeedFrontier { size, algorithms } => {
                    count = *size;
                    for seed in *algorithms {
                        batch.insert(
                            &self.ks.metadata,
                            self.key(&seed.alg_id.to_be_bytes()),
                            encode_epochs(seed.epochs),
                        );
                        for n in seed.nodes {
                            batch.insert(
                                &self.ks.nodes,
                                self.node_key(n.alg_id, n.left, n.height),
                                n.hash,
                            );
                        }
                    }
                },
            }
        }

        batch.insert(
            &self.ks.metadata,
            self.key(&LOG_META_KEY),
            count.to_be_bytes(),
        );
        batch
            .commit()
            .map_err(|e| FjallStorageError::Database(e.to_string()))?;
        Ok(())
    }
}
