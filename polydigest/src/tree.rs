//! The combinator driver: the multi-algorithm append-only log over one shared
//! data substrate.
//!
//! [`NaryMerkleLog`] is the **polydigest combinator's** runnable driver. It owns the
//! one shared store and, per algorithm, a single [`cml::AlgView`] frontier; it
//! drives **N** single-algorithm CML engines over that **one** substrate (D14 —
//! leaf data lives once, each algorithm is a frontier/hash view). The structural
//! per-algorithm work — the frontier carry, the proof generation, the root folds
//! — is the CML engine's; the combinator owns the timeline, the combined/binding
//! root, the atomic multi-tree append, and the seal.

use std::collections::HashMap;

use cml::engine::{self, AlgView};
use cml::{LogKind, reduction_count};
use spine::{
    ARITY_RANGE, Hasher, Subtree, constant_time_eq, evaluate, fold_frontier, frontier_for_size,
    nary_mr,
};

use crate::log_error::{LogError, LogResult as Result};
use crate::root::{
    combined_root, committed_active_algs, committed_active_at, validate_committed_epochs,
};
use crate::storage::{Storage, StorageReader};

/// Configuration for the n-ary Merkle tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TreeConfig {
    /// Arity for log-level nodes (k >= 2).
    /// Controls the base-k carry reduction schedule.
    pub arity: u64,
}

impl Default for TreeConfig {
    fn default() -> Self {
        Self { arity: 2 }
    }
}

/// An n-ary Merkle Append-Only Log — the polydigest combinator's driver over one
/// shared data substrate.
///
/// Owns the one storage backend and, per algorithm, a single [`AlgView`]
/// frontier (`algs`); the leaf data lives once in `storage`, each algorithm
/// contributing only its frontier/hash view (D14). The structural per-algorithm
/// operations delegate to the CML engine.
#[derive(Debug, Clone)]
pub struct NaryMerkleLog<S: Storage> {
    storage: S,
    config: TreeConfig,
    algs: HashMap<u64, AlgView>,
    /// Total number of log-level appends (leaves for `Flat`, subtrees for `Subtree`).
    count: u64,
    /// Whether appends are flat leaf or subtree appends.
    kind: LogKind,
}

/// Owned batch data computed by `build_append_state`.
///
/// Passed verbatim to `write_batch`; assembled before any state mutation so
/// a storage failure leaves `self.algs` and `self.count` unchanged.
/// Leaf payloads are not included here — `append_leaf` passes them directly
/// to `write_batch` because the raw bytes are also stored separately.
struct OwnedBatch {
    nodes: Vec<(u64, u64, u32, Vec<u8>)>,
    log_meta: Option<(u64, u8)>,
    checkpoint_roots: Vec<(u64, Vec<u8>)>,
}

impl<S: Storage> NaryMerkleLog<S> {
    /// Create a new empty n-ary Merkle log.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the initialization fails.
    pub async fn new(
        storage: S,
        hasher: Box<dyn Hasher>,
        config: TreeConfig,
    ) -> Result<Self, S::Error> {
        if !ARITY_RANGE.contains(&(config.arity)) {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: format!(
                    "invalid arity: must be between 2 and 256, got {}",
                    config.arity
                ),
            });
        }
        let mut log = Self {
            storage,
            config,
            algs: HashMap::new(),
            count: 0,
            kind: LogKind::Flat,
        };
        // Eagerly register algorithm 0 as active from index 0
        log.add_algorithm(0, hasher).await?;
        Ok(log)
    }

    /// **Resume** an append-only log onto the committed frontier of a
    /// [`crate::Sealed`], consuming nothing but the frontier.
    ///
    /// `resume` needs *only* the frontier — which a `Sealed` *is* — so it is
    /// **always available for any source kind, with no failure conditions**
    /// beyond storage I/O and a per-algorithm hasher. The `Sealed`'s frontier
    /// (sparse or dense, nulls and all) becomes the resumed log's **genesis
    /// frontier**: an EML is "a committed frontier you append real leaves onto"
    /// (the MMR view), never "a pure append-from-empty sequence", so nulls in
    /// the genesis frontier (e.g. from a sparse EMT origin) are admitted and
    /// forward appends add real leaves. The resumed log **cannot read the
    /// committed past** — only the peaks are carried, not the interior history —
    /// which is exactly the seal's one-way guarantee; the path to a readable
    /// historical tree is [`fill`](crate::fill), not `resume`.
    ///
    /// The resumed log is [`LogKind::Subtree`]: the committed past is not
    /// materialized as a dense leaf array, so a forward real leaf is appended as
    /// a single-leaf subtree via [`Self::append_subtree`] — whose digest is the
    /// leaf hash, byte-identical to a flat append. The frontier carry proceeds
    /// from the genesis frontier exactly as a fresh log's would from empty.
    ///
    /// `storage` is a fresh backend the resumed log writes forward into;
    /// `hashers` resolves each active algorithm's own hash (the `Sealed` froze
    /// digests, not hashers). Every algorithm carried in the `Sealed`'s frontier
    /// is reopened at the sealed size under its committed timeline; folding the
    /// seeded frontier reproduces that algorithm's sealed member root, so a
    /// consistency proof bridges the resume.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] if an algorithm in the frontier has
    /// no hasher in `hashers`, [`LogError::CorruptedMetadata`] on an invalid arity,
    /// or a storage error if the seeded frontier cannot be persisted.
    pub async fn resume(
        sealed: &crate::Sealed,
        mut storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
    ) -> Result<Self, S::Error> {
        let k = sealed.arity();
        if !ARITY_RANGE.contains(&k) {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: format!("invalid arity in sealed frontier: {k}"),
            });
        }
        let config = TreeConfig { arity: k };
        let size = sealed.tree_size();
        let coords = frontier_for_size(size, k);

        let mut hasher_map: HashMap<u64, Box<dyn Hasher>> = hashers.into_iter().collect();

        let mut algs = HashMap::new();
        let mut node_batch: Vec<(u64, u64, u32, Vec<u8>)> = Vec::new();
        let mut meta_batch: Vec<(u64, Vec<(u64, u64)>)> = Vec::new();
        let mut checkpoint_batch: Vec<(u64, Vec<u8>)> = Vec::new();

        for (alg_id, peaks) in sealed.frontiers() {
            let hasher = hasher_map
                .remove(alg_id)
                .ok_or(LogError::UnknownAlgorithm(*alg_id))?;

            // The resumed algorithm's committed timeline is carried from the
            // seal so its binding root at the sealed size is reproduced; a live
            // resumed algorithm keeps its open epoch.
            let epochs: Vec<(u64, u64)> = sealed
                .alg_epochs()
                .iter()
                .find(|(id, _)| id == alg_id)
                .map(|(_, e)| e.clone())
                .unwrap_or_else(|| vec![(0, u64::MAX)]);

            let view = AlgView {
                hasher,
                epochs: epochs.clone(),
                frontier: peaks.clone(),
                frontier_coords: coords.clone(),
            };

            // Persist the genesis frontier peaks (active ranges only) and the
            // checkpoint root so the resumed log is reloadable and forward
            // appends read a consistent frontier back.
            for (&(left, height), peak) in coords.iter().zip(peaks.iter()) {
                let cap = k.pow(height);
                if view.active_range(left, left + cap) {
                    node_batch.push((*alg_id, left, height, peak.clone()));
                }
            }
            let root = engine::compute_root(&view, k as usize);
            checkpoint_batch.push((*alg_id, root));
            meta_batch.push((*alg_id, epochs));
            algs.insert(*alg_id, view);
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = node_batch
            .iter()
            .map(|(id, left, height, h)| (*id, *left, *height, h.as_slice()))
            .collect();
        let metas_ref: Vec<(u64, &[(u64, u64)])> = meta_batch
            .iter()
            .map(|(id, e)| (*id, e.as_slice()))
            .collect();
        let checkpoints_ref: Vec<(u64, &[u8])> = checkpoint_batch
            .iter()
            .map(|(id, r)| (*id, r.as_slice()))
            .collect();

        storage
            .write_batch(
                &[],
                &nodes_ref,
                &metas_ref,
                Some((size, LogKind::Subtree.to_byte())),
                &checkpoints_ref,
            )
            .await
            .map_err(LogError::Storage)?;

        // A resumed log is subtree-kind: the committed past is not materialized
        // as a dense leaf array (the seal carried only the frontier peaks, not
        // the historical leaves), so forward appends commit leaf *digests* as
        // nodes rather than raw payloads. A single-leaf subtree's digest is the
        // leaf hash, so forward "real leaf" appends are byte-identical to a flat
        // append — the frontier-anchored model, with the past kept unreadable.
        Ok(Self {
            storage,
            config,
            algs,
            count: size,
            kind: LogKind::Subtree,
        })
    }

    /// Reconstruct an existing Merkle log from storage using the default configuration.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the reconstruction fails.
    pub async fn from_storage(
        storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
    ) -> Result<Self, S::Error> {
        Self::from_storage_with_config(storage, hashers, TreeConfig::default()).await
    }

    /// Reconstruct an existing Merkle log from storage with a specific configuration.
    ///
    /// # Errors
    ///
    /// Returns a storage error or validation error if the reconstruction fails.
    pub async fn from_storage_with_config(
        storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
        config: TreeConfig,
    ) -> Result<Self, S::Error> {
        if !ARITY_RANGE.contains(&(config.arity)) {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: format!(
                    "invalid arity: must be between 2 and 256, got {}",
                    config.arity
                ),
            });
        }

        let metas = storage
            .load_algorithm_metas()
            .await
            .map_err(LogError::Storage)?;

        let mut hasher_map: HashMap<u64, Box<dyn Hasher>> = hashers.into_iter().collect();

        // Validate 1:1 correspondence and duplicate IDs.
        let mut seen = std::collections::HashSet::new();
        for &(alg_id, _) in &metas {
            if !seen.insert(alg_id) {
                return Err(LogError::DuplicateAlgorithm(alg_id));
            }
            if !hasher_map.contains_key(&alg_id) {
                return Err(LogError::OrphanedMetadata(alg_id));
            }
        }
        let meta_ids: std::collections::HashSet<u64> = metas.iter().map(|&(id, _)| id).collect();
        for &alg_id in hasher_map.keys() {
            if !meta_ids.contains(&alg_id) {
                return Err(LogError::UnknownMetadata(alg_id));
            }
        }

        // Recover authoritative (count, kind) from persisted log metadata when
        // available; fall back to deterministic probing for legacy stores.
        let (global_size, kind) = match storage.load_log_meta().await.map_err(LogError::Storage)? {
            Some((count, kind_byte)) => {
                let kind =
                    LogKind::from_byte(kind_byte).ok_or_else(|| LogError::CorruptedMetadata {
                        alg_id: 0,
                        reason: format!("unknown LogKind byte: {kind_byte}"),
                    })?;
                (count, kind)
            },
            None => {
                let size = Self::determine_global_size(&storage, &metas).await?;
                let kind = if storage.len().await.map_err(LogError::Storage)? > 0 {
                    LogKind::Flat
                } else {
                    LogKind::Subtree
                };
                (size, kind)
            },
        };

        let mut algs = HashMap::new();
        let k = config.arity;
        for (alg_id, epochs) in metas {
            let hasher = hasher_map
                .remove(&alg_id)
                .ok_or(LogError::OrphanedMetadata(alg_id))?;
            let view = engine::reconstruct_view(
                &StorageReader(&storage),
                alg_id,
                hasher,
                &epochs,
                global_size,
                k,
            )
            .await?;
            algs.insert(alg_id, view);
        }

        // V6: verify loaded frontier against stored checkpoint roots.
        // A corrupted frontier node will produce a different root from the one
        // committed at write time, detecting the corruption before the log is used.
        let stored_roots: HashMap<u64, Vec<u8>> = storage
            .load_checkpoint_roots()
            .await
            .map_err(LogError::Storage)?
            .into_iter()
            .collect();

        for (&alg_id, view) in &algs {
            if let Some(stored_root) = stored_roots.get(&alg_id) {
                let actual_root = engine::compute_root(view, config.arity as usize);
                if &actual_root != stored_root {
                    return Err(LogError::CorruptedMetadata {
                        alg_id,
                        reason: format!(
                            "checkpoint root mismatch for algorithm {alg_id}: recomputed root \
                             differs from stored checkpoint"
                        ),
                    });
                }
            }
        }

        Ok(Self {
            storage,
            config,
            algs,
            count: global_size,
            kind,
        })
    }

    /// Build the next-state algorithm map and the batch to write, without
    /// mutating `self`.
    ///
    /// `digest_fn(alg_id, view)` returns the per-algorithm digest for the item
    /// being appended and any leaf-level node to persist. Returns the proposed
    /// new algorithm map and an [`OwnedBatch`] ready to pass directly to
    /// `write_batch`. The caller MUST write the batch to storage before swapping
    /// the returned map into `self.algs`.
    fn build_append_state<F>(
        &self,
        kind: LogKind,
        digest_fn: F,
    ) -> Result<(HashMap<u64, AlgView>, OwnedBatch), S::Error>
    where
        F: Fn(u64, &AlgView) -> (Vec<u8>, Option<(u64, u64, u32, Vec<u8>)>),
        S::Error: Send,
    {
        let mut new_algs = self.algs.clone();
        let mut batch_nodes: Vec<(u64, u64, u32, Vec<u8>)> = Vec::new();
        let log_meta_kind = kind;

        for (&alg_id, view) in &mut new_algs {
            if !view.is_active() {
                continue;
            }

            let (digest, extra_node) = digest_fn(alg_id, view);
            if let Some(node) = extra_node {
                batch_nodes.push(node);
            }

            // The single-algorithm frontier carry is the CML engine's; the
            // combinator drives it once per active algorithm over the one store.
            engine::carry(
                view,
                alg_id,
                digest,
                self.count,
                self.config.arity,
                &mut batch_nodes,
            )?;
        }

        let new_count = self.count + 1;
        let checkpoint_roots: Vec<(u64, Vec<u8>)> = new_algs
            .iter()
            .filter(|(_, s)| s.is_active())
            .map(|(&alg_id, s)| {
                let root = engine::compute_root(s, self.config.arity as usize);
                (alg_id, root)
            })
            .collect();

        let batch = OwnedBatch {
            nodes: batch_nodes,
            log_meta: Some((new_count, log_meta_kind.to_byte())),
            checkpoint_roots,
        };

        Ok((new_algs, batch))
    }

    /// Probe storage to estimate the current global size (legacy fallback only).
    ///
    /// Called only when no authoritative log metadata has been persisted. Sorts
    /// algorithms by ID before probing so the result is deterministic across
    /// replicas regardless of `HashMap` iteration order. Uses a linear scan
    /// rather than binary search because level-0 node presence is not guaranteed
    /// to be monotonic across deactivation/reactivation gaps.
    async fn determine_global_size(
        storage: &S,
        metas: &[(u64, Vec<(u64, u64)>)],
    ) -> Result<u64, S::Error> {
        let leaf_len = storage.len().await.map_err(LogError::Storage)?;
        if leaf_len > 0 {
            return Ok(leaf_len);
        }

        let mut max_frozen_end = 0u64;
        let mut active_algs: Vec<(u64, u64)> = Vec::new();
        for &(alg_id, ref epochs) in metas {
            if let Some(&(start, end)) = epochs.last() {
                if end == u64::MAX {
                    active_algs.push((alg_id, start));
                } else if end > max_frozen_end {
                    max_frozen_end = end;
                }
            }
        }

        if active_algs.is_empty() {
            return Ok(max_frozen_end);
        }

        // Deterministic probe target: lowest alg_id avoids HashMap ordering dependency.
        active_algs.sort_unstable_by_key(|&(id, _)| id);
        let (alg_id, start) = active_algs[0];

        // Linear scan: binary search is unsafe here because level-0 node presence
        // is non-monotonic across deactivation/reactivation gaps.
        let mut size = start;
        loop {
            if storage
                .get_node(alg_id, size, 0)
                .await
                .map_err(LogError::Storage)?
                .is_none()
            {
                break;
            }
            size += 1;
        }
        Ok(size)
    }

    /// Retrieve the tree configuration.
    #[must_use]
    pub fn config(&self) -> &TreeConfig {
        &self.config
    }

    /// Total number of log-level appends regardless of kind.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether this log uses flat leaf or subtree appends.
    #[must_use]
    pub fn kind(&self) -> LogKind {
        self.kind
    }

    /// Number of flat leaf appends (0 for subtree logs).
    #[must_use]
    pub fn size(&self) -> u64 {
        if self.kind == LogKind::Flat {
            self.count
        } else {
            0
        }
    }

    /// Number of subtree appends (0 for flat logs).
    #[must_use]
    pub fn subtree_count(&self) -> u64 {
        if self.kind == LogKind::Subtree {
            self.count
        } else {
            0
        }
    }

    /// Access the frontier stack of the default algorithm (0).
    #[must_use]
    pub fn frontier(&self) -> &[Vec<u8>] {
        self.frontier_for(0).unwrap_or(&[])
    }

    /// Access the frontier stack of a specific algorithm.
    #[must_use]
    pub fn frontier_for(&self, alg_id: u64) -> Option<&[Vec<u8>]> {
        self.algs.get(&alg_id).map(|s| s.frontier.as_slice())
    }

    /// Consume the log and return the underlying storage backend.
    #[must_use]
    pub fn into_storage(self) -> S {
        self.storage
    }

    /// Borrow the underlying storage backend.
    #[must_use]
    pub fn storage(&self) -> &S {
        &self.storage
    }

    /// Mutable access to the underlying storage backend.
    ///
    /// Bypasses all tree invariants (size tracking, checkpoint roots).
    /// Intended for test-only tampering; production callers should use the
    /// tree API.  V3 race safety is structural (non-Clone `FjallStorage`),
    /// not dependent on hiding this method.
    #[doc(hidden)]
    pub fn storage_mut(&mut self) -> &mut S {
        &mut self.storage
    }

    /// Register a new algorithm, activating it at the current tree size.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::DuplicateAlgorithm`] if already registered, or a
    /// storage error.
    pub async fn add_algorithm(
        &mut self,
        alg_id: u64,
        hasher: Box<dyn Hasher>,
    ) -> Result<(), S::Error> {
        if self.algs.contains_key(&alg_id) {
            return Err(LogError::DuplicateAlgorithm(alg_id));
        }

        let current_size = self.count;

        let epochs = vec![(current_size, u64::MAX)];

        // Persist metadata BEFORE committing in-memory state.
        self.storage
            .store_algorithm_meta(alg_id, &epochs)
            .await
            .map_err(LogError::Storage)?;

        let k = self.config.arity;
        let coords = frontier_for_size(current_size, k);
        let stack = vec![hasher.null(); coords.len()];

        self.algs.insert(
            alg_id,
            AlgView {
                hasher,
                epochs,
                frontier: stack,
                frontier_coords: coords,
            },
        );

        Ok(())
    }

    /// Deactivate (freeze) an algorithm at the current tree size.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] / [`LogError::FrozenAlgorithm`], or
    /// a storage error.
    pub async fn remove_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = self.count;

        let view = self
            .algs
            .get_mut(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;

        if !view.is_active() {
            return Err(LogError::FrozenAlgorithm(alg_id));
        }

        let mut new_epochs = view.epochs.clone();
        if let Some(last) = new_epochs.last_mut() {
            last.1 = current_size;
        }

        // Build updated state for checkpoint root computation.
        let frozen_root = {
            let frozen = AlgView {
                hasher: view.hasher.clone_box(),
                epochs: new_epochs.clone(),
                frontier: view.frontier.clone(),
                frontier_coords: view.frontier_coords.clone(),
            };
            engine::compute_root(&frozen, self.config.arity as usize)
        };

        let epochs_ref: &[(u64, u64)] = &new_epochs;
        // Commit epoch update + checkpoint root atomically (mirrors resume_algorithm).
        self.storage
            .write_batch(
                &[],
                &[],
                &[(alg_id, epochs_ref)],
                None,
                &[(alg_id, frozen_root.as_slice())],
            )
            .await
            .map_err(LogError::Storage)?;

        let view = self
            .algs
            .get_mut(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        view.epochs = new_epochs;
        Ok(())
    }

    /// Reactivate a frozen algorithm at the current tree size.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] / [`LogError::AlgorithmActive`], or
    /// a storage error.
    pub async fn resume_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = self.count;

        let mut new_epochs = {
            let view = self
                .algs
                .get(&alg_id)
                .ok_or(LogError::UnknownAlgorithm(alg_id))?;

            if view.is_active() {
                return Err(LogError::AlgorithmActive(alg_id));
            }

            view.epochs.clone()
        };

        new_epochs.push((current_size, u64::MAX));

        let k = self.config.arity;
        let coords = frontier_for_size(current_size, k);
        let mut frontier = Vec::with_capacity(coords.len());

        let temp_view = {
            let view = &self.algs[&alg_id];
            AlgView {
                hasher: view.hasher.clone_box(),
                epochs: new_epochs.clone(),
                frontier: Vec::new(),
                frontier_coords: Vec::new(),
            }
        };

        let mut mixed_to_store = Vec::new();
        for &(left, height) in &coords {
            let cap = k.pow(height);
            let (hash, mixed) = engine::reconstruct_subtree_root(
                &StorageReader(&self.storage),
                alg_id,
                &temp_view,
                left,
                left + cap,
                k,
                self.kind,
                true,
            )
            .await?;
            frontier.push(hash);
            mixed_to_store.extend(mixed);
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = mixed_to_store
            .iter()
            .map(|&(left, height, ref hash)| (alg_id, left, height, hash.as_slice()))
            .collect();

        // Compute the checkpoint root for the resumed algorithm from its new frontier.
        let resumed_view = AlgView {
            hasher: self.algs[&alg_id].hasher.clone_box(),
            epochs: new_epochs.clone(),
            frontier: frontier.clone(),
            frontier_coords: coords.clone(),
        };
        let resumed_root = engine::compute_root(&resumed_view, self.config.arity as usize);

        let epochs_ref: &[(u64, u64)] = &new_epochs;
        // Commit nodes + epoch update + checkpoint root atomically (closes V13).
        self.storage
            .write_batch(
                &[],
                &nodes_ref,
                &[(alg_id, epochs_ref)],
                None,
                &[(alg_id, resumed_root.as_slice())],
            )
            .await
            .map_err(LogError::Storage)?;

        let view = self
            .algs
            .get_mut(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        view.epochs = new_epochs;
        view.frontier = frontier;
        view.frontier_coords = coords;

        Ok(())
    }

    /// Append a single flat leaf to the log.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] on a kind conflict, capacity overflow, no active
    /// algorithms, or a storage error.
    pub async fn append_leaf(&mut self, data: &[u8]) -> Result<(), S::Error> {
        // Kind is only binding once an append has happened; an empty log
        // (including one reloaded from an empty store) accepts either kind.
        if self.kind == LogKind::Subtree && self.count > 0 {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append leaf after subtree appends".to_string(),
            });
        }

        if self.count >= (1u64 << 47) {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }

        if !self.algs.values().any(|s| s.is_active()) {
            return Err(LogError::NoActiveAlgorithms);
        }

        // `build_append_state` takes &self: the new alg map and batch are
        // assembled without touching self.algs; the swap happens only after
        // write_batch succeeds (structural rollback guarantee).
        let (new_algs, batch) = self.build_append_state(LogKind::Flat, |alg_id, view| {
            if view.is_active_at(self.count) {
                let leaf_hash = view.hasher.leaf(data);
                let node = (alg_id, self.count, 0u32, leaf_hash.clone());
                (leaf_hash, Some(node))
            } else {
                (view.hasher.null(), None)
            }
        })?;

        let leaf_entry = (self.count, data.to_vec());
        let leaves_ref: &[(u64, &[u8])] = &[(leaf_entry.0, leaf_entry.1.as_slice())];
        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = batch
            .nodes
            .iter()
            .map(|(a, l, h, hash)| (*a, *l, *h, hash.as_slice()))
            .collect();
        let checkpoint_refs: Vec<(u64, &[u8])> = batch
            .checkpoint_roots
            .iter()
            .map(|(id, r)| (*id, r.as_slice()))
            .collect();

        self.storage
            .write_batch(
                leaves_ref,
                &nodes_ref,
                &[],
                batch.log_meta,
                &checkpoint_refs,
            )
            .await
            .map_err(LogError::Storage)?;

        // Storage committed: safe to update in-memory state.
        self.algs = new_algs;
        self.count = batch.log_meta.unwrap().0;
        self.kind = LogKind::Flat;
        Ok(())
    }

    /// Append a structured subtree to the log.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] on a kind conflict, capacity overflow, no active
    /// algorithms, or a storage error.
    pub async fn append_subtree(&mut self, subtree: &Subtree) -> Result<(), S::Error> {
        if self.kind == LogKind::Flat && self.count > 0 {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append subtree after leaf appends".to_string(),
            });
        }

        if self.count >= (1u64 << 47) {
            return Err(LogError::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }

        if !self.algs.values().any(|s| s.is_active()) {
            return Err(LogError::NoActiveAlgorithms);
        }

        let (new_algs, batch) = self.build_append_state(LogKind::Subtree, |alg_id, view| {
            if view.is_active_at(self.count) {
                let root_hash = evaluate(view.hasher.as_ref(), subtree);
                let node = (alg_id, self.count, 0u32, root_hash.clone());
                (root_hash, Some(node))
            } else {
                (view.hasher.null(), None)
            }
        })?;

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = batch
            .nodes
            .iter()
            .map(|(a, l, h, hash)| (*a, *l, *h, hash.as_slice()))
            .collect();
        let checkpoint_refs: Vec<(u64, &[u8])> = batch
            .checkpoint_roots
            .iter()
            .map(|(id, r)| (*id, r.as_slice()))
            .collect();

        self.storage
            .write_batch(&[], &nodes_ref, &[], batch.log_meta, &checkpoint_refs)
            .await
            .map_err(LogError::Storage)?;

        // Storage committed: safe to update in-memory state.
        self.algs = new_algs;
        self.count = batch.log_meta.unwrap().0;
        self.kind = LogKind::Subtree;
        Ok(())
    }

    /// Compute the current combined root — the live primary root of the log,
    /// under the default algorithm (0).
    ///
    /// The combined root is the canonicalization fold ([`combined_root`]) over
    /// the per-algorithm member roots; per-algorithm member roots stay directly
    /// accessible via [`Self::root_for`]. For a single-algorithm log with a
    /// trivial timeline the fold promotes to the lone member root, so the primary
    /// root is byte-identical to that algorithm's raw root.
    #[must_use]
    pub fn root(&self) -> Vec<u8> {
        self.live_combined_root(0).unwrap_or_else(|_| Vec::new())
    }

    /// The live combined root under `alg_id`'s hash, folded from the in-memory
    /// per-algorithm frontiers at the current tip (the sync, no-storage peer of
    /// [`Self::combined_root_at`] at `size == self.count`). Per-algorithm member
    /// roots remain accessible via [`Self::root_for`].
    fn live_combined_root(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        if self.count == 0 {
            return Ok(view.hasher.empty());
        }
        // The active algorithms at the current tip are the fold's children.
        let active = self.active_algs_at(self.count);
        let mut member_roots = Vec::with_capacity(active.len());
        for &id in &active {
            member_roots.push((id, self.root_for(id)?));
        }
        let alg_epochs = self.committed_epochs_at(self.count);
        Ok(combined_root(
            view.hasher.as_ref(),
            &member_roots,
            &alg_epochs,
            self.count,
            self.config.arity,
        ))
    }

    /// Compute the current raw member root for a specific algorithm — the
    /// per-algorithm child of the combined root, the root the leaves
    /// authenticate against.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::compute_root(view, self.config.arity as usize))
    }

    /// Generate an inclusion proof for the item at `index` in a tree of size `tree_size`.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn inclusion_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<cml::proof::InclusionProof>, S::Error> {
        self.inclusion_proof_for(0, index, tree_size).await
    }

    /// Generate an inclusion proof for a specific algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn inclusion_proof_for(
        &self,
        alg_id: u64,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<cml::proof::InclusionProof>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::inclusion_proof(
            &StorageReader(&self.storage),
            view,
            alg_id,
            index,
            tree_size,
            self.count,
            self.config.arity,
        )
        .await?)
    }

    /// Produce a self-contained [`spine::LeafProof`] for the item at `index` in a
    /// tree of size `tree_size`.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn leaf_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<spine::LeafProof>, S::Error> {
        self.leaf_proof_for(0, index, tree_size).await
    }

    /// Produce a leaf proof for a specific algorithm. Returns `None` when no
    /// inclusion proof exists for `(index, tree_size)`.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn leaf_proof_for(
        &self,
        alg_id: u64,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<spine::LeafProof>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::leaf_proof(
            &StorageReader(&self.storage),
            view,
            alg_id,
            index,
            tree_size,
            self.count,
            self.config.arity,
        )
        .await?)
    }

    /// Generate a consistency proof between `old_size` and `new_size`.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn consistency_proof(
        &self,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<cml::proof::ConsistencyProof>, S::Error> {
        self.consistency_proof_for(0, old_size, new_size).await
    }

    /// Generate a consistency proof for a specific algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn consistency_proof_for(
        &self,
        alg_id: u64,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<cml::proof::ConsistencyProof>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::consistency_proof(
            &StorageReader(&self.storage),
            view,
            alg_id,
            old_size,
            new_size,
            self.count,
            self.config.arity,
        )
        .await?)
    }

    /// The committed epoch timeline at size `size`: `(alg_id, epochs)` for
    /// every algorithm registered by that size, sorted by algorithm ID.
    /// This is the timeline bound into the combined root (Design A+).
    #[must_use]
    pub fn committed_epochs_at(&self, size: u64) -> Vec<(u64, Vec<(u64, u64)>)> {
        let mut out: Vec<_> = self
            .algs
            .iter()
            .filter_map(|(&id, view)| view.epochs_at(size).map(|e| (id, e)))
            .collect();
        out.sort_unstable_by_key(|&(id, _)| id);
        out
    }

    /// Compute the current combined root hash of the default algorithm (0).
    pub async fn combined_root(&self) -> Vec<u8> {
        self.combined_root_for(0)
            .await
            .unwrap_or_else(|_| Vec::new())
    }

    /// Compute the current combined root hash for a specific algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] from the historical combined-root computation.
    pub async fn combined_root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        self.combined_root_at(alg_id, self.count).await
    }

    /// Build an `AuditPayload` at a historical tree size.
    ///
    /// Returns an error if `size == 0` or if no algorithms are active at
    /// that size.  `combined_roots` contains one entry per active algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] for an empty size, no active algorithms, or a read error.
    pub async fn audit_payload_at(
        &self,
        log_id: [u8; 32],
        size: u64,
    ) -> Result<crate::root::AuditPayload, S::Error> {
        if size == 0 {
            return Err(LogError::IndexOutOfBounds {
                index: 0,
                tree_size: 0,
            });
        }
        let active_algs = self.active_algs_at(size);
        if active_algs.is_empty() {
            return Err(LogError::NoActiveAlgorithms);
        }
        let alg_epochs = self.committed_epochs_at(size);
        let mut combined_roots = Vec::with_capacity(active_algs.len());
        for &id in &active_algs {
            let cr = self.combined_root_at(id, size).await?;
            combined_roots.push((id, cr));
        }
        Ok(crate::root::AuditPayload {
            log_id,
            tree_size: size,
            active_algs,
            combined_roots,
            alg_epochs,
        })
    }

    /// Build an `AuditPayload` at the current tip.
    ///
    /// # Errors
    ///
    /// As [`Self::audit_payload_at`].
    pub async fn audit_payload(
        &self,
        log_id: [u8; 32],
    ) -> Result<crate::root::AuditPayload, S::Error> {
        self.audit_payload_at(log_id, self.count).await
    }

    /// Build a `CouplingProof` at a historical tree size.
    ///
    /// `active_roots` are the raw per-algorithm roots at `size`; `alg_epochs`
    /// is the committed timeline.  Together they open the combined root.
    ///
    /// # Errors
    ///
    /// Returns [`LogError`] for an empty size, no active algorithms, or a read error.
    pub async fn coupling_proof_at(
        &self,
        size: u64,
    ) -> Result<crate::root::CouplingProof, S::Error> {
        if size == 0 {
            return Err(LogError::IndexOutOfBounds {
                index: 0,
                tree_size: 0,
            });
        }
        let active_algs = self.active_algs_at(size);
        if active_algs.is_empty() {
            return Err(LogError::NoActiveAlgorithms);
        }
        let alg_epochs = self.committed_epochs_at(size);
        let mut active_roots = Vec::with_capacity(active_algs.len());
        for &id in &active_algs {
            let r = self.root_for_at(id, size).await?;
            active_roots.push((id, r));
        }
        Ok(crate::root::CouplingProof {
            active_roots,
            alg_epochs,
        })
    }

    /// Verify an `AuditPayload` against the stored log data.
    ///
    /// Checks three things in sequence:
    /// 1. Structural validity: the payload's epoch timeline is well-formed, consistent with the
    ///    locally registered algorithms, and the derived active set matches `payload.active_algs`.
    /// 2. Cell integrity: streaming over every position in `0..tree_size` for every registered
    ///    algorithm; active cells must match the stored leaf or subtree-root hash;
    ///    committed-inactive cells must be the null constant (a non-null stored cell is a baked
    ///    tree↔epoch contradiction — the repudiation evidence).
    /// 3. Root recomputation: each active algorithm's combined root is recomputed from the data
    ///    seen during the pass and compared to `payload.combined_roots`; all must match.
    ///
    /// Activity is read from `payload.alg_epochs` (the committed timeline),
    /// never from local uncommitted epoch state — using local state would be
    /// circular and would miss the equivocation.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn verify_audit_payload(
        &self,
        payload: &crate::root::AuditPayload,
    ) -> Result<bool, S::Error> {
        let size = payload.tree_size;
        let current_size = self.count;

        // ── 1. Structural validation ──────────────────────────────────────
        if size == 0 || size > current_size {
            return Ok(false);
        }

        // Payload alg-ID set must equal the algorithms registered locally
        // that have any committed epochs at this size.
        let local_epochs = self.committed_epochs_at(size);
        let local_ids: Vec<u64> = local_epochs.iter().map(|&(id, _)| id).collect();
        let payload_ids: Vec<u64> = payload.alg_epochs.iter().map(|&(id, _)| id).collect();
        if local_ids != payload_ids {
            return Ok(false);
        }

        if !validate_committed_epochs(&payload.alg_epochs, size) {
            return Ok(false);
        }

        let derived_active = committed_active_algs(&payload.alg_epochs, size);
        if derived_active != payload.active_algs {
            return Ok(false);
        }

        // combined_roots must be indexed by exactly the active alg IDs.
        if payload.combined_roots.len() != payload.active_algs.len()
            || payload
                .combined_roots
                .iter()
                .zip(payload.active_algs.iter())
                .any(|((id, _), &expected)| *id != expected)
        {
            return Ok(false);
        }

        // ── 2. Streaming cell check ───────────────────────────────────────
        let is_flat = self.kind == LogKind::Flat;
        let k = self.config.arity as usize;
        let active_set: std::collections::HashSet<u64> =
            payload.active_algs.iter().copied().collect();

        // Per-algorithm rolling frontier (active-set only).
        let mut frontiers: HashMap<u64, Vec<Vec<u8>>> = payload
            .active_algs
            .iter()
            .map(|&id| (id, Vec::new()))
            .collect();

        for i in 0..size {
            let leaf_data = if is_flat {
                match self.storage.get_leaf(i).await {
                    Ok(d) => Some(d),
                    Err(e) => return Err(LogError::Storage(e)),
                }
            } else {
                None
            };

            for &(alg_id, _) in &payload.alg_epochs {
                let view = self
                    .algs
                    .get(&alg_id)
                    .ok_or(LogError::UnknownAlgorithm(alg_id))?;

                let digest = match committed_active_at(&payload.alg_epochs, alg_id, i) {
                    Some(true) => {
                        if let Some(ref d) = leaf_data {
                            let expected = view.hasher.leaf(d);
                            // Flat: the stored node is a cache; if present it
                            // must match the recomputed leaf hash.
                            if let Some(stored) = self
                                .storage
                                .get_node(alg_id, i, 0)
                                .await
                                .map_err(LogError::Storage)?
                            {
                                if !constant_time_eq(&expected, &stored) {
                                    return Ok(false);
                                }
                            }
                            expected
                        } else {
                            // Subtree: the stored node is authoritative and
                            // must exist for active-set algorithms.
                            match self
                                .storage
                                .get_node(alg_id, i, 0)
                                .await
                                .map_err(LogError::Storage)?
                            {
                                Some(v) => v,
                                None if active_set.contains(&alg_id) => return Ok(false),
                                None => view.hasher.null(),
                            }
                        }
                    },
                    Some(false) => {
                        let null = view.hasher.null();
                        if let Some(stored) = self
                            .storage
                            .get_node(alg_id, i, 0)
                            .await
                            .map_err(LogError::Storage)?
                        {
                            if !constant_time_eq(&stored, &null) {
                                return Ok(false);
                            }
                        }
                        null
                    },
                    None => return Ok(false),
                };

                if let Some(frontier) = frontiers.get_mut(&alg_id) {
                    frontier.push(digest);
                    let merges = reduction_count(i, k as u64);
                    for _ in 0..merges {
                        if frontier.len() < k {
                            return Ok(false);
                        }
                        let mut children = Vec::with_capacity(k);
                        for _ in 0..k {
                            children.push(frontier.pop().ok_or_else(|| {
                                LogError::CorruptedMetadata {
                                    alg_id,
                                    reason: "frontier underflow in audit".to_string(),
                                }
                            })?);
                        }
                        children.reverse();
                        let child_refs: Vec<&[u8]> =
                            children.iter().map(|c| c.as_slice()).collect();
                        let parent = nary_mr(view.hasher.as_ref(), &child_refs);
                        frontier.push(parent);
                    }
                }
            }
        }

        // ── 3. Root recomputation ─────────────────────────────────────────
        let mut recomputed_roots: Vec<(u64, Vec<u8>)> =
            Vec::with_capacity(payload.active_algs.len());
        for &id in &payload.active_algs {
            let view = self.algs.get(&id).ok_or(LogError::UnknownAlgorithm(id))?;
            let frontier = &frontiers[&id];
            let raw_root = if frontier.is_empty() {
                view.hasher.empty()
            } else {
                fold_frontier(frontier.clone(), k, |chunk| {
                    let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
                    nary_mr(view.hasher.as_ref(), &refs)
                })
            };
            recomputed_roots.push((id, raw_root));
        }

        // Recompute each algorithm's combined root via the canonicalization
        // fold over the recomputed member roots (promotion native; coverage
        // child committing all algorithms' null runs iff the activation is
        // non-trivial) and compare to the payload.
        for (i, &id) in payload.active_algs.iter().enumerate() {
            let view = self.algs.get(&id).ok_or(LogError::UnknownAlgorithm(id))?;

            let computed_cr = combined_root(
                view.hasher.as_ref(),
                &recomputed_roots,
                &payload.alg_epochs,
                payload.tree_size,
                k as u64,
            );

            if !constant_time_eq(&computed_cr, &payload.combined_roots[i].1) {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// The sorted set of algorithms active at the historical `size`
    /// (algorithms whose epochs cover the final position `size - 1`).
    fn active_algs_at(&self, size: u64) -> Vec<u64> {
        let mut active_algs = Vec::new();
        for (&id, view) in &self.algs {
            if size > 0 && view.is_active_at(size - 1) {
                active_algs.push(id);
            }
        }
        active_algs.sort_unstable();
        active_algs
    }

    /// Compute the combined root hash for a specific algorithm at a historical tree size.
    ///
    /// The combined root is the canonicalization fold ([`combined_root`]) over
    /// the per-algorithm member roots as children, under the target algorithm's
    /// own hash. **All algorithms' null-run-extents** enter the fold as a single
    /// coverage child — but only when the activation is non-trivial — because the
    /// null runs are the only per-tree-divergent collapse and so the minimal
    /// committed activation. Binding them makes activity/inactivity claims
    /// non-equivocable. Genesis promotion is native: a single member root with no
    /// null run folds to itself.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] / [`LogError::NoActiveAlgorithms`] /
    /// [`LogError::FrozenAlgorithm`], or a storage error.
    pub async fn combined_root_at(&self, alg_id: u64, size: u64) -> Result<Vec<u8>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;

        if size == 0 {
            return Ok(view.hasher.empty());
        }

        // 1. Gather active algorithms at the given historical size
        let active_algs = self.active_algs_at(size);

        if active_algs.is_empty() {
            return Err(LogError::NoActiveAlgorithms);
        }

        // Ensure the requested algorithm is active at this size
        if !active_algs.contains(&alg_id) {
            return Err(LogError::FrozenAlgorithm(alg_id));
        }

        // 2. Gather the per-algorithm member roots (the fold's children) and the committed timeline
        //    (the coverage child, iff non-trivial).
        let mut member_roots = Vec::with_capacity(active_algs.len());
        for &id in &active_algs {
            let r = self.root_for_at(id, size).await?;
            member_roots.push((id, r));
        }
        let alg_epochs = self.committed_epochs_at(size);

        // 3. Fold under the target algorithm's hasher. Promotion is native. The coverage child
        //    commits all algorithms' null runs, derived from the committed epochs at this size and
        //    arity.
        Ok(combined_root(
            view.hasher.as_ref(),
            &member_roots,
            &alg_epochs,
            size,
            self.config.arity,
        ))
    }

    /// The materialized digest of the frontier peak at coordinate
    /// `(left, height)` for `alg_id` — one perfect k-ary subtree root of the
    /// frontier. Returns the algorithm's null constant for a coordinate whose
    /// range carries no active leaf.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn peak_at(&self, alg_id: u64, left: u64, height: u32) -> Result<Vec<u8>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::peak_at(
            &StorageReader(&self.storage),
            view,
            alg_id,
            left,
            height,
            self.config.arity,
        )
        .await?)
    }

    /// Retrieve the raw root hash for a specific algorithm at a historical tree size.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] / [`LogError::IndexOutOfBounds`], or
    /// a storage error.
    pub async fn root_for_at(&self, alg_id: u64, size: u64) -> Result<Vec<u8>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;

        if size > self.count {
            return Err(LogError::IndexOutOfBounds {
                index: size,
                tree_size: self.count,
            });
        }

        Ok(engine::root_for_at(
            &StorageReader(&self.storage),
            view,
            alg_id,
            size,
            self.config.arity,
        )
        .await?)
    }

    /// Gather the frontier peaks of a single active algorithm at `size` — the
    /// structural snapshot facet the seal freezes. Used by the seal path; the
    /// combinator drives this once per active algorithm to assemble the
    /// [`spine::Seal`].
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub(crate) async fn frontier_peaks_at(
        &self,
        alg_id: u64,
        size: u64,
    ) -> Result<Vec<Vec<u8>>, S::Error> {
        let view = self
            .algs
            .get(&alg_id)
            .ok_or(LogError::UnknownAlgorithm(alg_id))?;
        Ok(engine::frontier_peaks(
            &StorageReader(&self.storage),
            view,
            alg_id,
            size,
            self.config.arity,
        )
        .await?)
    }

    /// Verify that the trees for all active algorithms have not diverged
    /// from the underlying leaf data stored in the database.
    ///
    /// # Errors
    ///
    /// Returns [`LogError::UnknownAlgorithm`] or a storage error.
    pub async fn verify_non_divergence(
        &self,
        checkpoint_size: Option<u64>,
        trusted_roots: &[(u64, Vec<u8>)],
    ) -> Result<bool, S::Error> {
        let start = checkpoint_size.unwrap_or(0);
        let end = self.count;
        if start > end {
            return Ok(false);
        }

        // 1. If starting from a checkpoint, verify tree consistency first
        if start > 0 {
            for (&id, view) in &self.algs {
                let check_start = std::cmp::max(start, view.first_activation());
                if check_start < end {
                    // check_start == first_activation() means the algorithm has
                    // no committed data at the checkpoint boundary; treat as empty.
                    let old_alg_size = if check_start == view.first_activation() {
                        0
                    } else {
                        view.effective_size_at(check_start)
                    };
                    let new_alg_size = view.effective_size_at(end);

                    let old_root = if old_alg_size == 0 {
                        view.hasher.empty()
                    } else {
                        // Trust boundary closed: retrieve starting root from trusted checkpoint
                        // parameter
                        let mut found = None;
                        for &(tid, ref r) in trusted_roots {
                            if tid == id {
                                found = Some(r.clone());
                                break;
                            }
                        }
                        found.ok_or(LogError::UnknownAlgorithm(id))?
                    };
                    let new_root = self.root_for_at(id, end).await?;

                    if old_alg_size < new_alg_size && old_alg_size > 0 {
                        // Verify consistency using standard O(log N) verification from old_alg_size
                        // to new_alg_size
                        if let Some(proof) = self
                            .consistency_proof_for(id, old_alg_size, new_alg_size)
                            .await?
                        {
                            if !cml::verify_consistency(
                                view.hasher.as_ref(),
                                old_alg_size,
                                new_alg_size,
                                self.config.arity,
                                &proof.start_hash,
                                &proof.path,
                                &old_root,
                                &new_root,
                            ) {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    } else if old_alg_size == new_alg_size {
                        // Ensure the root has not changed for frozen algorithms
                        if !constant_time_eq(&old_root, &new_root) {
                            return Ok(false);
                        }
                    }
                }
            }
        }

        // Reconstruct frontier stacks at checkpoint size and verify starting boundaries
        let mut alg_frontiers = HashMap::new();
        for (&alg_id, view) in &self.algs {
            if !view.is_active() {
                let deact_index = view.epochs.last().map_or(0, |&(_, end)| end);
                if deact_index < end
                    && self
                        .storage
                        .get_node(alg_id, deact_index, 0)
                        .await
                        .map_err(LogError::Storage)?
                        .is_some()
                {
                    return Ok(false); // Tampered: nodes exist beyond deactivation point!
                }
            }

            let mut frontier = Vec::new();
            let mut frontier_coords = Vec::new();
            let k = self.config.arity as usize;

            let alg_size_at_start = view.effective_size_at(start);

            if alg_size_at_start > 0 {
                let coords = frontier_for_size(alg_size_at_start, k as u64);
                for &(left, height) in &coords {
                    let hash = self.peak_at(alg_id, left, height).await?;
                    frontier.push(hash);
                    frontier_coords.push((left, height));
                }
            }

            if start > 0 {
                let folded = if frontier.is_empty() {
                    view.hasher.empty()
                } else {
                    fold_frontier(frontier.clone(), k, |chunk| {
                        let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
                        nary_mr(view.hasher.as_ref(), &refs)
                    })
                };
                let mut expected_root = None;
                for &(tid, ref r) in trusted_roots {
                    if tid == alg_id {
                        expected_root = Some(r.clone());
                        break;
                    }
                }

                let expected_root = match expected_root {
                    Some(r) => r,
                    None => {
                        if alg_size_at_start == 0 {
                            // start == 0: empty tree.
                            view.hasher.empty()
                        } else if start <= view.first_activation() {
                            // Pre-activation algorithm: null projections over [0, start)
                            // fold to null() by null promotion — no trusted root needed.
                            view.hasher.null()
                        } else {
                            return Err(LogError::UnknownAlgorithm(alg_id));
                        }
                    },
                };

                if !constant_time_eq(&folded, &expected_root) {
                    return Ok(false); // Starting state mismatch!
                }
            }

            alg_frontiers.insert(alg_id, (frontier, frontier_coords, alg_size_at_start));
        }

        // Stream leaf payloads from storage and rebuild stacks incrementally
        for i in start..end {
            let data = if self.kind == LogKind::Flat {
                match self.storage.get_leaf(i).await {
                    Ok(d) => Some(d),
                    Err(e) => return Err(LogError::Storage(e)),
                }
            } else {
                None
            };

            for (&alg_id, view) in &self.algs {
                let (frontier, frontier_coords, alg_size) = alg_frontiers
                    .get_mut(&alg_id)
                    .ok_or(LogError::UnknownAlgorithm(alg_id))?;

                let deact_index = if view.is_active() {
                    u64::MAX
                } else {
                    view.epochs.last().map_or(0, |&(_, end)| end)
                };

                if i >= deact_index {
                    continue;
                }

                let is_active = view.is_active_at(i);

                let digest = if is_active {
                    if let Some(ref d) = data {
                        // Flat: compute from raw leaf bytes; compare to cached
                        // tree node to detect cache tampering independently.
                        let computed = view.hasher.leaf(d);
                        let stored = self.peak_at(alg_id, i, 0).await?;
                        if !constant_time_eq(&computed, &stored) {
                            return Ok(false); // Cached node doesn't match raw leaf.
                        }
                        computed
                    } else {
                        // Subtree: only the stored root is available; tampering
                        // is detected by the parent-level recomputation below.
                        self.peak_at(alg_id, i, 0).await?
                    }
                } else {
                    view.hasher.null()
                };

                frontier.push(digest);
                frontier_coords.push((i, 0));
                *alg_size += 1;

                let merges = reduction_count(*alg_size - 1, self.config.arity);
                for _ in 0..merges {
                    if frontier.len() < self.config.arity as usize {
                        return Ok(false); // Frontier underflow!
                    }
                    let mut children = Vec::with_capacity(self.config.arity as usize);
                    let mut coords = Vec::with_capacity(self.config.arity as usize);
                    for _ in 0..self.config.arity as usize {
                        children.push(frontier.pop().ok_or_else(|| {
                            LogError::CorruptedMetadata {
                                alg_id,
                                reason: "frontier underflow".to_string(),
                            }
                        })?);
                        coords.push(frontier_coords.pop().ok_or_else(|| {
                            LogError::CorruptedMetadata {
                                alg_id,
                                reason: "frontier_coords underflow".to_string(),
                            }
                        })?);
                    }
                    children.reverse();
                    coords.reverse();

                    let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                    let parent = nary_mr(view.hasher.as_ref(), &child_refs);

                    let parent_left_index = coords[0].0;
                    let parent_height = coords[0].1 + 1;

                    let stored_parent = self
                        .peak_at(alg_id, parent_left_index, parent_height)
                        .await?;
                    if !constant_time_eq(&parent, &stored_parent) {
                        return Ok(false); // Internal node hash mismatch!
                    }

                    frontier.push(parent);
                    frontier_coords.push((parent_left_index, parent_height));
                }
            }
        }

        // Verify final recomputed roots match the current logger roots
        for (&alg_id, view) in &self.algs {
            let (frontier, ..) = &alg_frontiers[&alg_id];
            let folded = if frontier.is_empty() {
                view.hasher.empty()
            } else {
                fold_frontier(frontier.clone(), self.config.arity as usize, |chunk| {
                    let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
                    nary_mr(view.hasher.as_ref(), &refs)
                })
            };
            let final_root = self.root_for_at(alg_id, end).await?;
            if !constant_time_eq(&folded, &final_root) {
                return Ok(false); // Final root mismatch!
            }
        }

        Ok(true)
    }
}
