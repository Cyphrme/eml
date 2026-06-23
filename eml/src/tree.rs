//! Unified n-ary Merkle append-only log state machine.

use pmt::hasher::Hasher;
use pmt::mr::{evaluate, nary_mr};
use pmt::subtree::Subtree;
use pmt::topology::frontier_for_size;

use crate::error::Result;
use crate::schedule::reduction_count;
use crate::storage::Storage;

/// Whether log-level appends are flat leaf appends or subtree appends.
///
/// Decided on the first append and persisted in storage; read back at load so
/// `from_storage` never infers kind from counters or `len()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogKind {
    /// Each append is a raw leaf; the payload is stored verbatim for auditability.
    Flat,
    /// Each append is a subtree root; only the evaluated root hash is stored.
    Subtree,
}

const LOG_KIND_FLAT: u8 = 0;
const LOG_KIND_SUBTREE: u8 = 1;

/// Configuration for the n-ary Merkle tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TreeConfig {
    /// Arity for log-level nodes (k >= 2).
    /// Controls the base-k carry reduction schedule.
    pub log_arity: usize,
}

impl Default for TreeConfig {
    fn default() -> Self {
        Self { log_arity: 2 }
    }
}

/// State of a registered hashing algorithm.
#[derive(Debug)]
pub struct AlgState {
    /// Hasher instance.
    pub hasher: Box<dyn Hasher>,
    /// Epoch intervals: half-open `[start, end)`.
    /// `end == u64::MAX` represents an active (open) epoch.
    pub epochs: Vec<(u64, u64)>,
    /// Frontier stack: holds hashes of completed subtrees.
    pub frontier: Vec<Vec<u8>>,
    /// Coordinates of each frontier node: `(left_index, height)`.
    pub frontier_coords: Vec<(u64, u32)>,
}

impl Clone for AlgState {
    fn clone(&self) -> Self {
        Self {
            hasher: self.hasher.clone_box(),
            epochs: self.epochs.clone(),
            frontier: self.frontier.clone(),
            frontier_coords: self.frontier_coords.clone(),
        }
    }
}

impl AlgState {
    /// Whether this algorithm is currently active (not frozen).
    pub fn is_active(&self) -> bool {
        self.epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
    }

    /// Whether leaf/subtree index `i` falls within any of this algorithm's active epochs.
    pub fn is_active_at(&self, i: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= i && i < end)
    }

    /// The tree size for this algorithm.
    ///
    /// Active algorithms track the global tree size.
    /// Frozen algorithms stopped at their last deactivation point.
    pub fn tree_size(&self, global_size: u64) -> u64 {
        if self.is_active() {
            global_size
        } else {
            self.epochs.last().map_or(0, |&(_, end)| end)
        }
    }

    /// The activation index of the first epoch.
    pub fn first_activation(&self) -> u64 {
        self.epochs.first().map_or(0, |&(start, _)| start)
    }

    /// Whether algorithm has active content in the half-open range `[lo, hi)`.
    ///
    /// Definition 14b (Active range): true iff any epoch overlaps the interval.
    pub fn active_range(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start < hi && end > lo)
    }

    /// Whether the range `[lo, hi)` is fully contained within the active epochs.
    pub fn fully_active(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= lo && hi <= end)
    }

    /// The epoch timeline as it stood at size `size`, for commitment into
    /// the combined root and audit checkpoints (Design A+).
    ///
    /// Intervals beginning after `size` are dropped; an interval extending
    /// past `size` is encoded as open (`end == u64::MAX`), matching what the
    /// timeline looked like when the log was that size. An interval closed
    /// exactly at `size` stays closed — this is what distinguishes
    /// "deactivated at the tip" from "still live, log idle" (frontier
    /// freshness). Returns `None` if the algorithm was not yet registered.
    #[must_use]
    pub fn epochs_at(&self, size: u64) -> Option<Vec<(u64, u64)>> {
        let mut out = Vec::new();
        for &(start, end) in &self.epochs {
            if start > size {
                break;
            }
            if end > size {
                out.push((start, u64::MAX));
                break;
            }
            out.push((start, end));
        }
        if out.is_empty() { None } else { Some(out) }
    }
}

/// An n-ary Merkle Append-Only Log.
#[derive(Debug, Clone)]
pub struct NaryMerkleLog<S: Storage> {
    storage: S,
    config: TreeConfig,
    algs: std::collections::HashMap<u64, AlgState>,
    /// Total number of log-level appends (leaves for `Flat`, subtrees for `Subtree`).
    count: u64,
    /// Whether appends are flat leaf or subtree appends.
    kind: LogKind,
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
        if config.log_arity < 2 || config.log_arity > 256 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: format!(
                    "invalid log_arity: must be between 2 and 256, got {}",
                    config.log_arity
                ),
            });
        }
        let mut log = Self {
            storage,
            config,
            algs: std::collections::HashMap::new(),
            count: 0,
            kind: LogKind::Flat,
        };
        // Eagerly register algorithm 0 as active from index 0
        log.add_algorithm(0, hasher).await?;
        Ok(log)
    }

    /// **Resume** an append-only log onto the committed frontier of a
    /// [`pmt::Sealed`], consuming nothing but the frontier.
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
    /// Returns [`Error::UnknownAlgorithm`] if an algorithm in the frontier has
    /// no hasher in `hashers`, [`Error::CorruptedMetadata`] on an invalid arity,
    /// or a storage error if the seeded frontier cannot be persisted.
    pub async fn resume(
        sealed: &pmt::Sealed,
        mut storage: S,
        hashers: Vec<(u64, Box<dyn Hasher>)>,
    ) -> Result<Self, S::Error> {
        let k = sealed.arity();
        if !(2..=256).contains(&k) {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: format!("invalid arity in sealed frontier: {k}"),
            });
        }
        let config = TreeConfig {
            log_arity: k as usize,
        };
        let size = sealed.tree_size();
        let coords = frontier_for_size(size, k);

        let mut hasher_map: std::collections::HashMap<u64, Box<dyn Hasher>> =
            hashers.into_iter().collect();

        let mut algs = std::collections::HashMap::new();
        let mut node_batch: Vec<(u64, u64, u32, Vec<u8>)> = Vec::new();
        let mut meta_batch: Vec<(u64, Vec<(u64, u64)>)> = Vec::new();
        let mut checkpoint_batch: Vec<(u64, Vec<u8>)> = Vec::new();

        for (alg_id, peaks) in sealed.frontiers() {
            let hasher = hasher_map
                .remove(alg_id)
                .ok_or(crate::error::Error::UnknownAlgorithm(*alg_id))?;

            // The resumed algorithm's committed timeline is carried from the
            // seal so its binding root at the sealed size is reproduced; a live
            // resumed algorithm keeps its open epoch.
            let epochs: Vec<(u64, u64)> = sealed
                .alg_epochs()
                .iter()
                .find(|(id, _)| id == alg_id)
                .map(|(_, e)| e.clone())
                .unwrap_or_else(|| vec![(0, u64::MAX)]);

            let state = AlgState {
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
                if state.active_range(left, left + cap) {
                    node_batch.push((*alg_id, left, height, peak.clone()));
                }
            }
            let root = Self::compute_root_from_state(&state, k as usize);
            checkpoint_batch.push((*alg_id, root));
            meta_batch.push((*alg_id, epochs));
            algs.insert(*alg_id, state);
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
                Some((size, LOG_KIND_SUBTREE)),
                &checkpoints_ref,
            )
            .await
            .map_err(crate::error::Error::Storage)?;

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
        if config.log_arity < 2 || config.log_arity > 256 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: format!(
                    "invalid log_arity: must be between 2 and 256, got {}",
                    config.log_arity
                ),
            });
        }

        let metas = storage
            .load_algorithm_metas()
            .await
            .map_err(crate::error::Error::Storage)?;

        let mut hasher_map: std::collections::HashMap<u64, Box<dyn Hasher>> =
            hashers.into_iter().collect();

        // Validate 1:1 correspondence and duplicate IDs.
        let mut seen = std::collections::HashSet::new();
        for &(alg_id, _) in &metas {
            if !seen.insert(alg_id) {
                return Err(crate::error::Error::DuplicateAlgorithm(alg_id));
            }
            if !hasher_map.contains_key(&alg_id) {
                return Err(crate::error::Error::OrphanedMetadata(alg_id));
            }
        }
        let meta_ids: std::collections::HashSet<u64> = metas.iter().map(|&(id, _)| id).collect();
        for &alg_id in hasher_map.keys() {
            if !meta_ids.contains(&alg_id) {
                return Err(crate::error::Error::UnknownMetadata(alg_id));
            }
        }

        // Recover authoritative (count, kind) from persisted log metadata when
        // available; fall back to deterministic probing for legacy stores.
        let (global_size, kind) = match storage
            .load_log_meta()
            .await
            .map_err(crate::error::Error::Storage)?
        {
            Some((count, kind_byte)) => {
                let kind = if kind_byte == LOG_KIND_SUBTREE {
                    LogKind::Subtree
                } else {
                    LogKind::Flat
                };
                (count, kind)
            },
            None => {
                let size = Self::determine_global_size(&storage, &metas).await?;
                let kind = if storage.len().await.map_err(crate::error::Error::Storage)? > 0 {
                    LogKind::Flat
                } else {
                    LogKind::Subtree
                };
                (size, kind)
            },
        };

        let mut algs = std::collections::HashMap::new();
        let k = config.log_arity as u64;
        for (alg_id, epochs) in metas {
            let hasher = hasher_map
                .remove(&alg_id)
                .ok_or_else(|| crate::error::Error::OrphanedMetadata(alg_id))?;
            let state = Self::reconstruct_algorithm_state(
                &storage,
                alg_id,
                hasher,
                &epochs,
                global_size,
                k,
            )
            .await?;
            algs.insert(alg_id, state);
        }

        // V6: verify loaded frontier against stored checkpoint roots.
        // A corrupted frontier node will produce a different root from the one
        // committed at write time, detecting the corruption before the log is used.
        let stored_roots: std::collections::HashMap<u64, Vec<u8>> = storage
            .load_checkpoint_roots()
            .await
            .map_err(crate::error::Error::Storage)?
            .into_iter()
            .collect();

        for (&alg_id, state) in &algs {
            if let Some(stored_root) = stored_roots.get(&alg_id) {
                let actual_root = Self::compute_root_from_state(state, config.log_arity);
                if &actual_root != stored_root {
                    return Err(crate::error::Error::CorruptedMetadata {
                        alg_id,
                        reason: format!(
                            "checkpoint root mismatch for algorithm {}: recomputed root differs \
                             from stored checkpoint",
                            alg_id
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

    /// Compute the root hash from an algorithm's in-memory frontier.
    fn compute_root_from_state(state: &AlgState, k: usize) -> Vec<u8> {
        if state.frontier.is_empty() {
            return state.hasher.empty();
        }
        if state.frontier.len() == 1 {
            return state.frontier[0].clone();
        }
        let mut current = state.frontier.clone();
        while current.len() > k {
            let split_idx = current.len() - k;
            let right_elements = &current[split_idx..];
            let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
            let merged = pmt::mr::nary_mr(state.hasher.as_ref(), &refs);
            current.truncate(split_idx);
            current.push(merged);
        }
        let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
        pmt::mr::nary_mr(state.hasher.as_ref(), &refs)
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
        let leaf_len = storage.len().await.map_err(crate::error::Error::Storage)?;
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
                .map_err(crate::error::Error::Storage)?
                .is_none()
            {
                break;
            }
            size += 1;
        }
        Ok(size)
    }

    /// Reconstruct algorithm state from storage.
    async fn reconstruct_algorithm_state(
        storage: &S,
        alg_id: u64,
        hasher: Box<dyn Hasher>,
        epochs: &[(u64, u64)],
        global_size: u64,
        k: u64,
    ) -> Result<AlgState, S::Error> {
        Self::validate_epochs(alg_id, epochs, global_size)?;

        let is_active = epochs.last().is_some_and(|&(_, end)| end == u64::MAX);
        let tree_size = if is_active {
            global_size
        } else {
            epochs.last().map_or(0, |&(_, end)| end)
        };

        let mut state = AlgState {
            hasher,
            epochs: epochs.to_vec(),
            frontier: Vec::new(),
            frontier_coords: Vec::new(),
        };

        if tree_size == 0 {
            return Ok(state);
        }

        let coords = frontier_for_size(tree_size, k);
        let mut frontier = Vec::with_capacity(coords.len());
        for &(left, height) in &coords {
            let cap = k.pow(height);
            let hash = if !state.active_range(left, left + cap) {
                state.hasher.null()
            } else {
                storage
                    .get_node(alg_id, left, height)
                    .await
                    .map_err(crate::error::Error::Storage)?
                    .ok_or_else(|| crate::error::Error::CorruptedMetadata {
                        alg_id,
                        reason: format!(
                            "missing frontier node for algorithm {} at left {} height {}",
                            alg_id, left, height
                        ),
                    })?
            };
            frontier.push(hash);
        }

        state.frontier = frontier;
        state.frontier_coords = coords;

        Ok(state)
    }

    fn validate_epochs(
        alg_id: u64,
        epochs: &[(u64, u64)],
        global_size: u64,
    ) -> Result<(), S::Error> {
        if epochs.is_empty() {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id,
                reason: "epoch sequence is empty".to_string(),
            });
        }
        let mut last_end = 0;
        for (i, &(start, end)) in epochs.iter().enumerate() {
            if start > end {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch start {start} exceeds end {end}"),
                });
            }
            if start < last_end {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch start {start} is less than prior end {last_end}"),
                });
            }
            if end != u64::MAX && end > global_size {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("epoch end {end} exceeds global size {global_size}"),
                });
            }
            if end == u64::MAX && i != epochs.len() - 1 {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: "open epoch (end = u64::MAX) is not the final entry".to_string(),
                });
            }
            last_end = end;
        }
        if let Some(&(start, end)) = epochs.last() {
            if end == u64::MAX && start > global_size {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!("active epoch start {start} exceeds global size {global_size}"),
                });
            }
        }
        Ok(())
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
    pub async fn add_algorithm(
        &mut self,
        alg_id: u64,
        hasher: Box<dyn Hasher>,
    ) -> Result<(), S::Error> {
        if self.algs.contains_key(&alg_id) {
            return Err(crate::error::Error::DuplicateAlgorithm(alg_id));
        }

        let current_size = self.count;

        let epochs = vec![(current_size, u64::MAX)];

        // Persist metadata BEFORE committing in-memory state.
        self.storage
            .store_algorithm_meta(alg_id, &epochs)
            .await
            .map_err(crate::error::Error::Storage)?;

        let k = self.config.log_arity as u64;
        let coords = frontier_for_size(current_size, k);
        let stack = vec![hasher.null(); coords.len()];

        self.algs.insert(
            alg_id,
            AlgState {
                hasher,
                epochs,
                frontier: stack,
                frontier_coords: coords,
            },
        );

        Ok(())
    }

    /// Deactivate (freeze) an algorithm at the current tree size.
    pub async fn remove_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = self.count;

        let state = self
            .algs
            .get_mut(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if !state.is_active() {
            return Err(crate::error::Error::FrozenAlgorithm(alg_id));
        }

        let mut new_epochs = state.epochs.clone();
        if let Some(last) = new_epochs.last_mut() {
            last.1 = current_size;
        }

        self.storage
            .store_algorithm_meta(alg_id, &new_epochs)
            .await
            .map_err(crate::error::Error::Storage)?;

        state.epochs = new_epochs;
        Ok(())
    }

    /// Reactivate a frozen algorithm at the current tree size.
    pub async fn resume_algorithm(&mut self, alg_id: u64) -> Result<(), S::Error> {
        let current_size = self.count;

        let mut new_epochs = {
            let state = self
                .algs
                .get(&alg_id)
                .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

            if state.is_active() {
                return Err(crate::error::Error::AlgorithmActive(alg_id));
            }

            state.epochs.clone()
        };

        new_epochs.push((current_size, u64::MAX));

        let k = self.config.log_arity as u64;
        let coords = frontier_for_size(current_size, k);
        let mut frontier = Vec::with_capacity(coords.len());

        let temp_state = {
            let state = &self.algs[&alg_id];
            AlgState {
                hasher: state.hasher.clone_box(),
                epochs: new_epochs.clone(),
                frontier: Vec::new(),
                frontier_coords: Vec::new(),
            }
        };

        let mut mixed_to_store = Vec::new();
        for &(left, height) in &coords {
            let cap = k.pow(height);
            let (hash, mixed) = Self::reconstruct_subtree_root(
                &self.storage,
                alg_id,
                &temp_state,
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
        let resumed_state = AlgState {
            hasher: self.algs[&alg_id].hasher.clone_box(),
            epochs: new_epochs.clone(),
            frontier: frontier.clone(),
            frontier_coords: coords.clone(),
        };
        let resumed_root = Self::compute_root_from_state(&resumed_state, self.config.log_arity);

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
            .map_err(crate::error::Error::Storage)?;

        let state = self
            .algs
            .get_mut(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;
        state.epochs = new_epochs;
        state.frontier = frontier;
        state.frontier_coords = coords;

        Ok(())
    }

    /// Recursively resolve a subtree root and collect mixed boundary nodes.
    #[allow(clippy::type_complexity)]
    #[allow(clippy::too_many_arguments)]
    fn reconstruct_subtree_root<'a>(
        storage: &'a S,
        alg_id: u64,
        state: &'a AlgState,
        lo: u64,
        hi: u64,
        k: u64,
        kind: LogKind,
        store_mixed: bool,
    ) -> std::pin::Pin<
        Box<
            dyn std::future::Future<Output = Result<(Vec<u8>, Vec<(u64, u32, Vec<u8>)>), S::Error>>
                + Send
                + 'a,
        >,
    >
    where
        S: 'a,
    {
        Box::pin(async move {
            let size = hi - lo;
            if size == 0 {
                return Ok((state.hasher.empty(), Vec::new()));
            }
            if size == 1 {
                if state.is_active_at(lo) {
                    if kind == LogKind::Subtree {
                        if let Some(hash) = storage
                            .get_node(alg_id, lo, 0)
                            .await
                            .map_err(crate::error::Error::Storage)?
                        {
                            let expected = state.hasher.null().len();
                            if hash.len() != expected {
                                return Err(crate::error::Error::CorruptedMetadata {
                                    alg_id,
                                    reason: format!(
                                        "subtree node at left {} height 0 has wrong digest \
                                         length: expected {}, got {}",
                                        lo,
                                        expected,
                                        hash.len()
                                    ),
                                });
                            }
                            return Ok((hash, Vec::new()));
                        } else {
                            return Ok((state.hasher.null(), Vec::new()));
                        }
                    } else {
                        let data = storage
                            .get_leaf(lo)
                            .await
                            .map_err(crate::error::Error::Storage)?;
                        return Ok((state.hasher.leaf(&data), Vec::new()));
                    }
                }
                return Ok((state.hasher.null(), Vec::new()));
            }

            if !state.active_range(lo, hi) {
                return Ok((state.hasher.null(), Vec::new()));
            }

            let is_power_of_k = {
                let mut temp = size;
                while temp % k == 0 {
                    temp /= k;
                }
                temp == 1
            };

            if is_power_of_k {
                let height = {
                    let mut h = 0;
                    let mut temp = size;
                    while temp > 1 {
                        temp /= k;
                        h += 1;
                    }
                    h as u32
                };
                if state.fully_active(lo, hi) {
                    if let Some(hash) = storage
                        .get_node(alg_id, lo, height)
                        .await
                        .map_err(crate::error::Error::Storage)?
                    {
                        let expected = state.hasher.null().len();
                        if hash.len() != expected {
                            return Err(crate::error::Error::CorruptedMetadata {
                                alg_id,
                                reason: format!(
                                    "node at left {} height {} has wrong digest length: expected \
                                     {}, got {}",
                                    lo,
                                    height,
                                    expected,
                                    hash.len()
                                ),
                            });
                        }
                        return Ok((hash, Vec::new()));
                    }
                }

                let child_size = size / k;
                let mut child_hashes = Vec::with_capacity(k as usize);
                let mut mixed_nodes = Vec::new();
                for j in 0..k {
                    let c_lo = lo + j * child_size;
                    let c_hi = lo + (j + 1) * child_size;
                    let (child_hash, child_mixed) = Self::reconstruct_subtree_root(
                        storage,
                        alg_id,
                        state,
                        c_lo,
                        c_hi,
                        k,
                        kind,
                        store_mixed,
                    )
                    .await?;
                    child_hashes.push(child_hash);
                    mixed_nodes.extend(child_mixed);
                }
                let child_refs: Vec<&[u8]> = child_hashes.iter().map(|c| c.as_slice()).collect();
                let hash = nary_mr(state.hasher.as_ref(), &child_refs);

                if store_mixed {
                    mixed_nodes.push((lo, height, hash.clone()));
                }
                Ok((hash, mixed_nodes))
            } else {
                let coords = frontier_for_size(size, k);
                let mut component_hashes = Vec::with_capacity(coords.len());
                let mut mixed_nodes = Vec::new();
                for &(part_left, part_height) in &coords {
                    let cap = k.pow(part_height);
                    let c_lo = lo + part_left;
                    let c_hi = c_lo + cap;
                    let (part_root, part_mixed) = Self::reconstruct_subtree_root(
                        storage,
                        alg_id,
                        state,
                        c_lo,
                        c_hi,
                        k,
                        kind,
                        store_mixed,
                    )
                    .await?;
                    component_hashes.push(part_root);
                    mixed_nodes.extend(part_mixed);
                }

                let mut current = component_hashes;
                let k_usize = k as usize;
                while current.len() > k_usize {
                    let split_idx = current.len() - k_usize;
                    let right_elements = &current[split_idx..];
                    let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
                    let merged = nary_mr(state.hasher.as_ref(), &refs);
                    current.truncate(split_idx);
                    current.push(merged);
                }
                let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
                Ok((nary_mr(state.hasher.as_ref(), &refs), mixed_nodes))
            }
        })
    }

    /// Append a single flat leaf to the log.
    pub async fn append_leaf(&mut self, data: &[u8]) -> Result<(), S::Error> {
        // Kind is only binding once an append has happened; an empty log
        // (including one reloaded from an empty store) accepts either kind.
        if self.kind == LogKind::Subtree && self.count > 0 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append leaf after subtree appends".to_string(),
            });
        }

        if self.count >= (1u64 << 47) {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }

        if !self.algs.values().any(|s| s.is_active()) {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        let mut temp_algs = self.algs.clone();
        let mut batch_leaves = Vec::new();
        let mut batch_nodes = Vec::new();

        batch_leaves.push((self.count, data));

        for (&alg_id, state) in &mut temp_algs {
            if !state.is_active() {
                continue;
            }

            let digest = if state.is_active_at(self.count) {
                let leaf_hash = state.hasher.leaf(data);
                batch_nodes.push((alg_id, self.count, 0, leaf_hash.clone()));
                leaf_hash
            } else {
                state.hasher.null()
            };

            state.frontier.push(digest);
            state.frontier_coords.push((self.count, 0));

            let merges = reduction_count(self.count, self.config.log_arity as u64);
            for _ in 0..merges {
                let mut children = Vec::with_capacity(self.config.log_arity);
                let mut coords = Vec::with_capacity(self.config.log_arity);
                for _ in 0..self.config.log_arity {
                    children.push(state.frontier.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier stack underflow during reduction".to_string(),
                        }
                    })?);
                    coords.push(state.frontier_coords.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier_coords stack underflow during reduction".to_string(),
                        }
                    })?);
                }
                children.reverse();
                coords.reverse();
                let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                let parent_left_index = coords[0].0;
                let parent_height = coords[0].1 + 1;

                if parent != state.hasher.null() {
                    batch_nodes.push((alg_id, parent_left_index, parent_height, parent.clone()));
                }

                state.frontier.push(parent);
                state
                    .frontier_coords
                    .push((parent_left_index, parent_height));
            }
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = batch_nodes
            .iter()
            .map(|&(alg_id, left, height, ref hash)| (alg_id, left, height, hash.as_slice()))
            .collect();

        let new_count = self.count + 1;

        // Compute checkpoint roots from the updated temp frontier for all active algorithms.
        let checkpoint_roots_owned: Vec<(u64, Vec<u8>)> = temp_algs
            .iter()
            .filter(|(_, s)| s.is_active())
            .map(|(&alg_id, s)| {
                let root = Self::compute_root_from_state(s, self.config.log_arity);
                (alg_id, root)
            })
            .collect();
        let checkpoint_refs: Vec<(u64, &[u8])> = checkpoint_roots_owned
            .iter()
            .map(|(id, r)| (*id, r.as_slice()))
            .collect();

        self.storage
            .write_batch(
                &batch_leaves,
                &nodes_ref,
                &[],
                Some((new_count, LOG_KIND_FLAT)),
                &checkpoint_refs,
            )
            .await
            .map_err(crate::error::Error::Storage)?;

        self.algs = temp_algs;
        self.count = new_count;
        self.kind = LogKind::Flat;
        Ok(())
    }

    /// Append a structured subtree to the log.
    pub async fn append_subtree(&mut self, subtree: &Subtree) -> Result<(), S::Error> {
        if self.kind == LogKind::Flat && self.count > 0 {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "cannot append subtree after leaf appends".to_string(),
            });
        }

        if self.count >= (1u64 << 47) {
            return Err(crate::error::Error::CorruptedMetadata {
                alg_id: 0,
                reason: "log capacity exceeded (max 2^47 items)".to_string(),
            });
        }

        if !self.algs.values().any(|s| s.is_active()) {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        let mut temp_algs = self.algs.clone();
        let mut batch_nodes = Vec::new();

        for (&alg_id, state) in &mut temp_algs {
            if !state.is_active() {
                continue;
            }

            let digest = if state.is_active_at(self.count) {
                let root_hash = evaluate(state.hasher.as_ref(), subtree);
                batch_nodes.push((alg_id, self.count, 0, root_hash.clone()));
                root_hash
            } else {
                state.hasher.null()
            };

            state.frontier.push(digest);
            state.frontier_coords.push((self.count, 0));

            let merges = reduction_count(self.count, self.config.log_arity as u64);
            for _ in 0..merges {
                let mut children = Vec::with_capacity(self.config.log_arity);
                let mut coords = Vec::with_capacity(self.config.log_arity);
                for _ in 0..self.config.log_arity {
                    children.push(state.frontier.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier stack underflow during reduction".to_string(),
                        }
                    })?);
                    coords.push(state.frontier_coords.pop().ok_or_else(|| {
                        crate::error::Error::CorruptedMetadata {
                            alg_id,
                            reason: "frontier_coords stack underflow during reduction".to_string(),
                        }
                    })?);
                }
                children.reverse();
                coords.reverse();
                let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                let parent_left_index = coords[0].0;
                let parent_height = coords[0].1 + 1;

                if parent != state.hasher.null() {
                    batch_nodes.push((alg_id, parent_left_index, parent_height, parent.clone()));
                }

                state.frontier.push(parent);
                state
                    .frontier_coords
                    .push((parent_left_index, parent_height));
            }
        }

        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = batch_nodes
            .iter()
            .map(|&(alg_id, left, height, ref hash)| (alg_id, left, height, hash.as_slice()))
            .collect();

        let new_count = self.count + 1;

        let checkpoint_roots_owned: Vec<(u64, Vec<u8>)> = temp_algs
            .iter()
            .filter(|(_, s)| s.is_active())
            .map(|(&alg_id, s)| {
                let root = Self::compute_root_from_state(s, self.config.log_arity);
                (alg_id, root)
            })
            .collect();
        let checkpoint_refs: Vec<(u64, &[u8])> = checkpoint_roots_owned
            .iter()
            .map(|(id, r)| (*id, r.as_slice()))
            .collect();

        self.storage
            .write_batch(
                &[],
                &nodes_ref,
                &[],
                Some((new_count, LOG_KIND_SUBTREE)),
                &checkpoint_refs,
            )
            .await
            .map_err(crate::error::Error::Storage)?;

        self.algs = temp_algs;
        self.count = new_count;
        self.kind = LogKind::Subtree;
        Ok(())
    }

    /// Compute the current root hash of the default algorithm (0).
    #[must_use]
    pub fn root(&self) -> Vec<u8> {
        self.root_for(0).unwrap_or_else(|_| Vec::new())
    }

    /// Compute the current root hash for a specific algorithm.
    pub fn root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if state.frontier.is_empty() {
            return Ok(state.hasher.empty());
        }
        if state.frontier.len() == 1 {
            return Ok(state.frontier[0].clone());
        }
        let k = self.config.log_arity;
        let mut current = state.frontier.clone();
        while current.len() > k {
            let split_idx = current.len() - k;
            let right_elements = &current[split_idx..];
            let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
            let merged = nary_mr(state.hasher.as_ref(), &refs);
            current.truncate(split_idx);
            current.push(merged);
        }
        let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
        Ok(nary_mr(state.hasher.as_ref(), &refs))
    }

    /// Retrieve a node hash from storage, or return the null constant if it's inactive.
    async fn get_node_hash(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;
        let k = self.config.log_arity as u64;
        let cap = match k.checked_pow(height) {
            Some(c) => c,
            None => return Ok(state.hasher.null()),
        };
        let limit = match left.checked_add(cap) {
            Some(val) => val,
            None => return Ok(state.hasher.null()),
        };
        if !state.active_range(left, limit) {
            return Ok(state.hasher.null());
        }
        if let Some(hash) = self
            .storage
            .get_node(alg_id, left, height)
            .await
            .map_err(crate::error::Error::Storage)?
        {
            let expected = state.hasher.null().len();
            if hash.len() != expected {
                return Err(crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: format!(
                        "node at left {} height {} has wrong digest length: expected {}, got {}",
                        left,
                        height,
                        expected,
                        hash.len()
                    ),
                });
            }
            Ok(hash)
        } else {
            // Any node whose range has at least one active leaf will be stored
            // as a non-null value (null requires every active leaf to collide
            // with the null digest — negligible probability). A missing node
            // in any active range is therefore corruption, whether the range is
            // fully or only partially active.
            Err(crate::error::Error::CorruptedMetadata {
                alg_id,
                reason: format!(
                    "missing internal node for algorithm {} at left {} height {}",
                    alg_id, left, height
                ),
            })
        }
    }

    /// Generate an inclusion proof for the item at `index` in a tree of size `tree_size`.
    pub async fn inclusion_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<crate::proof::InclusionProof>, S::Error> {
        self.inclusion_proof_for(0, index, tree_size).await
    }

    /// Generate an inclusion proof for a specific algorithm.
    pub async fn inclusion_proof_for(
        &self,
        alg_id: u64,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<crate::proof::InclusionProof>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        let max_size = state.tree_size(self.count);

        if tree_size == 0 || index >= tree_size || tree_size > max_size {
            return Ok(None);
        }

        let k = self.config.log_arity as u64;
        let coords = frontier_for_size(tree_size, k);

        let mut target_f_idx = None;
        for (f_idx, &(left, height)) in coords.iter().enumerate() {
            let cap = k.pow(height);
            if index >= left && index < left + cap {
                target_f_idx = Some((f_idx, left, height));
                break;
            }
        }

        let (f_idx, left, height) = match target_f_idx {
            Some(val) => val,
            None => return Ok(None),
        };

        let mut path = Vec::new();
        self.log_level_bisection_path_to_height(alg_id, left, height, index, 0, &mut path)
            .await?;
        path.reverse();

        let mut hashes = Vec::with_capacity(coords.len());
        for &(l, h) in &coords {
            let hash = self.get_node_hash(alg_id, l, h).await?;
            hashes.push(hash);
        }

        struct MergeNode {
            hash: Vec<u8>,
            path: Vec<crate::proof::ProofStep>,
        }

        let mut current: Vec<MergeNode> = hashes
            .into_iter()
            .map(|h| MergeNode {
                hash: h,
                path: Vec::new(),
            })
            .collect();

        let mut target_idx = f_idx;
        let k_usize = self.config.log_arity;
        while current.len() > k_usize {
            let split_idx = current.len() - k_usize;

            let refs: Vec<&[u8]> = current[split_idx..]
                .iter()
                .map(|n| n.hash.as_slice())
                .collect();
            let merged_hash = nary_mr(state.hasher.as_ref(), &refs);

            let mut target_path = Vec::new();
            let mut is_target_merged = false;
            if target_idx >= split_idx {
                let mut siblings = Vec::with_capacity(k_usize - 1);
                for (j, item) in current.iter().enumerate().skip(split_idx) {
                    if j != target_idx {
                        siblings.push(item.hash.clone());
                    }
                }
                let step = crate::proof::ProofStep {
                    siblings,
                    position: target_idx - split_idx,
                };
                let mut p = std::mem::take(&mut current[target_idx].path);
                p.push(step);
                target_path = p;
                is_target_merged = true;
            }

            if is_target_merged {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: target_path,
                });
                target_idx = split_idx;
            } else {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: Vec::new(),
                });
            }
        }

        if current.len() > 1 {
            let mut siblings = Vec::with_capacity(current.len() - 1);
            for (j, item) in current.iter().enumerate() {
                if j != target_idx {
                    siblings.push(item.hash.clone());
                }
            }
            let step = crate::proof::ProofStep {
                siblings,
                position: target_idx,
            };
            current[target_idx].path.push(step);
        }

        path.extend(std::mem::take(&mut current[target_idx].path));

        // The log spine's shape is owned by the topology module; generation must
        // emit exactly the skeleton the verifier will check against. This holds by
        // construction — the pin guards against the producer and verifier drifting.
        debug_assert!(
            pmt::topology::inclusion_skeleton(k, tree_size, index).is_some_and(|skeleton| {
                skeleton.len() == path.len()
                    && path.iter().zip(skeleton.iter()).all(|(step, shape)| {
                        step.position == shape.position
                            && step.siblings.len() == shape.sibling_count
                    })
            }),
            "generated inclusion proof must match the canonical log skeleton"
        );

        Ok(Some(crate::proof::InclusionProof { path }))
    }

    /// Produce a self-contained [`pmt::LeafProof`] for the item at `index` in a
    /// tree of size `tree_size` — the live "is this a legitimate leaf?"
    /// witness, peer of the inclusion proof. It bundles the leaf digest with its
    /// trusted positional parameters `(index, tree_size, arity)` and the
    /// inclusion path, so a consumer verifies with one [`pmt::LeafProof::verify`]
    /// call against an authenticated root.
    pub async fn leaf_proof(
        &self,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<pmt::LeafProof>, S::Error> {
        self.leaf_proof_for(0, index, tree_size).await
    }

    /// Produce a leaf proof for a specific algorithm. Returns `None` when no
    /// inclusion proof exists for `(index, tree_size)` (out of range, or
    /// `tree_size` beyond the algorithm's committed size).
    pub async fn leaf_proof_for(
        &self,
        alg_id: u64,
        index: u64,
        tree_size: u64,
    ) -> Result<Option<pmt::LeafProof>, S::Error> {
        let Some(proof) = self.inclusion_proof_for(alg_id, index, tree_size).await? else {
            return Ok(None);
        };
        // The leaf digest is the height-0 node at the leaf's position.
        let leaf_hash = self.get_node_hash(alg_id, index, 0).await?;
        Ok(Some(pmt::LeafProof::new(
            leaf_hash,
            index,
            tree_size,
            self.config.log_arity as u64,
            proof.path,
        )))
    }

    /// Generate a consistency proof between `old_size` and `new_size`.
    pub async fn consistency_proof(
        &self,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<crate::proof::ConsistencyProof>, S::Error> {
        self.consistency_proof_for(0, old_size, new_size).await
    }

    /// Generate a consistency proof for a specific algorithm.
    pub async fn consistency_proof_for(
        &self,
        alg_id: u64,
        old_size: u64,
        new_size: u64,
    ) -> Result<Option<crate::proof::ConsistencyProof>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        let max_size = state.tree_size(self.count);

        if old_size == 0 || old_size >= new_size || new_size > max_size {
            return Ok(None);
        }

        let k = self.config.log_arity as u64;
        let old_coords = frontier_for_size(old_size, k);
        let &(boundary_left, boundary_height) =
            old_coords
                .last()
                .ok_or_else(|| crate::error::Error::CorruptedMetadata {
                    alg_id,
                    reason: "empty old_coords for non-zero old_size".to_string(),
                })?;

        let start_hash = self
            .get_node_hash(alg_id, boundary_left, boundary_height)
            .await?;

        let new_coords = frontier_for_size(new_size, k);
        let mut target_new_f_idx = None;
        for (f_idx, &(new_left, new_height)) in new_coords.iter().enumerate() {
            let cap = k.pow(new_height);
            if boundary_left >= new_left && boundary_left < new_left + cap {
                target_new_f_idx = Some((f_idx, new_left, new_height));
                break;
            }
        }

        let (f_idx, left, height) = match target_new_f_idx {
            Some(val) => val,
            None => return Ok(None),
        };

        if height < boundary_height {
            return Ok(None);
        }

        let mut path = Vec::new();
        self.log_level_bisection_path_to_height(
            alg_id,
            left,
            height,
            boundary_left,
            boundary_height,
            &mut path,
        )
        .await?;
        path.reverse();

        let mut hashes = Vec::with_capacity(new_coords.len());
        for &(l, h) in &new_coords {
            let hash = self.get_node_hash(alg_id, l, h).await?;
            hashes.push(hash);
        }

        struct MergeNode {
            hash: Vec<u8>,
            path: Vec<crate::proof::ProofStep>,
        }

        let mut current: Vec<MergeNode> = hashes
            .into_iter()
            .map(|h| MergeNode {
                hash: h,
                path: Vec::new(),
            })
            .collect();

        let mut target_idx = f_idx;
        let k_usize = self.config.log_arity;
        while current.len() > k_usize {
            let split_idx = current.len() - k_usize;

            let refs: Vec<&[u8]> = current[split_idx..]
                .iter()
                .map(|n| n.hash.as_slice())
                .collect();
            let merged_hash = nary_mr(state.hasher.as_ref(), &refs);

            let mut target_path = Vec::new();
            let mut is_target_merged = false;
            if target_idx >= split_idx {
                let mut siblings = Vec::with_capacity(k_usize - 1);
                for (j, item) in current.iter().enumerate().skip(split_idx) {
                    if j != target_idx {
                        siblings.push(item.hash.clone());
                    }
                }
                let step = crate::proof::ProofStep {
                    siblings,
                    position: target_idx - split_idx,
                };
                let mut p = std::mem::take(&mut current[target_idx].path);
                p.push(step);
                target_path = p;
                is_target_merged = true;
            }

            if is_target_merged {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: target_path,
                });
                target_idx = split_idx;
            } else {
                current.truncate(split_idx);
                current.push(MergeNode {
                    hash: merged_hash,
                    path: Vec::new(),
                });
            }
        }

        if current.len() > 1 {
            let mut siblings = Vec::with_capacity(current.len() - 1);
            for (j, item) in current.iter().enumerate() {
                if j != target_idx {
                    siblings.push(item.hash.clone());
                }
            }
            let step = crate::proof::ProofStep {
                siblings,
                position: target_idx,
            };
            current[target_idx].path.push(step);
        }

        path.extend(std::mem::take(&mut current[target_idx].path));

        Ok(Some(crate::proof::ConsistencyProof { start_hash, path }))
    }

    async fn log_level_bisection_path_to_height(
        &self,
        alg_id: u64,
        left_index: u64,
        height: u32,
        target_index: u64,
        target_height: u32,
        path: &mut Vec<crate::proof::ProofStep>,
    ) -> Result<(), S::Error> {
        let mut curr_left = left_index;
        let mut curr_height = height;
        let k = self.config.log_arity as u64;

        while curr_height > target_height {
            let child_capacity = k.pow(curr_height - 1);
            let child_idx = (target_index - curr_left) / child_capacity;

            let mut siblings = Vec::with_capacity(self.config.log_arity - 1);
            for j in 0..self.config.log_arity {
                let j_u64 = j as u64;
                if j_u64 == child_idx {
                    continue;
                }
                let c_left = curr_left + j_u64 * child_capacity;
                let hash = self.get_node_hash(alg_id, c_left, curr_height - 1).await?;
                siblings.push(hash);
            }

            path.push(crate::proof::ProofStep {
                siblings,
                position: child_idx as usize,
            });

            curr_left += child_idx * child_capacity;
            curr_height -= 1;
        }
        Ok(())
    }

    /// The committed epoch timeline at size `size`: `(alg_id, epochs)` for
    /// every algorithm registered by that size, sorted by algorithm ID.
    /// This is the timeline bound into the combined root (Design A+).
    #[must_use]
    pub fn committed_epochs_at(&self, size: u64) -> Vec<(u64, Vec<(u64, u64)>)> {
        let mut out: Vec<_> = self
            .algs
            .iter()
            .filter_map(|(&id, state)| state.epochs_at(size).map(|e| (id, e)))
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
    pub async fn combined_root_for(&self, alg_id: u64) -> Result<Vec<u8>, S::Error> {
        self.combined_root_at(alg_id, self.count).await
    }

    /// Build an `AuditPayload` at a historical tree size.
    ///
    /// Returns an error if `size == 0` or if no algorithms are active at
    /// that size.  `combined_roots` contains one entry per active algorithm.
    pub async fn audit_payload_at(
        &self,
        log_id: [u8; 32],
        size: u64,
    ) -> Result<crate::proof::AuditPayload, S::Error> {
        if size == 0 {
            return Err(crate::error::Error::IndexOutOfBounds {
                index: 0,
                tree_size: 0,
            });
        }
        let active_algs = self.active_algs_at(size);
        if active_algs.is_empty() {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }
        let alg_epochs = self.committed_epochs_at(size);
        let mut combined_roots = Vec::with_capacity(active_algs.len());
        for &id in &active_algs {
            let cr = self.combined_root_at(id, size).await?;
            combined_roots.push((id, cr));
        }
        Ok(crate::proof::AuditPayload {
            log_id,
            tree_size: size,
            active_algs,
            combined_roots,
            alg_epochs,
        })
    }

    /// Build an `AuditPayload` at the current tip.
    pub async fn audit_payload(
        &self,
        log_id: [u8; 32],
    ) -> Result<crate::proof::AuditPayload, S::Error> {
        self.audit_payload_at(log_id, self.count).await
    }

    /// Build a `CouplingProof` at a historical tree size.
    ///
    /// `active_roots` are the raw per-algorithm roots at `size`; `alg_epochs`
    /// is the committed timeline.  Together they open the combined root.
    pub async fn coupling_proof_at(
        &self,
        size: u64,
    ) -> Result<crate::proof::CouplingProof, S::Error> {
        if size == 0 {
            return Err(crate::error::Error::IndexOutOfBounds {
                index: 0,
                tree_size: 0,
            });
        }
        let active_algs = self.active_algs_at(size);
        if active_algs.is_empty() {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }
        let alg_epochs = self.committed_epochs_at(size);
        let mut active_roots = Vec::with_capacity(active_algs.len());
        for &id in &active_algs {
            let r = self.root_for_at(id, size).await?;
            active_roots.push((id, r));
        }
        Ok(crate::proof::CouplingProof {
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
    /// `verify_non_divergence` is a LOCAL self-integrity check (it trusts
    /// local epochs and stored roots); use this function to verify a payload
    /// before signing it.
    pub async fn verify_audit_payload(
        &self,
        payload: &crate::proof::AuditPayload,
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

        if !crate::proof::validate_committed_epochs(&payload.alg_epochs, size) {
            return Ok(false);
        }

        let derived_active = crate::proof::committed_active_algs(&payload.alg_epochs, size);
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
        let k = self.config.log_arity;
        let active_set: std::collections::HashSet<u64> =
            payload.active_algs.iter().copied().collect();

        // Per-algorithm rolling frontier (active-set only).
        let mut frontiers: std::collections::HashMap<u64, Vec<Vec<u8>>> = payload
            .active_algs
            .iter()
            .map(|&id| (id, Vec::new()))
            .collect();

        for i in 0..size {
            let leaf_data = if is_flat {
                match self.storage.get_leaf(i).await {
                    Ok(d) => Some(d),
                    Err(e) => return Err(crate::error::Error::Storage(e)),
                }
            } else {
                None
            };

            for &(alg_id, _) in &payload.alg_epochs {
                let state = self
                    .algs
                    .get(&alg_id)
                    .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

                let digest = match crate::proof::committed_active_at(&payload.alg_epochs, alg_id, i)
                {
                    Some(true) => {
                        if let Some(ref d) = leaf_data {
                            let expected = state.hasher.leaf(d);
                            // Flat: the stored node is a cache; if present it
                            // must match the recomputed leaf hash.
                            if let Some(stored) = self
                                .storage
                                .get_node(alg_id, i, 0)
                                .await
                                .map_err(crate::error::Error::Storage)?
                            {
                                if !crate::proof::constant_time_eq(&expected, &stored) {
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
                                .map_err(crate::error::Error::Storage)?
                            {
                                Some(v) => v,
                                None if active_set.contains(&alg_id) => return Ok(false),
                                None => state.hasher.null(),
                            }
                        }
                    },
                    Some(false) => {
                        let null = state.hasher.null();
                        if let Some(stored) = self
                            .storage
                            .get_node(alg_id, i, 0)
                            .await
                            .map_err(crate::error::Error::Storage)?
                        {
                            if !crate::proof::constant_time_eq(&stored, &null) {
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
                                crate::error::Error::CorruptedMetadata {
                                    alg_id,
                                    reason: "frontier underflow in audit".to_string(),
                                }
                            })?);
                        }
                        children.reverse();
                        let child_refs: Vec<&[u8]> =
                            children.iter().map(|c| c.as_slice()).collect();
                        let parent = nary_mr(state.hasher.as_ref(), &child_refs);
                        frontier.push(parent);
                    }
                }
            }
        }

        // ── 3. Root recomputation ─────────────────────────────────────────
        fn fold_to_root(hasher: &dyn Hasher, frontier: &[Vec<u8>], k: usize) -> Vec<u8> {
            if frontier.is_empty() {
                return hasher.empty();
            }
            if frontier.len() == 1 {
                return frontier[0].clone();
            }
            let mut cur = frontier.to_vec();
            while cur.len() > k {
                let split = cur.len() - k;
                let right: Vec<&[u8]> = cur[split..].iter().map(|v| v.as_slice()).collect();
                let merged = nary_mr(hasher, &right);
                cur.truncate(split);
                cur.push(merged);
            }
            let refs: Vec<&[u8]> = cur.iter().map(|v| v.as_slice()).collect();
            nary_mr(hasher, &refs)
        }

        let mut recomputed_roots: Vec<(u64, Vec<u8>)> =
            Vec::with_capacity(payload.active_algs.len());
        for &id in &payload.active_algs {
            let state = self
                .algs
                .get(&id)
                .ok_or(crate::error::Error::UnknownAlgorithm(id))?;
            let frontier = &frontiers[&id];
            let raw_root = fold_to_root(state.hasher.as_ref(), frontier, k);
            recomputed_roots.push((id, raw_root));
        }

        // Apply genesis-promotion rule (mirrors combined_root_at).
        let is_promoted =
            payload.alg_epochs.len() == 1 && payload.alg_epochs[0].1 == vec![(0u64, u64::MAX)];

        for (i, &id) in payload.active_algs.iter().enumerate() {
            let state = self
                .algs
                .get(&id)
                .ok_or(crate::error::Error::UnknownAlgorithm(id))?;

            let computed_cr = if is_promoted {
                recomputed_roots[i].1.clone()
            } else {
                let buf =
                    crate::proof::combined_root_preimage(&recomputed_roots, &payload.alg_epochs);
                state.hasher.hash(&buf)
            };

            if !crate::proof::constant_time_eq(&computed_cr, &payload.combined_roots[i].1) {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// The sorted set of algorithms active at the historical `size`
    /// (algorithms whose epochs cover the final position `size - 1`).
    fn active_algs_at(&self, size: u64) -> Vec<u64> {
        let mut active_algs = Vec::new();
        for (&id, alg_state) in &self.algs {
            if size > 0 && alg_state.is_active_at(size - 1) {
                active_algs.push(id);
            }
        }
        active_algs.sort_unstable();
        active_algs
    }

    /// Compute the combined root hash for a specific algorithm at a historical tree size.
    ///
    /// The combined root is a metaroot: a structural layer that, like any
    /// node, commits what is below it — except it spans every algorithm's
    /// tree. Its preimage covers the raw roots of all active algorithms AND
    /// the committed epoch timeline of every registered algorithm, because
    /// the timeline is part of the multi-algorithm structure (it decides
    /// which cells are null projections). Binding the timeline makes
    /// activity/inactivity claims non-equivocable: without it, an active
    /// position whose payload hashes to the null constant and a genuinely
    /// inactive position are byte-identical under the root, so inactivity
    /// would be forgeable by metadata substitution.
    ///
    /// **Genesis Promotion:** while the registry has ever contained only one
    /// algorithm and its timeline is the forced default `[(0, u64::MAX)]`
    /// (active from position 0, still open), the preimage carries zero
    /// information beyond the raw root, so the metaroot promotes to the raw
    /// root — the same discipline as singleton node promotion (hash only when
    /// hashing adds binding information). Any lifecycle event — a second
    /// registration, a tip deactivation, or a deactivate/resume — makes the
    /// timeline information-bearing and permanently switches to the hashed
    /// form. Promotion is keyed on the REGISTRY (never the active set): a
    /// sole-active algorithm may carry a pre-activation null prefix, which is
    /// precisely the case the timeline commitment exists to bind.
    pub async fn combined_root_at(&self, alg_id: u64, size: u64) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if size == 0 {
            return Ok(state.hasher.empty());
        }

        // 1. Gather active algorithms at the given historical size
        let active_algs = self.active_algs_at(size);

        if active_algs.is_empty() {
            return Err(crate::error::Error::NoActiveAlgorithms);
        }

        // Ensure the requested algorithm is active at this size
        if !active_algs.contains(&alg_id) {
            return Err(crate::error::Error::FrozenAlgorithm(alg_id));
        }

        // 2. Build the metaroot preimage: sorted active roots plus the committed epoch timeline of
        //    every registered algorithm.
        let mut active_roots = Vec::with_capacity(active_algs.len());
        for &id in &active_algs {
            let r = self.root_for_at(id, size).await?;
            active_roots.push((id, r));
        }
        let alg_epochs = self.committed_epochs_at(size);

        // Genesis promotion: registry-singleton with the forced default
        // timeline carries zero information beyond the raw root — promote.
        // Any lifecycle event switches permanently to the hashed form.
        // Keyed on the REGISTRY, not the active set (see doc comment above).
        if alg_epochs.len() == 1 && alg_epochs[0].1 == vec![(0u64, u64::MAX)] {
            return Ok(active_roots.into_iter().next().unwrap().1);
        }

        // 3. Hash the snapshot using the target algorithm's hasher
        let buf = crate::proof::combined_root_preimage(&active_roots, &alg_epochs);
        Ok(state.hasher.hash(&buf))
    }

    /// The materialized digest of the frontier peak at coordinate
    /// `(left, height)` for `alg_id` — one perfect k-ary subtree root of the
    /// frontier. Returns the algorithm's null constant for a coordinate whose
    /// range carries no active leaf, matching the projection the root fold uses.
    ///
    /// This is the per-peak read the seal freezes; folding the peaks at
    /// [`frontier_for_size`]`(size, k)` reproduces [`Self::root_for_at`] exactly.
    pub async fn peak_at(&self, alg_id: u64, left: u64, height: u32) -> Result<Vec<u8>, S::Error> {
        self.get_node_hash(alg_id, left, height).await
    }

    /// Retrieve the raw root hash for a specific algorithm at a historical tree size.
    pub async fn root_for_at(&self, alg_id: u64, size: u64) -> Result<Vec<u8>, S::Error> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

        if size > self.count {
            return Err(crate::error::Error::IndexOutOfBounds {
                index: size,
                tree_size: self.count,
            });
        }

        let alg_size = if size <= state.first_activation() {
            // Null projections fill [0, size); frontier geometry uses the global size.
            // For size == 0 this gives alg_size == 0 → empty() return below.
            size
        } else if state.is_active_at(size - 1) {
            size
        } else {
            state
                .epochs
                .iter()
                .filter(|&&(_, end)| end < size)
                .map(|&(_, end)| end)
                .max()
                .unwrap_or(0)
        };

        if alg_size == 0 {
            return Ok(state.hasher.empty());
        }

        let k = self.config.log_arity;
        let coords = frontier_for_size(alg_size, k as u64);

        let mut frontier = Vec::with_capacity(coords.len());
        for &(left, height) in &coords {
            let hash = self.get_node_hash(alg_id, left, height).await?;
            frontier.push(hash);
        }

        if frontier.is_empty() {
            return Ok(state.hasher.empty());
        }
        if frontier.len() == 1 {
            return Ok(frontier[0].clone());
        }

        let mut current = frontier;
        while current.len() > k {
            let split_idx = current.len() - k;
            let right_elements = &current[split_idx..];
            let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
            let merged = nary_mr(state.hasher.as_ref(), &refs);
            current.truncate(split_idx);
            current.push(merged);
        }
        let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
        Ok(nary_mr(state.hasher.as_ref(), &refs))
    }

    /// Verify that the trees for all active algorithms have not diverged
    /// from the underlying leaf data stored in the database.
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
            for (&id, state) in &self.algs {
                let check_start = std::cmp::max(start, state.first_activation());
                if check_start < end {
                    let get_alg_size = |s_val: u64| {
                        if s_val <= state.first_activation() {
                            0
                        } else if state.is_active_at(s_val - 1) {
                            s_val
                        } else {
                            state
                                .epochs
                                .iter()
                                .filter(|&&(_, end)| end < s_val)
                                .map(|&(_, end)| end)
                                .max()
                                .unwrap_or(0)
                        }
                    };

                    let old_alg_size = get_alg_size(check_start);
                    let new_alg_size = get_alg_size(end);

                    let old_root = if old_alg_size == 0 {
                        state.hasher.empty()
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
                        found.ok_or(crate::error::Error::UnknownAlgorithm(id))?
                    };
                    let new_root = self.root_for_at(id, end).await?;

                    if old_alg_size < new_alg_size && old_alg_size > 0 {
                        // Verify consistency using standard O(log N) verification from old_alg_size
                        // to new_alg_size
                        if let Some(proof) = self
                            .consistency_proof_for(id, old_alg_size, new_alg_size)
                            .await?
                        {
                            if !crate::proof::verify_consistency(
                                state.hasher.as_ref(),
                                old_alg_size,
                                new_alg_size,
                                self.config.log_arity as u64,
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
                        if !crate::proof::constant_time_eq(&old_root, &new_root) {
                            return Ok(false);
                        }
                    }
                }
            }
        }

        // Helper helper to fold a frontier to its root.
        fn fold_frontier(hasher: &dyn Hasher, frontier: &[Vec<u8>], k: usize) -> Vec<u8> {
            if frontier.is_empty() {
                return hasher.empty();
            }
            if frontier.len() == 1 {
                return frontier[0].clone();
            }
            let mut current = frontier.to_vec();
            while current.len() > k {
                let split_idx = current.len() - k;
                let right_elements = &current[split_idx..];
                let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
                let merged = nary_mr(hasher, &refs);
                current.truncate(split_idx);
                current.push(merged);
            }
            let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
            nary_mr(hasher, &refs)
        }

        // Reconstruct frontier stacks at checkpoint size and verify starting boundaries
        let mut alg_frontiers = std::collections::HashMap::new();
        for (&alg_id, state) in &self.algs {
            if !state.is_active() {
                let deact_index = state.epochs.last().map_or(0, |&(_, end)| end);
                if deact_index < end
                    && self
                        .storage
                        .get_node(alg_id, deact_index, 0)
                        .await
                        .map_err(crate::error::Error::Storage)?
                        .is_some()
                {
                    return Ok(false); // Tampered: nodes exist beyond deactivation point!
                }
            }

            let mut frontier = Vec::new();
            let mut frontier_coords = Vec::new();
            let k = self.config.log_arity;

            let alg_size_at_start = if start <= state.first_activation() {
                // Null projections span [0, start); use the global start so the
                // carry schedule (reduction_count(alg_size - 1, k)) matches the
                // global index at each step, matching the append path exactly.
                // When start == 0 this gives 0, leaving the frontier empty (correct).
                start
            } else if state.is_active_at(start - 1) {
                start
            } else {
                state
                    .epochs
                    .iter()
                    .filter(|&&(_, e)| e < start)
                    .map(|&(_, e)| e)
                    .max()
                    .unwrap_or(0)
            };

            if alg_size_at_start > 0 {
                let coords = frontier_for_size(alg_size_at_start, k as u64);
                for &(left, height) in &coords {
                    let hash = self.get_node_hash(alg_id, left, height).await?;
                    frontier.push(hash);
                    frontier_coords.push((left, height));
                }
            }

            if start > 0 {
                let folded = fold_frontier(state.hasher.as_ref(), &frontier, k);
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
                            state.hasher.empty()
                        } else if start <= state.first_activation() {
                            // Pre-activation algorithm: null projections over [0, start)
                            // fold to null() by null promotion — no trusted root needed.
                            state.hasher.null()
                        } else {
                            return Err(crate::error::Error::UnknownAlgorithm(alg_id));
                        }
                    },
                };

                if !crate::proof::constant_time_eq(&folded, &expected_root) {
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
                    Err(e) => return Err(crate::error::Error::Storage(e)),
                }
            } else {
                None
            };

            for (&alg_id, state) in &self.algs {
                let (frontier, frontier_coords, alg_size) = alg_frontiers
                    .get_mut(&alg_id)
                    .ok_or(crate::error::Error::UnknownAlgorithm(alg_id))?;

                let deact_index = if state.is_active() {
                    u64::MAX
                } else {
                    state.epochs.last().map_or(0, |&(_, end)| end)
                };

                if i >= deact_index {
                    continue;
                }

                let is_active = state.is_active_at(i);

                let digest = if is_active {
                    if let Some(ref d) = data {
                        // Flat: compute from raw leaf bytes; compare to cached
                        // tree node to detect cache tampering independently.
                        let computed = state.hasher.leaf(d);
                        let stored = self.get_node_hash(alg_id, i, 0).await?;
                        if !crate::proof::constant_time_eq(&computed, &stored) {
                            return Ok(false); // Cached node doesn't match raw leaf.
                        }
                        computed
                    } else {
                        // Subtree: only the stored root is available; tampering
                        // is detected by the parent-level recomputation below.
                        self.get_node_hash(alg_id, i, 0).await?
                    }
                } else {
                    state.hasher.null()
                };

                frontier.push(digest);
                frontier_coords.push((i, 0));
                *alg_size += 1;

                let merges = reduction_count(*alg_size - 1, self.config.log_arity as u64);
                for _ in 0..merges {
                    if frontier.len() < self.config.log_arity {
                        return Ok(false); // Frontier underflow!
                    }
                    let mut children = Vec::with_capacity(self.config.log_arity);
                    let mut coords = Vec::with_capacity(self.config.log_arity);
                    for _ in 0..self.config.log_arity {
                        children.push(frontier.pop().ok_or_else(|| {
                            crate::error::Error::CorruptedMetadata {
                                alg_id,
                                reason: "frontier underflow".to_string(),
                            }
                        })?);
                        coords.push(frontier_coords.pop().ok_or_else(|| {
                            crate::error::Error::CorruptedMetadata {
                                alg_id,
                                reason: "frontier_coords underflow".to_string(),
                            }
                        })?);
                    }
                    children.reverse();
                    coords.reverse();

                    let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
                    let parent = nary_mr(state.hasher.as_ref(), &child_refs);

                    let parent_left_index = coords[0].0;
                    let parent_height = coords[0].1 + 1;

                    let stored_parent = self
                        .get_node_hash(alg_id, parent_left_index, parent_height)
                        .await?;
                    if !crate::proof::constant_time_eq(&parent, &stored_parent) {
                        return Ok(false); // Internal node hash mismatch!
                    }

                    frontier.push(parent);
                    frontier_coords.push((parent_left_index, parent_height));
                }
            }
        }

        // Verify final recomputed roots match the current logger roots
        for (&alg_id, state) in &self.algs {
            let (frontier, ..) = &alg_frontiers[&alg_id];
            let folded = fold_frontier(state.hasher.as_ref(), frontier, self.config.log_arity);
            let final_root = self.root_for_at(alg_id, end).await?;
            if !crate::proof::constant_time_eq(&folded, &final_root) {
                return Ok(false); // Final root mismatch!
            }
        }

        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;

    #[derive(Debug)]
    struct TestHasher;
    impl Hasher for TestHasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            data.to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            children.concat()
        }

        fn empty(&self) -> Vec<u8> {
            Vec::new()
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            data.to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(TestHasher)
        }
    }

    #[test]
    fn test_epochs_at_snapshot_clamping() {
        let state = AlgState {
            hasher: Box::new(TestHasher),
            epochs: vec![(2, 5), (7, 12), (15, u64::MAX)],
            frontier: Vec::new(),
            frontier_coords: Vec::new(),
        };
        // Not yet registered.
        assert_eq!(state.epochs_at(1), None);
        // Mid-interval: encoded open, later intervals dropped.
        assert_eq!(state.epochs_at(3), Some(vec![(2, u64::MAX)]));
        // Exactly at a deactivation boundary: stays closed.
        assert_eq!(state.epochs_at(5), Some(vec![(2, 5)]));
        // Between intervals.
        assert_eq!(state.epochs_at(6), Some(vec![(2, 5)]));
        // Activation exactly at the snapshot: registered, open, no content.
        assert_eq!(state.epochs_at(7), Some(vec![(2, 5), (7, u64::MAX)]));
        // Past all closed intervals, inside the open one.
        assert_eq!(
            state.epochs_at(20),
            Some(vec![(2, 5), (7, 12), (15, u64::MAX)])
        );
    }

    #[test]
    fn test_leaf_proof_accepts_legit_and_rejects_forged() {
        use sha2::{Digest as _, Sha256};

        #[derive(Debug)]
        struct Sha256Hasher;
        impl Hasher for Sha256Hasher {
            fn leaf(&self, data: &[u8]) -> Vec<u8> {
                Sha256::digest(data).to_vec()
            }

            fn node(&self, children: &[&[u8]]) -> Vec<u8> {
                let mut h = Sha256::new();
                for c in children {
                    h.update(c);
                }
                h.finalize().to_vec()
            }

            fn empty(&self) -> Vec<u8> {
                Sha256::digest(b"").to_vec()
            }

            fn hash(&self, data: &[u8]) -> Vec<u8> {
                Sha256::digest(data).to_vec()
            }

            fn clone_box(&self) -> Box<dyn Hasher> {
                Box::new(Sha256Hasher)
            }
        }

        smol::block_on(async {
            let storage = MemoryStorage::new();
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config)
                .await
                .unwrap();

            let payloads: Vec<Vec<u8>> = (0..12u64)
                .map(|i| format!("item-{i}").into_bytes())
                .collect();
            for p in &payloads {
                log.append_leaf(p).await.unwrap();
            }

            let size = payloads.len() as u64;
            let root = log.root_for_at(0, size).await.unwrap();
            let h = Sha256Hasher;

            for index in 0..size {
                let proof = log
                    .leaf_proof(index, size)
                    .await
                    .unwrap()
                    .expect("in range");
                // Self-describing: positional fields carried, no re-supply.
                assert_eq!(proof.index, index);
                assert_eq!(proof.tree_size, size);
                assert_eq!(proof.log_arity, 2);
                // Legitimate leaf accepted.
                assert!(proof.verify(&h, &root), "index={index}");
                // Forged leaf at the same position rejected.
                let mut forged = proof.clone();
                forged.leaf_hash = h.leaf(b"forged-item");
                assert!(!forged.verify(&h, &root), "index={index}");
            }

            // Out of range yields no proof.
            assert!(log.leaf_proof(size, size).await.unwrap().is_none());
        });
    }

    #[test]
    fn test_structural_node_id_storage() {
        smol::block_on(async {
            let storage = MemoryStorage::new();
            let config = TreeConfig { log_arity: 2 };
            let mut log = NaryMerkleLog::new(storage, Box::new(TestHasher), config)
                .await
                .unwrap();

            log.append_leaf(b"a").await.unwrap();
            log.append_leaf(b"b").await.unwrap();

            let storage_ref = log.storage();
            let node_hash = storage_ref.get_node(0, 0, 1).await.unwrap();
            assert!(
                node_hash.is_some(),
                "node at coordinate (0, 1) should be stored"
            );
        });
    }
}

#[cfg(test)]
mod resume_tests {
    use pmt::hasher::Hasher;
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::storage::MemoryStorage;

    /// A real fixed-width (32-byte) hasher.
    #[derive(Debug, Clone)]
    struct Sha256Hasher;
    impl Hasher for Sha256Hasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut h = Sha256::new();
            for c in children {
                h.update(c);
            }
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            Sha256::digest(b"").to_vec()
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(self.clone())
        }
    }

    async fn eml_with(n: u64, k: usize) -> NaryMerkleLog<MemoryStorage> {
        let config = TreeConfig { log_arity: k };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for i in 0..n {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log
    }

    /// Append a real leaf forward onto a resumed (subtree-kind) log.
    async fn append_forward(log: &mut NaryMerkleLog<MemoryStorage>, data: &[u8]) {
        log.append_subtree(&pmt::Subtree::Leaf(data.to_vec()))
            .await
            .unwrap();
    }

    // ─────────────────────────────────────────────────────────────────────
    // RESUME from an EML-origin Sealed: the resumed log reproduces the sealed
    // member root, appends forward, and a consistency proof bridges the resume.
    // Swept across sizes and arities — resume has no failure conditions.
    // ─────────────────────────────────────────────────────────────────────

    #[test]
    fn resume_from_eml_origin_reproduces_root_and_appends() {
        smol::block_on(async {
            let h = Sha256Hasher;
            for k in [2usize, 3, 4] {
                for n in 1u64..16 {
                    let log = eml_with(n, k).await;
                    let sealed_member = log.root_for_at(0, n).await.unwrap();
                    let sealed = log.seal().await.unwrap();

                    let mut resumed = NaryMerkleLog::resume(
                        &sealed,
                        MemoryStorage::new(),
                        vec![(0, Box::new(Sha256Hasher))],
                    )
                    .await
                    .expect("resume never fails for a well-formed Sealed");

                    assert_eq!(resumed.count(), n);
                    assert_eq!(
                        resumed.root_for_at(0, n).await.unwrap(),
                        sealed_member,
                        "resumed root must reproduce the sealed member root (n={n}, k={k})"
                    );

                    append_forward(&mut resumed, b"fwd-0").await;
                    append_forward(&mut resumed, b"fwd-1").await;
                    assert_eq!(resumed.count(), n + 2);

                    // Consistency across the resume boundary holds.
                    let proof = resumed.consistency_proof(n, n + 2).await.unwrap();
                    assert!(
                        proof.is_some(),
                        "consistency must bridge resume (n={n}, k={k})"
                    );
                    let old_root = sealed_member.clone();
                    let new_root = resumed.root_for_at(0, n + 2).await.unwrap();
                    let proof = proof.unwrap();
                    assert!(
                        crate::proof::verify_consistency(
                            &h,
                            n,
                            n + 2,
                            k as u64,
                            &proof.start_hash,
                            &proof.path,
                            &old_root,
                            &new_root,
                        ),
                        "consistency proof must verify across resume (n={n}, k={k})"
                    );
                }
            }
        });
    }

    // (EMT-origin resume — building a Sealed from a mutable `emt::Emt` and
    // resuming an EML onto it — is exercised in `examples/tests/seal_embed.rs`
    // E5; it lives there to keep the `emt` dependency out of this crate and
    // preserve the no-EML↔EMT-edge DAG constraint.)

    // A missing hasher for an algorithm in the frontier is the one rejection.
    #[test]
    fn resume_rejects_missing_hasher() {
        smol::block_on(async {
            let log = eml_with(4, 2).await;
            let sealed = log.seal().await.unwrap();
            let err = NaryMerkleLog::resume(&sealed, MemoryStorage::new(), vec![])
                .await
                .unwrap_err();
            assert_eq!(err, crate::error::Error::UnknownAlgorithm(0));
        });
    }
}
