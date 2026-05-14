//! TSML Log — the core state machine.
//!
//! Implements Definitions 6-14c of the formal model: the TSML state tuple,
//! leaf value function, append (with node persistence), algorithm
//! add/remove/resume, root extraction, projection, and proof generation.

use std::collections::BTreeMap;

use crate::error::{Error, Result};
use crate::hasher::Hasher;
use crate::null::NullTable;
use crate::storage::Storage;

// ============================================================================
// Algorithm state
// ============================================================================

/// Per-algorithm state within the TSML log.
#[derive(Debug)]
struct AlgState {
    /// The hasher instance for this algorithm.
    hasher: Box<dyn Hasher>,
    /// Disjoint active epochs. Each epoch is `(start, end)` where
    /// `end == u64::MAX` means the algorithm is currently active.
    /// Epochs are in chronological order and non-overlapping.
    epochs: Vec<(u64, u64)>,
    /// Frontier stack: roots of complete subtrees along the right edge.
    stack: Vec<Vec<u8>>,
    /// Precomputed null subtree constants.
    null_table: NullTable,
}

impl AlgState {
    /// Whether this algorithm is currently active (not frozen).
    fn is_active(&self) -> bool {
        self.epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
    }

    /// Whether leaf index `i` falls within any of this algorithm's active epochs.
    fn is_active_at(&self, i: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start <= i && i < end)
    }

    /// The tree size for this algorithm.
    ///
    /// Active algorithms track the global tree size.
    /// Frozen algorithms stopped at their last deactivation point.
    fn tree_size(&self, global_size: u64) -> u64 {
        if self.is_active() {
            global_size
        } else {
            self.epochs.last().map_or(0, |&(_, end)| end)
        }
    }

    /// The activation index of the first epoch.
    fn first_activation(&self) -> u64 {
        self.epochs.first().map_or(0, |&(start, _)| start)
    }

    /// Whether algorithm has active content in the half-open range `[lo, hi)`.
    ///
    /// Definition 14b (Active range): true iff any epoch overlaps the interval.
    /// Generalizes `is_active_at` from a single index to an interval.
    fn active_range(&self, lo: u64, hi: u64) -> bool {
        self.epochs
            .iter()
            .any(|&(start, end)| start < hi && end > lo)
    }
}

// ============================================================================
// Count trailing ones
// ============================================================================

/// Count trailing one-bits in the binary representation of `n`.
///
/// Used by the append algorithm (Definition 8) to determine the number
/// of stack merges after pushing a new leaf.
/// Largest power of 2 strictly less than `n` (u64 variant).
///
/// Defined for `n > 1`. Panics if `n <= 1`.
fn largest_pow2_lt_u64(n: u64) -> u64 {
    debug_assert!(n > 1, "largest_pow2_lt_u64 requires n > 1, got {n}");
    1u64 << (63 - (n - 1).leading_zeros())
}

fn count_trailing_ones(n: u64) -> u32 {
    (!n).trailing_zeros()
}

// ============================================================================
// Null prefix peaks
// ============================================================================

/// Compute the frontier stack for a tree of `K` null leaves.
///
/// Definition 10 from the formal model. The stack decomposes `K` into its
/// binary components (MMR peaks), with subtrees ordered by descending bit
/// index (MSB first = largest subtrees at stack bottom).
///
/// For K=6 (binary 110): returns [N₂(a), N₁(a)] with N₁ on top.
fn null_prefix_peaks(hasher: &dyn Hasher, null_table: &mut NullTable, k: u64) -> Vec<Vec<u8>> {
    if k == 0 {
        return Vec::new();
    }

    let mut peaks = Vec::new();
    // Iterate bits from MSB to LSB (descending order).
    let bit_width = 64 - k.leading_zeros();
    for bit in (0..bit_width).rev() {
        if k & (1 << bit) != 0 {
            let null_root = null_table.get(hasher, bit as usize).to_vec();
            peaks.push(null_root);
        }
    }
    peaks
}

/// Extend a frozen frontier stack by appending null leaves.
///
/// The frozen stack represents a tree of `deact` leaves (positions `[0, deact)`).
/// This function appends `gap_size` null leaves (positions `[deact, deact+gap_size)`)
/// using the standard CTO-based frontier merge algorithm.
///
/// Sealed internal nodes are persisted into `storage` during CTO merges.
/// By Observation 2, purely-null subtrees are derivable from NullTable
/// and need not be stored; however, mixed nodes (combining previously-active
/// content with null gap leaves) must be persisted.
///
/// The result is the correct frontier stack for `deact + gap_size` leaves,
/// with real data in `[0, deact)` and null constants in `[deact, deact+gap_size)`.
///
/// Complexity: O(gap_size) total hash operations (amortized O(1) per append).
fn extend_with_nulls<S: Storage>(
    frozen: &[Vec<u8>],
    hasher: &dyn Hasher,
    storage: &mut S,
    alg_id: u64,
    deact: u64,
    gap_size: u64,
) -> Result<Vec<Vec<u8>>> {
    if gap_size == 0 {
        return Ok(frozen.to_vec());
    }

    let null_leaf = hasher.null();

    // Stack is MSB-first, same convention as Log::append().
    // push/pop operate on the end (LSB position).
    let mut stack: Vec<Vec<u8>> = frozen.to_vec();

    for i in 0..gap_size {
        let n = deact + i; // tree size before this append
        stack.push(null_leaf.clone());

        // Standard frontier merge: count trailing ones determines merge depth.
        let merges = n.trailing_ones();
        for j in 1..=merges {
            let right = stack.pop().expect("stack underflow during null extend");
            let left = stack.pop().expect("stack underflow during null extend");
            let parent = hasher.node(&left, &right);

            let height = j as usize;
            let left_pos = n + 1 - (1u64 << height);
            storage
                .store_node(alg_id, left_pos, height, &parent)
                .map_err(|e| Error::Storage(Box::new(e)))?;

            stack.push(parent);
        }
    }

    Ok(stack)
}

// ============================================================================
// TSML Log
// ============================================================================

/// Per-algorithm metadata snapshot (Definition 13).
///
/// Returned by [`Log::algorithms`]. Contains all the data an implementor
/// needs to serialize a state manifest in their chosen wire format.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlgorithmInfo {
    /// Algorithm identifier.
    pub id: u64,
    /// Current root hash for this algorithm.
    pub root: Vec<u8>,
    /// Global index at which this algorithm was first activated (inclusive).
    pub activation_index: u64,
    /// Global index at which this algorithm was last deactivated (exclusive).
    /// `None` if the algorithm is currently active.
    pub deactivation_index: Option<u64>,
    /// Effective tree size: last deactivation if frozen, else global tree size.
    pub tree_size: u64,
    /// Complete epoch history. Each `(start, end)` is an active interval.
    /// `end == None` means the epoch is currently open (algorithm is active).
    pub epochs: Vec<(u64, Option<u64>)>,
}

/// A Temporally-Sparse Merkle Log.
///
/// Maintains a single shared topology across multiple hash algorithms.
/// Each algorithm sees the global tree, but positions outside its active
/// window contain deterministic null constants.
///
/// # Model Mapping
///
/// This struct implements Definition 6 (TSML state):
/// `S = (storage, size, act, stacks, nodes)`
///
/// Raw leaf payloads and sealed internal node hashes are persisted
/// through the [`Storage`] backend. The log retains only frontier
/// stacks in memory (O(log n) per algorithm).
#[derive(Debug)]
pub struct Log<S: Storage> {
    /// Backend for raw leaf payloads and sealed internal node hashes.
    storage: S,
    /// Per-algorithm state, keyed by algorithm ID.
    algs: BTreeMap<u64, AlgState>,
}

impl<S: Storage> Log<S> {
    /// Create a new empty TSML log with the given storage backend.
    pub fn new(storage: S) -> Self {
        Self {
            storage,
            algs: BTreeMap::new(),
        }
    }

    /// Current number of leaves in the global log.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.storage.len()
    }

    // ========================================================================
    // Algorithm management (Definitions 9, 10, 11)
    // ========================================================================

    /// Register a new algorithm, activating it at the current tree size.
    ///
    /// Definition 9 (Add algorithm): the algorithm's frontier stack is
    /// initialized with null prefix peaks for all prior positions.
    ///
    /// # Errors
    ///
    /// Returns [`Error::DuplicateAlgorithm`] if `alg_id` is already registered.
    pub fn add_algorithm(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) -> Result<()> {
        if self.algs.contains_key(&alg_id) {
            return Err(Error::DuplicateAlgorithm(alg_id));
        }

        let activation = self.size();
        let mut null_table = NullTable::new(hasher.as_ref());
        let stack = null_prefix_peaks(hasher.as_ref(), &mut null_table, activation);

        // Eagerly populate null table to current tree height so that
        // proof generation (which takes &self) never needs mutation.
        if activation > 0 {
            let max_height = (64 - activation.leading_zeros()) as usize;
            null_table.ensure_height(hasher.as_ref(), max_height);
        }

        self.algs.insert(
            alg_id,
            AlgState {
                hasher,
                epochs: vec![(activation, u64::MAX)],
                stack,
                null_table,
            },
        );

        Ok(())
    }

    /// Deactivate (freeze) an algorithm at the current tree size.
    ///
    /// Definition 11 (Remove algorithm): sets the deactivation boundary.
    /// The algorithm's frontier stack becomes immutable; future appends
    /// do not update it.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::FrozenAlgorithm`] if already deactivated.
    pub fn remove_algorithm(&mut self, alg_id: u64) -> Result<()> {
        let current_size = self.size();
        let state = self
            .algs
            .get_mut(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        if !state.is_active() {
            return Err(Error::FrozenAlgorithm(alg_id));
        }

        if let Some(last) = state.epochs.last_mut() {
            last.1 = current_size;
        }
        Ok(())
    }

    /// Reactivate a frozen algorithm at the current tree size.
    ///
    /// The frozen frontier stack is fast-forwarded through the null gap
    /// (positions from deactivation to current size) using the standard
    /// CTO-based frontier algorithm. Sealed internal nodes are persisted
    /// into storage during the gap extension. A new active epoch
    /// `(current_size, ∞)` is appended.
    ///
    /// Complexity: O(gap) hash operations and node stores.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::AlgorithmActive`] if the algorithm is already active.
    pub fn resume_algorithm(&mut self, alg_id: u64) -> Result<()> {
        let current_size = self.storage.len();

        // Validate state and extract parameters.
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        if state.is_active() {
            return Err(Error::AlgorithmActive(alg_id));
        }

        let deactivation = state.epochs.last().unwrap().1;
        let gap = current_size - deactivation;

        if gap > 0 {
            // Split borrow: access self.algs (shared) and self.storage (mutable)
            // as disjoint fields.
            let state = &self.algs[&alg_id];
            let frozen_stack = state.stack.clone();
            let hasher = state.hasher.as_ref();
            let new_stack = extend_with_nulls(
                &frozen_stack,
                hasher,
                &mut self.storage,
                alg_id,
                deactivation,
                gap,
            )?;
            self.algs.get_mut(&alg_id).unwrap().stack = new_stack;
        }

        // Eagerly populate null table to current tree height.
        {
            let state = self.algs.get_mut(&alg_id).unwrap();
            let max_height = (64 - current_size.leading_zeros()) as usize;
            state
                .null_table
                .ensure_height(state.hasher.as_ref(), max_height);
        }

        self.algs
            .get_mut(&alg_id)
            .unwrap()
            .epochs
            .push((current_size, u64::MAX));
        Ok(())
    }

    /// Check whether an algorithm is currently active.
    ///
    /// Returns `None` if the algorithm is not registered.
    #[must_use]
    pub fn is_active(&self, alg_id: u64) -> Option<bool> {
        self.algs.get(&alg_id).map(|s| s.is_active())
    }

    /// Get the tree size for a specific algorithm.
    ///
    /// Active algorithms return the global tree size.
    /// Frozen algorithms return their deactivation point.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn tree_size(&self, alg_id: u64) -> Result<u64> {
        self.algs
            .get(&alg_id)
            .map(|s| s.tree_size(self.size()))
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    // ========================================================================
    // Append (Definition 8)
    // ========================================================================

    /// Append a new leaf payload to the log.
    ///
    /// Definition 8 (Append): pushes the leaf hash (or null constant) onto
    /// each active algorithm's frontier stack, then merges complete pairs
    /// by counting trailing ones in the pre-increment size. Sealed parent
    /// nodes are persisted into storage for O(log n) proof generation.
    ///
    /// Frozen algorithms are not updated.
    ///
    /// Returns the 0-based leaf index.
    ///
    /// # Errors
    ///
    /// Returns [`Error::NoActiveAlgorithms`] if no algorithms are active.
    pub fn append(&mut self, data: &[u8]) -> Result<u64> {
        // Check at least one algorithm is active.
        if !self.algs.values().any(|s| s.is_active()) {
            return Err(Error::NoActiveAlgorithms);
        }

        let index = self.size();
        let merge_count = count_trailing_ones(index);

        self.storage
            .store_leaf(index, data)
            .map_err(|e| Error::Storage(Box::new(e)))?;

        for (&alg_id, state) in self.algs.iter_mut() {
            if !state.is_active() {
                continue;
            }

            // Definition 7 (Leaf value): real hash or null constant.
            let digest = if state.is_active_at(index) {
                state.hasher.leaf(data)
            } else {
                state.null_table.leaf_null().to_vec()
            };

            state.stack.push(digest);

            // CTO merge with node persistence (Definition 8).
            // After merge j (1-indexed), the sealed subtree covers
            // [index + 1 - 2^j, index + 1) at height j.
            for j in 1..=merge_count {
                let right = state.stack.pop().expect("stack underflow in merge");
                let left = state.stack.pop().expect("stack underflow in merge");
                let parent = state.hasher.node(&left, &right);

                let height = j as usize;
                let left_pos = index + 1 - (1u64 << height);
                self.storage
                    .store_node(alg_id, left_pos, height, &parent)
                    .map_err(|e| Error::Storage(Box::new(e)))?;

                state.stack.push(parent);
            }

            // Eagerly populate null table to current tree height.
            let tree_size = index + 1;
            let max_height = (64 - tree_size.leading_zeros()) as usize;
            state
                .null_table
                .ensure_height(state.hasher.as_ref(), max_height);
        }

        Ok(index)
    }

    // ========================================================================
    // Root extraction (Definition 12)
    // ========================================================================

    /// Compute the current root hash for a specific algorithm.
    ///
    /// Definition 12 (Per-algorithm root): folds the frontier stack
    /// right-to-left via `node(a, left, acc)`.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn root(&self, alg_id: u64) -> Result<Vec<u8>> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        if state.stack.is_empty() {
            return Ok(state.hasher.empty());
        }

        // Fold right-to-left: the rightmost stack entry is the accumulator seed.
        let root = state
            .stack
            .iter()
            .rev()
            .cloned()
            .reduce(|acc, left| state.hasher.node(&left, &acc))
            .expect("non-empty stack has at least one element");

        Ok(root)
    }

    /// Returns an iterator over all registered algorithm IDs.
    pub fn algorithm_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.algs.keys().copied()
    }

    /// Returns the first activation index for an algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn activation_index(&self, alg_id: u64) -> Result<u64> {
        self.algs
            .get(&alg_id)
            .map(|s| s.first_activation())
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    /// Returns the last deactivation index for an algorithm.
    ///
    /// Returns `None` in the inner `Option` if the algorithm is currently active.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn deactivation_index(&self, alg_id: u64) -> Result<Option<u64>> {
        self.algs
            .get(&alg_id)
            .map(|s| {
                if s.is_active() {
                    None
                } else {
                    s.epochs.last().map(|&(_, end)| end)
                }
            })
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    /// Returns the full epoch history for an algorithm.
    ///
    /// Each epoch is `(start, end)` where `end == None` means active.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    pub fn epochs(&self, alg_id: u64) -> Result<Vec<(u64, Option<u64>)>> {
        self.algs
            .get(&alg_id)
            .map(|s| {
                s.epochs
                    .iter()
                    .map(|&(start, end)| {
                        if end == u64::MAX {
                            (start, None)
                        } else {
                            (start, Some(end))
                        }
                    })
                    .collect()
            })
            .ok_or(Error::UnknownAlgorithm(alg_id))
    }

    // ========================================================================
    // TSML Manifest (Definition 13)
    // ========================================================================

    /// Produce a snapshot of all registered algorithms' state.
    ///
    /// Definition 13 (TSML Manifest): returns the data needed to construct
    /// a state manifest. Each [`AlgorithmInfo`] contains the algorithm's
    /// root hash, activation/deactivation boundaries, and tree size.
    ///
    /// The serialization format is left to the implementor — TSML provides
    /// the raw data; the consumer chooses the wire encoding.
    pub fn algorithms(&self) -> Vec<AlgorithmInfo> {
        self.algs
            .keys()
            .map(|&id| {
                // Safe: id is from self.algs, so root/tree_size/etc. cannot fail.
                let root = self.root(id).expect("registered algorithm");
                let ts = self.tree_size(id).expect("registered algorithm");
                let activation_index = self.activation_index(id).expect("registered algorithm");
                let deactivation_index = self.deactivation_index(id).expect("registered algorithm");
                let epochs = self.epochs(id).expect("registered algorithm");
                AlgorithmInfo {
                    id,
                    root,
                    activation_index,
                    deactivation_index,
                    tree_size: ts,
                    epochs,
                }
            })
            .collect()
    }

    /// Returns the stack length for a specific algorithm (for testing invariants).
    #[cfg(test)]
    fn stack_len(&self, alg_id: u64) -> Option<usize> {
        self.algs.get(&alg_id).map(|s| s.stack.len())
    }

    /// Test accessor: compute subtree root over `[lo, hi)` for `alg_id`.
    ///
    /// Delegates to `subtree_root` (Definition 14c) without requiring
    /// callers to hold an `AlgState` reference.
    #[cfg(test)]
    pub(crate) fn test_subtree_root(&self, alg_id: u64, lo: u64, hi: u64) -> Result<Vec<u8>> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;
        self.subtree_root(state, alg_id, lo, hi)
    }

    // ========================================================================
    // Subtree root query (Definition 14c)
    // ========================================================================

    /// Compute the root hash of the subtree covering leaves `[lo, hi)` for
    /// algorithm `alg_id`.
    ///
    /// Definition 14c (Subtree root): dispatches through stored node lookups,
    /// NullTable for inactive ranges, and recursive binary splits for ranges
    /// not directly cached.
    ///
    /// This is the O(log n) mechanism that replaces projection-based proof
    /// generation.
    fn subtree_root(&self, state: &AlgState, alg_id: u64, lo: u64, hi: u64) -> Result<Vec<u8>> {
        let size = hi - lo;

        // Base cases.
        if size == 0 {
            return Ok(state.hasher.empty());
        }
        if size == 1 {
            // Single leaf: compute V(a, lo).
            if state.is_active_at(lo) {
                let data = self
                    .storage
                    .get_leaf(lo)
                    .map_err(|e| Error::Storage(Box::new(e)))?;
                return Ok(state.hasher.leaf(&data));
            } else {
                return Ok(state.null_table.leaf_null().to_vec());
            }
        }

        // Null range optimization: if no epoch overlaps [lo, hi), the entire
        // subtree is null-valued.
        if !state.active_range(lo, hi) {
            if size.is_power_of_two() {
                // Power-of-2 null range: direct NullTable lookup.
                let h = size.trailing_zeros() as usize;
                return Ok(state.null_table.get_precomputed(h).to_vec());
            } else {
                // Non-power-of-2 null range: decompose into power-of-2 subtrees.
                return self.null_range_root(state, size);
            }
        }

        // Stored node lookup: only valid for power-of-2 aligned ranges.
        if size.is_power_of_two() {
            let h = size.trailing_zeros() as usize;
            if let Some(hash) = self
                .storage
                .get_node(alg_id, lo, h)
                .map_err(|e| Error::Storage(Box::new(e)))?
            {
                return Ok(hash);
            }
        }

        // RFC 9162 binary split.
        let k = largest_pow2_lt_u64(size);
        let left = self.subtree_root(state, alg_id, lo, lo + k)?;
        let right = self.subtree_root(state, alg_id, lo + k, hi)?;
        Ok(state.hasher.node(&left, &right))
    }

    /// Compute the root of `size` consecutive null leaves for algorithm `a`.
    ///
    /// Definition 14d (Null range root): decomposes a non-power-of-2 null
    /// range into power-of-2 subtrees whose roots are NullTable lookups.
    /// Complexity: O(popcount(size)) hash operations.
    fn null_range_root(&self, state: &AlgState, size: u64) -> Result<Vec<u8>> {
        debug_assert!(size > 0, "null_range_root requires size > 0");

        if size == 1 {
            return Ok(state.null_table.leaf_null().to_vec());
        }

        // Decompose: largest power-of-2 subtree on the left, remainder on right.
        let k_bits = 63 - (size.leading_zeros() as u64);
        let k = 1u64 << k_bits;

        let left_root = state.null_table.get_precomputed(k_bits as usize).to_vec();

        let remainder = size - k;
        if remainder == 0 {
            return Ok(left_root);
        }

        let right_root = self.null_range_root(state, remainder)?;
        Ok(state.hasher.node(&left_root, &right_root))
    }

    // ========================================================================
    // Projection (Definition 14) — Specification Oracle
    // ========================================================================

    /// Compute the projected leaf hash sequence for an algorithm.
    ///
    /// Definition 14: for each global index `i` in `[0, tree_size(a))`,
    /// the projected leaf is `leaf(a, data[i])` if `active(a, i)`, else
    /// `N₀(a)` (the null leaf constant).
    ///
    /// **Oracle designation:** This is an O(n) specification oracle used
    /// exclusively by test code for equational law verification. Production
    /// proof generation uses `subtree_root` (Definition 14c).
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    #[cfg(test)]
    pub fn project(&self, alg_id: u64) -> Result<Vec<Vec<u8>>> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        let ts = state.tree_size(self.size());
        let mut leaves = Vec::with_capacity(ts as usize);
        for i in 0..ts {
            let leaf_hash = if state.is_active_at(i) {
                let data = self
                    .storage
                    .get_leaf(i)
                    .map_err(|e| Error::Storage(Box::new(e)))?;
                state.hasher.leaf(&data)
            } else {
                state.null_table.leaf_null().to_vec()
            };
            leaves.push(leaf_hash);
        }
        Ok(leaves)
    }

    // ========================================================================
    // Proof generation (Definitions 15-16 — Operational)
    // ========================================================================

    /// Generate an inclusion proof for leaf `index` under algorithm `alg_id`.
    ///
    /// Definition 15 (Inclusion proof — operational): uses range-based PATH
    /// algorithm with `subtree_root` for O(log n) sibling resolution.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::IndexOutOfBounds`] if `index >= tree_size(alg_id)`.
    pub fn inclusion_proof(&self, alg_id: u64, index: u64) -> Result<crate::proof::InclusionProof> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        let ts = state.tree_size(self.size());
        if ts == 0 || index >= ts {
            return Err(Error::IndexOutOfBounds {
                index,
                tree_size: ts,
            });
        }

        let path = self.path(state, alg_id, index, 0, ts)?;

        Ok(crate::proof::InclusionProof {
            index,
            tree_size: ts,
            path,
        })
    }

    /// RFC 9162 PATH algorithm (§2.1.3) using `subtree_root`.
    ///
    /// Recursively computes sibling hashes from leaf `m` within `[lo, hi)`.
    fn path(
        &self,
        state: &AlgState,
        alg_id: u64,
        m: u64,
        lo: u64,
        hi: u64,
    ) -> Result<Vec<Vec<u8>>> {
        let size = hi - lo;
        if size <= 1 {
            return Ok(Vec::new());
        }

        let k = largest_pow2_lt_u64(size);
        if m - lo < k {
            // Target is in the left subtree; right subtree is the sibling.
            let mut result = self.path(state, alg_id, m, lo, lo + k)?;
            result.push(self.subtree_root(state, alg_id, lo + k, hi)?);
            Ok(result)
        } else {
            // Target is in the right subtree; left subtree is the sibling.
            let mut result = self.path(state, alg_id, m, lo + k, hi)?;
            result.push(self.subtree_root(state, alg_id, lo, lo + k)?);
            Ok(result)
        }
    }

    /// Generate a consistency proof from `old_size` to the current tree
    /// for algorithm `alg_id`.
    ///
    /// Definition 16 (Consistency proof — operational): uses range-based
    /// SUBPROOF algorithm with `subtree_root` for O(log n) sibling resolution.
    ///
    /// # Errors
    ///
    /// Returns [`Error::UnknownAlgorithm`] if `alg_id` is not registered.
    /// Returns [`Error::IndexOutOfBounds`] if `old_size` is out of range.
    pub fn consistency_proof(
        &self,
        alg_id: u64,
        old_size: u64,
    ) -> Result<crate::proof::ConsistencyProof> {
        let state = self
            .algs
            .get(&alg_id)
            .ok_or(Error::UnknownAlgorithm(alg_id))?;

        let ts = state.tree_size(self.size());
        if old_size == 0 || old_size >= ts {
            return Err(Error::IndexOutOfBounds {
                index: old_size,
                tree_size: ts,
            });
        }

        let path = self.subproof(state, alg_id, old_size, 0, ts, true)?;

        Ok(crate::proof::ConsistencyProof {
            old_size,
            new_size: ts,
            path,
        })
    }

    /// RFC 9162 SUBPROOF algorithm (§2.1.4) using `subtree_root`.
    ///
    /// Recursively computes the intermediate hashes proving that the first
    /// `m` leaves (relative to `lo`) form a prefix of `[lo, hi)`.
    fn subproof(
        &self,
        state: &AlgState,
        alg_id: u64,
        m: u64,
        lo: u64,
        hi: u64,
        b: bool,
    ) -> Result<Vec<Vec<u8>>> {
        let size = hi - lo;
        if m == size {
            if b {
                return Ok(Vec::new());
            } else {
                return Ok(vec![self.subtree_root(state, alg_id, lo, hi)?]);
            }
        }

        let k = largest_pow2_lt_u64(size);
        if m <= k {
            let mut result = self.subproof(state, alg_id, m, lo, lo + k, b)?;
            result.push(self.subtree_root(state, alg_id, lo + k, hi)?);
            Ok(result)
        } else {
            let mut result = self.subproof(state, alg_id, m - k, lo + k, hi, false)?;
            result.push(self.subtree_root(state, alg_id, lo, lo + k)?);
            Ok(result)
        }
    }
}

impl Default for Log<crate::storage::MemoryStorage> {
    fn default() -> Self {
        Self::new(crate::storage::MemoryStorage::new())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;
    use sha2::{Digest, Sha256};

    /// SHA-256 implementation of the TSML Hasher trait.
    #[derive(Debug)]
    struct Sha256Hasher;

    impl Hasher for Sha256Hasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update([0x00]);
            h.update(data);
            h.finalize().to_vec()
        }

        fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update([0x01]);
            h.update(left);
            h.update(right);
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            Sha256::digest(b"").to_vec()
        }

        fn null(&self) -> Vec<u8> {
            Sha256::digest([0x02]).to_vec()
        }

        fn digest_len(&self) -> usize {
            32
        }
    }

    /// Second hasher for multi-algorithm tests (uses a different prefix to
    /// produce distinct outputs — simulates SHA-384 without importing it).
    #[derive(Debug)]
    struct AltHasher;

    impl Hasher for AltHasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update([0x00, 0xFF]); // extra byte distinguishes from Sha256Hasher
            h.update(data);
            h.finalize().to_vec()
        }

        fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update([0x01, 0xFF]);
            h.update(left);
            h.update(right);
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update([0xFF]);
            h.finalize().to_vec()
        }

        fn null(&self) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update([0x02, 0xFF]);
            h.finalize().to_vec()
        }

        fn digest_len(&self) -> usize {
            32
        }
    }

    /// Batch-compute the Merkle tree root via the canonical RFC 9162 mth.
    fn batch_root(hasher: &dyn Hasher, leaf_hashes: &[Vec<u8>]) -> Vec<u8> {
        crate::proof::mth(hasher, leaf_hashes)
    }

    // ---- A-EQUIV-TSML: incremental equals batch ----

    #[test]
    fn a_equiv_single_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..16u8 {
            log.append(&[i]).unwrap();

            let incremental = log.root(0).unwrap();
            let projected = log.project(0).unwrap();
            let batch = batch_root(&Sha256Hasher, &projected);
            assert_eq!(incremental, batch, "A-EQUIV-TSML failed at size {}", i + 1);
        }
    }

    #[test]
    fn a_equiv_mid_stream_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        // Append 4 leaves with only alg 0.
        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }

        // Add alg 1 mid-stream at index 4.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        // Append 4 more leaves with both algs active.
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }

        // Verify A-EQUIV for both algorithms.
        for alg_id in [0, 1] {
            let incremental = log.root(alg_id).unwrap();
            let projected = log.project(alg_id).unwrap();
            let hasher: &dyn Hasher = if alg_id == 0 {
                &Sha256Hasher
            } else {
                &AltHasher
            };
            let batch = batch_root(hasher, &projected);
            assert_eq!(incremental, batch, "A-EQUIV-TSML failed for alg {alg_id}");
        }
    }

    // ---- A-STACK-TSML: popcount invariant ----

    #[test]
    fn a_stack_popcount_invariant() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..20u8 {
            log.append(&[i]).unwrap();
            let expected = (log.size()).count_ones() as usize;
            assert_eq!(
                log.stack_len(0).unwrap(),
                expected,
                "A-STACK-TSML failed at size {}",
                log.size()
            );
        }
    }

    #[test]
    fn a_stack_frozen_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..6u8 {
            log.append(&[i]).unwrap();
        }

        // Freeze at size 6.
        log.remove_algorithm(0).unwrap();
        let frozen_stack_len = log.stack_len(0).unwrap();
        let expected = 6u64.count_ones() as usize; // popcount(6) = 2
        assert_eq!(frozen_stack_len, expected);

        // Further appends don't change the frozen stack.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();
        for i in 6..10u8 {
            log.append(&[i]).unwrap();
        }
        assert_eq!(log.stack_len(0).unwrap(), frozen_stack_len);
    }

    // ---- T-BOUND: temporal binding ----

    #[test]
    fn t_bound_null_prefix_differs_from_real_leaf() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        // Append 4 leaves.
        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }

        // Add alg 1 at index 4 — indices 0..4 are null for alg 1.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        // Append 4 more.
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }

        // The projected leaf at index 0 for alg 1 should be N₀, not leaf(data[0]).
        let state = log.algs.get(&1).unwrap();
        let null_leaf = state.null_table.leaf_null();
        let leaf0_data = log.storage.get_leaf(0).unwrap();
        let real_leaf = state.hasher.leaf(&leaf0_data);

        assert_ne!(
            null_leaf,
            real_leaf.as_slice(),
            "T-BOUND: null prefix position must differ from real leaf hash"
        );
    }

    // ---- ALG-IND: algorithm independence ----

    #[test]
    fn alg_ind_different_algorithms_different_roots() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..8u8 {
            log.append(&[i]).unwrap();
        }

        let root0 = log.root(0).unwrap();
        let root1 = log.root(1).unwrap();
        assert_ne!(
            root0, root1,
            "ALG-IND: different algorithms must produce different roots"
        );
    }

    // ---- Error cases ----

    #[test]
    fn error_duplicate_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        let err = log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap_err();
        assert_eq!(err, Error::DuplicateAlgorithm(0));
    }

    #[test]
    fn error_unknown_algorithm() {
        let log = Log::new(MemoryStorage::new());
        let err = log.root(99).unwrap_err();
        assert_eq!(err, Error::UnknownAlgorithm(99));
    }

    #[test]
    fn error_no_active_algorithms() {
        let mut log = Log::new(MemoryStorage::new());
        let err = log.append(b"data").unwrap_err();
        assert_eq!(err, Error::NoActiveAlgorithms);
    }

    #[test]
    fn error_double_freeze() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.append(b"data").unwrap();
        log.remove_algorithm(0).unwrap();
        let err = log.remove_algorithm(0).unwrap_err();
        assert_eq!(err, Error::FrozenAlgorithm(0));
    }

    // ---- Empty tree ----

    #[test]
    fn empty_tree_root() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        let root = log.root(0).unwrap();
        assert_eq!(root, Sha256Hasher.empty());
    }

    // ---- Frozen algorithm root stability ----

    #[test]
    fn frozen_root_is_stable() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..5u8 {
            log.append(&[i]).unwrap();
        }

        let root_before = log.root(0).unwrap();
        log.remove_algorithm(0).unwrap();
        let root_after = log.root(0).unwrap();

        assert_eq!(root_before, root_after, "root must not change on freeze");

        // Further appends to other algorithms don't change frozen root.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();
        for i in 5..10u8 {
            log.append(&[i]).unwrap();
        }
        let root_still = log.root(0).unwrap();
        assert_eq!(root_before, root_still, "frozen root must remain stable");
    }

    // ---- A-EQUIV-TSML for non-power-of-two sizes ----

    #[test]
    fn a_equiv_non_power_of_two() {
        // Test sizes that exercise the incomplete-tree fold path.
        for size in [1, 3, 5, 7, 9, 11, 13, 15, 17, 19] {
            let mut log = Log::new(MemoryStorage::new());
            log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

            for i in 0..size as u8 {
                log.append(&[i]).unwrap();
            }

            let incremental = log.root(0).unwrap();
            let projected = log.project(0).unwrap();
            let batch = batch_root(&Sha256Hasher, &projected);
            assert_eq!(incremental, batch, "A-EQUIV failed at size {size}");
        }
    }

    // ---- I-SOUND-TSML: inclusion proof soundness ----

    #[test]
    fn i_sound_single_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..12u8 {
            log.append(&[i]).unwrap();
        }

        let root = log.root(0).unwrap();
        let projected = log.project(0).unwrap();

        for idx in 0..12u64 {
            let proof = log.inclusion_proof(0, idx).unwrap();
            let leaf_hash = &projected[idx as usize];
            assert!(
                crate::proof::verify_inclusion(&Sha256Hasher, leaf_hash, &proof, &root),
                "I-SOUND-TSML failed at index {idx}"
            );
        }
    }

    #[test]
    fn i_sound_mid_stream_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }

        // Add alg 1 mid-stream.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 4..12u8 {
            log.append(&[i]).unwrap();
        }

        // Verify inclusion proofs for alg 1 (null prefix at 0..4, real at 4..12).
        let root = log.root(1).unwrap();
        let projected = log.project(1).unwrap();

        for idx in 0..12u64 {
            let proof = log.inclusion_proof(1, idx).unwrap();
            let leaf_hash = &projected[idx as usize];
            assert!(
                crate::proof::verify_inclusion(&AltHasher, leaf_hash, &proof, &root),
                "I-SOUND-TSML (mid-stream) failed at index {idx}"
            );
        }
    }

    // ---- K-SOUND-TSML: consistency proof soundness ----

    #[test]
    fn k_sound_single_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        // Build up to size 8, checking consistency at each step.
        let mut roots: Vec<Vec<u8>> = Vec::new();
        for i in 0..8u8 {
            log.append(&[i]).unwrap();
            roots.push(log.root(0).unwrap());
        }

        let current_root = log.root(0).unwrap();

        for old_size in 1..8u64 {
            let proof = log.consistency_proof(0, old_size).unwrap();
            let old_root = &roots[(old_size - 1) as usize];
            assert!(
                crate::proof::verify_consistency(&Sha256Hasher, &proof, old_root, &current_root),
                "K-SOUND-TSML failed for old_size={old_size}"
            );
        }
    }

    // ---- T-BOUND: proof-level temporal binding ----

    #[test]
    fn t_bound_inclusion_proof_at_null_position() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }

        // Add alg 1 at index 4 — indices 0..4 are null for alg 1.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }

        let root = log.root(1).unwrap();

        // Get the inclusion proof at a null-prefix position.
        let proof = log.inclusion_proof(1, 0).unwrap();

        // The proof DOES verify with the null leaf hash (this is correct —
        // the tree genuinely contains N₀ at position 0).
        let null_leaf = AltHasher.null();
        assert!(
            crate::proof::verify_inclusion(&AltHasher, &null_leaf, &proof, &root),
            "null leaf should verify at null position"
        );

        // But no real payload can produce a valid proof at that position.
        // T-BOUND: ∄ d. verify_inclusion(leaf(a, d), proof, root) = true
        for d in [b"any".as_slice(), b"data", b"", &[0], &[1], &[2], &[3]] {
            let forged_leaf = AltHasher.leaf(d);
            assert!(
                !crate::proof::verify_inclusion(&AltHasher, &forged_leaf, &proof, &root),
                "T-BOUND violated: real leaf verified at null position for data {:?}",
                d
            );
        }
    }

    // ---- Proof error cases ----

    #[test]
    fn inclusion_proof_out_of_bounds() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.append(b"data").unwrap();

        let err = log.inclusion_proof(0, 1).unwrap_err();
        assert_eq!(
            err,
            Error::IndexOutOfBounds {
                index: 1,
                tree_size: 1
            }
        );
    }

    #[test]
    fn consistency_proof_bounds() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }

        // old_size = 0 is invalid.
        let err = log.consistency_proof(0, 0).unwrap_err();
        assert_eq!(
            err,
            Error::IndexOutOfBounds {
                index: 0,
                tree_size: 4
            }
        );

        // old_size >= tree_size is invalid.
        let err = log.consistency_proof(0, 4).unwrap_err();
        assert_eq!(
            err,
            Error::IndexOutOfBounds {
                index: 4,
                tree_size: 4
            }
        );
    }

    // ---- TSML Manifest (Definition 13) ----

    #[test]
    fn algorithms_returns_manifest_data() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }

        // Add alg 1, then freeze alg 0.
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();
        log.remove_algorithm(0).unwrap();

        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }

        let infos = log.algorithms();
        assert_eq!(infos.len(), 2);

        // Alg 0: frozen at index 4, activated at 0.
        let a0 = infos.iter().find(|a| a.id == 0).unwrap();
        assert_eq!(a0.activation_index, 0);
        assert_eq!(a0.deactivation_index, Some(4));
        assert_eq!(a0.tree_size, 4);
        assert_eq!(a0.root, log.root(0).unwrap());

        // Alg 1: active, activated at 4.
        let a1 = infos.iter().find(|a| a.id == 1).unwrap();
        assert_eq!(a1.activation_index, 4);
        assert_eq!(a1.deactivation_index, None);
        assert_eq!(a1.tree_size, 8); // global tree size
        assert_eq!(a1.root, log.root(1).unwrap());
    }

    // ====================================================================
    // Reactivation tests
    // ====================================================================

    #[test]
    fn resume_basic_a_equiv() {
        // Add alg 0 at genesis, append 4, freeze, append 4 more, resume, append 4.
        // Alg 1 (keeper) stays active throughout to permit appends.
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        log.remove_algorithm(0).unwrap();
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();
        for i in 8..12u8 {
            log.append(&[i]).unwrap();
        }

        // A-EQUIV: incremental root must equal batch root.
        let root = log.root(0).unwrap();
        let projected = log.project(0).unwrap();

        let batch_root = crate::proof::mth(&Sha256Hasher, &projected);
        assert_eq!(root, batch_root, "A-EQUIV violated after resume");
    }

    #[test]
    fn resume_a_stack_invariant() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..3u8 {
            log.append(&[i]).unwrap();
        }
        log.remove_algorithm(0).unwrap();
        for i in 3..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();
        for i in 8..13u8 {
            log.append(&[i]).unwrap();
        }

        // A-STACK: stack length == popcount(tree_size)
        let ts = log.tree_size(0).unwrap();
        let expected_len = ts.count_ones() as usize;
        assert_eq!(
            log.stack_len(0).unwrap(),
            expected_len,
            "A-STACK violated after resume: tree_size={ts}"
        );
    }

    #[test]
    fn resume_error_active_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.append(b"a").unwrap();

        let err = log.resume_algorithm(0).unwrap_err();
        assert_eq!(err, Error::AlgorithmActive(0));
    }

    #[test]
    fn resume_error_unknown_algorithm() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        let err = log.resume_algorithm(99).unwrap_err();
        assert_eq!(err, Error::UnknownAlgorithm(99));
    }

    #[test]
    fn resume_inclusion_proof_soundness() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        // Epoch 1: leaves 0..4
        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        log.remove_algorithm(0).unwrap();

        // Gap: leaves 4..8 (null for alg 0)
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();

        // Epoch 2: leaves 8..12
        for i in 8..12u8 {
            log.append(&[i]).unwrap();
        }

        let root = log.root(0).unwrap();
        let projected = log.project(0).unwrap();

        // I-SOUND: proofs verify for all active positions.
        for &idx in &[0u64, 1, 2, 3, 8, 9, 10, 11] {
            let proof = log.inclusion_proof(0, idx).unwrap();
            assert!(
                crate::verify_inclusion(&Sha256Hasher, &projected[idx as usize], &proof, &root),
                "I-SOUND failed at active index {idx}"
            );
        }

        // Null positions (4..8) also produce valid proofs (over null leaf).
        for idx in 4..8u64 {
            let proof = log.inclusion_proof(0, idx).unwrap();
            assert!(
                crate::verify_inclusion(&Sha256Hasher, &projected[idx as usize], &proof, &root),
                "proof at null gap position {idx} failed"
            );
        }
    }

    #[test]
    fn resume_consistency_proof_soundness() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        let root_at_4 = log.root(0).unwrap();

        log.remove_algorithm(0).unwrap();
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();
        for i in 8..12u8 {
            log.append(&[i]).unwrap();
        }

        // K-SOUND: consistency from size 4 to current.
        let proof = log.consistency_proof(0, 4).unwrap();
        let root_now = log.root(0).unwrap();
        assert!(
            crate::verify_consistency(&Sha256Hasher, &proof, &root_at_4, &root_now),
            "K-SOUND failed after resume"
        );
    }

    #[test]
    fn resume_consistency_across_gap() {
        // Epoch 1: [0,4), gap: [4,8), epoch 2: [8,12).
        // Test consistency for EVERY old_size 1..12, including mid-gap positions.
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        log.remove_algorithm(0).unwrap();
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();
        for i in 8..12u8 {
            log.append(&[i]).unwrap();
        }

        let root_now = log.root(0).unwrap();
        let projected = log.project(0).unwrap();

        for old_size in 1..12u64 {
            let old_root = crate::proof::mth(&Sha256Hasher, &projected[..old_size as usize]);
            let proof = log.consistency_proof(0, old_size).unwrap();
            assert!(
                crate::verify_consistency(&Sha256Hasher, &proof, &old_root, &root_now),
                "K-SOUND across gap failed for old_size={old_size}"
            );
        }
    }

    #[test]
    fn resume_epochs_metadata() {
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        log.remove_algorithm(0).unwrap();
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();

        let epochs = log.epochs(0).unwrap();
        assert_eq!(epochs.len(), 2);
        assert_eq!(epochs[0], (0, Some(4)));
        assert_eq!(epochs[1], (8, None));

        assert_eq!(log.activation_index(0).unwrap(), 0);
        assert_eq!(log.deactivation_index(0).unwrap(), None); // currently active
    }

    #[test]
    fn resume_immediate_no_gap() {
        // Resume immediately after freeze (gap = 0).
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        let root_before = log.root(0).unwrap();
        log.remove_algorithm(0).unwrap();
        log.resume_algorithm(0).unwrap();

        // Root should be unchanged — zero-gap fast-forward is identity.
        let root_after = log.root(0).unwrap();
        assert_eq!(root_before, root_after, "zero-gap resume changed root");
    }

    #[test]
    fn resume_elide_multi_epoch() {
        // Build a scenario with a gap in the middle.
        // Epoch 1: [0, 4), gap: [4, 8), epoch 2: [8, 16).
        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(Sha256Hasher)).unwrap();
        log.add_algorithm(1, Box::new(AltHasher)).unwrap();

        for i in 0..4u8 {
            log.append(&[i]).unwrap();
        }
        log.remove_algorithm(0).unwrap();
        for i in 4..8u8 {
            log.append(&[i]).unwrap();
        }
        log.resume_algorithm(0).unwrap();
        for i in 8..16u8 {
            log.append(&[i]).unwrap();
        }

        let epochs = log.epochs(0).unwrap();
        let root = log.root(0).unwrap();

        // Proof for leaf in epoch 2 (index 10).
        let full_proof = log.inclusion_proof(0, 10).unwrap();
        let projected = log.project(0).unwrap();
        assert!(crate::verify_inclusion(
            &Sha256Hasher,
            &projected[10],
            &full_proof,
            &root
        ));

        let elided = crate::elide_inclusion_proof(&full_proof, &epochs);
        let rehydrated = crate::rehydrate_inclusion_proof(&elided, &Sha256Hasher);
        assert_eq!(rehydrated, full_proof, "multi-epoch elide roundtrip failed");
        assert!(crate::verify_inclusion(
            &Sha256Hasher,
            &projected[10],
            &rehydrated,
            &root
        ));
    }
}
