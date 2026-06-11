//! Inclusion and consistency proof structures and verification algorithms.
//!
//! # Security boundary: skeleton-pinned, prefix-chained
//!
//! An inclusion proof path runs leaf → root and splits into two regions:
//!
//! - The **log skeleton** — the trailing steps along the fixed-arity log spine.
//!   Their shape (count, per-step position and sibling count) is fully
//!   determined by `(index, tree_size, log_arity)` and is pinned exactly against
//!   [`crate::topology::inclusion_skeleton`]. Because there is no per-node domain
//!   separation, second-preimage safety rests entirely on this exactness: the
//!   verifier reconstructs the canonical topology and rejects any deviation.
//! - The **subtree prefix** — the leading steps below the leaf's log position,
//!   in application-defined (non-uniform) subtrees. These carry no topological
//!   claim and are verified by hash chaining alone.
//!
//! ## Canonical proof encoding
//!
//! Every accepted step hashes: it must carry at least one sibling. A zero-sibling
//! step would represent a *promoted* (singleton) node, whose parent equals its
//! child without any hashing — an inert no-op. Such steps are therefore rejected
//! everywhere ([`reconstruct_inclusion_root`]), and honest provers omit them
//! ([`crate::within_subtree_path`]). Omitting a promoted step never changes the
//! computed root, so completeness is preserved; in exchange, a fixed
//! `(leaf_hash, index, tree_size, root)` admits at most one accepting path
//! (modulo hash collisions), which closes prepend/insert malleability. This
//! concerns zero-*sibling* steps only; null-*valued* siblings from flat null
//! promotion are unaffected.

use crate::hasher::Hasher;
use crate::mr::nary_mr;

/// A single level in a Merkle proof path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// Sibling digests at this level (excluding the path node).
    /// Empty for promoted (singleton) nodes.
    pub siblings: Vec<Vec<u8>>,
    /// Position of the path node among all children (0-indexed).
    pub position: usize,
}

/// Inclusion proof: path from a leaf to the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InclusionProof {
    /// Path steps from leaf to root.
    pub path: Vec<ProofStep>,
}

/// Consistency proof: proves tree at `old_size` is a prefix of tree at `new_size`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistencyProof {
    /// Starting hash (representing the boundary node of the old tree).
    pub start_hash: Vec<u8>,
    /// Path steps from the boundary to the root.
    pub path: Vec<ProofStep>,
}

/// Timing-safe comparison of two byte slices.
#[inline]
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result = 0;
    for (&x, &y) in a.iter().zip(b.iter()) {
        result |= std::hint::black_box(x) ^ std::hint::black_box(y);
    }
    std::hint::black_box(result) == 0
}

/// Verify an inclusion proof.
///
/// Returns `true` if the proof demonstrates that `leaf_hash` is the leaf at
/// the given index in a tree of the given tree size with the given root.
#[must_use]
pub fn verify_inclusion(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
    root: &[u8],
) -> bool {
    reconstruct_inclusion_root(hasher, leaf_hash, index, tree_size, log_arity, path)
        .is_some_and(|computed| constant_time_eq(&computed, root))
}

use crate::topology::{frontier_for_size, inclusion_skeleton};

/// Verify a consistency proof.
///
/// Proves that the tree of size `old_size` with `old_root` is an append-only
/// prefix of the tree of size `new_size` with `new_root`.
#[must_use]
pub fn verify_consistency(
    hasher: &dyn Hasher,
    old_size: u64,
    new_size: u64,
    log_arity: u64,
    start_hash: &[u8],
    path: &[ProofStep],
    old_root: &[u8],
    new_root: &[u8],
) -> bool {
    reconstruct_consistency_roots(hasher, old_size, new_size, log_arity, start_hash, path).is_some_and(|(computed_old, computed_new)| {
        constant_time_eq(&computed_old, old_root) & constant_time_eq(&computed_new, new_root)
    })
}

// ============================================================================
// Committed epoch timeline (Design A+)
// ============================================================================
//
// The combined root is a metaroot: an extra structural layer that, like any
// node, commits what is below it — except it spans every algorithm's tree.
// Under Design A+ its preimage also covers the per-algorithm epoch timeline
// `(activation, deactivation)` as it stood at that size, because the timeline
// is part of the multi-algorithm structure (it decides which cells are null
// projections). Activity at a position is read from this committed field —
// never inferred from a digest equaling the null constant — which renders the
// `leaf(b"null") == null()` collision inert without forbidding any payload.

/// Canonical preimage of the combined root (the metaroot).
///
/// Layout (all integers `u64` big-endian; fixed-width counts and lengths make
/// the encoding unambiguous to parse and therefore injective):
///
/// ```text
/// n_active ‖ [ id ‖ root_len ‖ root ]*
/// n_algs   ‖ [ id ‖ n_epochs ‖ (start ‖ end)* ]*
/// ```
///
/// `active_roots` lists the raw roots of algorithms active at the tree size;
/// `alg_epochs` lists the committed epoch timeline of every registered
/// algorithm (active and frozen). An epoch open at that size is encoded with
/// `end == u64::MAX`.
#[must_use]
pub fn combined_root_preimage(
    active_roots: &[(u64, Vec<u8>)],
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&(active_roots.len() as u64).to_be_bytes());
    for (id, r) in active_roots {
        buf.extend_from_slice(&id.to_be_bytes());
        buf.extend_from_slice(&(r.len() as u64).to_be_bytes());
        buf.extend_from_slice(r);
    }
    buf.extend_from_slice(&(alg_epochs.len() as u64).to_be_bytes());
    for (id, epochs) in alg_epochs {
        buf.extend_from_slice(&id.to_be_bytes());
        buf.extend_from_slice(&(epochs.len() as u64).to_be_bytes());
        for &(start, end) in epochs {
            buf.extend_from_slice(&start.to_be_bytes());
            buf.extend_from_slice(&end.to_be_bytes());
        }
    }
    buf
}

/// Validate the structural well-formedness of a committed epoch timeline at
/// `tree_size`: entries strictly sorted by algorithm ID; at least one epoch
/// per algorithm; intervals ordered and non-overlapping (`start <= end`,
/// `start >= prior end`); only the final interval may be open
/// (`end == u64::MAX`); closed ends and open starts do not exceed `tree_size`.
#[must_use]
pub fn validate_committed_epochs(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    tree_size: u64,
) -> bool {
    if alg_epochs.windows(2).any(|w| w[0].0 >= w[1].0) {
        return false;
    }
    for (_, epochs) in alg_epochs {
        if epochs.is_empty() {
            return false;
        }
        let mut last_end = 0u64;
        for (i, &(start, end)) in epochs.iter().enumerate() {
            if start > end || start < last_end {
                return false;
            }
            if end == u64::MAX {
                if i != epochs.len() - 1 || start > tree_size {
                    return false;
                }
            } else if end > tree_size {
                return false;
            }
            last_end = end;
        }
    }
    true
}

/// Read the authenticated activity of `alg_id` at position `index` from a
/// committed epoch timeline. Returns `None` if the algorithm has no committed
/// timeline.
#[must_use]
pub fn committed_active_at(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    alg_id: u64,
    index: u64,
) -> Option<bool> {
    let idx = alg_epochs
        .binary_search_by_key(&alg_id, |&(id, _)| id)
        .ok()?;
    Some(
        alg_epochs[idx]
            .1
            .iter()
            .any(|&(start, end)| start <= index && index < end),
    )
}

/// Whether `alg_id` is live (final epoch still open) at the snapshot this
/// timeline was committed at. Returns `None` if the algorithm has no
/// committed timeline.
///
/// This answers the frontier-freshness query "is this key live right now?",
/// which is not derivable from the tree alone: a deactivation at the idle log
/// tip leaves no later positions to witness it.
#[must_use]
pub fn committed_is_live(alg_epochs: &[(u64, Vec<(u64, u64)>)], alg_id: u64) -> Option<bool> {
    let idx = alg_epochs
        .binary_search_by_key(&alg_id, |&(id, _)| id)
        .ok()?;
    Some(
        alg_epochs[idx]
            .1
            .last()
            .is_some_and(|&(_, end)| end == u64::MAX),
    )
}

/// Derive the active algorithm set at `tree_size` from a committed timeline:
/// the algorithms whose epochs cover the final position `tree_size - 1`.
/// Returned sorted by algorithm ID (inherited from the timeline ordering).
#[must_use]
pub fn committed_active_algs(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    tree_size: u64,
) -> Vec<u64> {
    if tree_size == 0 {
        return Vec::new();
    }
    let last = tree_size - 1;
    alg_epochs
        .iter()
        .filter(|(_, epochs)| epochs.iter().any(|&(start, end)| start <= last && last < end))
        .map(|&(id, _)| id)
        .collect()
}

/// Verify that a committed epoch timeline at `new_size` is an append-only
/// evolution of one previously committed at `old_size` — the temporal analog
/// of a consistency proof.
///
/// Allowed transitions per algorithm: the old intervals are preserved
/// verbatim, except that an interval open at the old snapshot may since have
/// closed at or after `old_size`; additional intervals and newly registered
/// algorithms may only begin at or after `old_size`; algorithms never
/// disappear. Both timelines must be well-formed at their respective sizes.
#[must_use]
pub fn verify_epoch_evolution(
    old_epochs: &[(u64, Vec<(u64, u64)>)],
    old_size: u64,
    new_epochs: &[(u64, Vec<(u64, u64)>)],
    new_size: u64,
) -> bool {
    if old_size > new_size {
        return false;
    }
    if !validate_committed_epochs(old_epochs, old_size)
        || !validate_committed_epochs(new_epochs, new_size)
    {
        return false;
    }
    let lookup = |timeline: &[(u64, Vec<(u64, u64)>)], id: u64| {
        timeline
            .binary_search_by_key(&id, |&(tid, _)| tid)
            .ok()
            .map(|i| timeline[i].1.clone())
    };
    for (id, old) in old_epochs {
        let Some(new) = lookup(new_epochs, *id) else {
            return false;
        };
        if new.len() < old.len() {
            return false;
        }
        let last = old.len() - 1;
        if new[..last] != old[..last] {
            return false;
        }
        let (o_start, o_end) = old[last];
        let (n_start, n_end) = new[last];
        if n_start != o_start {
            return false;
        }
        if o_end == u64::MAX {
            // Open at the old snapshot: may remain open, or close at/after it.
            if n_end != u64::MAX && n_end < old_size {
                return false;
            }
        } else if n_end != o_end {
            return false;
        }
        if new[old.len()..].iter().any(|&(start, _)| start < old_size) {
            return false;
        }
    }
    for (id, new) in new_epochs {
        if lookup(old_epochs, *id).is_none()
            && new.first().is_some_and(|&(start, _)| start < old_size)
        {
            return false;
        }
    }
    true
}

/// Configuration options for proof verification (local node policy).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifierConfig {
    /// Maximum number of active algorithms allowed (DoS mitigation).
    pub max_active_algorithms: usize,
    /// Maximum number of algorithms (active and frozen) in a committed epoch
    /// timeline (DoS mitigation).
    pub max_algorithms: usize,
    /// Maximum number of epoch intervals per algorithm (DoS mitigation).
    pub max_epochs_per_algorithm: usize,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self {
            max_active_algorithms: 8,
            max_algorithms: 64,
            max_epochs_per_algorithm: 1024,
        }
    }
}

/// A coupling proof that opens a combined root (metaroot) to its children:
/// the raw algorithm roots together with the committed epoch timeline. This
/// is the metadata-opening segment of inclusion/inactivity proofs: once
/// authenticated against the combined root, `alg_epochs` is the trusted
/// source for `active(X, p)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CouplingProof {
    /// The active roots at this tree size: (alg_id, raw_root_hash)
    pub active_roots: Vec<(u64, Vec<u8>)>,
    /// The committed epoch timeline at this tree size: `(alg_id, epochs)` for
    /// every registered algorithm (active and frozen), sorted by algorithm
    /// ID. Authenticated against the combined root together with the roots.
    pub alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

impl CouplingProof {
    /// Authenticate the proof against a combined root at `tree_size`.
    ///
    /// Validates structure (canonical ordering, bounds, well-formed epochs,
    /// active set consistent with the timeline) and reconstructs the
    /// combined-root preimage via [`combined_root_preimage`]. On success both
    /// `active_roots` and `alg_epochs` are authenticated by the root.
    #[must_use]
    pub fn authenticate(
        &self,
        hasher: &dyn Hasher,
        tree_size: u64,
        combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> bool {
        // Nothing is committed at size zero.
        if tree_size == 0 {
            return false;
        }

        // DoS Mitigation: assert counts do not exceed configuration limits
        // before allocating.
        if self.active_roots.len() > config.max_active_algorithms {
            return false;
        }
        if self.alg_epochs.len() > config.max_algorithms {
            return false;
        }
        if self
            .alg_epochs
            .iter()
            .any(|(_, e)| e.len() > config.max_epochs_per_algorithm)
        {
            return false;
        }

        // Validate active roots match expected active algorithms exactly to prevent
        // type-confusion/bypass
        if self.active_roots.len() != expected_active_algs.len() {
            return false;
        }
        for ((id, _), &expected_id) in self.active_roots.iter().zip(expected_active_algs.iter()) {
            if *id != expected_id {
                return false;
            }
        }

        // DoS Mitigation: assert individual companion root sizes are within bounds
        for (_, r) in &self.active_roots {
            if r.len() > 64 {
                return false;
            }
        }

        // Ensure the active roots list is canonically sorted by algorithm ID (prover requirement)
        // to prevent duplicate representation vectors or sorting malleability.
        if self.active_roots.windows(2).any(|w| w[0].0 >= w[1].0) {
            return false;
        }

        // The committed timeline must be well-formed and must imply exactly
        // the claimed active set: an algorithm cannot present a root without
        // a covering epoch, nor claim an epoch covering the tip without a
        // root.
        if !validate_committed_epochs(&self.alg_epochs, tree_size) {
            return false;
        }
        let derived = committed_active_algs(&self.alg_epochs, tree_size);
        if derived.len() != self.active_roots.len()
            || derived
                .iter()
                .zip(self.active_roots.iter())
                .any(|(&d, &(id, _))| d != id)
        {
            return false;
        }

        // Reconstruct the combined root mirroring the genesis-promotion rule
        // in combined_root_at: a registry-singleton with the forced default
        // timeline [(0, MAX)] means the combined root IS the raw root of that
        // algorithm (promoted form); otherwise hash the canonical preimage.
        let is_promoted =
            self.alg_epochs.len() == 1 && self.alg_epochs[0].1 == vec![(0u64, u64::MAX)];
        if is_promoted {
            constant_time_eq(&self.active_roots[0].1, combined_root)
        } else {
            let computed =
                hasher.hash(&combined_root_preimage(&self.active_roots, &self.alg_epochs));
            constant_time_eq(&computed, combined_root)
        }
    }

    /// Verify the coupling proof against a combined root for a given target algorithm.
    /// Returns the verified raw root hash for the target algorithm if successful.
    #[must_use]
    pub fn verify(
        &self,
        hasher: &dyn Hasher,
        target_alg_id: u64,
        tree_size: u64,
        combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> Option<Vec<u8>> {
        if !self.authenticate(hasher, tree_size, combined_root, expected_active_algs, config) {
            return None;
        }

        // Extract the target algorithm's root
        self.active_roots
            .iter()
            .find(|&&(id, _)| id == target_alg_id)
            .map(|(_, r)| r.clone())
    }
}

/// Validate that the trailing steps of an inclusion proof path match the
/// log-spine skeleton pinned by `(index, tree_size, k)`.
///
/// The skeleton — its length and, per step, the path node's position and sibling
/// count — is derived once by [`inclusion_skeleton`], the single authority on log
/// topology shared with proof generation. The trailing `skeleton.len()` steps are
/// checked field-by-field against it; the leading `path.len() - skeleton.len()`
/// steps are the subtree portion and carry no topological claim here (they are
/// verified by hash chaining in [`reconstruct_inclusion_root`]).
#[must_use]
pub fn verify_inclusion_path_structure(
    k: usize,
    index: u64,
    tree_size: u64,
    path: &[ProofStep],
) -> bool {
    let skeleton = match inclusion_skeleton(k as u64, tree_size, index) {
        Some(s) => s,
        None => return false,
    };
    if path.len() < skeleton.len() {
        return false;
    }
    let d = path.len() - skeleton.len();
    path[d..]
        .iter()
        .zip(skeleton.iter())
        .all(|(step, shape)| {
            step.position == shape.position && step.siblings.len() == shape.sibling_count
        })
}

/// Reconstruct the raw root from an inclusion proof path.
#[must_use]
pub fn reconstruct_inclusion_root(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
) -> Option<Vec<u8>> {
    let digest_len = hasher.empty().len();
    if digest_len == 0 || digest_len > 64 {
        return None;
    }
    if leaf_hash.len() != digest_len {
        return None;
    }
    if log_arity < 2 || log_arity > 256 {
        return None;
    }
    if tree_size == 0 {
        return None;
    }
    if index >= tree_size {
        return None;
    }
    if path.len() > 256 {
        return None;
    }

    if !verify_inclusion_path_structure(
        log_arity as usize,
        index,
        tree_size,
        path,
    ) {
        return None;
    }

    let mut current = leaf_hash.to_vec();

    for step in path {
        if step.siblings.len() > 256 {
            return None;
        }
        for sib in &step.siblings {
            if sib.len() != digest_len {
                return None;
            }
        }
        if step.siblings.is_empty() {
            // Canonical proof encoding: a zero-sibling step would be a promoted
            // (singleton) node, whose parent equals the child without hashing.
            // Such steps are inert no-ops, so honest provers omit them; rejecting
            // them here makes the accepting path unique for a fixed
            // (leaf_hash, index, tree_size, root). See the module docs.
            return None;
        }
        if step.position > step.siblings.len() {
            return None;
        }

        // Reconstruct the parent: insert current at position among siblings
        let mut children = Vec::with_capacity(step.siblings.len() + 1);
        for (i, sib) in step.siblings.iter().enumerate() {
            if i == step.position {
                children.push(current.as_slice());
            }
            children.push(sib.as_slice());
        }
        if step.position == step.siblings.len() {
            children.push(current.as_slice());
        }

        current = nary_mr(hasher, &children);
    }

    Some(current)
}

/// Reconstruct the old and new raw roots from a consistency proof path.
#[must_use]
pub fn reconstruct_consistency_roots(
    hasher: &dyn Hasher,
    old_size: u64,
    new_size: u64,
    log_arity: u64,
    start_hash: &[u8],
    path: &[ProofStep],
) -> Option<(Vec<u8>, Vec<u8>)> {
    let digest_len = hasher.empty().len();
    if digest_len == 0 || digest_len > 64 {
        return None;
    }
    if start_hash.len() != digest_len {
        return None;
    }
    if old_size == 0 || old_size >= new_size {
        return None;
    }
    if log_arity < 2 || log_arity > 256 {
        return None;
    }
    if path.len() > 256 {
        return None;
    }
    for step in path {
        if step.siblings.len() > 256 {
            return None;
        }
        for sib in &step.siblings {
            if sib.len() != digest_len {
                return None;
            }
        }
    }

    let k = log_arity;

    let old_coords = frontier_for_size(old_size, k);
    let new_coords = frontier_for_size(new_size, k);

    let &(boundary_left, boundary_height) = old_coords.last()?;

    let mut target_new_f_idx = None;
    for (f_idx, &(new_left, new_height)) in new_coords.iter().enumerate() {
        let cap = k.checked_pow(new_height)?;
        let limit = new_left.checked_add(cap)?;
        if boundary_left >= new_left && boundary_left < limit {
            target_new_f_idx = Some((f_idx, new_left, new_height));
            break;
        }
    }

    let (f_idx, _new_left, new_height) = target_new_f_idx?;

    if new_height < boundary_height {
        return None;
    }

    // We will populate a map from coordinate (left, height) to its hash
    use std::collections::HashMap;
    let mut map = HashMap::new();
    map.insert((boundary_left, boundary_height), start_hash.to_vec());

    let bisection_steps = (new_height - boundary_height) as usize;
    if path.len() < bisection_steps {
        return None;
    }

    // 1. Trace the bisection steps (first bisection_steps of path)
    let mut curr_left = boundary_left;
    let mut curr_height = boundary_height;
    for i in 0..bisection_steps {
        let step = &path[i];
        // Log-level nodes are never promoted (arity >= 2). Skip empty siblings checks.
        if step.siblings.len() != (k - 1) as usize {
            return None;
        }
        if step.position > step.siblings.len() {
            return None;
        }

        let child_capacity = k.checked_pow(curr_height)?;
        let parent_offset = (step.position as u64).checked_mul(child_capacity)?;
        let parent_left = curr_left.checked_sub(parent_offset)?;
        let parent_height = curr_height + 1;

        let current_hash = map.get(&(curr_left, curr_height))?.clone();

        // Reconstruct children
        let mut children = Vec::with_capacity(step.siblings.len() + 1);
        for (j, sib) in step.siblings.iter().enumerate() {
            let j_u64 = j as u64;
            let offset = j_u64.checked_mul(child_capacity)?;
            let c_left = if j_u64 < step.position as u64 {
                parent_left.checked_add(offset)?
            } else {
                let next_offset = offset.checked_add(child_capacity)?;
                parent_left.checked_add(next_offset)?
            };
            map.insert((c_left, curr_height), sib.clone());

            if j == step.position {
                children.push(current_hash.as_slice());
            }
            children.push(sib.as_slice());
        }
        if step.position == step.siblings.len() {
            children.push(current_hash.as_slice());
        }

        let parent_hash = nary_mr(hasher, &children);
        map.insert((parent_left, parent_height), parent_hash);

        curr_left = parent_left;
        curr_height = parent_height;
    }

    // 2. Trace the dynamic merge steps
    #[derive(Debug, Clone)]
    struct FrontierNode {
        left: u64,
        height: u32,
        hash: Option<Vec<u8>>,
    }

    let mut current_frontier: Vec<FrontierNode> = new_coords
        .iter()
        .enumerate()
        .map(|(idx, &(l, h))| {
            let hash = if idx == f_idx {
                map.get(&(l, h)).cloned()
            } else {
                None
            };
            FrontierNode {
                left: l,
                height: h,
                hash,
            }
        })
        .collect();

    let mut target_idx = f_idx;
    let mut proof_idx = bisection_steps;

    let k_usize = k as usize;
    while current_frontier.len() > k_usize {
        let split_idx = current_frontier.len() - k_usize;
        let is_target_merged = target_idx >= split_idx;

        if is_target_merged {
            if proof_idx >= path.len() {
                return None;
            }
            let step = &path[proof_idx];
            proof_idx += 1;

            if step.position != target_idx - split_idx || step.siblings.len() != k_usize - 1 {
                return None;
            }

            let mut children_hashes = Vec::with_capacity(k_usize);
            for j in 0..k_usize {
                let node_idx = split_idx + j;
                let hash = if node_idx == target_idx {
                    current_frontier[node_idx].hash.as_ref()?.clone()
                } else {
                    let sib_idx = if j < step.position { j } else { j - 1 };
                    let sib_hash = step.siblings[sib_idx].clone();
                    map.insert(
                        (
                            current_frontier[node_idx].left,
                            current_frontier[node_idx].height,
                        ),
                        sib_hash.clone(),
                    );
                    sib_hash
                };
                children_hashes.push(hash);
            }

            let refs: Vec<&[u8]> = children_hashes.iter().map(|v| v.as_slice()).collect();
            let parent_hash = nary_mr(hasher, &refs);

            let parent_left = current_frontier[split_idx].left;
            let parent_height = current_frontier[split_idx].height + 1;
            map.insert((parent_left, parent_height), parent_hash.clone());

            current_frontier.truncate(split_idx);
            current_frontier.push(FrontierNode {
                left: parent_left,
                height: parent_height,
                hash: Some(parent_hash),
            });
            target_idx = split_idx;
        } else {
            // Target is not merged, so we simulate the coordinate merge without consuming a proof
            // step
            let parent_left = current_frontier[split_idx].left;
            let parent_height = current_frontier[split_idx].height + 1;

            current_frontier.truncate(split_idx);
            current_frontier.push(FrontierNode {
                left: parent_left,
                height: parent_height,
                hash: None,
            });
        }
    }

    if current_frontier.len() > 1 {
        // Final root merge
        if proof_idx >= path.len() {
            return None;
        }
        let step = &path[proof_idx];
        proof_idx += 1;

        if step.position != target_idx || step.siblings.len() != current_frontier.len() - 1 {
            return None;
        }

        let mut children_hashes = Vec::with_capacity(current_frontier.len());
        for (j, node) in current_frontier.iter().enumerate() {
            let hash = if j == target_idx {
                node.hash.as_ref()?.clone()
            } else {
                let sib_idx = if j < step.position { j } else { j - 1 };
                let sib_hash = step.siblings[sib_idx].clone();
                map.insert((node.left, node.height), sib_hash.clone());
                sib_hash
            };
            children_hashes.push(hash);
        }

        let refs: Vec<&[u8]> = children_hashes.iter().map(|v| v.as_slice()).collect();
        let parent_hash = nary_mr(hasher, &refs);

        current_frontier = vec![FrontierNode {
            left: 0,
            height: 9999,
            hash: Some(parent_hash),
        }];
    }

    if proof_idx != path.len() {
        return None;
    }

    // 3. Reconstruct old root
    let mut old_hashes = Vec::with_capacity(old_coords.len());
    for coord in &old_coords {
        let hash = map.get(coord)?.clone();
        old_hashes.push(hash);
    }

    let computed_old_root = {
        if old_hashes.is_empty() {
            hasher.empty()
        } else if old_hashes.len() == 1 {
            old_hashes[0].clone()
        } else {
            let mut current = old_hashes;
            while current.len() > k_usize {
                let split_idx = current.len() - k_usize;
                let right_elements = &current[split_idx..];
                let refs: Vec<&[u8]> = right_elements.iter().map(|v| v.as_slice()).collect();
                let merged = nary_mr(hasher, &refs);
                current.truncate(split_idx);
                current.push(merged);
            }
            let refs: Vec<&[u8]> = current.iter().map(|v| v.as_slice()).collect();
            nary_mr(hasher, &refs)
        }
    };

    // 4. Reconstruct new root
    let computed_new_root = current_frontier[0].hash.as_ref()?.clone();

    Some((computed_old_root, computed_new_root))
}

/// Helper wrapper demonstrating inclusion verification with decoupled coupling proofs.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_inclusion_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
    coupling: &CouplingProof,
    combined_root: &[u8],
    expected_active_algs: &[u64],
    config: VerifierConfig,
) -> bool {
    let raw_root = match coupling.verify(
        hasher,
        alg_id,
        tree_size,
        combined_root,
        expected_active_algs,
        config,
    ) {
        Some(r) => r,
        None => return false,
    };

    // One-directional inactive⇒N₀ check: if the committed timeline marks
    // this position INACTIVE for alg_id, the leaf hash must equal the null
    // constant.  Active positions are unconstrained — a legitimate payload
    // `b"null"` hashes to null() but is never forbidden.  `None` (algorithm
    // not in the timeline at all) is rejected as an ill-formed proof.
    match committed_active_at(&coupling.alg_epochs, alg_id, index) {
        Some(false) => {
            if !constant_time_eq(leaf_hash, &hasher.null()) {
                return false;
            }
        },
        Some(true) => {},
        None => return false,
    }

    verify_inclusion(hasher, leaf_hash, index, tree_size, log_arity, path, &raw_root)
}

/// Verify an inactivity claim for a leaf at `index` using a coupling proof.
///
/// Succeeds iff:
/// - `index < tree_size`
/// - The coupling proof authenticates against `combined_root`.
/// - The committed timeline marks `alg_id` **inactive** at `index`.
/// - If `alg_id` has a committed root (it appears in `coupling.active_roots`),
///   an inclusion proof for the null constant at `index` verifies against that
///   root.  The caller must provide the matching Merkle path.
/// - If `alg_id` is frozen at `tree_size` (no committed root), `path` must be
///   empty — the committed timeline alone is sufficient evidence.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_inactivity_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
    coupling: &CouplingProof,
    combined_root: &[u8],
    expected_active_algs: &[u64],
    config: VerifierConfig,
) -> bool {
    if index >= tree_size {
        return false;
    }

    if !coupling.authenticate(hasher, tree_size, combined_root, expected_active_algs, config) {
        return false;
    }

    // Position must be committed-inactive for this algorithm.
    match committed_active_at(&coupling.alg_epochs, alg_id, index) {
        Some(false) => {},
        _ => return false,
    }

    // If alg_id has an active committed root, open it with a null-leaf
    // inclusion proof.  If it is frozen (not in active_roots), the timeline
    // commitment alone is the evidence and the path must be empty.
    if let Some((_, raw_root)) =
        coupling.active_roots.iter().find(|&&(id, _)| id == alg_id)
    {
        verify_inclusion(hasher, &hasher.null(), index, tree_size, log_arity, path, raw_root)
    } else {
        path.is_empty()
    }
}

/// Helper wrapper demonstrating consistency verification with decoupled coupling proofs.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_consistency_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    old_size: u64,
    new_size: u64,
    log_arity: u64,
    start_hash: &[u8],
    path: &[ProofStep],
    old_coupling: &CouplingProof,
    new_coupling: &CouplingProof,
    old_combined_root: &[u8],
    new_combined_root: &[u8],
    old_expected_active_algs: &[u64],
    new_expected_active_algs: &[u64],
    config: VerifierConfig,
) -> bool {
    let old_res = old_coupling.verify(
        hasher,
        alg_id,
        old_size,
        old_combined_root,
        old_expected_active_algs,
        config,
    );
    let new_res = new_coupling.verify(
        hasher,
        alg_id,
        new_size,
        new_combined_root,
        new_expected_active_algs,
        config,
    );

    match (old_res, new_res) {
        (Some(old_raw_root), Some(new_raw_root)) => {
            verify_consistency(
                hasher,
                old_size,
                new_size,
                log_arity,
                start_hash,
                path,
                &old_raw_root,
                &new_raw_root,
            )
        },
        _ => false,
    }
}

/// The raw payload of an audit verification checkpoint.
///
/// This is the Coz `pay` field — Cyphr signs this struct over a Coz
/// envelope to produce a checkpoint attestation; NEML does not implement
/// signing or consensus (NEML↔Cyphr boundary).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditPayload {
    /// Identifier of the log being audited.
    pub log_id: [u8; 32],
    /// The tree size that was verified.
    pub tree_size: u64,
    /// The list of active algorithm IDs at this checkpoint size.
    pub active_algs: Vec<u64>,
    /// The Combined Roots of the log at `tree_size` for each active algorithm.
    pub combined_roots: Vec<(u64, Vec<u8>)>,
    /// Committed epoch timeline at `tree_size`: `(alg_id, epochs)` for every
    /// registered algorithm (active and frozen), sorted by algorithm ID.
    /// Same value as `committed_epochs_at(tree_size)`.  Binding the timeline
    /// into the payload lets the signing attestation cover activation/
    /// deactivation boundaries, making activity claims non-equivocable.
    pub alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX: u64 = u64::MAX;

    #[test]
    fn test_combined_root_preimage_injective_sections() {
        // Moving an interval between algorithms or shifting a boundary must
        // change the encoding.
        let roots = vec![(0u64, vec![0xAA; 32])];
        let a = combined_root_preimage(&roots, &[(0, vec![(0, MAX)])]);
        let b = combined_root_preimage(&roots, &[(0, vec![(1, MAX)])]);
        let c = combined_root_preimage(&roots, &[(0, vec![(0, 5)])]);
        let d = combined_root_preimage(&roots, &[(0, vec![(0, 5), (7, MAX)])]);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(c, d);
        // Empty epoch section differs from empty active section swap.
        let e = combined_root_preimage(&[], &[(0, vec![(0, MAX)])]);
        let f = combined_root_preimage(&roots, &[]);
        assert_ne!(e, f);
    }

    #[test]
    fn test_validate_committed_epochs() {
        // Well-formed: closed, open, gap + resume.
        assert!(validate_committed_epochs(&[(0, vec![(0, MAX)])], 10));
        assert!(validate_committed_epochs(&[(0, vec![(0, 5)])], 10));
        assert!(validate_committed_epochs(
            &[(0, vec![(0, 3), (5, MAX)]), (1, vec![(2, 2)])],
            10
        ));
        // Resume at the deactivation boundary is legal.
        assert!(validate_committed_epochs(&[(0, vec![(0, 5), (5, MAX)])], 10));

        // Unsorted / duplicate algorithm IDs.
        assert!(!validate_committed_epochs(
            &[(1, vec![(0, MAX)]), (0, vec![(0, MAX)])],
            10
        ));
        assert!(!validate_committed_epochs(
            &[(0, vec![(0, MAX)]), (0, vec![(0, MAX)])],
            10
        ));
        // Empty timeline.
        assert!(!validate_committed_epochs(&[(0, vec![])], 10));
        // Overlap / disorder.
        assert!(!validate_committed_epochs(&[(0, vec![(0, 5), (4, MAX)])], 10));
        assert!(!validate_committed_epochs(&[(0, vec![(5, 3)])], 10));
        // Open epoch not last.
        assert!(!validate_committed_epochs(
            &[(0, vec![(0, MAX), (1, 2)])],
            10
        ));
        // Bounds beyond the snapshot size.
        assert!(!validate_committed_epochs(&[(0, vec![(0, 11)])], 10));
        assert!(!validate_committed_epochs(&[(0, vec![(11, MAX)])], 10));
        // Closed exactly at the snapshot size is legal (frontier deactivation).
        assert!(validate_committed_epochs(&[(0, vec![(0, 10)])], 10));
    }

    #[test]
    fn test_committed_activity_reads() {
        let timeline = vec![(0u64, vec![(0u64, 3u64), (5, MAX)]), (1, vec![(0, 10)])];
        assert_eq!(committed_active_at(&timeline, 0, 2), Some(true));
        assert_eq!(committed_active_at(&timeline, 0, 3), Some(false));
        assert_eq!(committed_active_at(&timeline, 0, 4), Some(false));
        assert_eq!(committed_active_at(&timeline, 0, 5), Some(true));
        assert_eq!(committed_active_at(&timeline, 1, 9), Some(true));
        assert_eq!(committed_active_at(&timeline, 2, 0), None);

        assert_eq!(committed_is_live(&timeline, 0), Some(true));
        assert_eq!(committed_is_live(&timeline, 1), Some(false));
        assert_eq!(committed_is_live(&timeline, 2), None);

        // Alg 1's epoch closes exactly at 10, so it still covers position 9.
        assert_eq!(committed_active_algs(&timeline, 10), vec![0, 1]);
        // Position 4 falls in alg 0's gap [3, 5).
        assert_eq!(committed_active_algs(&timeline, 5), vec![1]);
        assert_eq!(committed_active_algs(&timeline, 2), vec![0, 1]);
        assert!(committed_active_algs(&timeline, 0).is_empty());
    }

    #[test]
    fn test_verify_epoch_evolution() {
        let old = vec![(0u64, vec![(0u64, MAX)])];
        // Stays open; closes at/after the old snapshot; gains a resume.
        assert!(verify_epoch_evolution(&old, 5, &[(0, vec![(0, MAX)])], 9));
        assert!(verify_epoch_evolution(&old, 5, &[(0, vec![(0, 5)])], 9));
        assert!(verify_epoch_evolution(&old, 5, &[(0, vec![(0, 7)])], 9));
        assert!(verify_epoch_evolution(
            &old,
            5,
            &[(0, vec![(0, 6), (8, MAX)])],
            9
        ));
        // New algorithm registered after the old snapshot.
        assert!(verify_epoch_evolution(
            &old,
            5,
            &[(0, vec![(0, MAX)]), (1, vec![(5, MAX)])],
            9
        ));

        // Rewritten activation boundary.
        assert!(!verify_epoch_evolution(&old, 5, &[(0, vec![(1, MAX)])], 9));
        // Closed before the old snapshot (the old snapshot witnessed it open).
        assert!(!verify_epoch_evolution(&old, 5, &[(0, vec![(0, 4)])], 9));
        // Algorithm disappeared.
        assert!(!verify_epoch_evolution(&old, 5, &[(1, vec![(5, MAX)])], 9));
        // Backdated resume.
        assert!(!verify_epoch_evolution(
            &[(0, vec![(0, 2)])],
            5,
            &[(0, vec![(0, 2), (3, MAX)])],
            9
        ));
        // Backdated new algorithm (would have appeared in the old snapshot).
        assert!(!verify_epoch_evolution(
            &old,
            5,
            &[(0, vec![(0, MAX)]), (1, vec![(2, MAX)])],
            9
        ));
        // Closed interval mutated.
        assert!(!verify_epoch_evolution(
            &[(0, vec![(0, 3)])],
            5,
            &[(0, vec![(0, 4)])],
            9
        ));
        // Shrinking snapshot sizes.
        assert!(!verify_epoch_evolution(&old, 9, &old, 5));
    }
}
