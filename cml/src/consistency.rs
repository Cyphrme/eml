//! Consistency proof structure and verification — the append-only evolution
//! surface layered over the spine's inclusion proof.
//!
//! Inclusion, the proof step, and the canonical-encoding security boundary live
//! in the [`spine`] core and are re-exported here so a CML consumer reaches the
//! whole structural proof surface through `cml::proof::*`. This module owns only
//! what is append-only-specific and **epoch-free**: the [`ConsistencyProof`] (the
//! tree at `old_size` is a prefix of the tree at `new_size`).
//!
//! The *temporal* analog over the committed epoch timeline (`verify_epoch_evolution`)
//! and the coupling-wrapped consistency check are the `polydigest` combinator's
//! concern — they need the timeline, which the spine and CML do not see.

use spine::{ARITY_RANGE, Hasher, frontier_for_size, nary_mr};
// Re-export the spine proof surface so `cml::proof::*` reaches it while the
// originals live in `spine`. No parallels: these are the spine's, not copies.
pub use spine::{
    InclusionProof, ProofStep, constant_time_eq, reconstruct_inclusion_root, verify_inclusion,
    verify_inclusion_path_structure,
};

use crate::mountain::{BagNode, bag_peaks, bag_shape, covers_peak};

/// Consistency proof: proves tree at `old_size` is a prefix of tree at `new_size`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistencyProof {
    /// Starting hash (representing the boundary node of the old tree).
    pub start_hash: Vec<u8>,
    /// Path steps from the boundary to the root.
    pub path: Vec<ProofStep>,
}

/// Verify a consistency proof.
///
/// Returns `true` if the proof demonstrates that the tree of size `old_size`
/// with root `old_root` is an append-only prefix of the tree of size `new_size`
/// with root `new_root` (arity `arity`).
///
/// # Trust contract (security-critical)
///
/// `old_size`, `new_size`, `arity`, `old_root`, and `new_root` are
/// **trusted parameters** and MUST come from an authenticated source — signed
/// Tree Heads (STHs) or trusted checkpoints — never from the proof or any
/// caller-untrusted input. The verifier reconstructs both roots from the sizes
/// and the single shared `path`; if the sizes are attacker-controlled the
/// append-only guarantee is void.
///
/// Two further obligations follow from the length-hiding null-collapse design;
/// violating them defeats the guarantee even with a correct verifier:
///
/// * **Root equality stands in for tree equality only when the size is also bound.** All-null
///   (inactive) subtrees of *different* lengths share a root, so callers must never treat root
///   equality as "same tree" without pinning the corresponding size. This applies to caches, dedup,
///   and any comparison of stored/reconstructed roots.
/// * **The data-level guarantee needs *both* roots authenticated.** A `true` result binds the roots
///   (`old_root` is the genuine size-`old_size` prefix root of the size-`new_size` tree).
///   Concluding that the new *data* is a genuine extension of the old data holds only when
///   `new_root` is itself authenticated: a consistency proof carries perfect-subtree roots, not the
///   appended cells, and cannot witness an extension against an unauthenticated `new_root`.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_consistency(
    hasher: &dyn Hasher,
    old_size: u64,
    new_size: u64,
    arity: u64,
    start_hash: &[u8],
    path: &[ProofStep],
    old_root: &[u8],
    new_root: &[u8],
) -> bool {
    reconstruct_consistency_roots(hasher, old_size, new_size, arity, start_hash, path).is_some_and(
        |(computed_old, computed_new)| {
            constant_time_eq(&computed_old, old_root) & constant_time_eq(&computed_new, new_root)
        },
    )
}

/// Reconstruct the old and new raw roots from a consistency proof path.
///
/// Building block for [`verify_consistency`]; it computes both roots but does
/// not compare them to trusted ones. Callers must hold to the same trust
/// contract: `old_size`, `new_size`, and `arity` must be authenticated, and
/// the returned roots are only meaningful when checked against authenticated
/// roots with the matching sizes bound (see [`verify_consistency`] for the
/// length-binding and both-roots-authenticated obligations).
#[must_use]
pub fn reconstruct_consistency_roots(
    hasher: &dyn Hasher,
    old_size: u64,
    new_size: u64,
    arity: u64,
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
    if !ARITY_RANGE.contains(&arity) {
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

    let k = arity;

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
    for step in &path[..bisection_steps] {
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

    // 2. Fold the boundary mountain peak up through the bagPath to the new root.
    //
    // The path steps after the bisection are the boundary mountain peak's bagPath
    // under the MMR backward-bag (the same suffix an inclusion proof carries). The
    // bag shape says, at each step, which children are *single peaks* (recorded
    // into the map by their new coordinate, for the old-root reconstruction) and
    // which are *aggregate* sub-bags (newer peaks, opaque here — folded as a unit
    // via the proof's sibling digest, never needed individually for the old root).
    let peak_digest = map.get(&new_coords[f_idx])?.clone();

    let bag = bag_shape(new_coords.len(), k as usize)?;
    // Collect the bag nodes on the root → peak path, each with its path-child
    // position. The proof's bagPath stores these peak → root, so zip the reversed
    // bag-node list against `path[bisection_steps..]`.
    let mut bag_nodes_root_to_peak = Vec::new();
    if !collect_bag_path(&bag, f_idx, &mut bag_nodes_root_to_peak) {
        return None;
    }
    let bagpath = &path[bisection_steps..];
    if bagpath.len() != bag_nodes_root_to_peak.len() {
        return None;
    }
    // peak → root order: `bagpath[0]` is the innermost bag node (deepest, listed
    // last in root → peak), so the reversed bag-node list aligns with the path.
    let mut current = peak_digest;
    for (step, (children, position)) in bagpath.iter().zip(bag_nodes_root_to_peak.iter().rev()) {
        if step.position != *position || step.siblings.len() != children.len() - 1 {
            return None;
        }
        // Record any single-peak sibling into the map by its new coordinate (a
        // non-merged old peak is recovered here), then rebuild this bag node by
        // inserting `current` at `position` among the proof's sibling digests.
        let mut sib_iter = step.siblings.iter();
        let mut node_children: Vec<&[u8]> = Vec::with_capacity(children.len());
        for (child_pos, child) in children.iter().enumerate() {
            if child_pos == *position {
                node_children.push(current.as_slice());
                continue;
            }
            let sib = sib_iter.next()?;
            if let BagNode::Peak(j) = child {
                map.insert(new_coords[*j], sib.clone());
            }
            node_children.push(sib.as_slice());
        }
        current = nary_mr(hasher, &node_children);
    }

    // 3. The fold's result is the new root.
    let computed_new_root = current;

    // 4. Reconstruct the old root: bag the old peaks, each read from the map by
    // its own coordinate. An old peak that *merged* into a larger new mountain is
    // an interior node recovered by the bisection (phase 1); an old peak that did
    // *not* merge is a separate new peak recovered by the bagPath (phase 2, keyed
    // by its coordinate above). Either way it is in the map at its old coordinate.
    let mut old_hashes = Vec::with_capacity(old_coords.len());
    for coord in &old_coords {
        old_hashes.push(map.get(coord)?.clone());
    }
    let computed_old_root = bag_peaks(hasher, &old_hashes, k);

    Some((computed_old_root, computed_new_root))
}

/// Collect the bag nodes on the root → peak path to `Peak(f_idx)` in `node`,
/// each as `(children, path_child_position)`, appended to `out` in root → peak
/// order. Returns `false` if `f_idx` is not covered (a malformed proof).
fn collect_bag_path<'a>(
    node: &'a BagNode,
    f_idx: usize,
    out: &mut Vec<(&'a [BagNode], usize)>,
) -> bool {
    match node {
        BagNode::Peak(idx) => *idx == f_idx,
        BagNode::Bag(children) => {
            let Some(position) = children.iter().position(|c| covers_peak(c, f_idx)) else {
                return false;
            };
            out.push((children.as_slice(), position));
            collect_bag_path(&children[position], f_idx, out)
        },
    }
}
