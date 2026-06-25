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

use spine::{ARITY_RANGE, Hasher, fold_frontier, frontier_for_size, nary_mr};
// Re-export the spine proof surface so `cml::proof::*` reaches it while the
// originals live in `spine`. No parallels: these are the spine's, not copies.
pub use spine::{
    InclusionProof, ProofStep, constant_time_eq, reconstruct_inclusion_root, verify_inclusion,
    verify_inclusion_path_structure,
};

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

/// Sentinel height assigned to the synthetic root `FrontierNode` produced
/// at the end of the frontier merge loop in `reconstruct_consistency_roots`.
///
/// The root node is the sole remaining frontier entry after the merge
/// completes; its height is never read again. The sentinel distinguishes it
/// from any real node height and documents the intent in place of the magic
/// literal 9999.
const ROOT_SENTINEL_HEIGHT: u32 = u32::MAX;

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
            height: ROOT_SENTINEL_HEIGHT,
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

    let computed_old_root = if old_hashes.is_empty() {
        hasher.empty()
    } else {
        fold_frontier(old_hashes, k_usize, |chunk| {
            let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
            nary_mr(hasher, &refs)
        })
    };

    // 4. Reconstruct new root
    let computed_new_root = current_frontier[0].hash.as_ref()?.clone();

    Some((computed_old_root, computed_new_root))
}
