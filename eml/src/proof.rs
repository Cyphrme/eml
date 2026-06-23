//! Consistency proof structure and verification — the append-only evolution
//! surface layered over the kernel's inclusion and epoch construction.
//!
//! Inclusion, the binding root, coupling, and the canonical-encoding security
//! boundary live in the [`pmt`] kernel and are re-exported here so consumers
//! reach the whole proof surface through `eml_log::proof::*`. This module owns
//! only what is
//! append-only-specific: the [`ConsistencyProof`] (the tree at `old_size` is a
//! prefix of the tree at `new_size`) and the temporal analog of consistency
//! over the committed epoch timeline ([`verify_epoch_evolution`]).

use pmt::hasher::Hasher;
use pmt::mr::nary_mr;
// Re-export the kernel proof surface so `eml_log::proof::*` reaches it while
// the originals live in `pmt`. No parallels: these are the kernel's, not copies.
pub use pmt::proof::{
    AuditPayload, CouplingProof, InclusionProof, ProofStep, VerifierConfig, combined_root_preimage,
    committed_active_algs, committed_active_at, committed_is_live, constant_time_eq,
    reconstruct_inclusion_root, validate_committed_epochs, verify_inactivity_with_coupling,
    verify_inclusion, verify_inclusion_path_structure, verify_inclusion_with_coupling,
};
use pmt::topology::frontier_for_size;

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
/// with root `new_root` (arity `log_arity`).
///
/// # Trust contract (security-critical)
///
/// `old_size`, `new_size`, `log_arity`, `old_root`, and `new_root` are
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
    log_arity: u64,
    start_hash: &[u8],
    path: &[ProofStep],
    old_root: &[u8],
    new_root: &[u8],
) -> bool {
    reconstruct_consistency_roots(hasher, old_size, new_size, log_arity, start_hash, path)
        .is_some_and(|(computed_old, computed_new)| {
            constant_time_eq(&computed_old, old_root) & constant_time_eq(&computed_new, new_root)
        })
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

/// Reconstruct the old and new raw roots from a consistency proof path.
///
/// Building block for [`verify_consistency`]; it computes both roots but does
/// not compare them to trusted ones. Callers must hold to the same trust
/// contract: `old_size`, `new_size`, and `log_arity` must be authenticated, and
/// the returned roots are only meaningful when checked against authenticated
/// roots with the matching sizes bound (see [`verify_consistency`] for the
/// length-binding and both-roots-authenticated obligations).
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
    if !(2..=256).contains(&log_arity) {
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
        (Some(old_raw_root), Some(new_raw_root)) => verify_consistency(
            hasher,
            old_size,
            new_size,
            log_arity,
            start_hash,
            path,
            &old_raw_root,
            &new_raw_root,
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX: u64 = u64::MAX;

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
