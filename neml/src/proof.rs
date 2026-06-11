//! Inclusion and consistency proof structures and verification algorithms.

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

use crate::tree::frontier_for_size;

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

/// Configuration options for proof verification (local node policy).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifierConfig {
    /// Maximum number of active algorithms allowed (DoS mitigation).
    pub max_active_algorithms: usize,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self {
            max_active_algorithms: 8,
        }
    }
}

/// A coupling proof that binds a set of raw algorithm roots to a Signed Combined Root.
/// This allows verification of the combined root structure separately from individual trees.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CouplingProof {
    /// The active roots at this tree size: (alg_id, raw_root_hash)
    pub active_roots: Vec<(u64, Vec<u8>)>,
}

impl CouplingProof {
    /// Verify the coupling proof against a signed combined root for a given target algorithm.
    /// Returns the verified raw root hash for the target algorithm if successful.
    #[must_use]
    pub fn verify(
        &self,
        hasher: &dyn Hasher,
        target_alg_id: u64,
        combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> Option<Vec<u8>> {
        // DoS Mitigation: assert active roots count does not exceed configuration limit before
        // allocating
        if self.active_roots.len() > config.max_active_algorithms {
            return None;
        }

        // Validate active roots match expected active algorithms exactly to prevent
        // type-confusion/bypass
        if self.active_roots.len() != expected_active_algs.len() {
            return None;
        }
        for ((id, _), &expected_id) in self.active_roots.iter().zip(expected_active_algs.iter()) {
            if *id != expected_id {
                return None;
            }
        }

        // DoS Mitigation: assert individual companion root sizes are within bounds
        for (_, r) in &self.active_roots {
            if r.len() > 64 {
                return None;
            }
        }

        // Ensure the active roots list is canonically sorted by algorithm ID (prover requirement)
        // to prevent duplicate representation vectors or sorting malleability.
        if self.active_roots.windows(2).any(|w| w[0].0 >= w[1].0) {
            return None;
        }

        // Extract the target algorithm's root
        let mut target_root = None;
        for &(id, ref r) in &self.active_roots {
            if id == target_alg_id {
                target_root = Some(r.clone());
                break;
            }
        }
        let target_root = target_root?;

        // Reconstruct the combined root
        let match_ok = if self.active_roots.len() == 1 {
            // Singleton Promotion: the combined root is the raw root
            constant_time_eq(&self.active_roots[0].1, combined_root)
        } else {
            // Pre-allocate buffer capacity: each active root needs 8 (ID) + 8 (len) + r.len() (<=
            // 64) bytes. Using 80 bytes per entry avoids any dynamic heap reallocation
            // under DoS.
            let mut buf = Vec::with_capacity(self.active_roots.len() * 80);
            for (id, r) in &self.active_roots {
                buf.extend_from_slice(&id.to_be_bytes());
                buf.extend_from_slice(&(r.len() as u64).to_be_bytes());
                buf.extend_from_slice(r);
            }
            let computed = hasher.hash(&buf);
            constant_time_eq(&computed, combined_root)
        };

        if match_ok { Some(target_root) } else { None }
    }
}

/// Reconstruct the leaf index from a uniform Flat Log Mode path.
/// Returns `None` if the path does not match the uniform Flat Log Mode structure for `tree_size`
/// and `k`.
#[must_use]
pub fn reconstruct_index_from_path(k: u64, tree_size: u64, path: &[ProofStep]) -> Option<u64> {
    if k < 2 {
        return None;
    }
    let coords = frontier_for_size(tree_size, k);
    if coords.is_empty() {
        return None;
    }

    let mut next_node_id = coords.len();
    let mut frontier: Vec<usize> = (0..coords.len()).collect();
    let mut children_map = std::collections::HashMap::new();

    let k_usize = k as usize;
    while frontier.len() > k_usize {
        let split_idx = frontier.len() - k_usize;
        let parent_id = next_node_id;
        next_node_id += 1;
        let children = frontier[split_idx..].to_vec();
        children_map.insert(parent_id, children);
        frontier.truncate(split_idx);
        frontier.push(parent_id);
    }
    if frontier.len() > 1 {
        let parent_id = next_node_id;
        let children = frontier.clone();
        children_map.insert(parent_id, children);
        frontier = vec![parent_id];
    }

    let mut curr_node = frontier[0];
    let mut path_idx = path.len();

    while children_map.contains_key(&curr_node) {
        let children = &children_map[&curr_node];
        if path_idx == 0 {
            return None;
        }
        path_idx -= 1;
        let step = &path[path_idx];
        if step.siblings.len() != children.len() - 1 {
            return None;
        }
        if step.position >= children.len() {
            return None;
        }
        curr_node = children[step.position];
    }

    let f_idx = curr_node;
    if f_idx >= coords.len() {
        return None;
    }

    let (left, height) = coords[f_idx];
    if path_idx != height as usize {
        return None;
    }

    let mut offset = 0u64;
    let mut power = 1u64;
    for step in path.iter().take(path_idx) {
        if step.siblings.len() != k_usize - 1 {
            return None;
        }
        if step.position >= k_usize {
            return None;
        }
        let term = (step.position as u64).checked_mul(power)?;
        offset = offset.checked_add(term)?;
        power = power.checked_mul(k)?;
    }

    left.checked_add(offset)
}

fn path_length_to_frontier_node(k: u64, coords_len: usize, target_f_idx: usize) -> Option<usize> {
    if target_f_idx >= coords_len {
        return None;
    }

    let mut next_node_id = coords_len;
    let mut frontier: Vec<usize> = (0..coords_len).collect();
    let mut children_map = std::collections::HashMap::new();
    let mut spans = std::collections::HashMap::new();

    for i in 0..coords_len {
        spans.insert(i, (i, i));
    }

    let k_usize = k as usize;
    while frontier.len() > k_usize {
        let split_idx = frontier.len() - k_usize;
        let parent_id = next_node_id;
        next_node_id += 1;
        let children = frontier[split_idx..].to_vec();

        let min_idx = spans[&children[0]].0;
        let max_idx = spans[children.last()?].1;
        spans.insert(parent_id, (min_idx, max_idx));

        children_map.insert(parent_id, children);
        frontier.truncate(split_idx);
        frontier.push(parent_id);
    }
    if frontier.len() > 1 {
        let parent_id = next_node_id;
        let children = frontier.clone();

        let min_idx = spans[&children[0]].0;
        let max_idx = spans[children.last()?].1;
        spans.insert(parent_id, (min_idx, max_idx));

        children_map.insert(parent_id, children);
        frontier = vec![parent_id];
    }

    let root = frontier[0];
    let mut curr = root;
    let mut depth = 0;
    while children_map.contains_key(&curr) {
        let children = &children_map[&curr];
        let mut found = false;
        for &child in children {
            let (min_val, max_val) = spans[&child];
            if target_f_idx >= min_val && target_f_idx <= max_val {
                curr = child;
                depth += 1;
                found = true;
                break;
            }
        }
        if !found {
            return None;
        }
    }
    Some(depth)
}

/// Validate that the inclusion proof path matches the expected structure, sibling count, and
/// positions.
#[must_use]
pub fn verify_inclusion_path_structure(
    k: usize,
    index: u64,
    tree_size: u64,
    path: &[ProofStep],
) -> bool {
    if k < 2 {
        return false;
    }
    let k_u64 = k as u64;
    let coords = frontier_for_size(tree_size, k_u64);
    if coords.is_empty() {
        return false;
    }

    let mut target_f_idx = None;
    for (f_idx, &(left, height)) in coords.iter().enumerate() {
        if let Some(cap) = k_u64.checked_pow(height) {
            if index >= left && index < left + cap {
                target_f_idx = Some((f_idx, height));
                break;
            }
        }
    }
    let (f_idx, height) = match target_f_idx {
        Some(val) => val,
        None => return false,
    };

    let c = match path_length_to_frontier_node(k_u64, coords.len(), f_idx) {
        Some(depth) => depth,
        None => return false,
    };

    let expected_len = c + height as usize;
    if path.len() < expected_len {
        return false;
    }

    let d = path.len() - expected_len;
    reconstruct_index_from_path(k_u64, tree_size, &path[d..]) == Some(index)
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
            // Promoted node — current hash passes through unchanged
            continue;
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
        if step.siblings.is_empty() {
            // Promoted node
            curr_height += 1;
            let current_hash = map.get(&(curr_left, curr_height - 1))?.clone();
            map.insert((curr_left, curr_height), current_hash);
            continue;
        }
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
    let raw_root =
        match coupling.verify(hasher, alg_id, combined_root, expected_active_algs, config) {
            Some(r) => r,
            None => return false,
        };

    verify_inclusion(hasher, leaf_hash, index, tree_size, log_arity, path, &raw_root)
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
        old_combined_root,
        old_expected_active_algs,
        config,
    );
    let new_res = new_coupling.verify(
        hasher,
        alg_id,
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
}
