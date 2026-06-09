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
    /// 0-based leaf index of the target.
    pub index: u64,
    /// Size of the tree for which this proof is valid.
    pub tree_size: u64,
    /// Path steps from leaf to root.
    pub path: Vec<ProofStep>,
}

/// Consistency proof: proves tree at `old_size` is a prefix of tree at `new_size`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistencyProof {
    /// Size of the older tree.
    pub old_size: u64,
    /// Size of the newer tree.
    pub new_size: u64,
    /// The log arity (k) of the tree.
    pub log_arity: u64,
    /// Starting hash (representing the boundary node of the old tree).
    pub start_hash: Vec<u8>,
    /// Path steps from the boundary to the root.
    pub path: Vec<ProofStep>,
}

/// Verify an inclusion proof.
///
/// Returns `true` if the proof demonstrates that `leaf_hash` is the leaf at
/// the given index in a tree of the given tree size with the given root.
#[must_use]
pub fn verify_inclusion(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    proof: &InclusionProof,
    root: &[u8],
) -> bool {
    if proof.index >= proof.tree_size {
        return false;
    }
    if proof.path.len() > 256 {
        return false;
    }

    let mut current = leaf_hash.to_vec();

    for step in &proof.path {
        if step.siblings.len() > 256 {
            return false;
        }
        if step.siblings.is_empty() {
            // Promoted node — current hash passes through unchanged
            continue;
        }
        if step.position > step.siblings.len() {
            return false;
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

    current == root
}

fn frontier_for_size(n: u64, k: u64) -> Vec<(u64, u32)> {
    if k < 2 {
        return Vec::new();
    }
    let mut frontier = Vec::new();
    let mut curr_left = 0;
    let mut temp_n = n;
    while temp_n > 0 {
        let mut height = 0;
        let mut cap: u64 = 1;
        while let Some(next_cap) = cap.checked_mul(k) {
            if next_cap <= temp_n {
                cap = next_cap;
                height += 1;
            } else {
                break;
            }
        }
        frontier.push((curr_left, height));
        curr_left += cap;
        temp_n -= cap;
    }
    frontier
}

/// Verify a consistency proof.
///
/// Proves that the tree of size `old_size` with `old_root` is an append-only
/// prefix of the tree of size `new_size` with `new_root`.
#[must_use]
pub fn verify_consistency(
    hasher: &dyn Hasher,
    proof: &ConsistencyProof,
    old_root: &[u8],
    new_root: &[u8],
) -> bool {
    if proof.old_size == 0 || proof.old_size >= proof.new_size {
        return false;
    }
    if proof.log_arity < 2 || proof.log_arity > 256 {
        return false;
    }
    if proof.path.len() > 256 {
        return false;
    }

    let k = proof.log_arity;

    let old_coords = frontier_for_size(proof.old_size, k);
    let new_coords = frontier_for_size(proof.new_size, k);

    let &(boundary_left, boundary_height) = match old_coords.last() {
        Some(coords) => coords,
        None => return false,
    };

    let mut target_new_f_idx = None;
    for (f_idx, &(new_left, new_height)) in new_coords.iter().enumerate() {
        let cap = k.pow(new_height);
        if boundary_left >= new_left && boundary_left < new_left + cap {
            target_new_f_idx = Some((f_idx, new_left, new_height));
            break;
        }
    }

    let (f_idx, _new_left, new_height) = match target_new_f_idx {
        Some(val) => val,
        None => return false,
    };

    if new_height < boundary_height {
        return false;
    }

    // We will populate a map from coordinate (left, height) to its hash
    use std::collections::HashMap;
    let mut map = HashMap::new();
    map.insert((boundary_left, boundary_height), proof.start_hash.clone());

    let bisection_steps = (new_height - boundary_height) as usize;
    if proof.path.len() < bisection_steps {
        return false;
    }

    // 1. Trace the bisection steps (first bisection_steps of proof.path)
    let mut curr_left = boundary_left;
    let mut curr_height = boundary_height;
    for i in 0..bisection_steps {
        let step = &proof.path[i];
        if step.siblings.is_empty() {
            // Promoted node
            curr_height += 1;
            let current_hash = match map.get(&(curr_left, curr_height - 1)) {
                Some(h) => h.clone(),
                None => return false,
            };
            map.insert((curr_left, curr_height), current_hash);
            continue;
        }
        if step.position > step.siblings.len() {
            return false;
        }

        let child_capacity = k.pow(curr_height);
        let parent_left = match curr_left.checked_sub(step.position as u64 * child_capacity) {
            Some(val) => val,
            None => return false,
        };
        let parent_height = curr_height + 1;

        let current_hash = match map.get(&(curr_left, curr_height)) {
            Some(h) => h.clone(),
            None => return false,
        };

        // Reconstruct children
        let mut children = Vec::with_capacity(step.siblings.len() + 1);
        for (j, sib) in step.siblings.iter().enumerate() {
            let j_u64 = j as u64;
            let c_left = if j_u64 < step.position as u64 {
                parent_left + j_u64 * child_capacity
            } else {
                parent_left + (j_u64 + 1) * child_capacity
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
            if proof_idx >= proof.path.len() {
                return false;
            }
            let step = &proof.path[proof_idx];
            proof_idx += 1;

            if step.position != target_idx - split_idx || step.siblings.len() != k_usize - 1 {
                return false;
            }

            let mut children_hashes = Vec::with_capacity(k_usize);
            for j in 0..k_usize {
                let node_idx = split_idx + j;
                let hash = if node_idx == target_idx {
                    match &current_frontier[node_idx].hash {
                        Some(h) => h.clone(),
                        None => return false,
                    }
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
        if proof_idx >= proof.path.len() {
            return false;
        }
        let step = &proof.path[proof_idx];
        proof_idx += 1;

        if step.position != target_idx || step.siblings.len() != current_frontier.len() - 1 {
            return false;
        }

        let mut children_hashes = Vec::with_capacity(current_frontier.len());
        for (j, node) in current_frontier.iter().enumerate() {
            let hash = if j == target_idx {
                match &node.hash {
                    Some(h) => h.clone(),
                    None => return false,
                }
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

    if proof_idx != proof.path.len() {
        return false;
    }

    // 3. Reconstruct old root
    let mut old_hashes = Vec::with_capacity(old_coords.len());
    for coord in &old_coords {
        let hash = match map.get(coord) {
            Some(h) => h.clone(),
            None => return false,
        };
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
    let computed_new_root = match &current_frontier[0].hash {
        Some(h) => h.clone(),
        None => return false,
    };

    computed_old_root == old_root && computed_new_root == new_root
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
        _hasher: &dyn Hasher,
        _target_alg_id: u64,
        _combined_root: &[u8],
        _expected_active_algs: &[u64],
        _config: VerifierConfig,
    ) -> Option<Vec<u8>> {
        None
    }
}

/// Reconstruct the raw root from an inclusion proof path.
#[must_use]
pub fn reconstruct_inclusion_root(
    _hasher: &dyn Hasher,
    _leaf_hash: &[u8],
    _proof: &InclusionProof,
) -> Option<Vec<u8>> {
    None
}

/// Reconstruct the old and new raw roots from a consistency proof path.
#[must_use]
pub fn reconstruct_consistency_roots(
    _hasher: &dyn Hasher,
    _proof: &ConsistencyProof,
) -> Option<(Vec<u8>, Vec<u8>)> {
    None
}

/// Helper wrapper demonstrating inclusion verification with decoupled coupling proofs.
#[must_use]
pub fn verify_inclusion_with_coupling(
    _hasher: &dyn Hasher,
    _alg_id: u64,
    _leaf_hash: &[u8],
    _inclusion_proof: &InclusionProof,
    _coupling: &CouplingProof,
    _combined_root: &[u8],
    _expected_active_algs: &[u64],
    _config: VerifierConfig,
) -> bool {
    false
}

/// Helper wrapper demonstrating consistency verification with decoupled coupling proofs.
#[must_use]
pub fn verify_consistency_with_coupling(
    _hasher: &dyn Hasher,
    _alg_id: u64,
    _consistency_proof: &ConsistencyProof,
    _old_coupling: &CouplingProof,
    _new_coupling: &CouplingProof,
    _old_combined_root: &[u8],
    _new_combined_root: &[u8],
    _old_expected_active_algs: &[u64],
    _new_expected_active_algs: &[u64],
    _config: VerifierConfig,
) -> bool {
    false
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

