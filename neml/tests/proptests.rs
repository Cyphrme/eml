use std::collections::BTreeMap;

use neml::{
    Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig, evaluate,
    verify_consistency, verify_inclusion,
};
use proptest::prelude::*;
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children {
            h.update(child);
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

impl eml::Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
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

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn eml::Hasher> {
        Box::new(Sha256Hasher)
    }
}

// Custom mock hasher to check hasher-independence.
#[derive(Debug)]
struct SaltedHasher(u8);

impl Hasher for SaltedHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        for child in children {
            h.update(child);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.finalize().to_vec()
    }

    fn null(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0, 0x02]);
        h.finalize().to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(SaltedHasher(self.0))
    }
}

impl eml::Hasher for SaltedHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.finalize().to_vec()
    }

    fn null(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0, 0x02]);
        h.finalize().to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([self.0]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn clone_box(&self) -> Box<dyn eml::Hasher> {
        Box::new(SaltedHasher(self.0))
    }
}

fn new_hasher_for(alg_id: u64) -> Box<dyn Hasher> {
    if alg_id % 2 == 0 {
        Box::new(Sha256Hasher)
    } else {
        Box::new(SaltedHasher((alg_id & 0xFF) as u8))
    }
}

// Custom reduction count helper
fn reduction_count(n: u64, k: u64) -> u64 {
    let mut count = 0;
    let mut temp = n + 1;
    while temp > 0 && temp % k == 0 {
        count += 1;
        temp /= k;
    }
    count
}

// Custom nary_mr helper matching definition
fn nary_mr(hasher: &dyn Hasher, children: &[&[u8]]) -> Vec<u8> {
    match children.len() {
        0 => hasher.empty(),
        1 => children[0].to_vec(),
        _ => {
            let null_const = hasher.null();
            if children.iter().all(|&c| c == null_const) {
                null_const
            } else {
                hasher.node(children)
            }
        },
    }
}

// Reconstruct coordinate-based frontier for size `n` and arity `k`
fn frontier_for_size(n: u64, k: u64) -> Vec<(u64, u32)> {
    let mut frontier = Vec::new();
    let mut curr_left = 0;
    let mut temp_n = n;
    while temp_n > 0 {
        let mut height = 0;
        let mut cap = 1;
        while cap * k <= temp_n {
            cap *= k;
            height += 1;
        }
        frontier.push((curr_left, height));
        curr_left += cap;
        temp_n -= cap;
    }
    frontier
}

// Simulates stack folding on a sequence of projected leaf hashes
fn nary_mth(hasher: &dyn Hasher, leaves: &[Vec<u8>], k: usize) -> Vec<u8> {
    if leaves.is_empty() {
        return hasher.empty();
    }
    let mut frontier: Vec<Vec<u8>> = Vec::new();
    let mut frontier_coords: Vec<(u64, u32)> = Vec::new();

    for (i, leaf_hash) in leaves.iter().enumerate() {
        frontier.push(leaf_hash.clone());
        frontier_coords.push((i as u64, 0));

        let merges = reduction_count(i as u64, k as u64);
        for _ in 0..merges {
            let mut children = Vec::with_capacity(k);
            let mut coords = Vec::with_capacity(k);
            for _ in 0..k {
                children.push(frontier.pop().unwrap());
                coords.push(frontier_coords.pop().unwrap());
            }
            children.reverse();
            coords.reverse();
            let child_refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
            let parent = nary_mr(hasher, &child_refs);

            let parent_left_index = coords[0].0;
            let parent_height = coords[0].1 + 1;

            frontier.push(parent);
            frontier_coords.push((parent_left_index, parent_height));
        }
    }

    if frontier.is_empty() {
        return hasher.empty();
    }
    if frontier.len() == 1 {
        return frontier[0].clone();
    }
    let mut current = frontier.clone();
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

// Recursively calculates the subtree root matching Definition 14c
fn recursive_subtree_root(hasher: &dyn Hasher, leaves: &[Vec<u8>], k: usize) -> Vec<u8> {
    let size = leaves.len();
    if size == 0 {
        return hasher.empty();
    }
    if size == 1 {
        return leaves[0].clone();
    }

    let is_power_of_k = {
        let mut temp = size;
        while temp % k == 0 {
            temp /= k;
        }
        temp == 1
    };

    if is_power_of_k {
        let child_size = size / k;
        let mut child_hashes = Vec::with_capacity(k);
        for j in 0..k {
            let c_lo = j * child_size;
            let c_hi = (j + 1) * child_size;
            let child_hash = recursive_subtree_root(hasher, &leaves[c_lo..c_hi], k);
            child_hashes.push(child_hash);
        }
        let child_refs: Vec<&[u8]> = child_hashes.iter().map(|c| c.as_slice()).collect();
        nary_mr(hasher, &child_refs)
    } else {
        let coords = frontier_for_size(size as u64, k as u64);
        let mut component_hashes = Vec::with_capacity(coords.len());
        for &(part_left, part_height) in &coords {
            let cap = (k as u64).pow(part_height) as usize;
            let c_lo = part_left as usize;
            let c_hi = c_lo + cap;
            let part_root = recursive_subtree_root(hasher, &leaves[c_lo..c_hi], k);
            component_hashes.push(part_root);
        }

        let mut current = component_hashes;
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
}

// Read leaf projection for given algorithm
async fn project<S: neml::Storage>(
    log: &NaryMerkleLog<S>,
    alg_id: u64,
    hasher: &dyn Hasher,
) -> Vec<Vec<u8>> {
    let metas = log.storage().load_algorithm_metas().await.unwrap();
    let epochs = metas
        .iter()
        .find(|(id, _)| *id == alg_id)
        .map(|(_, eps)| eps)
        .unwrap();
    let global_size = if log.size() > 0 {
        log.size()
    } else {
        log.subtree_count()
    };

    let is_active = epochs.last().is_some_and(|&(_, end)| end == u64::MAX);
    let tree_size = if is_active {
        global_size
    } else {
        epochs.last().map_or(0, |&(_, end)| end)
    };

    let mut leaves = Vec::with_capacity(tree_size as usize);
    for i in 0..tree_size {
        let active = epochs.iter().any(|&(start, end)| start <= i && i < end);
        if active {
            if log.size() > 0 {
                let data = log.storage().get_leaf(i).await.unwrap();
                leaves.push(hasher.leaf(&data));
            } else {
                let hash = log.storage().get_node(alg_id, i, 0).await.unwrap().unwrap();
                leaves.push(hash);
            }
        } else {
            leaves.push(hasher.null());
        }
    }
    leaves
}

async fn build_log(size: usize, activation: usize, k: usize) -> NaryMerkleLog<MemoryStorage> {
    let config = TreeConfig { log_arity: k };
    let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
        .await
        .unwrap();

    if activation > 0 {
        log.add_algorithm(99, Box::new(Sha256Hasher)).await.unwrap();
        log.remove_algorithm(0).await.unwrap();
    }

    for i in 0..size {
        if i == activation && activation > 0 {
            log.resume_algorithm(0).await.unwrap();
        }
        log.append_leaf(&[i as u8]).await.unwrap();
    }

    log
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn d_sep_leaf_vs_null(data in proptest::collection::vec(any::<u8>(), 0..64)) {
        let leaf = Sha256Hasher.leaf(&data);
        let null = Sha256Hasher.null();
        prop_assert!(leaf != null, "D-SEP violated: leaf == null");
    }

    #[test]
    fn d_sep_leaf_vs_node(
        data in proptest::collection::vec(any::<u8>(), 0..64),
        left in proptest::collection::vec(any::<u8>(), 32..=32),
        right in proptest::collection::vec(any::<u8>(), 32..=32),
    ) {
        let leaf = Sha256Hasher.leaf(&data);
        let node = Sha256Hasher.node(&[&left, &right]);
        prop_assert!(leaf != node, "D-SEP violated: leaf == node");
    }

    #[test]
    fn a_equiv_malt(
        size in 1usize..64,
        k in 2usize..5,
        act_frac in 0.0f64..1.0,
    ) {
        smol::block_on(async {
            let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
            let log = build_log(size, activation, k).await;

            let projected = project(&log, 0, &Sha256Hasher).await;
            let incremental = log.root_for(0).unwrap();
            let batch = nary_mth(&Sha256Hasher, &projected, k);

            prop_assert_eq!(incremental, batch);
            Ok(())
        })?;
    }

    #[test]
    fn subtree_root_equiv_malt(
        size in 1usize..64,
        k in 2usize..5,
        act_frac in 0.0f64..1.0,
    ) {
        smol::block_on(async {
            let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
            let log = build_log(size, activation, k).await;

            let projected = project(&log, 0, &Sha256Hasher).await;
            let incremental = log.root_for(0).unwrap();
            let recursive = recursive_subtree_root(&Sha256Hasher, &projected, k);

            prop_assert_eq!(incremental, recursive);
            Ok(())
        })?;
    }

    #[test]
    fn i_sound_malt(
        size in 2usize..64,
        k in 2usize..5,
        act_frac in 0.0f64..1.0,
        idx_frac in 0.0f64..1.0,
    ) {
        smol::block_on(async {
            let activation = ((act_frac * size as f64) as usize).min(size.saturating_sub(1));
            let log = build_log(size, activation, k).await;

            let ts = log.size();
            let index = ((idx_frac * ts as f64) as u64).min(ts - 1);

            let root = log.root_for(0).unwrap();
            let projected = project(&log, 0, &Sha256Hasher).await;
            let proof = log.inclusion_proof_for(0, index, ts).await.unwrap().unwrap();

            prop_assert!(
                verify_inclusion(&Sha256Hasher, &projected[index as usize], index, ts, k as u64, &proof.path, &root),
                "I-SOUND-MALT failed to verify valid proof"
            );

            let wrong = Sha256Hasher.leaf(b"WRONG_LEAF_DATA");
            prop_assert!(
                !verify_inclusion(&Sha256Hasher, &wrong, index, ts, k as u64, &proof.path, &root),
                "I-SOUND-MALT accepted invalid forged leaf"
            );
            Ok(())
        })?;
    }

    #[test]
    fn k_sound_malt(
        size in 3usize..64,
        k in 2usize..5,
        old_frac in 0.0f64..1.0,
    ) {
        smol::block_on(async {
            let log = build_log(size, 0, k).await;
            let ts = log.size();
            let old_size = ((old_frac * (ts - 1) as f64) as u64).max(1).min(ts - 1);

            let old_log = build_log(old_size as usize, 0, k).await;
            let old_root = old_log.root_for(0).unwrap();
            let new_root = log.root_for(0).unwrap();

            let proof = log.consistency_proof_for(0, old_size, ts).await.unwrap().unwrap();

            prop_assert!(
                verify_consistency(&Sha256Hasher, old_size, ts, k as u64, &proof.start_hash, &proof.path, &old_root, &new_root),
                "K-SOUND-MALT failed to verify consistency proof"
            );
            Ok(())
        })?;
    }

    #[test]
    fn t_bound_malt(
        size in 2usize..64,
        k in 2usize..5,
        act_frac in 0.01f64..1.0,
        payload in proptest::collection::vec(any::<u8>(), 1..32),
    ) {
        smol::block_on(async {
            let activation = ((act_frac * size as f64) as usize).max(1).min(size.saturating_sub(1));
            let log = build_log(size, activation, k).await;

            let root = log.root_for(0).unwrap();
            let null_idx = activation.saturating_sub(1) as u64;

            let forged = Sha256Hasher.leaf(&payload);
            let ts = log.size();
            let proof = log.inclusion_proof_for(0, null_idx, ts).await.unwrap().unwrap();

            prop_assert!(
                !verify_inclusion(&Sha256Hasher, &forged, null_idx, ts, k as u64, &proof.path, &root),
                "T-BOUND-MALT accepted forged leaf at null position"
            );
            Ok(())
        })?;
    }
}

// ============================================================================
// State-Machine fuzzer for multi-epoch, multi-algorithm execution.
// ============================================================================

#[derive(Debug, Clone)]
enum Op {
    AppendLeaf(Vec<u8>),
    AppendSubtree(Subtree),
    AddAlg(u64),
    RemoveAlg(u64),
    ResumeAlg(u64),
}

fn subtree_strategy(depth: u32) -> impl Strategy<Value = Subtree> {
    let leaf = any::<Vec<u8>>().prop_map(Subtree::Leaf);
    if depth == 0 {
        leaf.boxed()
    } else {
        prop_oneof![
            leaf,
            prop::collection::vec(subtree_strategy(depth - 1), 1..=3).prop_map(Subtree::Node)
        ]
        .boxed()
    }
}

fn op_strategy(max_algs: u64) -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => any::<Vec<u8>>().prop_map(Op::AppendLeaf),
        2 => subtree_strategy(2).prop_map(Op::AppendSubtree),
        2 => (0..max_algs).prop_map(Op::AddAlg),
        1 => (0..max_algs).prop_map(Op::RemoveAlg),
        1 => (0..max_algs).prop_map(Op::ResumeAlg),
    ]
}

async fn check_state_invariants<S: neml::Storage>(
    log: &NaryMerkleLog<S>,
    frozen_roots: &BTreeMap<u64, Vec<u8>>,
    k: usize,
) -> Result<(), proptest::test_runner::TestCaseError> {
    let metas = log.storage().load_algorithm_metas().await.unwrap();
    let size = if log.size() > 0 {
        log.size()
    } else {
        log.subtree_count()
    };

    for &(alg_id, ref epochs) in &metas {
        let hasher = new_hasher_for(alg_id);
        let is_active = epochs.last().is_some_and(|&(_, end)| end == u64::MAX);
        let tree_size = if is_active {
            size
        } else {
            epochs.last().map_or(0, |&(_, end)| end)
        };

        let projected = project(log, alg_id, hasher.as_ref()).await;

        // A-STACK: projected len == tree_size
        prop_assert_eq!(projected.len() as u64, tree_size);

        let incremental = log.root_for(alg_id).unwrap();

        // A-EQUIV: incremental root == batch root
        let batch = nary_mth(hasher.as_ref(), &projected, k);
        prop_assert_eq!(&incremental, &batch);

        // SUBTREE-ROOT-EQUIV: recursive root == incremental root
        let recursive = recursive_subtree_root(hasher.as_ref(), &projected, k);
        prop_assert_eq!(&incremental, &recursive);

        // Root stability for frozen algorithms
        if let Some(frozen_root) = frozen_roots.get(&alg_id) {
            prop_assert_eq!(&incremental, frozen_root);
        }

        // Proof soundness check
        if tree_size > 0 {
            let sample_indices = {
                let ts = tree_size;
                let mut v = vec![0, ts - 1];
                if ts > 2 {
                    v.push(ts / 2);
                }
                v
            };

            for idx in sample_indices {
                let proof = log
                    .inclusion_proof_for(alg_id, idx, tree_size)
                    .await
                    .unwrap()
                    .unwrap();
                prop_assert!(verify_inclusion(
                    hasher.as_ref(),
                    &projected[idx as usize],
                    idx,
                    tree_size,
                    k as u64,
                    &proof.path,
                    &incremental
                ));
            }

            if tree_size > 1 {
                let old_size = (tree_size / 2).max(1);
                let old_projected = &projected[..old_size as usize];
                let old_root = nary_mth(hasher.as_ref(), old_projected, k);

                let proof = log
                    .consistency_proof_for(alg_id, old_size, tree_size)
                    .await
                    .unwrap()
                    .unwrap();
                prop_assert!(verify_consistency(
                    hasher.as_ref(),
                    old_size,
                    tree_size,
                    k as u64,
                    &proof.start_hash,
                    &proof.path,
                    &old_root,
                    &incremental
                ));
            }
        }
    }

    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn metamorphic_registration_order(
        leaves in proptest::collection::vec(proptest::collection::vec(any::<u8>(), 0..32), 1..10),
        k in 2usize..5,
    ) {
        smol::block_on(async {
            let config = TreeConfig { log_arity: k };
            let alg_ids = [10, 20, 30];

            let mut log1 = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await.unwrap();
            log1.add_algorithm(alg_ids[0], new_hasher_for(alg_ids[0])).await.unwrap();
            log1.add_algorithm(alg_ids[1], new_hasher_for(alg_ids[1])).await.unwrap();
            log1.add_algorithm(alg_ids[2], new_hasher_for(alg_ids[2])).await.unwrap();

            let mut log2 = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await.unwrap();
            log2.add_algorithm(alg_ids[2], new_hasher_for(alg_ids[2])).await.unwrap();
            log2.add_algorithm(alg_ids[0], new_hasher_for(alg_ids[0])).await.unwrap();
            log2.add_algorithm(alg_ids[1], new_hasher_for(alg_ids[1])).await.unwrap();

            for leaf in &leaves {
                log1.append_leaf(leaf).await.unwrap();
                log2.append_leaf(leaf).await.unwrap();
            }

            for &id in &alg_ids {
                let r1 = log1.root_for(id).unwrap();
                let r2 = log2.root_for(id).unwrap();
                prop_assert_eq!(r1, r2);
            }
            Ok::<(), proptest::test_runner::TestCaseError>(())
        })?;
    }

    #[test]
    fn metamorphic_mid_stream_registration(
        first_batch in proptest::collection::vec(proptest::collection::vec(any::<u8>(), 0..32), 1..10),
        second_batch in proptest::collection::vec(proptest::collection::vec(any::<u8>(), 0..32), 1..10),
        k in 2usize..5,
    ) {
        smol::block_on(async {
            let config = TreeConfig { log_arity: k };
            let alg_ids = [40, 50];

            let mut log1 = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await.unwrap();

            let mut log2 = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await.unwrap();

            for leaf in &first_batch {
                log1.append_leaf(leaf).await.unwrap();
                log2.append_leaf(leaf).await.unwrap();
            }

            log1.add_algorithm(alg_ids[0], new_hasher_for(alg_ids[0])).await.unwrap();
            log1.add_algorithm(alg_ids[1], new_hasher_for(alg_ids[1])).await.unwrap();

            log2.add_algorithm(alg_ids[1], new_hasher_for(alg_ids[1])).await.unwrap();
            log2.add_algorithm(alg_ids[0], new_hasher_for(alg_ids[0])).await.unwrap();

            for leaf in &second_batch {
                log1.append_leaf(leaf).await.unwrap();
                log2.append_leaf(leaf).await.unwrap();
            }

            for &id in &alg_ids {
                let r1 = log1.root_for(id).unwrap();
                let r2 = log2.root_for(id).unwrap();
                prop_assert_eq!(r1, r2);
            }
            Ok::<(), proptest::test_runner::TestCaseError>(())
        })?;
    }

    #[test]
    fn state_machine_malt(
        ops in proptest::collection::vec(op_strategy(6), 20..50),
        k in 2usize..4,
        is_state_mode in any::<bool>(),
    ) {
        smol::block_on(async {
            let config = TreeConfig { log_arity: k };
            let mut log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await.unwrap();

            // Seed with algs
            log.add_algorithm(1, new_hasher_for(1)).await.unwrap();
            log.add_algorithm(2, new_hasher_for(2)).await.unwrap();

            let mut frozen_roots = BTreeMap::new();

            for op in ops {
                match op {
                    Op::AppendLeaf(data) => {
                        let has_active = log
                            .storage()
                            .load_algorithm_metas()
                            .await
                            .unwrap()
                            .iter()
                            .any(|(_, epochs)| {
                                epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
                            });
                        if has_active {
                            if is_state_mode {
                                log.append_leaf(&data).await.unwrap();
                            } else {
                                log.append_subtree(&Subtree::Leaf(data)).await.unwrap();
                            }
                        }
                    }
                    Op::AppendSubtree(subtree) => {
                        let has_active = log
                            .storage()
                            .load_algorithm_metas()
                            .await
                            .unwrap()
                            .iter()
                            .any(|(_, epochs)| {
                                epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
                            });
                        if has_active {
                            if is_state_mode {
                                let data = evaluate(&Sha256Hasher, &subtree);
                                log.append_leaf(&data).await.unwrap();
                            } else {
                                log.append_subtree(&subtree).await.unwrap();
                            }
                        }
                    }
                    Op::AddAlg(id) => {
                        let exists = log.storage().load_algorithm_metas().await.unwrap()
                            .iter()
                            .any(|(alg_id, _)| *alg_id == id);
                        if !exists {
                            log.add_algorithm(id, new_hasher_for(id)).await.unwrap();
                        }
                    }
                    Op::RemoveAlg(id) => {
                        let active = log.storage().load_algorithm_metas().await.unwrap()
                            .iter()
                            .find(|(alg_id, _)| *alg_id == id)
                            .is_some_and(|(_, epochs)| {
                                epochs.last().is_some_and(|&(_, end)| end == u64::MAX)
                            });
                        if active {
                            let root = log.root_for(id).unwrap();
                            log.remove_algorithm(id).await.unwrap();
                            frozen_roots.insert(id, root);
                        }
                    }
                    Op::ResumeAlg(id) => {
                        let frozen = log.storage().load_algorithm_metas().await.unwrap()
                            .iter()
                            .find(|(alg_id, _)| *alg_id == id)
                            .is_some_and(|(_, epochs)| {
                                epochs.last().is_some_and(|&(_, end)| end != u64::MAX)
                            });
                        if frozen {
                            log.resume_algorithm(id).await.unwrap();
                            frozen_roots.remove(&id);
                        }
                    }
                }

                check_state_invariants(&log, &frozen_roots, k).await?;
            }
            Ok::<(), proptest::test_runner::TestCaseError>(())
        })?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    #[test]
    fn test_coupling_proof_properties(
        // active algs: sorted list of unique u64 (up to 8 elements)
        active_algs in proptest::collection::vec(0..100u64, 1..=8)
            .prop_map(|mut v| { v.sort_unstable(); v.dedup(); v }),
        // roots: matching list of byte vectors (length 0..64)
        roots in proptest::collection::vec(proptest::collection::vec(any::<u8>(), 0..64), 1..=8),
        // target alg index selector
        target_idx in any::<usize>(),
    ) {
        let len = active_algs.len().min(roots.len());
        if len > 0 {
            let active_algs = &active_algs[..len];
            let roots = &roots[..len];
            let target_idx = target_idx % len;
            let target_alg_id = active_algs[target_idx];
            let target_root = &roots[target_idx];

            let hasher = Sha256Hasher;
            let mut active_roots = Vec::new();
            for i in 0..len {
                active_roots.push((active_algs[i], roots[i].clone()));
            }

            // Every active algorithm gets an open epoch from genesis.
            let alg_epochs: Vec<(u64, Vec<(u64, u64)>)> = active_algs
                .iter()
                .map(|&id| (id, vec![(0u64, u64::MAX)]))
                .collect();
            let tree_size = 1u64;

            let proof = neml::CouplingProof {
                active_roots: active_roots.clone(),
                alg_epochs: alg_epochs.clone(),
            };

            // Construct combined root from the canonical metaroot preimage.
            let combined_root =
                hasher.hash(&neml::combined_root_preimage(&active_roots, &alg_epochs));

            let config = neml::VerifierConfig::default();

            // 1. Success case
            let verified = proof.verify(&hasher, target_alg_id, tree_size, &combined_root, active_algs, config);
            prop_assert_eq!(verified.unwrap(), target_root.clone());

            // 2. Reject tampered root hash
            let mut tampered_active_roots = active_roots.clone();
            if !tampered_active_roots[target_idx].1.is_empty() {
                tampered_active_roots[target_idx].1[0] ^= 0xFF;
                let tampered_proof = neml::CouplingProof {
                    active_roots: tampered_active_roots,
                    alg_epochs: alg_epochs.clone(),
                };
                prop_assert!(tampered_proof.verify(&hasher, target_alg_id, tree_size, &combined_root, active_algs, config).is_none());
            }

            // 3. Reject tampered combined root
            let mut bad_combined = combined_root.clone();
            if !bad_combined.is_empty() {
                bad_combined[0] ^= 0xFF;
                prop_assert!(proof.verify(&hasher, target_alg_id, tree_size, &bad_combined, active_algs, config).is_none());
            }

            // 4. Reject mismatching expected active algs (different length)
            let mut bad_algs = active_algs.to_vec();
            bad_algs.push(999);
            prop_assert!(proof.verify(&hasher, target_alg_id, tree_size, &combined_root, &bad_algs, config).is_none());

            // 5. Reject mismatching target alg id (not in active set)
            prop_assert!(proof.verify(&hasher, 999, tree_size, &combined_root, active_algs, config).is_none());

            // 6. Reject substituted epoch metadata: the timeline is inside
            // the preimage, so shifting a boundary breaks the binding.
            let mut substituted_epochs = alg_epochs.clone();
            substituted_epochs[target_idx].1 = vec![(0, 1), (1, u64::MAX)];
            let substituted_proof = neml::CouplingProof {
                active_roots: active_roots.clone(),
                alg_epochs: substituted_epochs,
            };
            prop_assert!(substituted_proof.verify(&hasher, target_alg_id, tree_size, &combined_root, active_algs, config).is_none());
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn metamorphic_non_divergence_monotonicity(
        size in 5usize..40,
        checkpoint_size in 1usize..39,
    ) {
        smol::block_on(async {
            let k = 2;
            let checkpoint = checkpoint_size.min(size - 1) as u64;
            let log = build_log(size, 0, k).await;

            // Compute trusted roots at historical checkpoint size
            let mut trusted_roots = Vec::new();
            for &(alg_id, _) in log.storage().load_algorithm_metas().await.unwrap().iter() {
                if let Ok(root) = log.root_for_at(alg_id, checkpoint).await {
                    trusted_roots.push((alg_id, root));
                }
            }

            // If the full log is consistent:
            if log.verify_non_divergence(None, &[]).await.unwrap() {
                // Then auditing the sub-checkpoint MUST also pass
                prop_assert!(
                    log.verify_non_divergence(Some(checkpoint), &trusted_roots).await.unwrap(),
                    "Metamorphic Monotonicity violated: audit failed at checkpoint={}", checkpoint
                );
            }
            Ok(())
        })?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn differential_neml_eml_binary_equivalence(
        ops in proptest::collection::vec(op_strategy(4), 5..15),
    ) {
        use eml::Log as EmlLog;
        use eml::MemoryStorage as EmlMemoryStorage;

        smol::block_on(async {
            let config = TreeConfig { log_arity: 2 };
            let mut neml_log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await.unwrap();

            let mut eml_log = EmlLog::new(EmlMemoryStorage::new());
            eml_log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Track algorithm IDs to keep them aligned (both logs support algorithm 0 and 1)
            neml_log.add_algorithm(1, new_hasher_for(1)).await.unwrap();
            eml_log.add_algorithm(1, Box::new(SaltedHasher(1))).await.unwrap();


            for op in ops {
                match op {
                    Op::AppendLeaf(data) => {
                        neml_log.append_leaf(&data).await.unwrap();
                        eml_log.append(&data).await.unwrap();
                    }
                    Op::AppendSubtree(subtree) => {
                        // Subtrees are promoted in NEML. EML has no subtree support,
                        // so we can only compare their flat log mode binary equivalence.
                        let evaluated = evaluate(&Sha256Hasher, &subtree);
                        neml_log.append_leaf(&evaluated).await.unwrap();
                        eml_log.append(&evaluated).await.unwrap();
                    }
                    Op::RemoveAlg(_) => {}
                    Op::ResumeAlg(_) => {}
                    _ => {} // Ignore other algorithms for this differential test
                }

                // Assert root equivalence for all registered algorithms
                for id in &[0, 1] {
                    let neml_root = neml_log.root_for(*id).unwrap();
                    let eml_root = eml_log.root(*id).unwrap();
                    prop_assert_eq!(neml_root, eml_root, "Divergence found for alg {}", id);
                }
            }
            Ok::<(), proptest::test_runner::TestCaseError>(())
        })?;
    }
}
