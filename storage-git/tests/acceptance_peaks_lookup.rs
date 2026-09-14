//! Acceptance tests for §2.1's peak index (SG2) and §2.4's position-lookup
//! algorithm (SG8), from `docs/specs/storage-git.md` alone.

#[path = "acceptance_support/mod.rs"]
mod support;

use std::collections::BTreeMap;

use polydigest::Storage;
use support::{FixtureHasher, bare_repo, find_entry, hex, new_log, new_memory_log, read_tree};

/// [SG2] For each base-`k` digit position `j` with nonzero digit `d_j`,
/// `peaks/hex(j, 2)` MUST exist and contain exactly `d_j` entries named
/// `hex(0, 2)` through `hex(d_j - 1, 2)`; no `peaks/hex(j, 2)` MUST exist for
/// a zero digit. The peak set derived from `peaks/` MUST equal
/// `frontier_for_size(n, k)`.
#[test]
fn sg2_peaks_index_matches_frontier_for_size() {
    smol::block_on(async {
        for k in [2u64, 3, 5] {
            let dir = tempfile::tempdir().unwrap();
            let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
            let staging = format!("refs/eml/storage/sg2-k{k}/staging");
            let mut log = new_log(&repo, &staging, k, FixtureHasher::new(32)).await;
            let local = repo.to_thread_local();

            for n in 0..40u64 {
                let tip = support::ref_target(&local, &staging).unwrap();
                assert_peaks_match_frontier(&local, tip, n, k);
                log.append_leaf(format!("leaf-{n}").as_bytes())
                    .await
                    .unwrap();
            }
        }
    });
}

fn assert_peaks_match_frontier(repo: &gix::Repository, tip: gix::ObjectId, n: u64, k: u64) {
    let frontier = spine::frontier_for_size(n, k);
    let mut by_height: BTreeMap<u32, Vec<u64>> = BTreeMap::new();
    for (left, height) in frontier {
        by_height.entry(height).or_default().push(left);
    }

    let peaks_tree = find_entry(repo, tip, "peaks").expect("peaks/ present").oid;
    let height_groups = read_tree(repo, peaks_tree);

    let mut present_heights: Vec<u32> = height_groups
        .iter()
        .map(|e| u32::from_str_radix(&e.name, 16).expect("hex(j,2) name"))
        .collect();
    present_heights.sort_unstable();
    let mut expected_heights: Vec<u32> = by_height.keys().copied().collect();
    expected_heights.sort_unstable();
    assert_eq!(
        present_heights, expected_heights,
        "n={n}, k={k}: peaks/ height groups must equal frontier_for_size's heights"
    );

    for (height, lefts) in &by_height {
        let group_name = hex(*height as u64, 2);
        let group = find_entry(repo, peaks_tree, &group_name)
            .unwrap_or_else(|| panic!("n={n}, k={k}: missing peaks/{group_name}"));
        let ordinals = read_tree(repo, group.oid);
        assert_eq!(
            ordinals.len(),
            lefts.len(),
            "n={n}, k={k}: peaks/{group_name} must contain exactly d_{height} = {} entries",
            lefts.len()
        );
        for q in 0..lefts.len() as u64 {
            let name = hex(q, 2);
            assert!(
                ordinals.iter().any(|e| e.name == name),
                "n={n}, k={k}: peaks/{group_name} must contain ordinal {name} (0..d_j-1)"
            );
        }
    }
}

/// [SG8] For every valid `(n, i)`, the value at the position-lookup path
/// derived from `frontier_for_size` and base-`k` digit descent MUST match an
/// independent, non-git reference implementation's (`MemoryStorage`) value
/// for the same `(n, i)` — leaves and every sealed node digest.
#[test]
fn sg8_position_lookup_matches_memory_storage_reference() {
    smol::block_on(async {
        for k in [2u64, 3, 4] {
            let dir = tempfile::tempdir().unwrap();
            let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
            let staging = format!("refs/eml/storage/sg8-k{k}/staging");
            let mut git_log = new_log(&repo, &staging, k, FixtureHasher::new(32)).await;
            let mut mem_log = new_memory_log(k, FixtureHasher::new(32)).await;

            let n_max = 30u64;
            for n in 0..n_max {
                let leaf = format!("leaf-{n}").into_bytes();
                git_log.append_leaf(&leaf).await.unwrap();
                mem_log.append_leaf(&leaf).await.unwrap();

                // Every leaf appended so far must read back identically.
                for i in 0..=n {
                    let git_leaf = git_log.storage().get_leaf(i).await.unwrap();
                    let mem_leaf = mem_log.storage().get_leaf(i).await.unwrap();
                    assert_eq!(
                        git_leaf,
                        mem_leaf,
                        "k={k}, n={}, i={i}: get_leaf mismatch",
                        n + 1
                    );
                }

                // Sweep every *aligned* (alg_id, left, height) coordinate — a
                // `T(left, height)` node is only ever created at a `left`
                // that is a multiple of `k^height` (the carry's own
                // reduction schedule; §2.4's descent likewise only ever
                // reaches aligned children) — and require agreement
                // (Some == Some with equal bytes, or both None).
                let cur = n + 1;
                for alg_id in [0u64] {
                    for height in 0..6u32 {
                        let cap = k.pow(height);
                        let mut left = 0u64;
                        while left <= cur {
                            let git_node = git_log
                                .storage()
                                .get_node(alg_id, left, height)
                                .await
                                .unwrap();
                            let mem_node = mem_log
                                .storage()
                                .get_node(alg_id, left, height)
                                .await
                                .unwrap();
                            assert_eq!(
                                git_node, mem_node,
                                "k={k}, n={cur}, alg={alg_id}, left={left}, height={height}: \
                                 get_node mismatch"
                            );
                            left += cap;
                        }
                    }
                }
            }
        }
    });
}
