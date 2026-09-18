//! KEY-DERIVED LAYOUT: the layout documented in
//! `docs/specs/storage-git.md` §2.1.
//!
//! Claim under test: every stored node and leaf's tree path is EXACTLY the
//! `byte1-be-trim` path of its key (`(alg_id, height, left)` for a node,
//! `index` for a leaf), with no other entries besides the named metadata
//! files -- no peak/child wiring, no decomposition, no opacity bookkeeping.
//!
//! Top-level namespace, matching `storage-git/src/layout.rs`'s own
//! `TOP_LEVEL_*` constants: node storage lives under `nodes`, keyed as
//! `nodes/<hex16(alg_id)>/<hex2(height)>/<trimmed(left)>`; leaf storage
//! lives under `leaves`, keyed as `leaves/<trimmed(index)>`; every other
//! top-level entry (`meta`, and per-algorithm `epochs` once an algorithm is
//! registered) is named metadata, never key-fanned-out. There is no
//! `roots` entry at any point in a log's life: a per-algorithm root is an
//! index over this layer's own data, which belongs at the application
//! layer, not here (head's ruling, 2026-09-17).

mod common;

use std::collections::HashSet;

use common::{WideHasher, hex2, hex16, init_repo, max_tree_width_recursive, trimmed_key_segments};
use gix::hash::Kind as HashKind;
use polydigest::{NaryMerkleLog, TreeConfig};
use storage_git::GitStorage;

/// Every leaf index and `(alg_id, left, height)` node coordinate a driven
/// sequence wrote, tracked independently of the layout under test -- the
/// ground truth `assert_layout_matches_written_keys` checks the real git
/// tree against.
#[derive(Default)]
struct Written {
    leaves: HashSet<u64>,
    nodes: HashSet<(u64, u64, u32)>,
}

fn expected_node_path(alg_id: u64, left: u64, height: u32) -> String {
    let mut segs = vec![hex16(alg_id), hex2(height)];
    segs.extend(common::trimmed_key_segments(left));
    segs.join("/")
}

fn expected_leaf_path(index: u64) -> String {
    trimmed_key_segments(index).join("/")
}

/// The single assertion this file exists to make: the exact set of `/`-
/// joined paths under `n` (resp. `l`) equals the exact set of derived paths
/// for every node (resp. leaf) coordinate `written` names -- catching a
/// missing entry, a stray entry, and a misplaced (non-`trimmed`) entry all
/// at once, since any of the three breaks set equality.
fn assert_layout_matches_written_keys(
    repo: &gix::Repository,
    tip: gix::ObjectId,
    written: &Written,
) {
    let n_paths: HashSet<String> = match common::find_child(repo, tip, "nodes") {
        Some(n) => common::enumerate_full_paths(repo, n.oid),
        None => HashSet::new(),
    };
    let expected_n_paths: HashSet<String> = written
        .nodes
        .iter()
        .map(|&(alg, left, height)| expected_node_path(alg, left, height))
        .collect();
    assert_eq!(
        n_paths,
        expected_n_paths,
        "n/ entries diverge from the exact set of byte1-be-trim key paths for every node \
         coordinate written -- missing: {:?}, stray: {:?}",
        expected_n_paths.difference(&n_paths).collect::<Vec<_>>(),
        n_paths.difference(&expected_n_paths).collect::<Vec<_>>()
    );

    let l_paths: HashSet<String> = match common::find_child(repo, tip, "leaves") {
        Some(l) => common::enumerate_full_paths(repo, l.oid),
        None => HashSet::new(),
    };
    let expected_l_paths: HashSet<String> = written
        .leaves
        .iter()
        .map(|&index| expected_leaf_path(index))
        .collect();
    assert_eq!(
        l_paths,
        expected_l_paths,
        "l/ entries diverge from the exact set of byte1-be-trim key paths for every leaf index \
         written -- missing: {:?}, stray: {:?}",
        expected_l_paths.difference(&l_paths).collect::<Vec<_>>(),
        l_paths.difference(&expected_l_paths).collect::<Vec<_>>()
    );
}

/// No entry at the top level of `C(n)` besides the two key-fanned-out
/// namespaces (`nodes`, `leaves`) and named metadata (`meta`, `epochs`) --
/// an exhaustive allow-list, not a sample. `roots` is deliberately absent
/// from this list: no tree this layer commits ever carries one (head's
/// ruling, 2026-09-17).
fn assert_top_level_is_exactly_namespaces_and_metadata(repo: &gix::Repository, tip: gix::ObjectId) {
    let allowed: HashSet<&str> = ["nodes", "leaves", "meta", "epochs"].into_iter().collect();
    for entry in common::read_tree_entries(repo, tip) {
        assert!(
            allowed.contains(entry.name.as_str()),
            "C(n) has an unexpected top-level entry {:?}: only nodes/leaves (key-fanned-out \
             storage) and meta/epochs (named metadata) are permitted",
            entry.name
        );
    }
}

/// [KEY-DERIVED LAYOUT] Fixed sequence exercising both namespaces: several
/// leaves (populating `l`), a second algorithm added, removed and resumed
/// across leaf boundaries (populating `n` at more than one height and more
/// than one algorithm, including a merge into an existing peak), at arity 2.
///
/// [finding 6] The expected key set is derived from an INDEPENDENT
/// `MemoryStorage` oracle driven through the identical operation sequence,
/// never from querying the `GitStorage` instance under test -- deriving
/// "what should exist" from the same backend the assertion is about would
/// make a dropped node invisible to both sides of the comparison at once (a
/// node `GitStorage` silently drops is a node this file would then never
/// expect to find either, since the old query-the-backend-under-test
/// approach could only ever notice a key it itself believes it holds).
/// `MemoryStorage` never drops a node it is given, so `mem.leaves`/
/// `mem.nodes` are the ground truth for every key that MUST exist,
/// independent of whatever `GitStorage` actually did with it.
#[test]
fn nodes_and_leaves_sit_exactly_at_their_derived_key_paths() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/key-layout/staging";
        let git = GitStorage::new(repo.clone(), staging, 2).unwrap();
        let mut log = NaryMerkleLog::new(git, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        let mut mem_log = NaryMerkleLog::new(
            polydigest::MemoryStorage::new(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();

        for i in 0..4u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            log.append_leaf(&leaf).await.unwrap();
            mem_log.append_leaf(&leaf).await.unwrap();
        }
        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        mem_log
            .add_algorithm(1, Box::new(WideHasher))
            .await
            .unwrap();
        for i in 4..7u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            log.append_leaf(&leaf).await.unwrap();
            mem_log.append_leaf(&leaf).await.unwrap();
        }
        log.remove_algorithm(0).await.unwrap();
        mem_log.remove_algorithm(0).await.unwrap();
        log.append_leaf(b"leaf-7").await.unwrap();
        mem_log.append_leaf(b"leaf-7").await.unwrap();
        log.resume_algorithm(0).await.unwrap();
        mem_log.resume_algorithm(0).await.unwrap();
        for i in 8..13u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            log.append_leaf(&leaf).await.unwrap();
            mem_log.append_leaf(&leaf).await.unwrap();
        }

        assert_eq!(
            log.size(),
            mem_log.size(),
            "fixture sanity: git and memory must agree on size before deriving the oracle"
        );

        // Ground truth, straight from the independent MemoryStorage oracle's
        // own fields -- never from asking GitStorage what it thinks it holds.
        let written = Written {
            leaves: (0..mem_log.storage().leaves.len() as u64).collect(),
            nodes: mem_log.storage().nodes.keys().copied().collect(),
        };

        let local = repo.to_thread_local();
        let tip = local
            .try_find_reference(staging)
            .unwrap()
            .unwrap()
            .peel_to_id()
            .unwrap()
            .detach();

        assert_top_level_is_exactly_namespaces_and_metadata(&local, tip);
        assert_layout_matches_written_keys(&local, tip, &written);

        let widest = max_tree_width_recursive(&local, tip);
        assert!(
            widest <= 256,
            "SG2's byte1-be-trim bound (docs/specs/storage-git.md §2.1): no tree object may \
             exceed 256 entries, found a tree with {widest}"
        );
    });
}

// `trimmed_key_segments`'s own correctness -- checked once, here, rather
// than once per `tests/*.rs` binary that pulls in `common`.
#[cfg(test)]
mod trimmed_key_segments_tests {
    use crate::common::trimmed_key_segments;

    #[test]
    fn trimmed_shrinks_path_for_small_keys() {
        assert_eq!(trimmed_key_segments(0), vec!["1", "00"]);
        assert_eq!(trimmed_key_segments(0xab), vec!["1", "ab"]);
        assert_eq!(trimmed_key_segments(0x0100), vec!["2", "01", "00"]);
        assert_eq!(
            trimmed_key_segments(u64::MAX),
            vec!["8", "ff", "ff", "ff", "ff", "ff", "ff", "ff", "ff"]
        );
    }

    #[test]
    fn trimmed_length_segment_prevents_cross_length_collision() {
        assert_ne!(trimmed_key_segments(1)[0], trimmed_key_segments(256)[0]);
    }

    #[test]
    fn every_key_round_trips_to_a_distinct_path() {
        let mut seen = std::collections::HashSet::new();
        for k in [0u64, 1, 2, 255, 256, 65535, 65536, 1_000_000, u64::MAX] {
            let p = trimmed_key_segments(k);
            assert!(seen.insert(p.clone()), "key {k} collided with path {p:?}");
        }
    }
}
