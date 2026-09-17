//! KEY-DERIVED LAYOUT (`[TT20]`/`[TT21]`,
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-tip-tree-gate.md`):
//! the ratified layout, decided by two spikes -- `spike-report.md` and its
//! prototype crate `storage-git-keyed`
//! (`.worktrees/spike-key-layout/storage-git-keyed/`).
//!
//! Claim under test: every stored node and leaf's tree path is EXACTLY the
//! `byte1-be-trim` path of its key (`(alg_id, height, left)` for a node,
//! `index` for a leaf), with no other entries besides the named metadata
//! files -- no peak/child wiring, no decomposition, no opacity bookkeeping.
//!
//! Assumed top-level namespace, taken from the prototype's own layout
//! (`storage-git-keyed/src/build.rs::node_path`/`leaf_path`,
//! `storage-git-keyed/src/lib.rs`'s own `write_batch`): node storage lives
//! under `n`, keyed as `n/<hex16(alg_id)>/<hex2(height)>/<trimmed(left)>`;
//! leaf storage lives under `l`, keyed as `l/<trimmed(index)>`; every other
//! top-level entry (`meta`, and per-algorithm `e`/`r` once an algorithm is
//! registered) is named metadata, never key-fanned-out. If a landed
//! implementation chooses different top-level names, this file's assertions
//! on those two literal names are what would need updating -- the
//! underlying claim they check (every non-metadata entry sits at exactly
//! `trimmed(key)`, nothing stray, no tree over 256 entries) does not depend
//! on the choice of name.
//!
//! RED at 60f93fe: today's layout is peak-wired
//! (`peaks/hex(height,2)/hex(q,2)/...`, `storage-git/src/build.rs::
//! build_peaks`) -- there is no top-level `n` or `l` entry at all, so every
//! lookup below fails outright, and `n_paths`/`l_paths` are computed as
//! empty sets against a nonexistent tree.

mod common;

use std::collections::HashSet;

use common::{WideHasher, hex2, hex16, init_repo, max_tree_width_recursive, trimmed_key_segments};
use gix::hash::Kind as HashKind;
use polydigest::{NaryMerkleLog, Storage, TreeConfig};
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
    let n_paths: HashSet<String> = match common::find_child(repo, tip, "n") {
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

    let l_paths: HashSet<String> = match common::find_child(repo, tip, "l") {
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
/// namespaces (`n`, `l`) and named metadata (`meta`, `e`, `r`) -- an
/// exhaustive allow-list, not a sample.
fn assert_top_level_is_exactly_namespaces_and_metadata(repo: &gix::Repository, tip: gix::ObjectId) {
    let allowed: HashSet<&str> = ["n", "l", "meta", "e", "r"].into_iter().collect();
    for entry in common::read_tree_entries(repo, tip) {
        assert!(
            allowed.contains(entry.name.as_str()),
            "C(n) has an unexpected top-level entry {:?}: only n/l (key-fanned-out storage) and \
             meta/e/r (named metadata) are permitted",
            entry.name
        );
    }
}

/// [KEY-DERIVED LAYOUT] Fixed sequence exercising both namespaces: several
/// leaves (populating `l`), a second algorithm added, removed and resumed
/// across leaf boundaries (populating `n` at more than one height and more
/// than one algorithm, including a merge into an existing peak -- the same
/// shape TT20's completeness property drives), at arity 2.
#[test]
fn nodes_and_leaves_sit_exactly_at_their_derived_key_paths() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/key-layout/staging";
        let git = GitStorage::new(repo.clone(), staging, 2).unwrap();
        let mut log = NaryMerkleLog::new(git, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();

        let mut written = Written::default();
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
            written.leaves.insert(u64::from(i));
        }
        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        for i in 4..7u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
            written.leaves.insert(u64::from(i));
        }
        log.remove_algorithm(0).await.unwrap();
        log.append_leaf(b"leaf-7").await.unwrap();
        written.leaves.insert(7);
        log.resume_algorithm(0).await.unwrap();
        for i in 8..13u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
            written.leaves.insert(u64::from(i));
        }

        // Ground truth for `n`'s expected keys: every `(alg, left, height)`
        // coordinate `frontier_for_size` names at any size this sequence
        // passed through, for every algorithm still (or ever) registered --
        // an independent enumeration of what MUST have been given a digest
        // at some point, not a re-derivation of storage-git's own internal
        // bookkeeping.
        for size in [4u64, 7, 8, 13] {
            for &(left, height) in &spine::frontier_for_size(size, 2) {
                for alg in [0u64, 1] {
                    if log
                        .storage()
                        .get_node(alg, left, height)
                        .await
                        .unwrap()
                        .is_some()
                    {
                        written.nodes.insert((alg, left, height));
                    }
                }
            }
        }

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
            "spike-report.md's byte1-be-trim bound: no tree object may exceed 256 entries, found \
             a tree with {widest}"
        );
    });
}

// `trimmed_key_segments`'s own correctness -- ported test-for-test from
// `storage-git-keyed::pathscheme::tests` -- checked once, here, rather than
// once per `tests/*.rs` binary that pulls in `common`.
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
