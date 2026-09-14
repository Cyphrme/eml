//! Acceptance tests for `docs/specs/storage-git.md` §2's object layout:
//! SG1 (the four top-level entries), SG4 (materialized-vs-opaque node
//! shape), SG5 (entry modes), and the observable consequence of SG6/SG7
//! (canonical, collision-free sibling order).
//!
//! Written from the spec alone: this file never reads `storage-git`'s own
//! tests or the bodies of its private modules (`build.rs`, `read.rs`,
//! `gitutil.rs`, `layout.rs`, `historical.rs`), only its public API
//! (`storage_git::GitStorage`) plus `gix` used directly to inspect the git
//! objects it produces.

#[path = "acceptance_support/mod.rs"]
mod support;

use support::{FixtureHasher, RawEntry, bare_repo, find_entry, hex, new_log, read_tree};

/// [SG1] `C(n)` MUST be a git tree object with exactly the four top-level
/// entries `meta` (blob), `epochs` (tree), `roots` (tree), and `peaks`
/// (tree), present even when empty.
#[test]
fn sg1_checkpoint_tree_has_exactly_four_top_level_entries() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/sg1/staging",
            2,
            FixtureHasher::new(32),
        )
        .await;

        let local = repo.to_thread_local();

        // n = 0: an algorithm has been registered but nothing appended yet.
        let tip0 = support::ref_target(&local, "refs/eml/storage/sg1/staging")
            .expect("staging ref exists once an algorithm is registered");
        assert_top_level_shape(&local, tip0);

        // n > 0, and again after several more appends.
        for i in 0..5u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
            let tip = support::ref_target(&local, "refs/eml/storage/sg1/staging").unwrap();
            assert_top_level_shape(&local, tip);
        }
    });
}

fn assert_top_level_shape(repo: &gix::Repository, tree: gix::ObjectId) {
    let entries = read_tree(repo, tree);
    let mut names: Vec<&str> = entries.iter().map(|e| e.name.as_str()).collect();
    names.sort_unstable();
    assert_eq!(
        names,
        vec!["epochs", "meta", "peaks", "roots"],
        "C(n) must carry exactly meta/epochs/roots/peaks and nothing else, got {names:?}"
    );

    let meta = find_entry(repo, tree, "meta").unwrap();
    assert!(meta.mode.is_blob(), "meta must be a blob");
    let epochs = find_entry(repo, tree, "epochs").unwrap();
    assert!(epochs.mode.is_tree(), "epochs must be a tree");
    let roots = find_entry(repo, tree, "roots").unwrap();
    assert!(roots.mode.is_tree(), "roots must be a tree");
    let peaks = find_entry(repo, tree, "peaks").unwrap();
    assert!(peaks.mode.is_tree(), "peaks must be a tree");
}

/// [SG4] `T(left, 0)` MAY carry a `leaf` blob; `T(left, h > 0)` MAY carry
/// `hex(c, 2)` child entries for `c = 0..k-1`. For a flat log every sealed
/// node is materialized: a height-0 peak MUST carry `leaf` (and no
/// `hex(c,2)` children — those only ever exist at h > 0), and a height-h > 0
/// peak MUST carry all `k` children.
#[test]
fn sg4_flat_log_nodes_are_fully_materialized() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let k = 2u64;
        let mut log = new_log(
            &repo,
            "refs/eml/storage/sg4/staging",
            k,
            FixtureHasher::new(32),
        )
        .await;
        for i in 0..8u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/sg4/staging").unwrap();

        let frontier = spine::frontier_for_size(8, k);
        assert!(!frontier.is_empty());
        for (left, height) in frontier {
            let peak = resolve_peak(&local, tip, left, height, k);
            let node_entries = read_tree(&local, peak);
            if height == 0 {
                assert!(
                    node_entries.iter().any(|e| e.name == "leaf"),
                    "T({left},0) must carry a materialized leaf blob (flat log)"
                );
                assert!(
                    !node_entries
                        .iter()
                        .any(|e| e.name.len() == 2 && u8::from_str_radix(&e.name, 16).is_ok()),
                    "T({left},0) must not carry hex(c,2) children"
                );
            } else {
                for c in 0..k {
                    assert!(
                        node_entries.iter().any(|e| e.name == hex(c, 2)),
                        "T({left},{height}) must carry materialized child hex({c},2)"
                    );
                }
                assert!(
                    !node_entries.iter().any(|e| e.name == "leaf"),
                    "an internal node (h>0) must never carry a leaf blob"
                );
            }
            assert!(
                node_entries.iter().any(|e| e.name == "digest"),
                "T({left},{height}) must carry a digest/ subtree"
            );
        }
    });
}

/// Resolve a peak `T(left, height)`'s tree object id by walking
/// `peaks/hex(j,2)/hex(q,2)` per §2.4/§2.1 — `q` is the peak's left-to-right
/// ordinal among same-height peaks, taken from `frontier_for_size`'s own
/// order (SG2).
fn resolve_peak(
    repo: &gix::Repository,
    tip: gix::ObjectId,
    left: u64,
    height: u32,
    k: u64,
) -> gix::ObjectId {
    let n_hint = left + k.pow(height); // any size at least covering this peak resolves the same sealed node
    let frontier = spine::frontier_for_size(n_hint, k);
    let same_height: Vec<u64> = frontier
        .iter()
        .filter(|&&(_, h)| h == height)
        .map(|&(l, _)| l)
        .collect();
    let q = same_height
        .iter()
        .position(|&l| l == left)
        .expect("peak must appear in its own covering frontier");
    let path = format!("peaks/{}/{}", hex(height as u64, 2), hex(q as u64, 2));
    support::resolve_path(repo, tip, &path)
        .unwrap_or_else(|| panic!("no entry at {path}"))
        .oid
}

/// [SG5] Every blob entry uses mode `100644`; every tree entry uses mode
/// `40000`; nothing this layer writes is ever a symlink or a gitlink.
#[test]
fn sg5_entry_modes_are_canonical_blob_and_tree() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/sg5/staging",
            3,
            FixtureHasher::new(32),
        )
        .await;
        log.add_algorithm(7, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();
        for i in 0..11u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/sg5/staging").unwrap();
        assert_modes_recursive(&local, tip);
    });
}

fn assert_modes_recursive(repo: &gix::Repository, tree: gix::ObjectId) {
    for entry in read_tree(repo, tree) {
        assert!(
            !entry.mode.is_link(),
            "{}: must never be a symlink",
            entry.name
        );
        assert!(
            !entry.mode.is_commit(),
            "{}: must never be a gitlink",
            entry.name
        );
        if entry.mode.is_tree() {
            assert_eq!(
                entry.mode.value(),
                0o40000,
                "{}: tree entry must use mode 40000",
                entry.name
            );
            assert_modes_recursive(repo, entry.oid);
        } else {
            assert_eq!(
                entry.mode.value(),
                0o100644,
                "{}: blob entry must use mode 100644",
                entry.name
            );
        }
    }
}

/// Observable consequence of [SG6]/[SG7]: every sibling group this layer
/// writes is byte-lexicographically sorted in git's own canonical order, and
/// no name collides with or prefixes a sibling's. `storage-git`'s internal
/// tree-builder (the function SG7 actually names) is a private
/// implementation detail this suite has no access to (its bodies are
/// off-limits by dispatch), so this test checks the artifact SG7 exists to
/// protect — every tree this layer ever produced, walked recursively — not
/// SG7's own release-mode-only failure mode against a deliberately
/// unsorted input, which requires calling the private builder directly.
#[test]
fn sg6_sg7_sibling_entries_are_canonically_sorted() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let mut log = new_log(
            &repo,
            "refs/eml/storage/sg6/staging",
            4,
            FixtureHasher::new(32),
        )
        .await;
        log.add_algorithm(1, Box::new(FixtureHasher::new(16)))
            .await
            .unwrap();
        for i in 0..23u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, "refs/eml/storage/sg6/staging").unwrap();
        assert_sorted_recursive(&local, tip);
    });
}

fn assert_sorted_recursive(repo: &gix::Repository, tree: gix::ObjectId) {
    let entries = read_tree(repo, tree);
    for pair in entries.windows(2) {
        let (a, b): (&RawEntry, &RawEntry) = (&pair[0], &pair[1]);
        let order = gix::objs::tree::name_order(
            a.name.as_bytes(),
            a.mode.is_tree(),
            b.name.as_bytes(),
            b.mode.is_tree(),
        );
        assert_eq!(
            order,
            std::cmp::Ordering::Less,
            "sibling '{}' must sort strictly before '{}' in git's canonical order (SG6/SG7)",
            a.name,
            b.name
        );
    }
    for entry in entries {
        if entry.mode.is_tree() {
            assert_sorted_recursive(repo, entry.oid);
        }
    }
}
