//! Acceptance tests for `docs/specs/storage-git.md` §2's object layout:
//! SG5 (entry modes) and the observable consequence of SG6/SG7 (canonical,
//! collision-free sibling order).
//!
//! Retired from this file: SG1's "exactly four top-level entries, one of
//! them `peaks`" and SG4's materialized-vs-opaque node shape, both
//! navigated via `peaks/hex(height,2)/hex(q,2)/...` (`resolve_peak`, below
//! no longer), encode the peak-and-children hierarchy the ratified
//! key-derived layout ("THE DESIGN", `spike-report.md` and its prototype
//! `storage-git-keyed/`) eliminates outright ("no peak/child wiring, no
//! decomposition, no opacity bookkeeping anywhere") -- there is no `peaks/`
//! tree to navigate under that design, and no materialized/opaque
//! distinction left to assert, so both tests would need this file's own
//! entire premise rewritten, not patched. `key_derived_layout.rs`'s
//! `nodes_and_leaves_sit_exactly_at_their_derived_key_paths` supersedes
//! SG1's top-level-shape claim with the new design's own (an exhaustive
//! allow-list over `n`/`l`/`meta`/`e`/`r`), and the completeness property
//! (`completeness_property.rs`) supersedes SG4's "every digest given is
//! present" concern with a stronger, MemoryStorage-backed oracle rather
//! than a peak-shape inspection.
//!
//! Written from the spec alone: this file never reads `storage-git`'s own
//! tests or the bodies of its private modules (`build.rs`, `read.rs`,
//! `gitutil.rs`, `layout.rs`, `historical.rs`), only its public API
//! (`storage_git::GitStorage`) plus `gix` used directly to inspect the git
//! objects it produces.

#[path = "acceptance_support/mod.rs"]
mod support;

use support::{FixtureHasher, RawEntry, bare_repo, new_log, read_tree};

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
/// implementation detail this suite deliberately never reads, so this test
/// checks the artifact SG7 exists to
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
