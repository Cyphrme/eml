//! Pins the ruling (2026-09-16) that a **resumed** log appends ordinary
//! leaves going forward, storing their real bytes exactly as a flat log
//! does -- never the same-digest, no-bytes subtree shortcut
//! (`polydigest::NaryMerkleLog::resume`'s own doc, `polydigest/src/tree.rs:
//! 110-122`, already describes the result as "a committed frontier you
//! append real leaves onto"). This crate-level half checks the two defects
//! the shortcut produces once storage-git is in the loop:
//!
//! 1. `append_leaf` on a resumed log must succeed and stay in parity with `MemoryStorage`,
//!    node-for-node and leaf-for-leaf (the polydigest-level half of this same claim lives in
//!    `polydigest/tests/resume_forward_leaves.rs`; this file is the storage-git-specific half).
//! 2. Independent of (1) and already reproducible today with `polydigest`/`storage-git` alone (no
//!    `append_leaf` involved): a node created and folded away *within the very same write* -- which
//!    a chained (double) resume triggers -- is never persisted anywhere in `storage-git`'s object
//!    layout, unlike `MemoryStorage`, which never drops a node it was given.
//! 3. The storage-cost consequence of the shortcut: `inherited/`'s archive of superseded opaque
//!    peaks must stay bounded by the sealed frontier's own peak count, not grow with the number of
//!    forward appends.

mod common;

use std::collections::HashSet;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig, frontier_for_size};
use proptest::prelude::*;
use storage_git::GitStorage;

// ============================================================================
// 1. Ordinary `append_leaf` onto a resumed log, differentially against `MemoryStorage` -- size,
//    root, every historical frontier coordinate, and every forward leaf's own bytes.
// ============================================================================

/// Seal a fresh `n`-leaf, arity-`k` `GitStorage` log and return `(sealed,
/// tmpdir)` -- the tmpdir must outlive every read from the sealed log's own
/// repository, so the caller holds it until done.
async fn seal_git(n: u64, k: u64, ref_name: &str) -> polydigest::Sealed {
    let (_dir, repo) = init_repo(HashKind::Sha1);
    let git = GitStorage::new(repo, ref_name, k).unwrap();
    let mut log = NaryMerkleLog::new(git, Box::new(WideHasher), TreeConfig { arity: k })
        .await
        .unwrap();
    for i in 0..n {
        log.append_leaf(format!("orig-{i}").as_bytes())
            .await
            .unwrap();
    }
    log.seal().await.unwrap()
}

/// Same as [`seal_git`], over `MemoryStorage`, so both backends seal the
/// identical entry sequence.
async fn seal_mem(n: u64, k: u64) -> polydigest::Sealed {
    let mut log = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(WideHasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    for i in 0..n {
        log.append_leaf(format!("orig-{i}").as_bytes())
            .await
            .unwrap();
    }
    log.seal().await.unwrap()
}

/// Resume `sealed` onto a fresh `GitStorage` in a brand-new repository, then
/// append `m` ordinary forward leaves via `append_leaf`, asserting parity
/// against an identically-resumed `MemoryStorage` log after every step:
/// size, `root_for(0)`, every coordinate either backend's frontier has ever
/// named, and every forward leaf's own bytes via `get_leaf`.
///
/// Swept across a single-peak seed (`n=4,k=2`) and a multi-peak seed
/// (`n=5,k=2`, crossing a peak merge partway through the forward run) by the
/// two `#[test]`s below.
async fn resumed_ordinary_append_matches_memory(n: u64, k: u64, m: u64, ref_name: &str) {
    let git_sealed = seal_git(n, k, &format!("{ref_name}/src")).await;
    let mem_sealed = seal_mem(n, k).await;

    let (_dir, repo) = init_repo(HashKind::Sha1);
    let git_storage = GitStorage::new(repo, format!("{ref_name}/dst"), k).unwrap();
    let mut git_log =
        NaryMerkleLog::resume(&git_sealed, git_storage, vec![(0, Box::new(WideHasher))])
            .await
            .expect("resume onto fresh git storage never fails for a well-formed Sealed");
    let mut mem_log = NaryMerkleLog::resume(
        &mem_sealed,
        MemoryStorage::new(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .expect("resume onto fresh memory storage never fails for a well-formed Sealed");

    let mut coord_history: HashSet<(u64, u32)> = frontier_for_size(n, k).into_iter().collect();

    for i in 0..m {
        let bytes = format!("fwd-{i}").into_bytes();
        git_log
            .append_leaf(&bytes)
            .await
            .expect("append_leaf must succeed on a resumed GitStorage log");
        mem_log
            .append_leaf(&bytes)
            .await
            .expect("append_leaf must succeed on a resumed MemoryStorage log");

        assert_eq!(
            git_log.count(),
            mem_log.count(),
            "count diverged after forward leaf {i}"
        );
        assert_eq!(
            git_log.root_for(0).ok(),
            mem_log.root_for(0).ok(),
            "root_for(0) diverged after forward leaf {i}"
        );

        coord_history.extend(frontier_for_size(git_log.count(), k));
        for &(left, height) in &coord_history {
            let g = git_log.storage().get_node(0, left, height).await.unwrap();
            let mm = mem_log.storage().get_node(0, left, height).await.unwrap();
            assert_eq!(
                g, mm,
                "get_node(alg=0, left={left}, height={height}) diverged after forward leaf {i}"
            );
        }
    }

    for i in 0..m {
        let idx = n + i;
        let expected = format!("fwd-{i}").into_bytes();
        let g = git_log.storage().get_leaf(idx).await;
        let mm = mem_log.storage().get_leaf(idx).await;
        assert_eq!(
            g.as_deref().ok(),
            mm.as_deref().ok(),
            "get_leaf({idx}) diverged between git and mem"
        );
        assert_eq!(
            g.unwrap(),
            expected,
            "get_leaf({idx}) must return the forward entry's own bytes"
        );
    }
}

/// Single-peak resume (`frontier_for_size(4,2)` has exactly one coordinate).
#[test]
fn resumed_ordinary_leaf_append_matches_memory_single_peak() {
    smol::block_on(async {
        assert_eq!(frontier_for_size(4, 2).len(), 1, "fixture sanity");
        resumed_ordinary_append_matches_memory(4, 2, 3, "refs/eml/storage/resume-leaf/single")
            .await;
    });
}

/// Multi-peak resume (`frontier_for_size(5,2)` has two coordinates), so the
/// merge a single-peak seed cannot trigger is covered too.
#[test]
fn resumed_ordinary_leaf_append_matches_memory_multi_peak() {
    smol::block_on(async {
        assert_eq!(frontier_for_size(5, 2).len(), 2, "fixture sanity");
        resumed_ordinary_append_matches_memory(5, 2, 3, "refs/eml/storage/resume-leaf/multi").await;
    });
}

// ============================================================================
// 2. GB71: a node created and folded away within one write is lost by storage-git, independent of
//    the append_leaf guard above -- reproduced with `append_subtree` alone (today's only working
//    forward-append path on a resumed log), via a *double* resume: seal, resume, append to size 3,
//    reseal from that live frontier, resume a second instance, append once more to size 4.
//    `MemoryStorage` never drops a node it was given, so it is the parity oracle this test's every
//    assertion is checked against.
// ============================================================================

/// The double-resume GB71 sequence, applied identically to a git-backed and
/// a memory-backed log; returns `(git_log, mem_log)` for the caller to
/// assert against. `_dirs` must be named (not `_`) by the caller so the
/// temporary repositories outlive the reads.
async fn run_gb71_sequence() -> (
    NaryMerkleLog<GitStorage>,
    NaryMerkleLog<MemoryStorage>,
    Vec<tempfile::TempDir>,
) {
    let mut dirs = Vec::new();
    let k = 2u64;

    // Stage 0: a two-leaf log, sealed (one peak).
    let (dir0, repo0) = init_repo(HashKind::Sha1);
    dirs.push(dir0);
    let git0 = GitStorage::new(repo0, "refs/eml/storage/gb71/0", k).unwrap();
    let mut git_log0 = NaryMerkleLog::new(git0, Box::new(WideHasher), TreeConfig { arity: k })
        .await
        .unwrap();
    let mut mem_log0 = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(WideHasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    for data in [b"a".as_slice(), b"b".as_slice()] {
        git_log0.append_leaf(data).await.unwrap();
        mem_log0.append_leaf(data).await.unwrap();
    }
    let git_sealed0 = git_log0.seal().await.unwrap();
    let mem_sealed0 = mem_log0.seal().await.unwrap();

    // Stage 1: resume, append a subtree to size 3 (two peaks: (0,1) and
    // (2,0)), reseal from that live frontier.
    let (dir1, repo1) = init_repo(HashKind::Sha1);
    dirs.push(dir1);
    let git1 = GitStorage::new(repo1, "refs/eml/storage/gb71/1", k).unwrap();
    let mut git_log1 = NaryMerkleLog::resume(&git_sealed0, git1, vec![(0, Box::new(WideHasher))])
        .await
        .unwrap();
    let mut mem_log1 = NaryMerkleLog::resume(
        &mem_sealed0,
        MemoryStorage::new(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .unwrap();
    git_log1
        .append_subtree(&Subtree::Leaf(b"c".to_vec()))
        .await
        .unwrap();
    mem_log1
        .append_subtree(&Subtree::Leaf(b"c".to_vec()))
        .await
        .unwrap();
    assert_eq!(
        frontier_for_size(3, k).len(),
        2,
        "fixture sanity: size 3 has two peaks"
    );
    let git_sealed1 = git_log1.seal().await.unwrap();
    let mem_sealed1 = mem_log1.seal().await.unwrap();

    // Stage 2: resume a SECOND instance, append once more to size 4 (merges
    // both peaks into one; the newly appended leaf's own node at
    // (left=3, height=0) is created and folded away within this one write).
    let (dir2, repo2) = init_repo(HashKind::Sha1);
    dirs.push(dir2);
    let git2 = GitStorage::new(repo2, "refs/eml/storage/gb71/2", k).unwrap();
    let mut git_log2 = NaryMerkleLog::resume(&git_sealed1, git2, vec![(0, Box::new(WideHasher))])
        .await
        .unwrap();
    let mut mem_log2 = NaryMerkleLog::resume(
        &mem_sealed1,
        MemoryStorage::new(),
        vec![(0, Box::new(WideHasher))],
    )
    .await
    .unwrap();
    git_log2
        .append_subtree(&Subtree::Leaf(b"d".to_vec()))
        .await
        .unwrap();
    mem_log2
        .append_subtree(&Subtree::Leaf(b"d".to_vec()))
        .await
        .unwrap();
    assert_eq!(git_log2.count(), 4);
    assert_eq!(mem_log2.count(), 4);

    (git_log2, mem_log2, dirs)
}

/// GB71: `get_node(0, 3, 0)` -- the just-appended leaf's own coordinate --
/// must read back identically on both backends. Quoted in the dispatch: at
/// the base tip this reproduces as `git=None, mem=Some(_)`.
#[test]
fn gb71_new_leaf_node_folded_away_within_one_write_matches_memory() {
    smol::block_on(async {
        let (git_log, mem_log, _dirs) = run_gb71_sequence().await;
        let g = git_log.storage().get_node(0, 3, 0).await.unwrap();
        let m = mem_log.storage().get_node(0, 3, 0).await.unwrap();
        assert_eq!(
            g, m,
            "get_node(alg=0, left=3, height=0) diverged: git={g:?} mem={m:?}"
        );
    });
}

/// GB71: a consistency proof from the pre-merge size (3) to the post-merge
/// size (4) must succeed on both backends alike. Quoted in the dispatch: at
/// the base tip `storage-git` errors with `CorruptedMetadata` naming the
/// same missing coordinate.
#[test]
fn gb71_consistency_proof_across_the_merge_matches_memory() {
    smol::block_on(async {
        let (git_log, mem_log, _dirs) = run_gb71_sequence().await;
        let g = git_log.consistency_proof_for(0, 3, 4).await;
        let m = mem_log.consistency_proof_for(0, 3, 4).await;
        match (&g, &m) {
            (Ok(gv), Ok(mv)) => assert_eq!(
                gv.is_some(),
                mv.is_some(),
                "consistency_proof_for(0,3,4) presence diverged"
            ),
            _ => panic!("consistency_proof_for(0,3,4) success diverged: git={g:?} mem={m:?}"),
        }
    });
}

// ============================================================================
// 3. Storage-cost property: after a resume from a `k`-peak seal followed by `m` forward leaf
//    appends, `inherited/`'s archive holds at most `k` entries and does not grow with `m` --
//    forward nodes are recomputable, not archived. Measured directly off the checkpoint tree's own
//    `inherited/` section through public `gix` reads (never this crate's private `gitutil`), so the
//    count reflects exactly what a stranger reading the repository would see.
// ============================================================================

/// Count every leaf entry under `tree`'s `inherited/hex(height,2)/
/// hex(left,16)` section (§Departure 3 amendment, `storage-git/src/build.rs`
/// `build_inherited`), or 0 if the checkpoint carries no `inherited/` at
/// all.
fn count_inherited_entries(repo: &gix::Repository, tree: gix::ObjectId) -> usize {
    let Ok(top) = repo.find_tree(tree) else {
        return 0;
    };
    let Some(inherited_entry) = top
        .decode()
        .unwrap()
        .entries
        .iter()
        .find(|e| e.filename == "inherited")
        .map(|e| e.oid.to_owned())
    else {
        return 0;
    };
    let inherited_tree = repo.find_tree(inherited_entry).unwrap();
    let mut count = 0usize;
    for height_entry in &inherited_tree.decode().unwrap().entries {
        let sub = repo.find_tree(height_entry.oid).unwrap();
        count += sub.decode().unwrap().entries.len();
    }
    count
}

/// After resuming from a `k`-peak seal and appending `m` ordinary forward
/// leaves, `inherited/`'s entry count must never exceed `k` and must be the
/// same at `m` as it was at `m=1` (it does not grow with `m`). A malformed
/// version looks exactly like today's: every forward "leaf" (actually a
/// same-digest opaque subtree, since `append_leaf` itself is refused) that
/// is later superseded by a merge adds its own permanent `inherited/` entry,
/// so the count grows roughly linearly in `m` instead of staying flat.
fn assert_inherited_bounded_by_peaks(n: u64, k: u64, peaks: usize, m: u64, ref_name: &str) {
    smol::block_on(async {
        let (_src_dir, src_repo) = init_repo(HashKind::Sha1);
        let git_src = GitStorage::new(src_repo, format!("{ref_name}/src"), k).unwrap();
        let mut src_log =
            NaryMerkleLog::new(git_src, Box::new(WideHasher), TreeConfig { arity: k })
                .await
                .unwrap();
        for i in 0..n {
            src_log
                .append_leaf(format!("orig-{i}").as_bytes())
                .await
                .unwrap();
        }
        assert_eq!(
            frontier_for_size(n, k).len(),
            peaks,
            "fixture sanity: n={n},k={k} must resume to {peaks} peaks"
        );
        let sealed = src_log.seal().await.unwrap();

        let (dst_dir, dst_repo) = init_repo(HashKind::Sha1);
        let dst_repo_local = dst_repo.to_thread_local();
        let git_dst = GitStorage::new(dst_repo, format!("{ref_name}/dst"), k).unwrap();
        let mut log = NaryMerkleLog::resume(&sealed, git_dst, vec![(0, Box::new(WideHasher))])
            .await
            .unwrap();

        let mut counts = Vec::with_capacity(m as usize);
        for i in 0..m {
            log.append_leaf(format!("fwd-{i}").as_bytes())
                .await
                .expect("append_leaf must succeed on the resumed log");
            let tree = log.storage().tree_at(log.count()).unwrap();
            counts.push(count_inherited_entries(&dst_repo_local, tree));
        }

        for (i, &c) in counts.iter().enumerate() {
            assert!(
                c <= peaks,
                "inherited/ entry count {c} at forward append {i} exceeds the sealed peak count \
                 {peaks} (n={n}, k={k}, m={m})"
            );
        }
        if let (Some(&first), Some(&last)) = (counts.first(), counts.last()) {
            assert_eq!(
                first, last,
                "inherited/ entry count must not grow with m (n={n}, k={k}, m={m}): \
                 counts={counts:?}"
            );
        }
        drop(dst_dir);
    });
}

#[test]
fn inherited_archive_bounded_by_peaks_single_peak_seed() {
    assert_inherited_bounded_by_peaks(4, 2, 1, 6, "refs/eml/storage/inherited-cost/single");
}

#[test]
fn inherited_archive_bounded_by_peaks_multi_peak_seed() {
    assert_inherited_bounded_by_peaks(5, 2, 2, 6, "refs/eml/storage/inherited-cost/multi");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]

    /// The same storage-cost property, swept over the sealed size (varying
    /// the peak count) and the number of forward appends.
    #[test]
    fn inherited_archive_never_exceeds_sealed_peak_count(n in 1u64..12, m in 1u64..8) {
        let peaks = frontier_for_size(n, 2).len();
        assert_inherited_bounded_by_peaks(
            n,
            2,
            peaks,
            m,
            "refs/eml/storage/inherited-cost/prop",
        );
    }
}
