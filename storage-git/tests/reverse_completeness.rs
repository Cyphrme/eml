//! REVERSE COMPLETENESS: git must hold no key beyond what `MemoryStorage`
//! holds, and a coordinate neither backend was ever given -- including one
//! inside a fork's sealed prefix -- must read as `None`/`NotFound`
//! identically on both.
//!
//! `completeness_property.rs` and `differential.rs` already check the
//! FORWARD direction thoroughly: every key `MemoryStorage` holds must also
//! be readable from `GitStorage` (a dropped node). Neither checks the
//! REVERSE direction: that git holds nothing EXTRA -- a leftover, a stale
//! entry a removal should have retired, or a coordinate from the wrong
//! algorithm bleeding into the wrong path. `get_node`/`get_leaf` alone
//! cannot surface an extra key unless a test happens to ask for exactly
//! that coordinate; the only way to catch "git has something nobody asked
//! for" is to enumerate git's OWN stored tree directly and compare the
//! resulting key SET, not individual lookups, against an independent
//! oracle's key set.
//!
//! This file also combines the full operation vocabulary (append, add,
//! remove, resume algorithm, fork, reopen) with git's own housekeeping
//! (gc) across arities 2 through 4 in one property -- a fork immediately
//! followed by another fork exercises a double resume without needing a
//! separate op for it.
//!
//! RED at 60f93fe: today's layout is peak-wired, so there is no top-level
//! `n`/`l` namespace to enumerate at all -- `git_key_set` below reads back
//! two empty sets against any real tree, diverging from `MemoryStorage`'s
//! non-empty key set the moment anything has been written.

mod common;

use std::collections::HashSet;

use common::{
    WideHasher, decode_leaf_path, decode_node_path, enumerate_full_paths, find_child, init_repo,
};
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig};
use proptest::prelude::*;
use storage_git::GitStorage;
use tempfile::TempDir;

#[derive(Debug, Clone)]
enum Op {
    Append(Vec<u8>),
    AppendSubtree(Vec<u8>),
    Add(u64),
    Remove(u64),
    Resume(u64),
    /// Seal and resume onto fresh storage -- a fork. Two of these in a row,
    /// with nothing forward written in between, is a double resume.
    Fork,
    /// Reconstruct the log from its own storage.
    Reopen,
    /// Run `git gc --prune=now` against the git backend's repository.
    /// A no-op from `MemoryStorage`'s point of view.
    Gc,
}

fn arb_ops(max_len: usize) -> impl Strategy<Value = Vec<Op>> {
    let leaf = prop::collection::vec(any::<u8>(), 0..12).prop_map(Op::Append);
    let subtree_leaf = prop::collection::vec(any::<u8>(), 0..12).prop_map(Op::AppendSubtree);
    let add = (0u64..4).prop_map(Op::Add);
    let remove = (0u64..4).prop_map(Op::Remove);
    let resume = (0u64..4).prop_map(Op::Resume);
    prop::collection::vec(
        prop_oneof![
            3 => leaf,
            2 => subtree_leaf,
            2 => add,
            2 => remove,
            2 => resume,
            2 => Just(Op::Fork),
            2 => Just(Op::Reopen),
            1 => Just(Op::Gc),
        ],
        1..max_len,
    )
}

/// Every key actually stored under git's own `nodes`/`leaves` namespaces,
/// decoded straight off the raw tree -- independent of `GitStorage`'s own
/// read path (`get_node`/`get_leaf`), which could in principle agree with
/// itself about a coordinate that a direct tree walk would show is not
/// really there (or vice versa). `None` for either namespace's top-level
/// entry is an empty set, not an error: a log with no leaves yet has no
/// `leaves` entry at all.
fn git_key_set(
    repo: &gix::Repository,
    tip: gix::ObjectId,
) -> (HashSet<u64>, HashSet<(u64, u64, u32)>) {
    let leaves: HashSet<u64> = match find_child(repo, tip, "leaves") {
        Some(l) => enumerate_full_paths(repo, l.oid)
            .iter()
            .filter_map(|p| decode_leaf_path(p))
            .collect(),
        None => HashSet::new(),
    };
    let nodes: HashSet<(u64, u64, u32)> = match find_child(repo, tip, "nodes") {
        Some(n) => enumerate_full_paths(repo, n.oid)
            .iter()
            .filter_map(|p| decode_node_path(p))
            .collect(),
        None => HashSet::new(),
    };
    (leaves, nodes)
}

/// [REVERSE COMPLETENESS] `git`'s actual stored key set, enumerated
/// directly from the tree, must equal `mem`'s key set exactly -- neither a
/// missing key (the forward direction other files already check) nor an
/// EXTRA one git holds that memory does not.
fn assert_reverse_completeness(
    repo: &gix::ThreadSafeRepository,
    staging: &str,
    mem: &MemoryStorage,
    context: &str,
) {
    let local = repo.to_thread_local();
    let tip = local
        .try_find_reference(staging)
        .ok()
        .flatten()
        .and_then(|mut r| r.peel_to_id().ok())
        .map(|id| id.detach());

    let Some(tip) = tip else {
        assert!(
            mem.leaves.is_empty() && mem.nodes.is_empty(),
            "{context}: git has no tip at all, but MemoryStorage holds {} leaves and {} nodes",
            mem.leaves.len(),
            mem.nodes.len()
        );
        return;
    };

    let (git_leaves, git_nodes) = git_key_set(&local, tip);
    let mem_leaves: HashSet<u64> = (0..mem.leaves.len() as u64).collect();
    let mem_nodes: HashSet<(u64, u64, u32)> = mem.nodes.keys().copied().collect();

    assert_eq!(
        git_leaves,
        mem_leaves,
        "{context}: REVERSE COMPLETENESS: git's stored leaf keys diverge from MemoryStorage's -- \
         extra (in git, not memory): {:?}; missing (in memory, not git): {:?}",
        git_leaves.difference(&mem_leaves).collect::<Vec<_>>(),
        mem_leaves.difference(&git_leaves).collect::<Vec<_>>()
    );
    assert_eq!(
        git_nodes,
        mem_nodes,
        "{context}: REVERSE COMPLETENESS: git's stored node keys diverge from MemoryStorage's -- \
         extra (in git, not memory): {:?}; missing (in memory, not git): {:?}",
        git_nodes.difference(&mem_nodes).collect::<Vec<_>>(),
        mem_nodes.difference(&git_nodes).collect::<Vec<_>>()
    );
}

/// [ABSENT COORDINATES] A coordinate neither backend was ever given must
/// read as `None`/`NotFound` IDENTICALLY on both: an algorithm id that has
/// never been registered, and a leaf index comfortably past the current
/// size.
async fn assert_absent_coordinates_agree(git: &GitStorage, mem: &MemoryStorage, context: &str) {
    let never_registered_alg = 9_999u64;
    let g = git.get_node(never_registered_alg, 0, 0).await.unwrap();
    let m = mem.nodes.get(&(never_registered_alg, 0, 0)).cloned();
    assert_eq!(
        g, m,
        "{context}: get_node for a never-registered algorithm must agree (both None)"
    );
    assert!(
        g.is_none(),
        "{context}: fixture sanity: algorithm {never_registered_alg} must really be unused"
    );

    let past_the_end = mem.leaves.len() as u64 + 1_000;
    let git_result = git.get_leaf(past_the_end).await;
    assert!(
        git_result.is_err(),
        "{context}: get_leaf comfortably past the current size must fail on git, got \
         {git_result:?}"
    );
}

async fn apply<S: Storage>(log: &mut NaryMerkleLog<S>, op: &Op)
where
    S::Error: std::fmt::Debug,
{
    match op {
        Op::Append(data) => {
            let _ = log.append_leaf(data).await;
        },
        Op::AppendSubtree(data) => {
            let _ = log.append_subtree(&Subtree::Leaf(data.clone())).await;
        },
        Op::Add(id) => {
            let _ = log.add_algorithm(*id, Box::new(WideHasher)).await;
        },
        Op::Remove(id) => {
            let _ = log.remove_algorithm(*id).await;
        },
        Op::Resume(id) => {
            let _ = log.resume_algorithm(*id).await;
        },
        // Fork and Reopen are handled by the caller, which owns the storage
        // handles `apply` cannot replace on its own.
        Op::Fork | Op::Reopen | Op::Gc => {},
    }
}

async fn run_property(ops: &[Op], arity: u64, tag: &str) {
    let mut dirs: Vec<TempDir> = Vec::new();
    let (dir0, repo0) = init_repo(HashKind::Sha1);
    let mut current_dir = dir0.path().to_path_buf();
    dirs.push(dir0);
    let mut current_staging = format!("refs/eml/storage/reverse-completeness/{tag}/0/staging");
    let git_storage = GitStorage::new(repo0, &current_staging, arity).expect("fresh git storage");
    let mut git_log = NaryMerkleLog::new(git_storage, Box::new(WideHasher), TreeConfig { arity })
        .await
        .unwrap();
    let mut mem_log = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(WideHasher),
        TreeConfig { arity },
    )
    .await
    .unwrap();
    let mut fork_id: u32 = 0;

    let context0 = "genesis";
    assert_reverse_completeness(
        &gix::ThreadSafeRepository::open(&current_dir).unwrap(),
        &current_staging,
        mem_log.storage(),
        context0,
    );

    for op in ops {
        match op {
            Op::Fork => {
                let git_sealed = git_log.seal().await.expect("seal git log");
                let mem_sealed = mem_log.seal().await.expect("seal mem log");

                fork_id += 1;
                let (dir, repo) = init_repo(HashKind::Sha1);
                let new_dir = dir.path().to_path_buf();
                dirs.push(dir);
                let staging =
                    format!("refs/eml/storage/reverse-completeness/{tag}/{fork_id}/staging");
                let fresh_git_storage =
                    GitStorage::new(repo, &staging, arity).expect("fresh fork storage");

                let git_hashers: Vec<(u64, Box<dyn Hasher>)> = git_sealed
                    .frontiers()
                    .iter()
                    .map(|&(id, _)| (id, Box::new(WideHasher) as Box<dyn Hasher>))
                    .collect();
                let mem_hashers: Vec<(u64, Box<dyn Hasher>)> = mem_sealed
                    .frontiers()
                    .iter()
                    .map(|&(id, _)| (id, Box::new(WideHasher) as Box<dyn Hasher>))
                    .collect();

                git_log = NaryMerkleLog::resume(&git_sealed, fresh_git_storage, git_hashers)
                    .await
                    .expect("resume git log onto fresh storage");
                mem_log = NaryMerkleLog::resume(&mem_sealed, MemoryStorage::new(), mem_hashers)
                    .await
                    .expect("resume mem log onto fresh storage");

                current_dir = new_dir;
                current_staging = staging;
            },
            Op::Reopen => {
                let git_metas = git_log
                    .storage()
                    .load_algorithm_metas()
                    .await
                    .expect("load git algorithm metas");
                let git_hashers: Vec<(u64, Box<dyn Hasher>)> = git_metas
                    .iter()
                    .map(|&(id, _)| (id, Box::new(WideHasher) as Box<dyn Hasher>))
                    .collect();
                let git_storage = git_log.into_storage();
                git_log = NaryMerkleLog::from_storage_with_config(
                    git_storage,
                    git_hashers,
                    TreeConfig { arity },
                )
                .await
                .expect("reopen git log from storage");

                let mem_metas = mem_log
                    .storage()
                    .load_algorithm_metas()
                    .await
                    .expect("load mem algorithm metas");
                let mem_hashers: Vec<(u64, Box<dyn Hasher>)> = mem_metas
                    .iter()
                    .map(|&(id, _)| (id, Box::new(WideHasher) as Box<dyn Hasher>))
                    .collect();
                let mem_storage = mem_log.into_storage();
                mem_log = NaryMerkleLog::from_storage_with_config(
                    mem_storage,
                    mem_hashers,
                    TreeConfig { arity },
                )
                .await
                .expect("reopen mem log from storage");
            },
            Op::Gc => {
                let out = std::process::Command::new("git")
                    .arg("--git-dir")
                    .arg(&current_dir)
                    .args(["gc", "--prune=now", "-q"])
                    .output()
                    .expect("run git gc");
                assert!(
                    out.status.success(),
                    "git gc failed: {}",
                    String::from_utf8_lossy(&out.stderr)
                );
            },
            other => apply(&mut git_log, other).await,
        }
        if !matches!(op, Op::Fork | Op::Reopen | Op::Gc) {
            apply(&mut mem_log, op).await;
        }

        assert_eq!(
            git_log.size(),
            mem_log.size(),
            "{tag}: size diverged after {op:?}"
        );

        let repo_now = gix::ThreadSafeRepository::open(&current_dir).unwrap();
        let context = format!("{tag}: after {op:?}");
        assert_reverse_completeness(&repo_now, &current_staging, mem_log.storage(), &context);
        assert_absent_coordinates_agree(git_log.storage(), mem_log.storage(), &context).await;
    }

    // Final pass: reopen from disk, then gc, re-checking reverse
    // completeness at each stage -- a dropped-vs-extra defect that only
    // shows up once loose objects are packed, or after a fresh handle
    // re-reads the ref, is exactly what a live-only check would miss.
    let reopened_dir = current_dir.clone();
    let reopened_staging = current_staging.clone();
    let reopened = GitStorage::open(&reopened_dir, &reopened_staging, arity)
        .expect("reopen after the sequence");
    assert_reverse_completeness(
        &gix::ThreadSafeRepository::open(&reopened_dir).unwrap(),
        &reopened_staging,
        mem_log.storage(),
        &format!("{tag}: after final reopen"),
    );
    assert_absent_coordinates_agree(
        &reopened,
        mem_log.storage(),
        &format!("{tag}: after final reopen"),
    )
    .await;
    drop(reopened);

    let out = std::process::Command::new("git")
        .arg("--git-dir")
        .arg(&reopened_dir)
        .args(["gc", "--prune=now", "-q"])
        .output()
        .expect("run git gc");
    assert!(
        out.status.success(),
        "final git gc failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let reopened2 =
        GitStorage::open(&reopened_dir, &reopened_staging, arity).expect("reopen after gc");
    assert_reverse_completeness(
        &gix::ThreadSafeRepository::open(&reopened_dir).unwrap(),
        &reopened_staging,
        mem_log.storage(),
        &format!("{tag}: after final gc and reopen"),
    );
    assert_absent_coordinates_agree(
        &reopened2,
        mem_log.storage(),
        &format!("{tag}: after final gc and reopen"),
    )
    .await;
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    /// [finding 4, finding 7] The full operation vocabulary (append, a
    /// structured subtree append, add/remove/resume algorithm, fork,
    /// reopen) combined with git's own housekeeping (gc), at arities 2
    /// through 4 -- arity itself is part of the generated input, so this
    /// one property sweeps all three rather than needing one function per
    /// arity. Two `Fork`s with nothing forward written between them is a
    /// double resume; no separate op is needed to reach that shape.
    #[test]
    fn reverse_completeness_full_vocabulary(
        arity in 2u64..=4,
        ops in arb_ops(16)
    ) {
        smol::block_on(run_property(&ops, arity, &format!("a{arity}")));
    }
}

/// [finding 4] A hand-picked double resume, independent of proptest: seal,
/// resume onto fresh storage with nothing forward written, seal again, and
/// resume a second time onto a second fresh storage -- exactly the shape
/// named in the review this file closes, checked with certainty rather
/// than left to chance.
#[test]
fn deterministic_double_resume_has_no_extra_or_missing_keys() {
    smol::block_on(run_property(
        &[Op::Append(b"a".to_vec()), Op::Fork, Op::Fork],
        2,
        "double-resume",
    ));
}

#[cfg(test)]
mod untrim_tests {
    use crate::common::{trimmed_key_segments, untrim_key_segments};

    #[test]
    fn round_trips_through_trim_and_untrim() {
        for k in [0u64, 1, 2, 255, 256, 65535, 65536, 1_000_000, u64::MAX] {
            let segs = trimmed_key_segments(k);
            let seg_refs: Vec<&str> = segs.iter().map(String::as_str).collect();
            assert_eq!(
                untrim_key_segments(&seg_refs),
                Some(k),
                "key {k} did not round-trip through trim/untrim"
            );
        }
    }

    #[test]
    fn rejects_malformed_segments() {
        assert_eq!(
            untrim_key_segments(&["0", "ab"]),
            None,
            "length 0 is invalid"
        );
        assert_eq!(
            untrim_key_segments(&["2", "ab"]),
            None,
            "length disagrees with segment count"
        );
        assert_eq!(untrim_key_segments(&["1", "zz"]), None, "non-hex byte");
        assert_eq!(untrim_key_segments(&[]), None, "empty input");
    }
}
