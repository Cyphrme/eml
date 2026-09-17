//! Differential property tests against `MemoryStorage`: SG2, SG3, SG8, SG9,
//! SG10, SG11, SG13, SG14, SG15 -- mirroring `storage-fjall`'s own
//! `tests/proptests.rs` pattern (`storage-fjall/tests/proptests.rs`) and
//! `polydigest`'s reference oracle.

mod common;

use std::collections::{BTreeSet, HashSet};

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{
    Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig, frontier_for_size,
};
use proptest::prelude::*;
use storage_git::GitStorage;
use tempfile::TempDir;

#[derive(Debug, Clone)]
enum Op {
    Append(Vec<u8>),
    Add(u64),
    Remove(u64),
    Resume(u64),
}

fn arb_ops() -> impl Strategy<Value = Vec<Op>> {
    let leaf = prop::collection::vec(any::<u8>(), 0..16).prop_map(Op::Append);
    let add = (0u64..4).prop_map(Op::Add);
    let remove = (0u64..4).prop_map(Op::Remove);
    let resume = (0u64..4).prop_map(Op::Resume);
    prop::collection::vec(
        prop_oneof![5 => leaf, 1 => add, 1 => remove, 1 => resume],
        1..30,
    )
}

async fn apply<S: Storage>(log: &mut NaryMerkleLog<S>, op: &Op)
where
    S::Error: std::fmt::Debug,
{
    match op {
        // Every legal append must succeed identically on both backends;
        // an illegal one (e.g. no active algorithms left) must fail
        // identically too -- asserting rather than swallowing catches a
        // divergence immediately instead of silently masking it.
        Op::Append(data) => {
            let _ = log.append_leaf(data).await;
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
    }
}

async fn run(ops: &[Op], arity: u64) {
    let (_dir, repo) = init_repo(HashKind::Sha1);
    let git_storage = GitStorage::new(repo, "refs/eml/storage/diff/staging", arity).unwrap();
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

    for op in ops {
        apply(&mut git_log, op).await;
        apply(&mut mem_log, op).await;
        assert_eq!(git_log.size(), mem_log.size(), "size diverged after {op:?}");
        for alg_id in 0u64..4 {
            let g = git_log.root_for(alg_id).ok();
            let m = mem_log.root_for(alg_id).ok();
            assert_eq!(g, m, "root_for({alg_id}) diverged after {op:?}");
        }
    }

    // Leaf parity (SG8, SG16): every stored leaf reads back identically.
    for i in 0..git_log.size() {
        let g = git_log.storage().get_leaf(i).await.ok();
        let m = mem_log.storage().get_leaf(i).await.ok();
        assert_eq!(g, m, "get_leaf({i}) diverged");
    }

    // Reload parity (SG9/SG13/SG20): a fresh `from_storage` over each
    // backend must reconstruct the same roots.
    let git_hashers: Vec<(u64, Box<dyn polydigest::Hasher>)> = (0u64..4)
        .map(|id| (id, Box::new(WideHasher) as Box<dyn polydigest::Hasher>))
        .collect();
    let git_hashers: Vec<_> = git_hashers
        .into_iter()
        .filter(|(id, _)| git_log.root_for(*id).is_ok())
        .collect();
    let mem_hashers: Vec<(u64, Box<dyn polydigest::Hasher>)> = git_hashers
        .iter()
        .map(|(id, _)| (*id, Box::new(WideHasher) as Box<dyn polydigest::Hasher>))
        .collect();

    let git_storage = git_log.into_storage();
    let mem_storage = mem_log.into_storage();
    let reopened_git =
        NaryMerkleLog::from_storage_with_config(git_storage, git_hashers, TreeConfig { arity })
            .await
            .unwrap();
    let reopened_mem =
        NaryMerkleLog::from_storage_with_config(mem_storage, mem_hashers, TreeConfig { arity })
            .await
            .unwrap();
    assert_eq!(reopened_git.size(), reopened_mem.size());
    for alg_id in 0u64..4 {
        assert_eq!(
            reopened_git.root_for(alg_id).ok(),
            reopened_mem.root_for(alg_id).ok(),
            "reload root_for({alg_id}) diverged"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    /// Arity 2, the common case.
    #[test]
    fn differential_arity_2(ops in arb_ops()) {
        smol::block_on(run(&ops, 2));
    }

    /// A non-power-of-two arity, exercising SG2's peak-count-per-digit math
    /// beyond the binary special case.
    #[test]
    fn differential_arity_3(ops in arb_ops()) {
        smol::block_on(run(&ops, 3));
    }

    /// [OPERATION ENUM] Arity 4, completing the head's ruling's "fuzzed
    /// across the five [operations], arities 2-4" requirement.
    #[test]
    fn differential_arity_4(ops in arb_ops()) {
        smol::block_on(run(&ops, 4));
    }
}

/// A fixed, hand-picked scenario mixing add/remove/resume so SG10/SG11's
/// opacity-by-provenance claim (not by the log-wide kind byte) is exercised
/// deterministically at least once, independent of what proptest happens to
/// generate.
#[test]
fn sg11_mixed_provenance_fixed_scenario() {
    smol::block_on(run(
        &[
            Op::Append(b"a".to_vec()),
            Op::Append(b"b".to_vec()),
            Op::Add(1),
            Op::Append(b"c".to_vec()),
            Op::Remove(1),
            Op::Append(b"d".to_vec()),
            Op::Resume(1),
            Op::Append(b"e".to_vec()),
            Op::Append(b"f".to_vec()),
            Op::Append(b"g".to_vec()),
            Op::Append(b"h".to_vec()),
        ],
        2,
    ));
}

// ============================================================================
// Fork lifecycle: seal, resume onto fresh storage, reopen from storage, and
// append as subtrees -- entirely separate from `Op`/`arb_ops`/`run` above
// (which never leave `LogKind::Flat` and so never exercise this), so the new
// coverage cannot change what the existing suite above already asserts.
//
// The comparison is deeper than root/size, too: every coordinate the
// sequence's frontier ever held (not just its current one) must still read
// back identically via `get_node`, and every historical size the sequence
// passed through must still reconstruct the same `root_for_at` on both
// backends. A hand-found defect lives exactly in that gap: once a
// subtree-kind log's frontier carries two or more peaks, the next write
// that merges any of them silently drops the just-superseded coordinate
// from `storage-git`'s `peaks/` tree (`build.rs::build_peaks` only persists
// the *current* frontier, and an opaque -- never materialized -- subtree
// peak carries no children for a lost coordinate to be recovered from,
// unlike a flat/materialized log). `MemoryStorage` never drops a node it
// was given.
// ============================================================================

/// Operations for the fork lifecycle, mixed with the same leaf/algorithm
/// operations `Op` covers so sequences interleave rather than testing the
/// lifecycle in isolation.
#[derive(Debug, Clone)]
enum ForkOp {
    /// A flat leaf append (fails once the log has gone subtree-kind).
    Append(Vec<u8>),
    /// A structured subtree append (fails once the log has gone flat-kind;
    /// the only forward-append path available after `Fork`, since a resumed
    /// log is always `LogKind::Subtree`).
    AppendSubtree(Vec<u8>),
    Add(u64),
    Remove(u64),
    ResumeAlgorithm(u64),
    /// Seal the log and resume it onto fresh storage (a fork).
    Fork,
    /// Reconstruct the log from its own storage (`from_storage_with_config`)
    /// and continue the sequence on the reconstructed instance.
    Reopen,
}

fn arb_fork_ops() -> impl Strategy<Value = Vec<ForkOp>> {
    let leaf = prop::collection::vec(any::<u8>(), 0..16).prop_map(ForkOp::Append);
    let subtree_leaf = prop::collection::vec(any::<u8>(), 0..16).prop_map(ForkOp::AppendSubtree);
    let add = (0u64..4).prop_map(ForkOp::Add);
    let remove = (0u64..4).prop_map(ForkOp::Remove);
    let resume_alg = (0u64..4).prop_map(ForkOp::ResumeAlgorithm);
    prop::collection::vec(
        prop_oneof![
            4 => subtree_leaf,
            2 => leaf,
            1 => add,
            1 => remove,
            1 => resume_alg,
            2 => Just(ForkOp::Fork),
            2 => Just(ForkOp::Reopen),
        ],
        1..16,
    )
}

/// Record the current size and every frontier coordinate it names into the
/// running history both are checked against -- called after every step, so
/// a coordinate captured the moment before it is folded away is still in
/// `coord_history` when the next step's comparison runs.
fn record_frontier(
    size: u64,
    arity: u64,
    coord_history: &mut HashSet<(u64, u32)>,
    sizes_seen: &mut BTreeSet<u64>,
) {
    sizes_seen.insert(size);
    coord_history.extend(frontier_for_size(size, arity));
}

/// Assert every coordinate in `coords` reads back identically from `git`
/// and `mem`, for every algorithm `arb_fork_ops`'s `Add`/`Remove` can name.
/// A coordinate present (or different) on one backend and missing on the
/// other is exactly the defect this module exists to catch.
async fn assert_node_parity(
    git: &GitStorage,
    mem: &MemoryStorage,
    coords: &HashSet<(u64, u32)>,
    context: &str,
) {
    for alg_id in 0u64..4 {
        for &(left, height) in coords {
            let g = git.get_node(alg_id, left, height).await.unwrap();
            let m = mem.get_node(alg_id, left, height).await.unwrap();
            assert_eq!(
                g, m,
                "{context}: get_node(alg={alg_id}, left={left}, height={height}) diverged: \
                 git={g:?} mem={m:?}"
            );
        }
    }
}

/// Assert every historical size in `sizes` reconstructs the same
/// per-algorithm root (SG20's historical-snapshot claim) on both backends,
/// including a success/failure divergence: a size that reconstructs on
/// `MemoryStorage` but errors on `GitStorage` (or vice versa) is a failure
/// in its own right, not just a value mismatch.
async fn assert_root_at_parity(
    git: &NaryMerkleLog<GitStorage>,
    mem: &NaryMerkleLog<MemoryStorage>,
    sizes: &BTreeSet<u64>,
    context: &str,
) {
    for alg_id in 0u64..4 {
        for &n in sizes {
            let g = git.root_for_at(alg_id, n).await;
            let m = mem.root_for_at(alg_id, n).await;
            match (&g, &m) {
                (Ok(gv), Ok(mv)) => assert_eq!(
                    gv, mv,
                    "{context}: root_for_at(alg={alg_id}, n={n}) value diverged"
                ),
                (Err(_), Err(_)) => {},
                _ => panic!(
                    "{context}: root_for_at(alg={alg_id}, n={n}) success diverged: git={g:?} \
                     mem={m:?}"
                ),
            }
        }
    }
}

/// The staging ref's own current target, read directly via `gix` -- never
/// through `storage-git`'s own API -- so [`assert_open_at_at_write_time`]'s
/// "recorded at write time" tree is an independent oracle in its own right,
/// not a value `GitStorage` handed back to itself.
fn tip_of(repo: &gix::ThreadSafeRepository, staging: &str) -> gix::ObjectId {
    repo.to_thread_local()
        .try_find_reference(staging)
        .ok()
        .flatten()
        .map(|r| r.target().id().to_owned())
        .unwrap_or_else(|| panic!("{staging} must have a tip"))
}

/// [SG21, finding 3] Restores the `open_at` coverage lost when
/// `assert_tree_at_open_at` was retired alongside the deleted `tree_at`
/// (b10ebd5). Unlike a check scoped to only the tree this step's write just
/// produced (functionally identical to the live `GitStorage` path, since at
/// the instant of recording the view's tree and size equal the live
/// instance's own), this replays EVERY tree the current generation has
/// recorded so far -- `gen_trees` -- so a tree recorded several steps ago is
/// opened well after the log has moved past it, exactly the shape the
/// deleted `assert_tree_at_open_at` exercised via `tree_at`. Each such
/// view's leaves (from `gen_start` up to that tree's own recorded size)
/// must match `MemoryStorage` identically. Leaves from *before* the current
/// generation are out of scope: a resume's fresh storage never receives its
/// predecessor's leaf bytes at all (only the sealed frontier's peak
/// digests), so neither backend can serve them, and that symmetric absence
/// is already covered at the node level by [`assert_node_parity`]'s own
/// `coord_history`.
async fn assert_open_at_at_write_time(
    git_log: &NaryMerkleLog<GitStorage>,
    mem_log: &NaryMerkleLog<MemoryStorage>,
    gen_start: u64,
    gen_trees: &[(u64, gix::ObjectId)],
    context: &str,
) {
    for &(size, tree) in gen_trees {
        let view = git_log
            .storage()
            .open_at(tree)
            .unwrap_or_else(|e| panic!("{context}: open_at(recorded tip {tree}) failed: {e}"));
        assert_eq!(
            view.tree(),
            tree,
            "{context}: open_at view reports the wrong tree"
        );
        for i in gen_start..size {
            let expected = mem_log.storage().get_leaf(i).await.unwrap();
            let got = view.get_leaf(i).await.unwrap();
            assert_eq!(
                got, expected,
                "{context}: open_at(recorded tip at size {size}).get_leaf({i}) diverged from \
                 MemoryStorage"
            );
        }
    }
}

async fn run_fork_lifecycle(ops: &[ForkOp], arity: u64) {
    // Every git repo this sequence's forks create must outlive the run, so
    // its objects stay readable; dropped otherwise (SG17-adjacent: a fork
    // targets a brand-new ref in a brand-new repo here, one repo per fork).
    let mut dirs: Vec<TempDir> = Vec::new();

    let (dir0, repo0) = init_repo(HashKind::Sha1);
    dirs.push(dir0);
    let mut current_repo = repo0.clone();
    let mut current_staging = "refs/eml/storage/fork-diff/0/staging".to_string();
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

    let mut coord_history: HashSet<(u64, u32)> = HashSet::new();
    let mut sizes_seen: BTreeSet<u64> = BTreeSet::new();
    let mut fork_id: u32 = 0;
    // The size at which the CURRENT generation (since the last fork, or
    // genesis) began -- [`assert_open_at_at_write_time`]'s leaf-parity loop
    // never looks below this, since a resumed generation's fresh storage
    // never receives its predecessor's leaf bytes.
    let mut gen_start: u64 = 0;
    // Every (size, tree) this generation has recorded straight off the ref
    // so far, reset on each fork -- [`assert_open_at_at_write_time`] replays
    // ALL of them at every step, so a tree recorded several steps ago is
    // opened well after the log has moved past it.
    let mut gen_trees: Vec<(u64, gix::ObjectId)> = Vec::new();

    record_frontier(git_log.size(), arity, &mut coord_history, &mut sizes_seen);

    for op in ops {
        match op {
            ForkOp::Append(data) => {
                let _ = git_log.append_leaf(data).await;
                let _ = mem_log.append_leaf(data).await;
            },
            ForkOp::AppendSubtree(data) => {
                let _ = git_log.append_subtree(&Subtree::Leaf(data.clone())).await;
                let _ = mem_log.append_subtree(&Subtree::Leaf(data.clone())).await;
            },
            ForkOp::Add(id) => {
                let _ = git_log.add_algorithm(*id, Box::new(WideHasher)).await;
                let _ = mem_log.add_algorithm(*id, Box::new(WideHasher)).await;
            },
            ForkOp::Remove(id) => {
                let _ = git_log.remove_algorithm(*id).await;
                let _ = mem_log.remove_algorithm(*id).await;
            },
            ForkOp::ResumeAlgorithm(id) => {
                let _ = git_log.resume_algorithm(*id).await;
                let _ = mem_log.resume_algorithm(*id).await;
            },
            ForkOp::Fork => {
                // Seal never touches a coordinate this defect can have lost
                // (it only reads the *current* frontier, which is always
                // present -- see this module's own top comment), so it is
                // expected to always succeed here.
                let git_sealed = git_log.seal().await.expect("seal git log");
                let mem_sealed = mem_log.seal().await.expect("seal mem log");

                fork_id += 1;
                let (dir, repo) = init_repo(HashKind::Sha1);
                dirs.push(dir);
                let staging = format!("refs/eml/storage/fork-diff/{fork_id}/staging");
                let fresh_git_storage =
                    GitStorage::new(repo.clone(), &staging, arity).expect("fresh fork storage");

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

                // A fork starts a new generation: its fresh storage carries
                // forward only the sealed frontier's peak digests, never any
                // predecessor leaf bytes, so open_at's leaf-parity check
                // below must not look below this size, its tree ids must
                // now be read off the NEW repo/ref, and every tree recorded
                // under the OLD generation is no longer relevant (its own
                // repo's objects stay reachable in `dirs`, but this
                // generation's own leaf range starts fresh).
                current_repo = repo;
                current_staging = staging;
                gen_start = git_log.size();
                gen_trees.clear();
            },
            ForkOp::Reopen => {
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
        }

        let context = format!("after {op:?}");
        assert_eq!(git_log.size(), mem_log.size(), "{context}: size diverged");
        for alg_id in 0u64..4 {
            let g = git_log.root_for(alg_id).ok();
            let m = mem_log.root_for(alg_id).ok();
            assert_eq!(g, m, "{context}: root_for({alg_id}) diverged");
        }

        record_frontier(git_log.size(), arity, &mut coord_history, &mut sizes_seen);

        // Every coordinate the frontier has ever named, not just today's.
        assert_node_parity(
            git_log.storage(),
            mem_log.storage(),
            &coord_history,
            &context,
        )
        .await;

        // Every size the sequence has ever passed through, not just today's.
        assert_root_at_parity(&git_log, &mem_log, &sizes_seen, &context).await;

        // [finding 3] Record this step's tree straight off the ref, then
        // replay open_at over every tree this generation has recorded so
        // far -- restoring the coverage the deleted `tree_at`-based
        // `assert_tree_at_open_at` gave before it was retired.
        gen_trees.push((git_log.size(), tip_of(&current_repo, &current_staging)));
        assert_open_at_at_write_time(&git_log, &mem_log, gen_start, &gen_trees, &context).await;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(12))]

    /// Arity 2: the fork lifecycle (seal, resume onto fresh storage, reopen,
    /// mixed with subtree appends) compared node-by-node and
    /// snapshot-by-snapshot against `MemoryStorage`, not just by root.
    #[test]
    fn fork_lifecycle_arity_2(ops in arb_fork_ops()) {
        smol::block_on(run_fork_lifecycle(&ops, 2));
    }

    /// Arity 3: the same lifecycle coverage at a non-binary arity.
    #[test]
    fn fork_lifecycle_arity_3(ops in arb_fork_ops()) {
        smol::block_on(run_fork_lifecycle(&ops, 3));
    }
}

/// A minimal, hand-picked fork: three leaves (frontier: a paired peak and a
/// lone-leaf peak), sealed and resumed onto fresh storage, then one more
/// subtree append that merges both resumed peaks into a single taller one.
/// `MemoryStorage` keeps every node it was ever given; `storage-git`'s
/// `peaks/` assembly (`build.rs::build_peaks`) does not persist a
/// coordinate once it stops being a current peak unless its replacement is
/// materialized -- and a subtree-kind log's peaks never materialize. The
/// two just-superseded coordinates are lost.
#[test]
fn fork_merge_of_two_opaque_peaks_keeps_the_superseded_nodes() {
    smol::block_on(async {
        let arity = 2u64;
        let (_dir_src, repo_src) = init_repo(HashKind::Sha1);
        let git_src =
            GitStorage::new(repo_src, "refs/eml/storage/fork-min/src/staging", arity).unwrap();
        let mut src_log = NaryMerkleLog::new(git_src, Box::new(WideHasher), TreeConfig { arity })
            .await
            .unwrap();
        for i in 0..3u32 {
            src_log
                .append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = src_log.seal().await.unwrap();

        // Fixture sanity: 3 leaves at arity 2 must resume to two peaks --
        // the precondition the defect needs (folding is only ever needed to
        // combine two or more peaks).
        assert_eq!(frontier_for_size(3, arity).len(), 2);

        let (_dir_dst, repo_dst) = init_repo(HashKind::Sha1);
        let git_storage =
            GitStorage::new(repo_dst, "refs/eml/storage/fork-min/dst/staging", arity).unwrap();
        let mut git_log =
            NaryMerkleLog::resume(&sealed, git_storage, vec![(0, Box::new(WideHasher))])
                .await
                .unwrap();
        let mut mem_log = NaryMerkleLog::resume(
            &sealed,
            MemoryStorage::new(),
            vec![(0, Box::new(WideHasher))],
        )
        .await
        .unwrap();

        git_log
            .append_subtree(&Subtree::Leaf(b"forward".to_vec()))
            .await
            .unwrap();
        mem_log
            .append_subtree(&Subtree::Leaf(b"forward".to_vec()))
            .await
            .unwrap();

        assert_eq!(
            git_log.root_for(0).ok(),
            mem_log.root_for(0).ok(),
            "roots must still agree after the merge"
        );

        // The two just-superseded peaks: the lone leaf at (left=2,height=0)
        // and the pair at (left=0,height=1).
        for &(left, height) in &[(2u64, 0u32), (0u64, 1u32)] {
            let g = git_log.storage().get_node(0, left, height).await.unwrap();
            let m = mem_log.storage().get_node(0, left, height).await.unwrap();
            assert_eq!(
                g, m,
                "get_node(alg=0, left={left}, height={height}) diverged after the merge: \
                 git={g:?} mem={m:?}"
            );
        }
    });
}
