//! Content-addressing properties for `storage-git`, per the head's ruling
//! (2026-09-16): "Anything that violates content addressing is not going to
//! fly." Each property below names a guarantee a content-addressed store
//! must hold and what a malformed version would look like -- three
//! (fidelity, history independence, stability) hold at this tip, checked
//! here broadly enough to lock them in; the fourth (no history state) does
//! not, and is pinned red as a defect for the next implementation pass to
//! fix, per this dispatch's report.

mod common;

use std::collections::HashSet;

use common::{WideHasher, init_repo};
use gix::ObjectId;
use gix::create::{Kind as CreateKind, Options as CreateOptions};
use gix::hash::Kind as HashKind;
use polydigest::{MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig, frontier_for_size};
use storage_git::GitStorage;

fn init_repo_at(dir: &std::path::Path, hash: HashKind) -> gix::ThreadSafeRepository {
    let opts = CreateOptions {
        object_hash: Some(hash),
        ..Default::default()
    };
    gix::ThreadSafeRepository::init_opts(dir, CreateKind::Bare, opts, Default::default())
        .expect("init bare repository")
}

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

// ============================================================================
// (a) FIDELITY -- after any sequence of writes, reopens, seals and resumes, including a double
//     resume, every leaf and every node polydigest ever wrote is readable at its key,
//     byte-identical, exactly as MemoryStorage returns it (storage-fjall's own semantics:
//     `storage-fjall/src/lib.rs` `store_node` 201-217, `write_batch` 343 onward, persists every
//     leaf by index and every node by (alg_id, left, height), as given, and never rebuilds or
//     discards). A malformed version drops a node that was created and folded away within a
//     single write once its parent leaves `peaks/` -- exactly GB71's shape
//     (`resume_forward_leaf.rs`), which `086c181` fixed for the general case. This sweep checks
//     that fix broadly: every resume-chain depth, arity, and forward-append count sampled here
//     agrees with MemoryStorage on every frontier coordinate the chain ever named, not merely the
//     one coordinate GB71 pins.
// ============================================================================

/// Chain `depth` resumes, `per_hop` forward `Subtree::Leaf` appends each,
/// starting from an `n0`-leaf, arity-`k` origin seal; after every hop,
/// assert every frontier coordinate the chain has named so far (across
/// every intermediate size, not merely the final one) reads back
/// identically from `GitStorage` and `MemoryStorage`.
async fn assert_fidelity_across_chain(n0: u64, k: u64, depth: usize, per_hop: u64, tag: &str) {
    let mut git_sealed = seal_git(n0, k, &format!("refs/eml/content-addr/fidelity/{tag}/g0")).await;
    let mut mem_sealed = seal_mem(n0, k).await;
    let mut dirs = Vec::new();

    for hop in 0..depth {
        let (dir, repo) = init_repo(HashKind::Sha1);
        dirs.push(dir);
        let git = GitStorage::new(
            repo,
            format!("refs/eml/content-addr/fidelity/{tag}/g{}", hop + 1),
            k,
        )
        .unwrap();
        let mut git_log = NaryMerkleLog::resume(&git_sealed, git, vec![(0, Box::new(WideHasher))])
            .await
            .unwrap();
        let mut mem_log = NaryMerkleLog::resume(
            &mem_sealed,
            MemoryStorage::new(),
            vec![(0, Box::new(WideHasher))],
        )
        .await
        .unwrap();

        for i in 0..per_hop {
            let bytes = format!("h{hop}-{i}").into_bytes();
            git_log
                .append_subtree(&Subtree::Leaf(bytes.clone()))
                .await
                .unwrap();
            mem_log.append_subtree(&Subtree::Leaf(bytes)).await.unwrap();
        }

        // Every frontier coordinate at every size from the origin up to this
        // hop's final count -- not merely the final frontier -- must agree.
        let mut coords: HashSet<(u64, u32)> = HashSet::new();
        for size in n0..=git_log.count() {
            coords.extend(frontier_for_size(size, k));
        }
        for &(left, height) in &coords {
            let g = git_log.storage().get_node(0, left, height).await.unwrap();
            let m = mem_log.storage().get_node(0, left, height).await.unwrap();
            assert_eq!(
                g, m,
                "FIDELITY: get_node(alg=0, left={left}, height={height}) diverged at hop {hop} \
                 (n0={n0}, k={k}, depth={depth}, per_hop={per_hop}): git={g:?} mem={m:?}"
            );
        }

        git_sealed = git_log.seal().await.unwrap();
        mem_sealed = mem_log.seal().await.unwrap();
    }
}

#[test]
fn fidelity_holds_across_resume_chains() {
    smol::block_on(async {
        for k in [2u64, 3] {
            for n0 in [1u64, 2, 3, 5, 7, 11] {
                for depth in [1usize, 2, 3] {
                    for per_hop in [1u64, 2, 3] {
                        assert_fidelity_across_chain(
                            n0,
                            k,
                            depth,
                            per_hop,
                            &format!("{k}-{n0}-{depth}-{per_hop}"),
                        )
                        .await;
                    }
                }
            }
        }
    });
}

// ============================================================================
// (b) HISTORY INDEPENDENCE -- the tree committed at size n is a pure function of the content
//     written up to n. Two logs with identical content built through different write sequences
//     (single appends against batched writes, with or without a reopen in between) produce the
//     identical tree id. A malformed version bakes incidental write-pattern state (e.g. how many
//     separate write_batch calls it took, or whether the process restarted midway) into the
//     committed tree, so replaying the same content differently yields a different tree id even
//     though nothing a reader could call "content" differs.
// ============================================================================

/// Building `n` leaves through `n` separate `append_leaf` calls (`n` distinct
/// `write_batch` commits) must produce the identical `tree_at(n)` as building
/// the identical final leaves, nodes, algorithm metadata, and checkpoint
/// roots through exactly one `write_batch` call -- the same content, batched
/// differently.
#[test]
fn history_independence_single_appends_vs_one_batched_write() {
    smol::block_on(async {
        let k = 2u64;
        let n = 7u64;

        // Oracle: the complete final state a from-genesis flat build reaches.
        let mut mem = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        for i in 0..n {
            mem.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let mem_storage = mem.into_storage();
        let final_meta = mem_storage.load_log_meta().await.unwrap();
        let final_roots = mem_storage.load_checkpoint_roots().await.unwrap();
        let final_metas = mem_storage.load_algorithm_metas().await.unwrap();

        // Incremental: n separate append_leaf calls on git.
        let (_dir1, repo1) = init_repo(HashKind::Sha1);
        let git1 = GitStorage::new(repo1, "refs/eml/content-addr/history-indep/incr", k).unwrap();
        let mut log1 = NaryMerkleLog::new(git1, Box::new(WideHasher), TreeConfig { arity: k })
            .await
            .unwrap();
        for i in 0..n {
            log1.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let tree_incremental = log1.storage().tree_at(n).unwrap();

        // Batched: one single write_batch call carrying the identical final
        // leaves, nodes, algorithm metadata, log metadata and checkpoint
        // roots the incremental build ended up with.
        let (_dir2, repo2) = init_repo(HashKind::Sha1);
        let mut git2 =
            GitStorage::new(repo2, "refs/eml/content-addr/history-indep/batch", k).unwrap();
        let leaves: Vec<(u64, Vec<u8>)> = (0..n)
            .map(|i| (i, format!("leaf-{i}").into_bytes()))
            .collect();
        let leaves_ref: Vec<(u64, &[u8])> =
            leaves.iter().map(|(i, d)| (*i, d.as_slice())).collect();
        let nodes_owned: Vec<(u64, u64, u32, Vec<u8>)> = mem_storage
            .nodes
            .iter()
            .map(|(&(alg, left, height), hash)| (alg, left, height, hash.clone()))
            .collect();
        let nodes_ref: Vec<(u64, u64, u32, &[u8])> = nodes_owned
            .iter()
            .map(|(a, l, h, d)| (*a, *l, *h, d.as_slice()))
            .collect();
        let metas_ref: Vec<(u64, &[(u64, u64)])> = final_metas
            .iter()
            .map(|(id, e)| (*id, e.as_slice()))
            .collect();
        let roots_ref: Vec<(u64, &[u8])> = final_roots
            .iter()
            .map(|(id, r)| (*id, r.as_slice()))
            .collect();
        git2.write_batch(&leaves_ref, &nodes_ref, &metas_ref, final_meta, &roots_ref)
            .await
            .unwrap();
        let tree_batched = git2.tree_at(n).unwrap();

        assert_eq!(
            tree_incremental, tree_batched,
            "HISTORY INDEPENDENCE: identical content committed via n incremental append_leaf \
             calls (tree={tree_incremental}) must equal the same content committed via one \
             batched write_batch call (tree={tree_batched})"
        );
    });
}

/// Building `n` leaves straight through, in one process, must produce the
/// identical `tree_at(n)` as building the first `n1` leaves, dropping the
/// `GitStorage` instance and reopening the same repository path from disk,
/// then appending the remaining `n - n1` -- a reopen in between changes
/// nothing a reader could call "content".
#[test]
fn history_independence_reopen_midway_matches_no_reopen() {
    smol::block_on(async {
        let k = 2u64;
        let n = 7u64;
        let n1 = 3u64;

        let dir_no_reopen = tempfile::tempdir().unwrap();
        let repo_no_reopen = init_repo_at(dir_no_reopen.path(), HashKind::Sha1);
        let git_no_reopen =
            GitStorage::new(repo_no_reopen, "refs/eml/content-addr/reopen/straight", k).unwrap();
        let mut log_no_reopen =
            NaryMerkleLog::new(git_no_reopen, Box::new(WideHasher), TreeConfig { arity: k })
                .await
                .unwrap();
        for i in 0..n {
            log_no_reopen
                .append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let tree_no_reopen = log_no_reopen.storage().tree_at(n).unwrap();

        let dir_reopen = tempfile::tempdir().unwrap();
        {
            let repo = init_repo_at(dir_reopen.path(), HashKind::Sha1);
            let git = GitStorage::new(repo, "refs/eml/content-addr/reopen/split", k).unwrap();
            let mut log = NaryMerkleLog::new(git, Box::new(WideHasher), TreeConfig { arity: k })
                .await
                .unwrap();
            for i in 0..n1 {
                log.append_leaf(format!("leaf-{i}").as_bytes())
                    .await
                    .unwrap();
            }
        } // drop: instance and its in-memory state are gone.
        let git_reopened =
            GitStorage::open(dir_reopen.path(), "refs/eml/content-addr/reopen/split", k).unwrap();
        let mut log_reopened =
            NaryMerkleLog::from_storage(git_reopened, vec![(0, Box::new(WideHasher))])
                .await
                .unwrap();
        for i in n1..n {
            log_reopened
                .append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let tree_reopened = log_reopened.storage().tree_at(n).unwrap();

        assert_eq!(
            tree_no_reopen, tree_reopened,
            "HISTORY INDEPENDENCE: identical content committed straight through \
             (tree={tree_no_reopen}) must equal the same content committed with a reopen at size \
             {n1} (tree={tree_reopened})"
        );
    });
}

// ============================================================================
// (c) STABILITY -- tree_at(k) returns the tree id originally committed at size k, for every k,
//     including a fork's resume point, and still does after `git gc --prune=now --aggressive` and
//     a fresh open. A malformed version relies on a dangling, not-yet-pruned object surviving only
//     by accident between writes; gc collects everything unreachable from the current ref, so a
//     reconstruction that needed one of those objects starts failing, or silently returns a
//     different tree, the moment gc actually runs.
// ============================================================================

/// A resumed log's `tree_at(k)`, sampled at the fork point and at every size
/// reached by three forward subtree appends, must return the identical
/// object id before and after `git gc --prune=now --aggressive` plus a fresh
/// `GitStorage::open`.
#[test]
fn stability_survives_gc_at_a_forks_resume_point() {
    smol::block_on(async {
        let k = 2u64;
        let n0 = 5u64;

        let (_odir, orepo) = init_repo(HashKind::Sha1);
        let ogit = GitStorage::new(orepo, "refs/eml/content-addr/stability/origin", k).unwrap();
        let mut olog = NaryMerkleLog::new(ogit, Box::new(WideHasher), TreeConfig { arity: k })
            .await
            .unwrap();
        for i in 0..n0 {
            olog.append_leaf(format!("orig-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = olog.seal().await.unwrap();

        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().to_path_buf();
        {
            let repo = init_repo_at(&path, HashKind::Sha1);
            let git = GitStorage::new(repo, "refs/eml/content-addr/stability/fork", k).unwrap();
            let mut log = NaryMerkleLog::resume(&sealed, git, vec![(0, Box::new(WideHasher))])
                .await
                .unwrap();
            for i in 0..4u64 {
                log.append_subtree(&Subtree::Leaf(format!("fwd-{i}").into_bytes()))
                    .await
                    .unwrap();
            }
        }

        let sample_sizes = [0u64, n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4];
        let read_all =
            |path: &std::path::Path| -> Vec<(u64, Result<ObjectId, storage_git::GitStorageError>)> {
                let mut git =
                    GitStorage::open(path, "refs/eml/content-addr/stability/fork", k).unwrap();
                git.register_hasher(0, Box::new(WideHasher));
                sample_sizes.iter().map(|&m| (m, git.tree_at(m))).collect()
            };

        let before = read_all(&path);

        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(&path)
            .arg("gc")
            .arg("--prune=now")
            .arg("--aggressive")
            .status()
            .expect("git gc must run (git binary must be on PATH)");
        assert!(status.success(), "git gc exited non-zero: {status:?}");

        let after = read_all(&path);

        for ((size, before_result), (_, after_result)) in before.iter().zip(after.iter()) {
            assert_eq!(
                before_result.as_ref().ok(),
                after_result.as_ref().ok(),
                "STABILITY: tree_at({size}) diverged across gc: before={before_result:?} \
                 after={after_result:?}"
            );
        }
    });
}

// ============================================================================
// (d) NO HISTORY STATE -- nothing in a committed tree changes value after it is written. Named
//     suspect: meta's existing flat/subtree kind byte (`storage-git/src/layout.rs`'s
//     `encode_meta`, `storage-git/src/build.rs:114-116`). RED: within a single log's own life the
//     byte cannot change (`append_leaf`/`append_subtree` refuse the other kind once one is bound,
//     `polydigest/src/tree.rs:778,847`), but at size 0 -- before any append has bound anything --
//     GitStorage::tree_at(0) reconstructs meta using the log's CURRENT (i.e. final, whatever it
//     later became) kind byte rather than a value derived from the zero-leaf content itself. Two
//     logs with byte-identical content at n=0 (no leaves, no nodes, no algorithm epochs beyond the
//     default) therefore commit to two DIFFERENT tree ids for that n=0 tree, solely because one
//     log's history later happens to append leaves and the other later happens to append subtrees.
//     A conforming version would either give every log's tree_at(0) the same, content-derived kind
//     (or omit kind from a tree that has no committed appends to characterize at all), so that
//     "no content yet" always addresses the same object regardless of what is appended afterward.
// ============================================================================

#[test]
fn no_history_state_kind_byte_at_size_zero_is_content_addressed() {
    smol::block_on(async {
        let k = 2u64;

        // Log A: will end up Flat-kind (its first ever append is append_leaf).
        let (_dir_a, repo_a) = init_repo(HashKind::Sha1);
        let git_a = GitStorage::new(repo_a, "refs/eml/content-addr/kind-zero/flat", k).unwrap();
        let mut log_a = NaryMerkleLog::new(git_a, Box::new(WideHasher), TreeConfig { arity: k })
            .await
            .unwrap();
        log_a.append_leaf(b"x").await.unwrap();
        let tree_at_0_flat = log_a
            .storage()
            .tree_at(0)
            .expect("tree_at(0) must be reconstructable before any real content exists");

        // Log B: will end up Subtree-kind (its first ever append is append_subtree).
        let (_dir_b, repo_b) = init_repo(HashKind::Sha1);
        let git_b = GitStorage::new(repo_b, "refs/eml/content-addr/kind-zero/subtree", k).unwrap();
        let mut log_b = NaryMerkleLog::new(git_b, Box::new(WideHasher), TreeConfig { arity: k })
            .await
            .unwrap();
        log_b
            .append_subtree(&Subtree::Leaf(b"x".to_vec()))
            .await
            .unwrap();
        let tree_at_0_subtree = log_b
            .storage()
            .tree_at(0)
            .expect("tree_at(0) must be reconstructable before any real content exists");

        assert_eq!(
            tree_at_0_flat, tree_at_0_subtree,
            "NO HISTORY STATE: tree_at(0) for two logs with byte-identical (empty) content at \
             size 0 must be the same object regardless of what kind each log's history later \
             decides -- got flat-destined={tree_at_0_flat} subtree-destined={tree_at_0_subtree}"
        );
    });
}
