//! The tip-tree contract, per the head's design ruling (2026-09-16):
//! storage-git keeps the COMPLETE tree by construction (every leaf and node
//! ever written, by coordinate), one tip ref points DIRECTLY at that tree
//! object (never a commit), it NEVER creates commits, and it NEVER renders
//! or reconstructs a tree for a past size -- that reconstruction is exactly
//! the defect class the merge gate's latest refusal names (RV20/RV21,
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-regate-after-revert.md`):
//! storage making its own commits, and storage rebuilding history it should
//! simply have kept. None of the five properties below calls `tree_at` or
//! `register_hasher` -- both scoped to the historical-reconstruction path
//! [`no_reconstruction_of_historical_trees_in_source`] pins as deleted --
//! and none compares a derived value against another derivation of the same
//! value: every assertion below is checked against an independent oracle
//! (`MemoryStorage`, a tree id recorded straight off the ref at write time,
//! or a `git` command run against the raw object database), never a
//! recomputation compared with itself. That last failure mode is not
//! hypothetical: the previous round's stability property compared
//! `tree_at` before gc against `tree_at` after gc -- a reconstruction
//! against a reconstruction -- and was green by construction (RV6).

mod common;

use std::path::Path;
use std::process::{Command, Stdio};

use common::{WideHasher, init_repo};
use gix::ObjectId;
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig};
use storage_git::GitStorage;

/// Run `git <args>` against the repository whose git-dir is `dir`, returning
/// trimmed stdout. Panics with stderr on a nonzero exit -- every call here
/// is expected to succeed; a failure is either a test-setup bug or (for
/// [`checkpoint`]/[`assert_all_checkpoints_resolve`]) itself evidence that a
/// tree this suite recorded no longer exists, which is exactly a WRITTEN IS
/// KEPT violation surfacing through `git`'s own error rather than through a
/// Rust assertion.
fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("--git-dir")
        .arg(dir)
        .args(args)
        .stdin(Stdio::null())
        .output()
        .expect("run git");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

fn gc(dir: &Path) {
    git(dir, &["gc", "--prune=now", "--aggressive", "-q"]);
}

fn ref_target(repo: &gix::Repository, name: &str) -> Option<ObjectId> {
    repo.try_find_reference(name)
        .ok()
        .flatten()
        .map(|r| r.target().id().to_owned())
}

fn hasher_pairs(ids: impl IntoIterator<Item = u64>) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.into_iter()
        .map(|id| (id, Box::new(WideHasher) as Box<dyn Hasher>))
        .collect()
}

// ============================================================================
// 1. NO COMMITS
//
// An implementation could plausibly wrap a checkpoint in a commit for its own
// convenience -- a human-readable `git log`, or an attempt to anchor gc
// reachability itself instead of leaving that to the checkpoint layer. That
// is exactly the responsibility the head's design reserves for the
// checkpoint layer alone ("we have a tip ref that always points at the
// latest tree... commits are higher level permanent commitments, this ref is
// more low level"). Checked exhaustively over the whole object database
// (`git cat-file --batch-check --batch-all-objects`), not a sample of
// coordinates this suite happens to touch, and after every write shape this
// crate's public API exposes: leaves, `add_algorithm`, `remove_algorithm`,
// `resume_algorithm`, a seal, and a resume onto a second ref in the same
// repository.
// ============================================================================

/// [NO COMMITS] Mutation demonstrated in this dispatch's report (see the
/// final turn): wrapping the tip in a `git commit-tree` object inside
/// `GitStorage::write_batch` turns this red immediately, on the very first
/// write, both by the exhaustive object-type scan and by the per-ref kind
/// check below.
#[test]
fn no_commits_created_and_every_staging_ref_targets_a_tree() {
    smol::block_on(async {
        let k = 2u64;
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging_a = "refs/eml/storage/no-commits/a";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging_a, k).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        for i in 0..6u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log.remove_algorithm(1).await.unwrap();
        for i in 6..9u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log.resume_algorithm(1).await.unwrap();
        for i in 9..11u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = log.seal().await.unwrap();

        let staging_b = "refs/eml/storage/no-commits/b";
        let resumed_storage = GitStorage::new(repo.clone(), staging_b, k).unwrap();
        let resume_hashers = hasher_pairs(sealed.frontiers().iter().map(|&(id, _)| id));
        let mut resumed = NaryMerkleLog::resume(&sealed, resumed_storage, resume_hashers)
            .await
            .unwrap();
        for i in 0..3u64 {
            resumed
                .append_subtree(&Subtree::Leaf(format!("fwd-{i}").into_bytes()))
                .await
                .unwrap();
        }
        drop(resumed);

        // Exhaustive, BEFORE any gc: a stray commit object that nothing
        // currently references would be pruned by gc and vanish from this
        // scan, silently laundering exactly the defect this property
        // exists to catch -- so the object-database scan below runs first,
        // and gc (a second, weaker scan of only what survives collection)
        // runs after it, never before.
        //
        // Exhaustive: no commit object anywhere in the object database --
        // never a sample of the coordinates this suite happens to know
        // about.
        let listing = git(
            dir.path(),
            &[
                "cat-file",
                "--batch-check=%(objecttype)",
                "--batch-all-objects",
                "--unordered",
            ],
        );
        let types: Vec<&str> = listing.lines().collect();
        assert!(
            !types.is_empty(),
            "sanity: the object database must not be empty after these writes"
        );
        assert!(
            types.iter().all(|&t| t != "commit"),
            "NO COMMITS: found a commit object among {} objects after writes, add_algorithm, \
             remove_algorithm, resume_algorithm, a seal, and a resume -- storage-git must never \
             create one:\n{listing}",
            types.len()
        );

        // Every staging ref this run created resolves directly to a tree,
        // never a commit.
        let local = repo.to_thread_local();
        for staging in [staging_a, staging_b] {
            let target = ref_target(&local, staging)
                .unwrap_or_else(|| panic!("{staging} must exist after a write"));
            let kind = local.find_header(target).unwrap().kind();
            assert_eq!(
                kind,
                gix::objs::Kind::Tree,
                "NO COMMITS: {staging} must resolve directly to a tree object, never a commit \
                 (got {kind:?})"
            );
        }

        // Re-check after gc too: whatever survives collection must still
        // contain no commit -- gc must never be the thing that quietly
        // removes the evidence of one.
        gc(dir.path());
        let listing_after_gc = git(
            dir.path(),
            &[
                "cat-file",
                "--batch-check=%(objecttype)",
                "--batch-all-objects",
                "--unordered",
            ],
        );
        assert!(
            listing_after_gc.lines().all(|t| t != "commit"),
            "NO COMMITS: found a commit object after gc:\n{listing_after_gc}"
        );
    });
}

// ============================================================================
// 2. COMPLETENESS
//
// An implementation could plausibly drop a digest for every algorithm but
// the first it happens to handle -- exactly RV21's mutation M2 (dropping
// internal-node digests for algorithms other than 0 in `resolve_node`),
// which the gate found `content_addressing.rs`'s own fidelity property (RV6)
// too narrow to catch: it left `content_addressing` and `resume_forward_leaf`
// green, and only `differential` caught it. This property widens exactly
// that gap: every algorithm, every key `MemoryStorage` holds (not merely
// frontier coordinates), across a double resume, a mid-lifecycle reopen from
// disk, and gc.
// ============================================================================

/// Compare `git` against `mem` at every leaf/node key `mem` holds -- an
/// independent oracle that never shares a code path with `GitStorage`, never
/// a second read of `git` against itself.
async fn assert_completeness(git: &GitStorage, mem: &MemoryStorage, context: &str) {
    for (i, expected) in mem.leaves.iter().enumerate() {
        let got = git.get_leaf(i as u64).await.unwrap();
        assert_eq!(
            &got, expected,
            "{context}: COMPLETENESS: get_leaf({i}) diverged from MemoryStorage"
        );
    }
    for (&(alg, left, height), expected) in &mem.nodes {
        let got = git.get_node(alg, left, height).await.unwrap();
        assert_eq!(
            got.as_ref(),
            Some(expected),
            "{context}: COMPLETENESS: get_node(alg={alg}, left={left}, height={height}) diverged \
             from MemoryStorage (git={got:?})"
        );
    }
}

/// [COMPLETENESS] Mutation demonstrated in this dispatch's report: skipping
/// non-zero algorithms in `build::resolve_node`'s digest-map assembly (RV21's
/// M2) turns this red -- `get_node` for algorithm 1 returns `None` where
/// `MemoryStorage` holds a value.
#[test]
fn completeness_every_leaf_and_node_key_survives_gc_and_reopen_across_a_double_resume() {
    smol::block_on(async {
        let k = 2u64;

        // Generation 0: a flat log, algorithm 0 from genesis, algorithm 1
        // registered mid-log (an add_algorithm at an arbitrary size).
        let (_dir0, repo0) = init_repo(HashKind::Sha1);
        let mut git0 = NaryMerkleLog::new(
            GitStorage::new(repo0, "refs/eml/storage/complete/g0", k).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        let mut mem0 = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        for i in 0..3u32 {
            let b = format!("g0-{i}").into_bytes();
            git0.append_leaf(&b).await.unwrap();
            mem0.append_leaf(&b).await.unwrap();
        }
        git0.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        mem0.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        for i in 3..6u32 {
            let b = format!("g0-{i}").into_bytes();
            git0.append_leaf(&b).await.unwrap();
            mem0.append_leaf(&b).await.unwrap();
        }
        let git_sealed0 = git0.seal().await.unwrap();
        let mem_sealed0 = mem0.seal().await.unwrap();

        // Generation 1: first resume (a fork), forward subtree appends, with
        // a genuine reopen from disk midway.
        let (dir1, repo1) = init_repo(HashKind::Sha1);
        let staging1 = "refs/eml/storage/complete/g1";
        let git_storage1 = GitStorage::new(repo1, staging1, k).unwrap();
        let git_hashers1 = hasher_pairs(git_sealed0.frontiers().iter().map(|&(id, _)| id));
        let mem_hashers1 = hasher_pairs(mem_sealed0.frontiers().iter().map(|&(id, _)| id));
        let mut git_log1 = NaryMerkleLog::resume(&git_sealed0, git_storage1, git_hashers1)
            .await
            .unwrap();
        let mut mem_log1 = NaryMerkleLog::resume(&mem_sealed0, MemoryStorage::new(), mem_hashers1)
            .await
            .unwrap();
        for i in 0..3u64 {
            let b = format!("g1-{i}").into_bytes();
            git_log1
                .append_subtree(&Subtree::Leaf(b.clone()))
                .await
                .unwrap();
            mem_log1.append_subtree(&Subtree::Leaf(b)).await.unwrap();
        }
        let git_metas1 = git_log1.storage().load_algorithm_metas().await.unwrap();
        drop(git_log1); // genuine reopen from disk, not an in-memory reuse
        let reopened1 = GitStorage::open(dir1.path(), staging1, k).unwrap();
        let mut git_log1 = NaryMerkleLog::from_storage_with_config(
            reopened1,
            hasher_pairs(git_metas1.iter().map(|&(id, _)| id)),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        for i in 3..6u64 {
            let b = format!("g1-{i}").into_bytes();
            git_log1
                .append_subtree(&Subtree::Leaf(b.clone()))
                .await
                .unwrap();
            mem_log1.append_subtree(&Subtree::Leaf(b)).await.unwrap();
        }
        let git_sealed1 = git_log1.seal().await.unwrap();
        let mem_sealed1 = mem_log1.seal().await.unwrap();

        // Generation 2: a SECOND resume (a double resume) from generation
        // 1's own resumed-and-grown state, plus a remove_algorithm at this
        // new, arbitrary size.
        let (dir2, repo2) = init_repo(HashKind::Sha1);
        let staging2 = "refs/eml/storage/complete/g2";
        let git_storage2 = GitStorage::new(repo2, staging2, k).unwrap();
        let git_hashers2 = hasher_pairs(git_sealed1.frontiers().iter().map(|&(id, _)| id));
        let mem_hashers2 = hasher_pairs(mem_sealed1.frontiers().iter().map(|&(id, _)| id));
        let mut git_log2 = NaryMerkleLog::resume(&git_sealed1, git_storage2, git_hashers2)
            .await
            .unwrap();
        let mut mem_log2 = NaryMerkleLog::resume(&mem_sealed1, MemoryStorage::new(), mem_hashers2)
            .await
            .unwrap();
        for i in 0..3u64 {
            let b = format!("g2-{i}").into_bytes();
            git_log2
                .append_subtree(&Subtree::Leaf(b.clone()))
                .await
                .unwrap();
            mem_log2.append_subtree(&Subtree::Leaf(b)).await.unwrap();
        }
        let _ = git_log2.remove_algorithm(1).await;
        let _ = mem_log2.remove_algorithm(1).await;
        for i in 3..6u64 {
            let b = format!("g2-{i}").into_bytes();
            git_log2
                .append_subtree(&Subtree::Leaf(b.clone()))
                .await
                .unwrap();
            mem_log2.append_subtree(&Subtree::Leaf(b)).await.unwrap();
        }

        assert_completeness(git_log2.storage(), mem_log2.storage(), "live").await;

        drop(git_log2);
        gc(dir2.path());
        let reopened2 = GitStorage::open(dir2.path(), staging2, k).unwrap();
        assert_completeness(&reopened2, mem_log2.storage(), "after gc and reopen").await;
    });
}

// ============================================================================
// 3. WRITTEN IS KEPT
//
// An implementation could plausibly "clean up" a superseded checkpoint --
// deleting an old tip's tree object once a new write supersedes it, on the
// theory that only the current tip matters -- exactly the defect class the
// head's ruling forbids ("historical.rs and tree_at's reconstruction are to
// be deleted" implies the *complete* tree, every size ever committed, must
// still be there for a checkpoint commit to reference later; nothing in
// storage-git's own retention should assume otherwise). This oracle never
// recomputes anything: each recorded id was read straight off the ref right
// after the write that produced it, and every check below is `git` reading
// the raw object database against that recorded id -- never storage-git's
// own API a second time.
// ============================================================================

/// Wrap `tree` in a one-off commit and point a dedicated ref at it,
/// simulating the checkpoint layer the head's design assigns this exact
/// responsibility to ("the checkpoint layer... commits the tree storage
/// already wrote, and those commits are the tree heads"). Every checkpoint
/// gets its own ref, so gc keeps each one reachable independent of the
/// others -- a missing checkpoint never masks another.
fn checkpoint(dir: &Path, tree: ObjectId, label: &str) {
    let commit = git(
        dir,
        &[
            "commit-tree",
            &tree.to_string(),
            "-m",
            &format!("checkpoint {label}"),
        ],
    );
    git(
        dir,
        &["update-ref", &format!("refs/checkpoints/{label}"), &commit],
    );
}

/// Every `(label, tree)` pair in `recorded` must still resolve through its
/// own checkpoint ref, to the exact id recorded -- never a fabricated or
/// re-derived value, the id the ref itself held the moment it was written.
fn assert_all_checkpoints_resolve(dir: &Path, recorded: &[(String, ObjectId)]) {
    for (label, tree) in recorded {
        let resolved = git(
            dir,
            &["rev-parse", &format!("refs/checkpoints/{label}^{{tree}}")],
        );
        assert_eq!(
            resolved,
            tree.to_string(),
            "WRITTEN IS KEPT: checkpoint {label}'s tree {tree} no longer resolves through its own \
             commit after growth, reopen and gc"
        );
    }
}

#[test]
fn written_is_kept_after_growth_reopen_and_gc() {
    smol::block_on(async {
        let k = 2u64;
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kept/staging";
        let local = repo.to_thread_local();
        let mut recorded: Vec<(String, ObjectId)> = Vec::new();

        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging, k).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();

        let record = |label: &str, recorded: &mut Vec<(String, ObjectId)>| {
            let tip =
                ref_target(&local, staging).unwrap_or_else(|| panic!("{label} must have a tip"));
            recorded.push((label.to_string(), tip));
        };

        log.append_leaf(b"one").await.unwrap();
        record("after-leaf-1", &mut recorded);
        log.append_leaf(b"two").await.unwrap();
        record("after-leaf-2", &mut recorded);
        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        record("after-add-algorithm", &mut recorded);
        log.append_leaf(b"three").await.unwrap();
        record("after-leaf-3", &mut recorded);
        log.remove_algorithm(1).await.unwrap();
        record("after-remove-algorithm", &mut recorded);
        log.append_leaf(b"four").await.unwrap();
        record("after-leaf-4", &mut recorded);
        log.resume_algorithm(1).await.unwrap();
        record("after-resume-algorithm", &mut recorded);
        log.append_leaf(b"five").await.unwrap();
        record("after-leaf-5", &mut recorded);

        for (label, tree) in &recorded {
            checkpoint(dir.path(), *tree, label);
        }

        for i in 5..10u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        drop(log);

        let _reopened = GitStorage::open(dir.path(), staging, k).unwrap();
        gc(dir.path());

        assert_all_checkpoints_resolve(dir.path(), &recorded);
    });
}

/// [WRITTEN IS KEPT] The genesis write of a resume from an EMPTY seal is
/// preserved exactly the same way -- the case the previous,
/// reconstruction-based stability property could not even state cleanly
/// (RV4: a resumed empty log's size-0 tree carried a kind byte only a
/// *reconstruction* ever disagreed with). Recording and checking the tree
/// the ref actually holds, with no reconstruction involved, needs no such
/// special case.
#[test]
fn written_is_kept_for_a_resume_from_an_empty_seal() {
    smol::block_on(async {
        let k = 2u64;
        let src = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        let sealed = src.seal().await.unwrap();

        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/kept-empty/staging";
        let local = repo.to_thread_local();
        let storage = GitStorage::new(repo, staging, k).unwrap();
        let mut log = NaryMerkleLog::resume(&sealed, storage, Vec::new())
            .await
            .unwrap();

        let mut recorded = Vec::new();
        let tip0 = ref_target(&local, staging)
            .expect("a resume from an empty seal must still commit a genesis tree");
        recorded.push(("genesis".to_string(), tip0));

        log.add_algorithm(0, Box::new(WideHasher)).await.unwrap();
        recorded.push((
            "after-add-algorithm".to_string(),
            ref_target(&local, staging).unwrap(),
        ));

        log.append_leaf(b"first").await.unwrap();
        recorded.push((
            "after-first-leaf".to_string(),
            ref_target(&local, staging).unwrap(),
        ));

        for (label, tree) in &recorded {
            checkpoint(dir.path(), *tree, label);
        }

        for i in 1..6u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        drop(log);
        let _reopened = GitStorage::open(dir.path(), staging, k).unwrap();
        gc(dir.path());

        assert_all_checkpoints_resolve(dir.path(), &recorded);
    });
}

// ============================================================================
// 4. NO RECONSTRUCTION
//
// The design's own words: "it NEVER renders or reconstructs a tree for a
// past size." `historical.rs` and `GitStorage::tree_at` are the exact named
// symbols the dispatch orders deleted. This is a mechanical source lint, not
// a runtime API check, precisely because a deleted method cannot be called
// to prove its own absence -- checked three independent ways (file
// existence, `mod historical`, and the literal method name) so a half-fix
// that clears only one of them still turns this red.
// ============================================================================

/// [NO RECONSTRUCTION] Red today, for the design's own reason: at 1e88e94
/// `storage-git/src/historical.rs` exists, `lib.rs` declares `mod
/// historical;`, and defines `pub fn tree_at`. Demonstrated in this
/// dispatch's report to survive a half-fix too: renaming `tree_at` alone
/// (leaving `historical.rs` and `mod historical` in place) still fails this
/// lint on the file-existence and module-declaration checks.
#[test]
fn no_reconstruction_of_historical_trees_in_source() {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let src_dir = Path::new(manifest_dir).join("src");

    let historical_path = src_dir.join("historical.rs");
    let mut offending = Vec::new();
    if historical_path.exists() {
        offending.push(format!("{} still exists", historical_path.display()));
    }

    for entry in std::fs::read_dir(&src_dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        for needle in [
            "mod historical",
            "fn tree_at",
            "historical::reconstruct",
            "historical::validate_hashers",
        ] {
            if text.contains(needle) {
                offending.push(format!("{}: contains {needle:?}", path.display()));
            }
        }
    }

    assert!(
        offending.is_empty(),
        "NO RECONSTRUCTION: storage-git's own source still carries historical-reconstruction \
         remnants -- GitStorage::tree_at and the historical module must be deleted outright, not \
         merely unreferenced:\n{}",
        offending.join("\n")
    );
}

// ============================================================================
// 5. HISTORY INDEPENDENCE
//
// An implementation could plausibly bake incidental write-pattern state into
// a checkpoint -- for instance, a byte recording "is this the very first
// write this instance ever made" (a stand-in for provenance the crate's own
// docs already disclaim needing, Departure 4 in `src/lib.rs`) -- so two
// logs with byte-identical logical content, reached through a different
// number or shape of `write_batch` calls, would commit to two different tip
// trees. Checked directly against the staging ref -- never `tree_at` --
// widened past the prior single-scenario coverage to two arities, a flat and
// a subtree-kind log, and both a single-vs-batched and a reopen-midway
// write-sequence split.
// ============================================================================

fn tip_tree(repo: &gix::ThreadSafeRepository, staging: &str) -> ObjectId {
    ref_target(&repo.to_thread_local(), staging)
        .unwrap_or_else(|| panic!("{staging} must have a tip"))
}

/// `n` leaves through `n` separate `append_leaf` calls must produce the
/// identical tip tree as building the identical final state through exactly
/// one `write_batch` call -- the same content, batched differently.
async fn assert_single_vs_batched_flat(k: u64, n: u64, tag: &str) {
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

    let (_dir1, repo1) = init_repo(HashKind::Sha1);
    let staging1 = format!("refs/eml/storage/hist-indep/{tag}/incr");
    let git1 = GitStorage::new(repo1.clone(), &staging1, k).unwrap();
    let mut log1 = NaryMerkleLog::new(git1, Box::new(WideHasher), TreeConfig { arity: k })
        .await
        .unwrap();
    for i in 0..n {
        log1.append_leaf(format!("leaf-{i}").as_bytes())
            .await
            .unwrap();
    }
    drop(log1);
    let tree_incremental = tip_tree(&repo1, &staging1);

    let (_dir2, repo2) = init_repo(HashKind::Sha1);
    let staging2 = format!("refs/eml/storage/hist-indep/{tag}/batch",);
    let mut git2 = GitStorage::new(repo2.clone(), &staging2, k).unwrap();
    let leaves: Vec<(u64, Vec<u8>)> = (0..n)
        .map(|i| (i, format!("leaf-{i}").into_bytes()))
        .collect();
    let leaves_ref: Vec<(u64, &[u8])> = leaves.iter().map(|(i, d)| (*i, d.as_slice())).collect();
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
    drop(git2);
    let tree_batched = tip_tree(&repo2, &staging2);

    assert_eq!(
        tree_incremental, tree_batched,
        "HISTORY INDEPENDENCE (k={k}, n={n}, {tag}): {n} incremental append_leaf calls \
         (tip={tree_incremental}) must reach the identical tip tree as one batched write_batch \
         call (tip={tree_batched})"
    );
}

/// Building `n` subtree-kind leaves straight through must produce the
/// identical tip tree as building the first `n1`, dropping the instance and
/// reopening the same repository path from disk, then appending the rest --
/// a reopen in between changes nothing a reader could call content, for a
/// subtree-kind log exactly as it does for a flat one.
async fn assert_reopen_midway_matches_straight_through_subtree(k: u64, n: u64, n1: u64, tag: &str) {
    let dir_straight = tempfile::tempdir().unwrap();
    let opts = gix::create::Options {
        object_hash: Some(HashKind::Sha1),
        ..Default::default()
    };
    let repo_straight = gix::ThreadSafeRepository::init_opts(
        dir_straight.path(),
        gix::create::Kind::Bare,
        opts,
        Default::default(),
    )
    .unwrap();
    let staging_straight = format!("refs/eml/storage/hist-indep/{tag}/straight");
    let git_straight = GitStorage::new(repo_straight.clone(), &staging_straight, k).unwrap();
    let mut log_straight =
        NaryMerkleLog::new(git_straight, Box::new(WideHasher), TreeConfig { arity: k })
            .await
            .unwrap();
    for i in 0..n {
        log_straight
            .append_subtree(&Subtree::Leaf(format!("leaf-{i}").into_bytes()))
            .await
            .unwrap();
    }
    drop(log_straight);
    let tree_straight = tip_tree(&repo_straight, &staging_straight);

    let dir_split = tempfile::tempdir().unwrap();
    let repo_split = gix::ThreadSafeRepository::init_opts(
        dir_split.path(),
        gix::create::Kind::Bare,
        opts,
        Default::default(),
    )
    .unwrap();
    let staging_split = format!("refs/eml/storage/hist-indep/{tag}/split");
    {
        let git_split = GitStorage::new(repo_split.clone(), &staging_split, k).unwrap();
        let mut log_split =
            NaryMerkleLog::new(git_split, Box::new(WideHasher), TreeConfig { arity: k })
                .await
                .unwrap();
        for i in 0..n1 {
            log_split
                .append_subtree(&Subtree::Leaf(format!("leaf-{i}").into_bytes()))
                .await
                .unwrap();
        }
    } // drop: instance and its in-memory state are gone.
    let git_reopened = GitStorage::open(dir_split.path(), &staging_split, k).unwrap();
    let mut log_reopened = NaryMerkleLog::from_storage_with_config(
        git_reopened,
        hasher_pairs([0]),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    for i in n1..n {
        log_reopened
            .append_subtree(&Subtree::Leaf(format!("leaf-{i}").into_bytes()))
            .await
            .unwrap();
    }
    drop(log_reopened);
    let tree_reopened = tip_tree(&repo_split, &staging_split);

    assert_eq!(
        tree_straight, tree_reopened,
        "HISTORY INDEPENDENCE (k={k}, n={n}, n1={n1}, {tag}, subtree-kind): straight-through \
         (tip={tree_straight}) must equal a reopen at size {n1} (tip={tree_reopened})"
    );
}

#[test]
fn history_independence_single_vs_batched_flat_across_arities() {
    smol::block_on(async {
        for &k in &[2u64, 3] {
            for &n in &[1u64, 5, 7] {
                assert_single_vs_batched_flat(k, n, &format!("flat-{k}-{n}")).await;
            }
        }
    });
}

#[test]
fn history_independence_reopen_midway_matches_straight_through_subtree_across_arities() {
    smol::block_on(async {
        for &k in &[2u64, 3] {
            for &(n, n1) in &[(7u64, 3u64), (9, 4)] {
                assert_reopen_midway_matches_straight_through_subtree(
                    k,
                    n,
                    n1,
                    &format!("subtree-{k}-{n}-{n1}"),
                )
                .await;
            }
        }
    });
}
