//! The tip-tree contract, per the head's design ruling (2026-09-16):
//! storage-git keeps the COMPLETE tree by construction (every leaf and node
//! ever written, by coordinate), one tip ref points DIRECTLY at that tree
//! object (never a commit), it NEVER creates commits, and it NEVER renders
//! or reconstructs a tree for a past size -- that reconstruction is exactly
//! the defect class an earlier revert refusal names: storage making its own
//! commits, and storage rebuilding history it should simply have kept. None
//! of the properties below calls `tree_at` or
//! `register_hasher` -- both scoped to the historical-reconstruction path
//! [`no_reconstruction_no_public_tree_id_accessor_takes_an_argument`] and
//! [`no_reconstruction_no_public_api_accepts_a_hasher`] pin as absent, each
//! by a narrow, named tripwire over the crate's own parsed source (not a
//! general no-reconstruction guarantee -- see each test's own doc comment
//! for exactly what it catches and what it does not) -- and none compares a
//! derived value
//! against another derivation of the same value: every assertion below is
//! checked against an independent oracle (`MemoryStorage`, a tree id
//! recorded straight off the ref at write time, or a `git` command run
//! against the raw object database), never a recomputation compared with
//! itself. That last failure mode is not hypothetical: the previous round's
//! stability property compared `tree_at` before gc against `tree_at` after
//! gc -- a reconstruction against a reconstruction -- and was green by
//! construction regardless of whether the design underneath actually held.

mod common;

use std::path::Path;
use std::process::{Command, Stdio};

use common::{WideHasher, init_repo};
use gix::ObjectId;
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, Subtree, TreeConfig};
use quote::ToTokens;
use storage_git::GitStorage;
use syn::visit::{self, Visit};

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
// repository -- swept across arities 2, 3 and 4 (finding 4), not pinned to
// the binary case alone.
// ============================================================================

/// [NO COMMITS] Demonstrated by mutation: wrapping the tip in a `git commit-tree` object inside
/// `GitStorage::write_batch` turns this red immediately, on the very first
/// write, both by the exhaustive object-type scan and by the per-ref kind
/// check below.
async fn assert_no_commits_and_tree_tip(k: u64) {
    let (dir, repo) = init_repo(HashKind::Sha1);
    let staging_a = format!("refs/eml/storage/no-commits/{k}/a");
    let mut log = NaryMerkleLog::new(
        GitStorage::new(repo.clone(), &staging_a, k).unwrap(),
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

    let staging_b = format!("refs/eml/storage/no-commits/{k}/b");
    let resumed_storage = GitStorage::new(repo.clone(), &staging_b, k).unwrap();
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
        "sanity (k={k}): the object database must not be empty after these writes"
    );
    assert!(
        types.iter().all(|&t| t != "commit"),
        "NO COMMITS (k={k}): found a commit object among {} objects after writes, add_algorithm, \
         remove_algorithm, resume_algorithm, a seal, and a resume -- storage-git must never \
         create one:\n{listing}",
        types.len()
    );

    // Every staging ref this run created resolves directly to a tree,
    // never a commit.
    let local = repo.to_thread_local();
    for staging in [&staging_a, &staging_b] {
        let target = ref_target(&local, staging)
            .unwrap_or_else(|| panic!("{staging} must exist after a write"));
        let kind = local.find_header(target).unwrap().kind();
        assert_eq!(
            kind,
            gix::objs::Kind::Tree,
            "NO COMMITS (k={k}): {staging} must resolve directly to a tree object, never a commit \
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
        "NO COMMITS (k={k}): found a commit object after gc:\n{listing_after_gc}"
    );
}

#[test]
fn no_commits_created_and_every_staging_ref_targets_a_tree() {
    smol::block_on(async {
        for &k in &[2u64, 3, 4] {
            assert_no_commits_and_tree_tip(k).await;
        }
    });
}

// ============================================================================
// 2. COMPLETENESS
//
// An implementation could plausibly drop a digest for every algorithm but
// the first it happens to handle -- a defect actually seen once, dropping
// internal-node digests for algorithms other than 0 in `resolve_node`,
// which a narrower fidelity property (`content_addressing.rs`) was too
// narrow to catch: it left `content_addressing` and `resume_forward_leaf`
// green, and only `differential` caught it. This property widens exactly
// that gap: every algorithm, every key `MemoryStorage` holds (not merely
// frontier coordinates), across a double resume, a mid-lifecycle reopen from
// disk, and gc -- swept across arities 2, 3 and 4.
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

/// [COMPLETENESS] Demonstrated by mutation: skipping
/// non-zero algorithms in `build::resolve_node`'s digest-map assembly
/// turns this red -- `get_node` for algorithm 1 returns `None` where
/// `MemoryStorage` holds a value.
async fn assert_completeness_across_double_resume(k: u64) {
    // Generation 0: a flat log, algorithm 0 from genesis, algorithm 1
    // registered mid-log (an add_algorithm at an arbitrary size).
    let (_dir0, repo0) = init_repo(HashKind::Sha1);
    let mut git0 = NaryMerkleLog::new(
        GitStorage::new(repo0, format!("refs/eml/storage/complete/{k}/g0"), k).unwrap(),
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
    let staging1 = format!("refs/eml/storage/complete/{k}/g1");
    let git_storage1 = GitStorage::new(repo1, &staging1, k).unwrap();
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
    let reopened1 = GitStorage::open(dir1.path(), &staging1, k).unwrap();
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
    let staging2 = format!("refs/eml/storage/complete/{k}/g2");
    let git_storage2 = GitStorage::new(repo2, &staging2, k).unwrap();
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

    assert_completeness(
        git_log2.storage(),
        mem_log2.storage(),
        &format!("k={k}: live"),
    )
    .await;

    drop(git_log2);
    gc(dir2.path());
    let reopened2 = GitStorage::open(dir2.path(), &staging2, k).unwrap();
    assert_completeness(
        &reopened2,
        mem_log2.storage(),
        &format!("k={k}: after gc and reopen"),
    )
    .await;
}

#[test]
fn completeness_every_leaf_and_node_key_survives_gc_and_reopen_across_a_double_resume() {
    smol::block_on(async {
        for &k in &[2u64, 3, 4] {
            assert_completeness_across_double_resume(k).await;
        }
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

/// [finding 5] The reopen used to be a discarded `let _reopened = ...`,
/// asserting nothing at all -- a reopened handle that silently forgot every
/// leaf, or that pointed its `tip_tree()` at some earlier tree, would still
/// have passed. This now asserts both, through the reopened handle itself:
/// [finding 2] its `tip_tree()` accessor equals the ref's own target the
/// instant reopening completes, and every leaf ever written is still
/// readable back out of it, before gc runs at all.
async fn assert_written_is_kept_after_growth_reopen_and_gc(k: u64) {
    let (dir, repo) = init_repo(HashKind::Sha1);
    let staging = format!("refs/eml/storage/kept/{k}/staging");
    let local = repo.to_thread_local();
    let mut recorded: Vec<(String, ObjectId)> = Vec::new();

    let mut log = NaryMerkleLog::new(
        GitStorage::new(repo.clone(), &staging, k).unwrap(),
        Box::new(WideHasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();

    let record = |label: &str, recorded: &mut Vec<(String, ObjectId)>| {
        let tip = ref_target(&local, &staging)
            .unwrap_or_else(|| panic!("k={k}: {label} must have a tip"));
        recorded.push((label.to_string(), tip));
    };

    let mut all_leaves: Vec<Vec<u8>> = Vec::new();
    log.append_leaf(b"one").await.unwrap();
    all_leaves.push(b"one".to_vec());
    record("after-leaf-1", &mut recorded);
    log.append_leaf(b"two").await.unwrap();
    all_leaves.push(b"two".to_vec());
    record("after-leaf-2", &mut recorded);
    log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
    record("after-add-algorithm", &mut recorded);
    log.append_leaf(b"three").await.unwrap();
    all_leaves.push(b"three".to_vec());
    record("after-leaf-3", &mut recorded);
    log.remove_algorithm(1).await.unwrap();
    record("after-remove-algorithm", &mut recorded);
    log.append_leaf(b"four").await.unwrap();
    all_leaves.push(b"four".to_vec());
    record("after-leaf-4", &mut recorded);
    log.resume_algorithm(1).await.unwrap();
    record("after-resume-algorithm", &mut recorded);
    log.append_leaf(b"five").await.unwrap();
    all_leaves.push(b"five".to_vec());
    record("after-leaf-5", &mut recorded);

    for (label, tree) in &recorded {
        checkpoint(dir.path(), *tree, label);
    }

    for i in 5..10u32 {
        let leaf = format!("leaf-{i}").into_bytes();
        log.append_leaf(&leaf).await.unwrap();
        all_leaves.push(leaf);
    }
    let final_tip =
        ref_target(&local, &staging).unwrap_or_else(|| panic!("k={k}: tip must exist before drop"));
    drop(log);

    let reopened = GitStorage::open(dir.path(), &staging, k).unwrap();
    assert_eq!(
        reopened.tip_tree(),
        Some(final_tip),
        "k={k}: reopen: tip_tree() must equal the ref's own target immediately after reopening \
         from disk"
    );
    for (i, expected) in all_leaves.iter().enumerate() {
        let got = reopened.get_leaf(i as u64).await.unwrap();
        assert_eq!(
            &got, expected,
            "k={k}: reopen: get_leaf({i}) diverged from what was written, read through the \
             reopened handle"
        );
    }

    gc(dir.path());

    assert_all_checkpoints_resolve(dir.path(), &recorded);
}

#[test]
fn written_is_kept_after_growth_reopen_and_gc() {
    smol::block_on(async {
        for &k in &[2u64, 3, 4] {
            assert_written_is_kept_after_growth_reopen_and_gc(k).await;
        }
    });
}

/// [WRITTEN IS KEPT] The genesis write of a resume from an EMPTY seal is
/// preserved exactly the same way -- the case the previous,
/// reconstruction-based stability property could not even state cleanly (a
/// resumed empty log's size-0 tree carried a kind byte only a
/// *reconstruction* ever disagreed with). Recording and checking the tree
/// the ref actually holds, with no reconstruction involved, needs no such
/// special case. Same reopen fix as
/// [`assert_written_is_kept_after_growth_reopen_and_gc`], for the
/// resumed-from-empty lifecycle: the reopened handle's
/// `tip_tree()` and every leaf it holds are asserted, not discarded.
async fn assert_written_is_kept_for_a_resume_from_an_empty_seal(k: u64) {
    let src = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(WideHasher),
        TreeConfig { arity: k },
    )
    .await
    .unwrap();
    let sealed = src.seal().await.unwrap();

    let (dir, repo) = init_repo(HashKind::Sha1);
    let staging = format!("refs/eml/storage/kept-empty/{k}/staging");
    let local = repo.to_thread_local();
    let storage = GitStorage::new(repo, &staging, k).unwrap();
    let mut log = NaryMerkleLog::resume(&sealed, storage, Vec::new())
        .await
        .unwrap();

    let mut recorded = Vec::new();
    let tip0 = ref_target(&local, &staging).unwrap_or_else(|| {
        panic!("k={k}: a resume from an empty seal must still commit a genesis tree")
    });
    recorded.push(("genesis".to_string(), tip0));

    log.add_algorithm(0, Box::new(WideHasher)).await.unwrap();
    recorded.push((
        "after-add-algorithm".to_string(),
        ref_target(&local, &staging).unwrap(),
    ));

    log.append_leaf(b"first").await.unwrap();
    recorded.push((
        "after-first-leaf".to_string(),
        ref_target(&local, &staging).unwrap(),
    ));

    for (label, tree) in &recorded {
        checkpoint(dir.path(), *tree, label);
    }

    let mut all_leaves: Vec<Vec<u8>> = vec![b"first".to_vec()];
    for i in 1..6u32 {
        let leaf = format!("leaf-{i}").into_bytes();
        log.append_leaf(&leaf).await.unwrap();
        all_leaves.push(leaf);
    }
    let final_tip =
        ref_target(&local, &staging).unwrap_or_else(|| panic!("k={k}: tip must exist before drop"));
    drop(log);

    let reopened = GitStorage::open(dir.path(), &staging, k).unwrap();
    assert_eq!(
        reopened.tip_tree(),
        Some(final_tip),
        "k={k}: reopen: tip_tree() must equal the ref's own target immediately after reopening \
         from disk"
    );
    for (i, expected) in all_leaves.iter().enumerate() {
        let got = reopened.get_leaf(i as u64).await.unwrap();
        assert_eq!(
            &got, expected,
            "k={k}: reopen: get_leaf({i}) diverged from what was written, read through the \
             reopened handle"
        );
    }

    gc(dir.path());

    assert_all_checkpoints_resolve(dir.path(), &recorded);
}

#[test]
fn written_is_kept_for_a_resume_from_an_empty_seal() {
    smol::block_on(async {
        for &k in &[2u64, 3, 4] {
            assert_written_is_kept_for_a_resume_from_an_empty_seal(k).await;
        }
    });
}

// ============================================================================
// 4. TWO NAMED TRIPWIRES, NOT A NO-RECONSTRUCTION GUARANTEE
//
// An earlier review found that the two checks below, despite
// this section's former header calling them "a structural, rename-proof
// check," catch exactly ONE historical shape each -- not reconstruction in
// general. That review demonstrated eight compiling evasions of the design's
// own "never renders or reconstructs a tree for a past size" rule that both
// checks let straight through: a free `pub fn` in a `pub mod` (module
// privacy gates ordinary item paths, not this lint, which only walks
// INHERENT impls on named types), a wrapper return type (`TreeId`,
// `TreeRef`) instead of `ObjectId` in the token text, a `pub trait
// Checkpoints` implemented for `GitStorage`, and a parameter type aliased
// away from the literal name `Hasher`. A textual name lint on `tree_at`
// alone would have been weaker still (renaming the method name defeats it
// outright); this lint is stronger than that but not "rename-proof" against
// anything except the two specific narrow shapes it names below, and its
// own doc comments say so rather than implying more.
//
// What each check actually does: parse every `.rs` file under `src/` as a
// syntax tree (`syn::parse_file`) and walk its `impl GitStorage { .. }` /
// `impl GitReadOnlyView { .. }` blocks (inherent impls only, not trait
// impls) for a `pub fn` whose SHAPE matches one of two named patterns --
// see each test's own doc comment for which. This does survive a rename of
// the METHOD or its containing MODULE while the shape stays the same
// (demonstrated by that same review, against `tree_at` renamed to
// `checkpoint_at` with `historical.rs` renamed to `reconstruction.rs`):
// renaming changes neither the type an inherent impl is on nor the `pub`
// keyword on the method itself. It does not survive a DIFFERENT shape
// carrying the same capability, which is exactly what those eight evasions
// were.
// ============================================================================

/// One `pub fn` found inside an inherent `impl <target-type> { .. }` block
/// anywhere in `src/`, described by shape rather than by name: which file
/// declared it (for a readable failure message only), its name (likewise --
/// never matched against), the token text of each non-`self` parameter's
/// type, and the token text of its return type (`""` for `-> ()`).
struct PubMethod {
    file: String,
    name: String,
    params: Vec<String>,
    ret: String,
}

/// Walks one parsed file's inherent impl blocks (never `impl Trait for
/// Type` -- a trait impl's method visibility is bounded by the trait's own,
/// already-public surface, e.g. `polydigest::Storage`, not by anything this
/// crate could quietly widen) for any block whose `Self` type's last path
/// segment names one of `targets`, collecting every `pub fn` inside it.
struct ImplVisitor<'a> {
    targets: &'a [&'a str],
    file: String,
    out: Vec<PubMethod>,
}

impl<'a> Visit<'a> for ImplVisitor<'a> {
    fn visit_item_impl(&mut self, node: &'a syn::ItemImpl) {
        if node.trait_.is_none() {
            if let syn::Type::Path(tp) = &*node.self_ty {
                if let Some(seg) = tp.path.segments.last() {
                    let type_name = seg.ident.to_string();
                    if self.targets.contains(&type_name.as_str()) {
                        for item in &node.items {
                            if let syn::ImplItem::Fn(f) = item {
                                if matches!(f.vis, syn::Visibility::Public(_)) {
                                    let params = f
                                        .sig
                                        .inputs
                                        .iter()
                                        .filter_map(|arg| match arg {
                                            syn::FnArg::Receiver(_) => None,
                                            syn::FnArg::Typed(pt) => {
                                                Some(pt.ty.to_token_stream().to_string())
                                            },
                                        })
                                        .collect();
                                    let ret = match &f.sig.output {
                                        syn::ReturnType::Default => String::new(),
                                        syn::ReturnType::Type(_, ty) => {
                                            ty.to_token_stream().to_string()
                                        },
                                    };
                                    self.out.push(PubMethod {
                                        file: self.file.clone(),
                                        name: f.sig.ident.to_string(),
                                        params,
                                        ret,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        visit::visit_item_impl(self, node);
    }
}

/// Every `pub fn` inherently implemented on any of `targets`, across every
/// `.rs` file directly under `manifest_dir/src` (this crate declares no
/// nested `src/` submodule directories, so one level is exhaustive).
fn public_methods_on(targets: &[&str]) -> Vec<PubMethod> {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let src_dir = Path::new(manifest_dir).join("src");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&src_dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let parsed = syn::parse_file(&text)
            .unwrap_or_else(|e| panic!("{}: failed to parse as Rust: {e}", path.display()));
        let mut visitor = ImplVisitor {
            targets,
            file: path.display().to_string(),
            out: Vec::new(),
        };
        visitor.visit_file(&parsed);
        out.extend(visitor.out);
    }
    out
}

fn format_methods(methods: &[&PubMethod]) -> String {
    methods
        .iter()
        .map(|m| {
            format!(
                "{} :: pub fn {}({:?}) -> {:?}",
                m.file, m.name, m.params, m.ret
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// [NARROW TRIPWIRE] Catches exactly this shape: an inherent
/// `GitStorage` method whose return type's tokens mention `ObjectId` AND
/// which takes at least one argument beyond `&self` -- e.g. the deleted
/// `GitStorage::tree_at(&self, n: u64) -> Result<ObjectId, GitStorageError>`,
/// under that name or any rename of the method or its containing module
/// (demonstrated by an earlier review against `tree_at` ->
/// `checkpoint_at`, `historical.rs` -> `reconstruction.rs`). It does NOT
/// catch a same-capability accessor in a different shape: that review also
/// showed a
/// free `pub fn` outside any inherent impl, a wrapper return type whose
/// tokens do not contain the literal string `ObjectId` (e.g. a `TreeId`
/// newtype), or a `pub trait` implemented for `GitStorage` all compile and
/// leave this test green. Green today would mean the only method returning
/// a tree id is the parameterless `tip_tree` -- there is no
/// argument-taking accessor of this exact shape to find.
#[test]
fn no_reconstruction_no_public_tree_id_accessor_takes_an_argument() {
    let methods = public_methods_on(&["GitStorage"]);
    assert!(
        !methods.is_empty(),
        "sanity: GitStorage must expose at least one public method"
    );

    let offending: Vec<&PubMethod> = methods
        .iter()
        .filter(|m| m.ret.contains("ObjectId") && !m.params.is_empty())
        .collect();

    assert!(
        offending.is_empty(),
        "NO RECONSTRUCTION: GitStorage exposes a public method that returns a tree id AND takes \
         an argument naming which one -- storage-git must never render or reconstruct a tree for \
         a past size, so the only tree id it may ever hand out is the current tip, which needs no \
         argument to select it:\n{}",
        format_methods(&offending)
    );
}

/// [NARROW TRIPWIRE] Catches exactly this shape: an inherent
/// `GitStorage`/`GitReadOnlyView` method with a parameter whose type tokens
/// contain the literal substring `Hasher` -- e.g. the deleted
/// `GitStorage::register_hasher(&mut self, alg_id: u64, hasher: Box<dyn
/// Hasher>)`, under any rename of the method itself (this check is keyed on
/// the parameter's TYPE, not the method's name). It does NOT catch the same
/// capability spelled differently: that same review showed a parameter whose type is
/// aliased away from the literal name `Hasher` (`use spine::Hasher as
/// Fold;` and a parameter typed `Box<dyn Fold>`) compiles and leaves this
/// test green. Green today would mean this crate's live write/read path
/// still never computes a digest or folds a root (SG26) -- there is no
/// method of this exact shape to find.
#[test]
fn no_reconstruction_no_public_api_accepts_a_hasher() {
    let methods = public_methods_on(&["GitStorage", "GitReadOnlyView"]);

    let offending: Vec<&PubMethod> = methods
        .iter()
        .filter(|m| m.params.iter().any(|p| p.contains("Hasher")))
        .collect();

    assert!(
        offending.is_empty(),
        "NO RECONSTRUCTION: a public method accepts a hasher -- this crate's live path never \
         computes a digest or folds a root, so no public method may accept one under any name:\n{}",
        format_methods(&offending)
    );
}

// ============================================================================
// 5. TIP ACCESSOR
//
// Once `tree_at` is deleted, `GitStorage` has no public
// accessor for the current tip tree at all -- and the checkpoint layer the
// head's design assigns commit-wrapping responsibility to needs exactly
// that (it "commits the tree storage already wrote"). This pins the method
// the implementer must add: `pub fn tip_tree(&self) -> Option<ObjectId>`
// (`None` only for a genesis instance whose staging ref has never been
// written). Calling it here, on a method that does not exist yet, is a
// compile failure until it is added; a stub that never updates, or that
// caches a stale
// value, is caught by the equality assertion against `ref_target` (an
// independent oracle, the ref itself) after every write shape this crate's
// public API exposes.
// ============================================================================

/// [TIP ACCESSOR] `tip_tree()` must equal the ref's own target after every
/// write shape (leaves, add/remove/resume algorithm, seal, a resume onto
/// fresh storage, and a reopen from disk) and must never lag behind it --
/// checked by direct equality against `ref_target` immediately after each
/// step, so a stale cache (returning what used to be the tip) or a cache
/// that updates only sometimes both turn this red immediately.
#[test]
fn tip_tree_accessor_matches_the_ref_after_every_write_shape() {
    smol::block_on(async {
        let k = 2u64;
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/tip-accessor/staging";
        let local = repo.to_thread_local();

        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging, k).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();

        let mut seen = Vec::new();
        let check = |log: &NaryMerkleLog<GitStorage>, step: &str, seen: &mut Vec<ObjectId>| {
            let expected = ref_target(&local, staging);
            let got = log.storage().tip_tree();
            assert_eq!(
                got, expected,
                "TIP ACCESSOR: after {step}, tip_tree() must equal the ref's own target"
            );
            if let Some(id) = got {
                seen.push(id);
            }
        };

        log.append_leaf(b"one").await.unwrap();
        check(&log, "append_leaf(one)", &mut seen);
        log.append_leaf(b"two").await.unwrap();
        check(&log, "append_leaf(two)", &mut seen);
        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        check(&log, "add_algorithm(1)", &mut seen);
        log.append_leaf(b"three").await.unwrap();
        check(&log, "append_leaf(three)", &mut seen);
        log.remove_algorithm(1).await.unwrap();
        check(&log, "remove_algorithm(1)", &mut seen);
        log.resume_algorithm(1).await.unwrap();
        check(&log, "resume_algorithm(1)", &mut seen);
        log.append_leaf(b"four").await.unwrap();
        check(&log, "append_leaf(four)", &mut seen);

        // Every observed tip so far must be distinct: a content-changing
        // write that left the accessor pointing at an earlier tree would
        // still (incorrectly) pass the direct per-step check above only if
        // it happened to repeat a value, which never legitimately happens
        // here since every step changes the tree's content.
        let mut dedup = seen.clone();
        dedup.sort();
        dedup.dedup();
        assert_eq!(
            dedup.len(),
            seen.len(),
            "TIP ACCESSOR: two different write steps reported the identical tip -- tip_tree() \
             must never return an earlier tree"
        );

        let sealed = log.seal().await.unwrap();
        let staging2 = "refs/eml/storage/tip-accessor/resumed";
        let resumed_storage = GitStorage::new(repo.clone(), staging2, k).unwrap();
        let hashers = hasher_pairs(sealed.frontiers().iter().map(|&(id, _)| id));
        let mut resumed = NaryMerkleLog::resume(&sealed, resumed_storage, hashers)
            .await
            .unwrap();
        assert_eq!(
            resumed.storage().tip_tree(),
            ref_target(&local, staging2),
            "TIP ACCESSOR: after resume onto fresh storage, tip_tree() must equal the ref's own \
             target"
        );
        resumed
            .append_subtree(&Subtree::Leaf(b"fwd".to_vec()))
            .await
            .unwrap();
        assert_eq!(
            resumed.storage().tip_tree(),
            ref_target(&local, staging2),
            "TIP ACCESSOR: after a forward append on the resumed log, tip_tree() must equal the \
             ref's own target"
        );
        drop(resumed);

        let reopened = GitStorage::open(dir.path(), staging2, k).unwrap();
        assert_eq!(
            reopened.tip_tree(),
            ref_target(&local, staging2),
            "TIP ACCESSOR: after reopening from disk, tip_tree() must equal the ref's own target"
        );
    });
}

// ============================================================================
// 6. HISTORY INDEPENDENCE
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

// ============================================================================
// 7. CANONICAL SIZE ZERO
//
// The spec's SG9 states that at n == 0, `meta.kind` is fixed to the
// canonical value 0x00 for every log, independent of whether it is a fresh
// log or an empty-seal resume -- every `polydigest` accessor is
// observationally identical between the two at count 0 (`kind()`'s only
// effect gates `flat_leaf_count`/`subtree_leaf_count`, both 0 regardless of
// kind at count 0; `begin_flat`/`begin_subtree`'s own conflict check is
// itself count>0-gated). The write side was never made to honor this:
// a fresh log's `C(0)` carries kind 0, a resume from an empty seal commits
// kind 1, and identical (arity, count=0, key set) content therefore gets
// two different tree ids -- a history-independence gap at exactly the one
// size every log passes through.
// ============================================================================

/// [CANONICAL SIZE ZERO] RED at 60f93fe: a fresh log and a log
/// resumed from an empty seal, both at count 0 with algorithm 0 the only
/// registered algorithm, must commit the identical `C(0)` -- kind is
/// observationally meaningless at count 0, so encoding the caller's
/// requested kind there makes two provenance-different-but-content-
/// identical logs diverge for no benefit. Once each takes one real forward
/// step (a flat leaf vs. a forward subtree leaf), the trees MUST
/// (correctly) diverge: kind genuinely distinguishes history once count
/// exceeds 0, so this canonicalization must never bleed forward past it.
#[test]
fn canonical_size_zero_tree_is_independent_of_requested_kind() {
    smol::block_on(async {
        let k = 2u64;

        // A fresh log: `NaryMerkleLog::new` eagerly registers algorithm 0,
        // writing `meta` at count 0 with kind fixed at its default (0).
        let (_dir_fresh, repo_fresh) = init_repo(HashKind::Sha1);
        let staging_fresh = "refs/eml/storage/canonical-zero/fresh";
        let fresh_storage = GitStorage::new(repo_fresh.clone(), staging_fresh, k).unwrap();
        let mut fresh_log =
            NaryMerkleLog::new(fresh_storage, Box::new(WideHasher), TreeConfig { arity: k })
                .await
                .unwrap();

        // A log resumed from an EMPTY seal: `NaryMerkleLog::resume` always
        // writes `log_meta = Some((size, LogKind::Subtree.to_byte()))`, even
        // at size 0 -- the exact divergence this test pins.
        let empty_src = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(WideHasher),
            TreeConfig { arity: k },
        )
        .await
        .unwrap();
        let empty_sealed = empty_src.seal().await.unwrap();

        let (_dir_resumed, repo_resumed) = init_repo(HashKind::Sha1);
        let staging_resumed = "refs/eml/storage/canonical-zero/resumed";
        let resumed_storage = GitStorage::new(repo_resumed.clone(), staging_resumed, k).unwrap();
        let mut resumed_log = NaryMerkleLog::resume(
            &empty_sealed,
            resumed_storage,
            vec![(0, Box::new(WideHasher) as Box<dyn Hasher>)],
        )
        .await
        .unwrap();

        let tip_fresh = ref_target(&repo_fresh.to_thread_local(), staging_fresh)
            .expect("a fresh log with algorithm 0 registered must have a tip at count 0");
        let tip_resumed = ref_target(&repo_resumed.to_thread_local(), staging_resumed)
            .expect("a resume from an empty seal must commit a genesis tree at count 0");
        assert_eq!(
            tip_fresh, tip_resumed,
            "CANONICAL SIZE ZERO: a fresh log and a resume from an empty seal, both at count 0 \
             with only algorithm 0 registered, must commit the identical C(0) regardless of the \
             requested kind byte"
        );

        // One real forward step each -- the trees must now (correctly)
        // diverge: kind is no longer observationally meaningless once count
        // exceeds 0.
        fresh_log.append_leaf(b"x").await.unwrap();
        resumed_log
            .append_subtree(&Subtree::Leaf(b"x".to_vec()))
            .await
            .unwrap();

        let tip_fresh_after = ref_target(&repo_fresh.to_thread_local(), staging_fresh).unwrap();
        let tip_resumed_after =
            ref_target(&repo_resumed.to_thread_local(), staging_resumed).unwrap();
        assert_ne!(
            tip_fresh_after, tip_resumed_after,
            "kind must genuinely distinguish histories once count exceeds 0 -- the size-zero \
             canonicalization must not bleed forward"
        );
    });
}
