//! [APPLY PRECONDITION PARITY] Merge-gate blocking conditions AC6/AC21
//! (`.ledger/deposits/git-backend/lead-maintainer/storage-git-apply-contract-gate.md`):
//! `Storage::apply`'s documented MUSTs -- reject a duplicate algorithm
//! registration, reject an append at the wrong position, and (by the same
//! logic, stated in `WriteOp::SeedFrontier`'s own doc as a precondition in
//! prose) reject seeding a frontier onto a store that is not genuinely
//! fresh -- must hold identically on both `MemoryStorage` and `GitStorage`.
//! Every test here drives `Storage::apply` directly, bypassing
//! `NaryMerkleLog`, exactly as the gate's own probe did.
//!
//! Found RED during this gate's test-authoring pass and fixed by
//! `f781b0b` (landed after this file's own `9177ffd`, so every test below
//! is pinned green against the fix, not against the original defect):
//!
//! - `seed_frontier_onto_a_populated_store_is_rejected_on_git` and `..._on_memory`:
//!   `WriteOp::SeedFrontier` silently rewound `append_count`/`count` on a store that already held
//!   committed appends, on both backends. `MemoryStorage`'s validation arm for this variant was
//!   `WriteOp::SeedFrontier { .. } => {}` -- literally empty. `GitStorage` only checked that the
//!   seeded algorithm ids were not already registered; it never checked that the store itself was
//!   fresh.
//! - `duplicate_add_algorithm_in_one_batch_is_rejected_on_memory`: a batch carrying two
//!   `WriteOp::AddAlgorithm` for the same id returned `Ok(())` on `MemoryStorage`, silently
//!   overwriting the first registration, although the trait's own `apply` doc makes rejecting a
//!   duplicate registration a MUST. `GitStorage` already rejected this (the parity target the fix
//!   brought `MemoryStorage` up to).
//!
//! Two more asymmetries were found while enumerating every MUST this file
//! checks (not in the gate's deposit; found during this pass, same root
//! cause as the two above -- `MemoryStorage`'s `SeedFrontier` and
//! `AddAlgorithm` validation arms not projecting registration state the
//! way `GitStorage`'s `known()` closure does), and fixed by the same commit:
//!
//! - `seed_frontier_with_a_duplicate_algorithm_id_is_rejected_on_memory`: a single `SeedFrontier`
//!   batch naming the same `alg_id` twice in its own `algorithms` list returned `Ok(())` on
//!   `MemoryStorage` (silently keeping only the last write) and `Err` on `GitStorage`.
//! - `add_then_remove_same_algorithm_in_one_batch_matches_across_backends`: a single batch that
//!   both registers and immediately freezes the same algorithm id was accepted on `GitStorage`
//!   (its `known()` closure projects `registered_this_batch` forward within the call) but rejected
//!   on `MemoryStorage` (whose two-pass validator checked `RemoveAlgorithm`'s precondition against
//!   `self.algorithm_metas` alone, never against what the same batch just registered) -- the
//!   opposite direction from the other three: `MemoryStorage` wrongly refused a batch `GitStorage`
//!   correctly accepted.
//!
//! Enumerated and confirmed identical on both backends from the start (pinned
//! green, never blocking, included so the coverage-vs-doc gap stated in the
//! dispatch is visible): an append at a position other than the current count
//! (`AppendLeaf` and `AppendSubtree`, each), a `RemoveAlgorithm`/
//! `ResumeAlgorithm` naming an algorithm the store has never registered.
//! NOT checked here (out of the trait doc's stated MUSTs, so left as an
//! open question rather than assumed either way): resuming an algorithm
//! that is currently active (never frozen), or removing an
//! already-frozen algorithm a second time.

mod common;

use common::init_repo;
use gix::hash::Kind as HashKind;
use polydigest::{AlgorithmSeed, MemoryStorage, Storage, WriteOp};
use storage_git::GitStorage;

/// Populate a fresh store with `n` leaves via direct `Storage::apply`
/// calls, bypassing `NaryMerkleLog` -- the same level the gate's own probe
/// drove this defect at.
async fn append_n_leaves<S: Storage>(storage: &mut S, n: u64) {
    for i in 0..n {
        storage
            .apply(&[WriteOp::AppendLeaf {
                at: i,
                data: format!("leaf-{i}").as_bytes(),
                nodes: &[],
            }])
            .await
            .unwrap_or_else(|_| panic!("append_n_leaves: leaf {i} must apply cleanly"));
    }
}

// ============================================================================
// 1. THE REWIND DEFECT (AC6, AC21) -- blocking
// ============================================================================

#[test]
fn seed_frontier_onto_a_populated_store_is_rejected_on_memory() {
    smol::block_on(async {
        let mut storage = MemoryStorage::new();
        append_n_leaves(&mut storage, 5).await;
        assert_eq!(storage.append_count().await.unwrap(), 5);
        assert_eq!(storage.len().await.unwrap(), 5);
        let leaf4_before = storage.get_leaf(4).await.unwrap();

        let result = storage
            .apply(&[WriteOp::SeedFrontier {
                size: 2,
                algorithms: &[],
            }])
            .await;

        assert!(
            result.is_err(),
            "SeedFrontier onto a MemoryStorage that already holds 5 committed appends must be \
             rejected, not silently rewind the count -- got {result:?}"
        );
        assert_eq!(
            storage.append_count().await.unwrap(),
            5,
            "a rejected SeedFrontier must leave append_count untouched"
        );
        assert_eq!(
            storage.len().await.unwrap(),
            5,
            "a rejected SeedFrontier must leave the leaf count untouched"
        );
        assert_eq!(
            storage.get_leaf(4).await.unwrap(),
            leaf4_before,
            "a rejected SeedFrontier must leave leaf 4 readable and unchanged"
        );
    });
}

#[test]
fn seed_frontier_onto_a_populated_store_is_rejected_on_git() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage =
            GitStorage::new(repo, "refs/eml/storage/apply-parity/rewind/staging", 2).unwrap();
        append_n_leaves(&mut storage, 5).await;
        assert_eq!(storage.append_count().await.unwrap(), 5);
        assert_eq!(storage.len().await.unwrap(), 5);
        let tip_before = storage.tip_tree();
        let leaf4_before = storage.get_leaf(4).await.unwrap();

        let result = storage
            .apply(&[WriteOp::SeedFrontier {
                size: 2,
                algorithms: &[],
            }])
            .await;

        assert!(
            result.is_err(),
            "SeedFrontier onto a GitStorage that already holds 5 committed appends must be \
             rejected, not silently rewind the staging ref -- got {result:?}"
        );
        assert_eq!(
            storage.append_count().await.unwrap(),
            5,
            "a rejected SeedFrontier must leave append_count untouched"
        );
        assert_eq!(
            storage.len().await.unwrap(),
            5,
            "a rejected SeedFrontier must leave the leaf count untouched"
        );
        assert_eq!(
            storage.tip_tree(),
            tip_before,
            "a rejected SeedFrontier must leave the staging ref's observed tip untouched"
        );
        assert_eq!(
            storage.get_leaf(4).await.unwrap(),
            leaf4_before,
            "a rejected SeedFrontier must leave leaf 4 readable and unchanged, not orphan its \
             still-present blob behind an unreadable index"
        );
    });
}

/// [COHERENCE INVARIANT] No backend may ever report `append_count() <
/// len()` -- an in-order append moves both forward together by exactly one,
/// so the only way to observe fewer appends than stored leaves is a write
/// that rewound `append_count` without touching the leaves it already
/// committed. Checked independently of whether the rejecting backend
/// happens to return `Err` (AC6's own framing: the pair `count=2,
/// leaves_still=5` is "the exact pair the derived-kind rule reads"), so
/// this stays meaningful even if some future fix chose a different
/// enforcement shape than a hard error.
#[test]
fn seed_frontier_rewind_never_leaves_memory_storage_incoherent() {
    smol::block_on(async {
        let mut storage = MemoryStorage::new();
        append_n_leaves(&mut storage, 5).await;

        let result = storage
            .apply(&[WriteOp::SeedFrontier {
                size: 2,
                algorithms: &[],
            }])
            .await;

        let count = storage.append_count().await.unwrap();
        let len = storage.len().await.unwrap();
        assert!(
            count >= len,
            "MemoryStorage must never report append_count() ({count}) < len() ({len}) -- this is \
             the incoherent pair AC6 names as exactly what the derived-kind rule reads; \
             SeedFrontier result was {result:?}"
        );
    });
}

// ============================================================================
// 2. BACKEND PARITY ON DUPLICATE REGISTRATION (AC6, AC21) -- blocking
// ============================================================================

#[test]
fn duplicate_add_algorithm_in_one_batch_is_rejected_on_memory() {
    smol::block_on(async {
        let mut storage = MemoryStorage::new();
        let ops = [
            WriteOp::AddAlgorithm {
                alg_id: 7,
                epochs: &[(0, u64::MAX)],
            },
            WriteOp::AddAlgorithm {
                alg_id: 7,
                epochs: &[(0, u64::MAX)],
            },
        ];
        let result = storage.apply(&ops).await;
        assert!(
            result.is_err(),
            "a batch registering algorithm 7 twice must be rejected on MemoryStorage, matching \
             the trait's own apply doc (\"MUST return an error ... a duplicate registration\") \
             and GitStorage's existing behavior -- got {result:?}"
        );
    });
}

/// Pinned green: this is the parity target the memory-side test above must
/// come to match, not a new claim.
#[test]
fn duplicate_add_algorithm_in_one_batch_is_rejected_on_git() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage =
            GitStorage::new(repo, "refs/eml/storage/apply-parity/dup-add/staging", 2).unwrap();
        let ops = [
            WriteOp::AddAlgorithm {
                alg_id: 7,
                epochs: &[(0, u64::MAX)],
            },
            WriteOp::AddAlgorithm {
                alg_id: 7,
                epochs: &[(0, u64::MAX)],
            },
        ];
        let result = storage.apply(&ops).await;
        assert!(
            result.is_err(),
            "a batch registering algorithm 7 twice must be rejected on GitStorage -- got \
             {result:?}"
        );
    });
}

// ============================================================================
// 3. ADDITIONAL ASYMMETRIES FOUND WHILE ENUMERATING (same root cause as #1, not in the gate's
//    deposit)
// ============================================================================

#[test]
fn seed_frontier_with_a_duplicate_algorithm_id_is_rejected_on_memory() {
    smol::block_on(async {
        let mut storage = MemoryStorage::new();
        let seeds = [
            AlgorithmSeed {
                alg_id: 3,
                epochs: &[(0, u64::MAX)],
                nodes: &[],
            },
            AlgorithmSeed {
                alg_id: 3,
                epochs: &[(0, u64::MAX)],
                nodes: &[],
            },
        ];
        let result = storage
            .apply(&[WriteOp::SeedFrontier {
                size: 0,
                algorithms: &seeds,
            }])
            .await;
        assert!(
            result.is_err(),
            "a SeedFrontier batch naming algorithm 3 twice in its own algorithms list must be \
             rejected on MemoryStorage, matching GitStorage's existing behavior -- got {result:?}"
        );
    });
}

/// Pinned green: this is the parity target the memory-side test above must
/// come to match, not a new claim.
#[test]
fn seed_frontier_with_a_duplicate_algorithm_id_is_rejected_on_git() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage =
            GitStorage::new(repo, "refs/eml/storage/apply-parity/dup-seed/staging", 2).unwrap();
        let seeds = [
            AlgorithmSeed {
                alg_id: 3,
                epochs: &[(0, u64::MAX)],
                nodes: &[],
            },
            AlgorithmSeed {
                alg_id: 3,
                epochs: &[(0, u64::MAX)],
                nodes: &[],
            },
        ];
        let result = storage
            .apply(&[WriteOp::SeedFrontier {
                size: 0,
                algorithms: &seeds,
            }])
            .await;
        assert!(
            result.is_err(),
            "a SeedFrontier batch naming algorithm 3 twice in its own algorithms list must be \
             rejected on GitStorage -- got {result:?}"
        );
    });
}

/// A single atomic batch that registers algorithm 11 and freezes it again
/// in the same call must be treated identically by both backends -- whether
/// that means both accept it (as an atomic register-then-freeze) or both
/// reject it is a design choice for the head, but the two backends
/// disagreeing on a batch where every individual op's own stated
/// precondition is satisfied is a parity bug either way. `GitStorage`
/// accepts it today; this test pins `MemoryStorage` to match, since
/// `GitStorage`'s behavior is the one that fits an atomic-batch semantics
/// where later ops in the same call see earlier ones' effects.
#[test]
fn add_then_remove_same_algorithm_in_one_batch_matches_across_backends() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut git = GitStorage::new(
            repo,
            "refs/eml/storage/apply-parity/add-then-remove/staging",
            2,
        )
        .unwrap();
        let ops = [
            WriteOp::AddAlgorithm {
                alg_id: 11,
                epochs: &[(0, u64::MAX)],
            },
            WriteOp::RemoveAlgorithm {
                alg_id: 11,
                epochs: &[(0, 0)],
            },
        ];
        let git_result = git.apply(&ops).await;
        assert!(
            git_result.is_ok(),
            "GitStorage's own current behavior (the parity target) must accept a batch that \
             registers and freezes the same algorithm atomically -- got {git_result:?}"
        );

        let mut mem = MemoryStorage::new();
        let mem_result = mem.apply(&ops).await;
        assert!(
            mem_result.is_ok(),
            "MemoryStorage must match GitStorage and accept a batch that registers and freezes \
             the same algorithm atomically -- MemoryStorage's two-pass validator currently checks \
             RemoveAlgorithm's precondition against self.algorithm_metas alone, never against \
             what this same batch just registered, so it wrongly refuses this batch today -- got \
             {mem_result:?}"
        );
    });
}

// ============================================================================
// 4. PARITY ALREADY HELD, PINNED GREEN (enumerated for coverage, not blocking -- named MUSTs from
//    the trait's own apply doc)
// ============================================================================

#[test]
fn append_leaf_at_wrong_position_is_rejected_on_both_backends() {
    smol::block_on(async {
        let mut mem = MemoryStorage::new();
        let mem_result = mem
            .apply(&[WriteOp::AppendLeaf {
                at: 5,
                data: b"x",
                nodes: &[],
            }])
            .await;
        assert!(mem_result.is_err(), "MemoryStorage: {mem_result:?}");

        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut git = GitStorage::new(
            repo,
            "refs/eml/storage/apply-parity/wrong-pos-leaf/staging",
            2,
        )
        .unwrap();
        let git_result = git
            .apply(&[WriteOp::AppendLeaf {
                at: 5,
                data: b"x",
                nodes: &[],
            }])
            .await;
        assert!(git_result.is_err(), "GitStorage: {git_result:?}");
    });
}

#[test]
fn append_subtree_at_wrong_position_is_rejected_on_both_backends() {
    smol::block_on(async {
        let mut mem = MemoryStorage::new();
        let mem_result = mem
            .apply(&[WriteOp::AppendSubtree { at: 5, nodes: &[] }])
            .await;
        assert!(mem_result.is_err(), "MemoryStorage: {mem_result:?}");

        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut git = GitStorage::new(
            repo,
            "refs/eml/storage/apply-parity/wrong-pos-subtree/staging",
            2,
        )
        .unwrap();
        let git_result = git
            .apply(&[WriteOp::AppendSubtree { at: 5, nodes: &[] }])
            .await;
        assert!(git_result.is_err(), "GitStorage: {git_result:?}");
    });
}

#[test]
fn remove_unregistered_algorithm_is_rejected_on_both_backends() {
    smol::block_on(async {
        let mut mem = MemoryStorage::new();
        let mem_result = mem
            .apply(&[WriteOp::RemoveAlgorithm {
                alg_id: 9,
                epochs: &[(0, 3)],
            }])
            .await;
        assert!(mem_result.is_err(), "MemoryStorage: {mem_result:?}");

        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut git = GitStorage::new(
            repo,
            "refs/eml/storage/apply-parity/unreg-remove/staging",
            2,
        )
        .unwrap();
        let git_result = git
            .apply(&[WriteOp::RemoveAlgorithm {
                alg_id: 9,
                epochs: &[(0, 3)],
            }])
            .await;
        assert!(git_result.is_err(), "GitStorage: {git_result:?}");
    });
}

#[test]
fn resume_unregistered_algorithm_is_rejected_on_both_backends() {
    smol::block_on(async {
        let mut mem = MemoryStorage::new();
        let mem_result = mem
            .apply(&[WriteOp::ResumeAlgorithm {
                alg_id: 9,
                epochs: &[(0, 3)],
                nodes: &[],
            }])
            .await;
        assert!(mem_result.is_err(), "MemoryStorage: {mem_result:?}");

        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut git = GitStorage::new(
            repo,
            "refs/eml/storage/apply-parity/unreg-resume/staging",
            2,
        )
        .unwrap();
        let git_result = git
            .apply(&[WriteOp::ResumeAlgorithm {
                alg_id: 9,
                epochs: &[(0, 3)],
                nodes: &[],
            }])
            .await;
        assert!(git_result.is_err(), "GitStorage: {git_result:?}");
    });
}
