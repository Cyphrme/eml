//! Acceptance tests guarding purity under reopen, corruption-freedom after
//! reopen, and digest/child retention on a touched node -- the properties
//! the merge gate found `storage-git`'s opacity fix broke (GB44 in
//! `.ledger/state/2026-09-14-the-git-backend-in-three-layers.md`, resolving
//! the SG10/SG11 conflict the gate deposit at
//! `.ledger/deposits/git-backend/lead-maintainer/storage-git-merge-gate.md`
//! names as SGG10/SGG11).
//!
//! Written from `docs/specs/storage-git.md` (SG9-SG11, SG18, SG25) and the
//! two ledger documents above, against `storage-git`'s public API alone
//! (`GitStorage`, `GitStorageError`) plus `polydigest`'s combinator surface.
//! Not derived from `storage-git`'s private modules (`build.rs`,
//! `historical.rs`, ...) or from its existing test suite.

#[path = "acceptance_support/mod.rs"]
mod support;

use std::collections::HashSet;
use std::path::Path;

use polydigest::{LogError, NaryMerkleLog, TreeConfig};
use proptest::prelude::*;
use spine::Hasher;
use storage_git::GitStorage;
use support::FixtureHasher;

const ARITY: u64 = 2;
const ALG_DOMAIN: [u64; 3] = [0, 1, 2];
const HASHER_WIDTH: usize = 20;

fn hasher() -> FixtureHasher {
    FixtureHasher::new(HASHER_WIDTH)
}

/// One legal step of a randomized operation sequence over a flat log:
/// append, add/remove/resume an algorithm -- exactly the mix GB44's SGG10
/// probe interleaves ("append a0 leaves, add_algorithm(1), append a1,
/// remove_algorithm(1), append a2, then resume_algorithm(1) and one more
/// append").
#[derive(Debug, Clone)]
enum Op {
    Append(u8),
    Add(u64),
    Remove(u64),
    Resume(u64),
}

/// A raw, possibly-illegal proposal for one step, paired with whether the
/// reopening writer should reopen its log (through `from_storage_with_config`
/// -- "polydigest's from-storage path") immediately before this step.
#[derive(Debug, Clone)]
enum RawOp {
    Append(u8),
    Add(u64),
    Remove(u64),
    Resume(u64),
}

// Weighted so an Add/Remove/Resume cycle on the same algorithm id -- the
// shape SGG10/SGG11 need -- shows up often within a short sequence, rather
// than being crowded out by plain appends. The reopen flag is chosen
// per-variant (not independently of it): `resume_algorithm` is the one op
// that revisits already-sealed, multi-algorithm coordinates (SGG11's own
// account of the cause), so a reopen immediately before *it* is what
// actually exercises the divergence -- a reopen before a plain append or
// an epoch-only add/remove touches nothing pre-existing and proves
// nothing. Skewing reopen-before-resume high keeps that combination from
// being crowded out by the many op sequences that never happen to line
// the two up.
fn raw_step_strategy() -> impl Strategy<Value = (RawOp, bool)> {
    prop_oneof![
        2 => any::<u8>()
            .prop_flat_map(|b| (Just(RawOp::Append(b)), prop::bool::weighted(0.2))),
        3 => (0u64..3)
            .prop_flat_map(|id| (Just(RawOp::Add(id)), prop::bool::weighted(0.2))),
        3 => (0u64..3)
            .prop_flat_map(|id| (Just(RawOp::Remove(id)), prop::bool::weighted(0.2))),
        4 => (0u64..3)
            .prop_flat_map(|id| (Just(RawOp::Resume(id)), prop::bool::weighted(0.85))),
    ]
}

/// Filter a raw op stream down to one every legal replay accepts, tracking
/// exactly the state `add_algorithm`/`remove_algorithm`/`resume_algorithm`
/// themselves enforce (`polydigest::LogError::{Duplicate,Unknown,Frozen,
/// Active}Algorithm`). Algorithm `0` starts registered and active, matching
/// `NaryMerkleLog::new`'s own eager registration. A `Remove` that would
/// leave no algorithm active is also skipped -- not because it is illegal,
/// but because the resulting `NoActiveAlgorithms` failure on the next
/// append is a `polydigest`-level constraint identical for both writers,
/// not a `storage-git` purity question, and would only add noise to what
/// this test is checking.
///
/// Each kept step also carries the sorted set of algorithm ids known
/// (ever registered) immediately *before* it -- exactly the hashers
/// `from_storage_with_config` must be supplied if the reopening writer
/// reopens right before this step.
fn normalize(raw: &[(RawOp, bool)]) -> Vec<(Op, bool, Vec<u64>)> {
    let mut known: HashSet<u64> = [0].into_iter().collect();
    let mut active: HashSet<u64> = [0].into_iter().collect();
    let mut out = Vec::new();
    for (op, reopen) in raw {
        let known_before: Vec<u64> = {
            let mut v: Vec<u64> = known.iter().copied().collect();
            v.sort_unstable();
            v
        };
        match *op {
            RawOp::Append(b) => out.push((Op::Append(b), *reopen, known_before)),
            RawOp::Add(id) => {
                if !known.contains(&id) {
                    known.insert(id);
                    active.insert(id);
                    out.push((Op::Add(id), *reopen, known_before));
                }
            },
            RawOp::Remove(id) => {
                if active.contains(&id) && active.len() > 1 {
                    active.remove(&id);
                    out.push((Op::Remove(id), *reopen, known_before));
                }
            },
            RawOp::Resume(id) => {
                if known.contains(&id) && !active.contains(&id) {
                    active.insert(id);
                    out.push((Op::Resume(id), *reopen, known_before));
                }
            },
        }
    }
    out
}

async fn apply_op(
    log: &mut NaryMerkleLog<GitStorage>,
    op: &Op,
) -> Result<(), LogError<storage_git::GitStorageError>> {
    match *op {
        Op::Append(b) => log.append_leaf(&[b]).await,
        Op::Add(id) => log.add_algorithm(id, Box::new(hasher())).await,
        Op::Remove(id) => log.remove_algorithm(id).await,
        Op::Resume(id) => log.resume_algorithm(id).await,
    }
}

/// Run `ops` against a fresh `GitStorage`-backed log rooted at `dir`. When
/// `reopen_enabled`, a step whose `reopen` flag is set first drops the live
/// log, reopens a brand-new `GitStorage` from disk (`GitStorage::new` over
/// a freshly reopened repository -- "polydigest's from-storage path"), and
/// reconstructs the log through `NaryMerkleLog::from_storage_with_config`
/// before applying that step.
async fn run_writer(
    dir: &Path,
    staging_ref: &str,
    ops: &[(Op, bool, Vec<u64>)],
    reopen_enabled: bool,
) -> Result<NaryMerkleLog<GitStorage>, String> {
    let repo = support::bare_repo(dir, gix::hash::Kind::Sha1);
    let mut storage =
        GitStorage::new(repo, staging_ref, ARITY).map_err(|e| format!("initial open: {e}"))?;
    for id in ALG_DOMAIN {
        storage.register_hasher(id, Box::new(hasher()));
    }
    let mut log = NaryMerkleLog::new(storage, Box::new(hasher()), TreeConfig { arity: ARITY })
        .await
        .map_err(|e| format!("new log: {e:?}"))?;

    for (i, (op, reopen, known_before)) in ops.iter().enumerate() {
        if reopen_enabled && *reopen {
            drop(log);
            let repo2 = support::reopen_repo(dir);
            let mut storage2 = GitStorage::new(repo2, staging_ref, ARITY)
                .map_err(|e| format!("reopen at step {i}: {e}"))?;
            for id in ALG_DOMAIN {
                storage2.register_hasher(id, Box::new(hasher()));
            }
            let hashers: Vec<(u64, Box<dyn Hasher>)> = known_before
                .iter()
                .map(|&id| (id, Box::new(hasher()) as Box<dyn Hasher>))
                .collect();
            log = NaryMerkleLog::from_storage_with_config(
                storage2,
                hashers,
                TreeConfig { arity: ARITY },
            )
            .await
            .map_err(|e| format!("reopen-reconstruct at step {i}: {e:?}"))?;
        }
        apply_op(&mut log, op)
            .await
            .map_err(|e| format!("op {i} ({op:?}) failed: {e:?}"))?;
    }
    Ok(log)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// **SG9 purity, under GB44.** A continuous writer and a writer that
    /// reopens through `from_storage_with_config` at arbitrary points, run
    /// over the identical operation sequence, must end at byte-identical
    /// staging tips and identical `tree_at(n)` for every `n`. The gate found
    /// 111 of 125 sequences of exactly this shape diverge (SGG10).
    #[test]
    fn purity_under_reopen_matches_continuous_writer(
        raw in prop::collection::vec(raw_step_strategy(), 3..14)
    ) {
        let ops = normalize(&raw);
        prop_assume!(!ops.is_empty());

        let result: Result<(), String> = smol::block_on(async {
            let dir_a = tempfile::tempdir().map_err(|e| format!("tempdir a: {e}"))?;
            let dir_b = tempfile::tempdir().map_err(|e| format!("tempdir b: {e}"))?;
            let staging_ref = "refs/eml/storage/purity/staging";

            let continuous = run_writer(dir_a.path(), staging_ref, &ops, false).await?;
            let reopening = run_writer(dir_b.path(), staging_ref, &ops, true).await?;

            if continuous.count() != reopening.count() {
                return Err(format!(
                    "counts diverged: continuous={} reopening={}",
                    continuous.count(),
                    reopening.count()
                ));
            }

            let n = continuous.count();
            for m in 0..=n {
                let id_a = continuous
                    .storage()
                    .tree_at(m)
                    .map_err(|e| format!("tree_at({m}) continuous: {e}"))?;
                let id_b = reopening
                    .storage()
                    .tree_at(m)
                    .map_err(|e| format!("tree_at({m}) reopening: {e}"))?;
                if id_a != id_b {
                    return Err(format!(
                        "tree_at({m}) diverged by reopen alone: continuous={id_a} \
                         reopening={id_b}, over ops {ops:?}"
                    ));
                }
            }
            Ok(())
        });

        if let Err(msg) = result {
            prop_assert!(false, "{msg}");
        }
    }

}

/// **No corruption after reopen (GB44 / SGG11).** The gate's own minimal
/// repro: reopening once before `resume_algorithm`, then reopening a
/// SECOND time afterward, must succeed cleanly -- never
/// `LogError::CorruptedMetadata`. SGG11 shows the loss surfaces exactly on
/// this second reopen, not on the resume that introduced it, so a test
/// that only reopens once (as `purity_under_reopen_matches_continuous_writer`
/// above already does, incidentally) cannot exercise this specific claim.
#[test]
fn reopen_after_resume_on_a_reopened_log_stays_clean() {
    let result: Result<(), String> = smol::block_on(async {
        let dir = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
        let staging_ref = "refs/eml/storage/reopen-clean/staging";
        let repo = support::bare_repo(dir.path(), gix::hash::Kind::Sha1);

        let mut storage =
            GitStorage::new(repo, staging_ref, ARITY).map_err(|e| format!("open: {e}"))?;
        storage.register_hasher(0, Box::new(hasher()));
        storage.register_hasher(1, Box::new(hasher()));
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher()), TreeConfig { arity: ARITY })
            .await
            .map_err(|e| format!("new: {e:?}"))?;

        // a0 = 0, a1 = 1, a2 = 1 -- SGG11's smallest divergent case.
        log.add_algorithm(1, Box::new(hasher()))
            .await
            .map_err(|e| format!("add_algorithm(1): {e:?}"))?;
        log.append_leaf(b"leaf-0")
            .await
            .map_err(|e| format!("append leaf-0: {e:?}"))?;
        log.remove_algorithm(1)
            .await
            .map_err(|e| format!("remove_algorithm(1): {e:?}"))?;
        log.append_leaf(b"leaf-1")
            .await
            .map_err(|e| format!("append leaf-1: {e:?}"))?;
        drop(log);

        // First reopen, before resume_algorithm.
        let repo2 = support::reopen_repo(dir.path());
        let mut storage2 =
            GitStorage::new(repo2, staging_ref, ARITY).map_err(|e| format!("reopen 1: {e}"))?;
        storage2.register_hasher(0, Box::new(hasher()));
        storage2.register_hasher(1, Box::new(hasher()));
        let hashers1: Vec<(u64, Box<dyn Hasher>)> = vec![
            (0, Box::new(hasher()) as Box<dyn Hasher>),
            (1, Box::new(hasher())),
        ];
        let mut reopened = NaryMerkleLog::from_storage_with_config(
            storage2,
            hashers1,
            TreeConfig { arity: ARITY },
        )
        .await
        .map_err(|e| format!("reconstruct 1: {e:?}"))?;

        reopened
            .resume_algorithm(1)
            .await
            .map_err(|e| format!("resume_algorithm(1): {e:?}"))?;
        let final_count = reopened.count();
        drop(reopened);

        // Second reopen, after resume_algorithm -- this is where SGG11
        // says the loss surfaces.
        let repo3 = support::reopen_repo(dir.path());
        let mut storage3 =
            GitStorage::new(repo3, staging_ref, ARITY).map_err(|e| format!("reopen 2: {e}"))?;
        storage3.register_hasher(0, Box::new(hasher()));
        storage3.register_hasher(1, Box::new(hasher()));
        let hashers2: Vec<(u64, Box<dyn Hasher>)> = vec![
            (0, Box::new(hasher()) as Box<dyn Hasher>),
            (1, Box::new(hasher())),
        ];

        match NaryMerkleLog::from_storage_with_config(
            storage3,
            hashers2,
            TreeConfig { arity: ARITY },
        )
        .await
        {
            Ok(reopened2) => {
                if reopened2.count() != final_count {
                    return Err(format!(
                        "second reopen count diverged: expected {final_count}, got {}",
                        reopened2.count()
                    ));
                }
                Ok(())
            },
            Err(e) => Err(format!("second reopen must succeed cleanly, got {e:?}")),
        }
    });

    if let Err(msg) = result {
        panic!("{msg}");
    }
}

/// **A touched node keeps its stored digests (SG3/SG10/SG11, GB44).** After
/// `resume_algorithm` on a reopened log, every algorithm's digest
/// previously stored at a frontier node is still present, and a
/// materialized node keeps its children. This is GB44's/SGG11's own
/// smallest divergent case: arity 2, algorithm 0 baseline, algorithm 1
/// added then removed before a leaf each, reopened, then resumed.
#[test]
fn resume_algorithm_on_reopened_log_keeps_prior_digests_and_children() {
    let result: Result<(), String> = smol::block_on(async {
        let dir = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
        let staging_ref = "refs/eml/storage/resume-keeps-digests/staging";
        let repo = support::bare_repo(dir.path(), gix::hash::Kind::Sha1);

        let mut storage =
            GitStorage::new(repo, staging_ref, ARITY).map_err(|e| format!("open: {e}"))?;
        storage.register_hasher(0, Box::new(hasher()));
        storage.register_hasher(1, Box::new(hasher()));
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher()), TreeConfig { arity: ARITY })
            .await
            .map_err(|e| format!("new: {e:?}"))?;

        // a0 = 0, a1 = 1, a2 = 1 -- SGG11's smallest divergent case.
        log.add_algorithm(1, Box::new(hasher()))
            .await
            .map_err(|e| format!("add_algorithm(1): {e:?}"))?;
        log.append_leaf(b"leaf-0")
            .await
            .map_err(|e| format!("append leaf-0: {e:?}"))?;
        log.remove_algorithm(1)
            .await
            .map_err(|e| format!("remove_algorithm(1): {e:?}"))?;
        log.append_leaf(b"leaf-1")
            .await
            .map_err(|e| format!("append leaf-1: {e:?}"))?;
        drop(log);

        // Reopen through polydigest's from-storage path before resuming --
        // exactly the provenance boundary GB44 rules opacity must survive.
        let repo2 = support::reopen_repo(dir.path());
        let mut storage2 =
            GitStorage::new(repo2, staging_ref, ARITY).map_err(|e| format!("reopen: {e}"))?;
        storage2.register_hasher(0, Box::new(hasher()));
        storage2.register_hasher(1, Box::new(hasher()));
        let hashers: Vec<(u64, Box<dyn Hasher>)> = vec![
            (0, Box::new(hasher()) as Box<dyn Hasher>),
            (1, Box::new(hasher())),
        ];
        let mut reopened =
            NaryMerkleLog::from_storage_with_config(storage2, hashers, TreeConfig { arity: ARITY })
                .await
                .map_err(|e| format!("reconstruct: {e:?}"))?;

        reopened
            .resume_algorithm(1)
            .await
            .map_err(|e| format!("resume_algorithm(1): {e:?}"))?;

        let repo3 = support::reopen_repo(dir.path()).to_thread_local();
        let tip = support::ref_target(&repo3, staging_ref)
            .ok_or_else(|| "staging ref missing after resume".to_string())?;

        // n = 2, arity 2: one peak, T(0,1), at peaks/01/00.
        let peak_path = format!("peaks/{}/{}", support::hex(1, 2), support::hex(0, 2));
        let peak = support::resolve_path(&repo3, tip, &peak_path)
            .ok_or_else(|| format!("{peak_path} missing"))?;

        // Materialized: still carries both children (SG4/SG10).
        for child in [support::hex(0, 2), support::hex(1, 2)] {
            if support::find_entry(&repo3, peak.oid, &child).is_none() {
                return Err(format!(
                    "{peak_path} lost child {child} after resume_algorithm"
                ));
            }
        }

        // Every algorithm previously stored at this node keeps its digest
        // (SG3/SG11): algorithm 0's digest must survive alongside
        // algorithm 1's freshly written one.
        let digest_tree = support::find_entry(&repo3, peak.oid, "digest")
            .ok_or_else(|| format!("{peak_path} has no digest/ subtree"))?;
        for alg_id in [0u64, 1u64] {
            let name = support::hex(alg_id, 16);
            if support::find_entry(&repo3, digest_tree.oid, &name).is_none() {
                return Err(format!(
                    "{peak_path}/digest lost algorithm {alg_id}'s entry after resume_algorithm"
                ));
            }
        }

        Ok(())
    });

    if let Err(msg) = result {
        panic!("{msg}");
    }
}

// A resumed seal's opacity, and the refusal a resumption onto a ref that
// already holds a log's own committed objects now gets, are covered in
// `acceptance_opacity.rs` (`resume_onto_a_ref_that_already_holds_a_log_is_refused`,
// `resume_onto_a_fresh_ref_is_independent_of_how_the_storage_was_constructed`,
// and `resume_onto_an_empty_ref_still_yields_opaque_peaks`), against the
// public `NaryMerkleLog::resume` path a caller actually uses -- rather than
// as a feature-gated module written against a call this crate never ends up
// needing.
