//! EVERY KEY PERSISTED: `storage-git` must not drop a digest it was handed.
//!
//! The underlying finding: `storage-git`'s `resolve_node` (`src/build.rs`)
//! overlays a touched coordinate's fresh digest onto its existing node, then
//! carries that node's OLD children forward by object id without
//! descending into any child this same batch also touched -- so a digest
//! `resume_algorithm` hands a descendant of an already-existing peak is
//! written nowhere. `MemoryStorage` never drops a node it is given;
//! `storage-git` does, at the exact gate scenario below and (per the fuzzed
//! property) at other placements too.
//!
//! RED at 60f93fe: `gate_scenario_k2_...` fails because `get_node(0, 4, 2)`
//! and `get_node(0, 6, 1)` come back `None` on `GitStorage` where
//! `MemoryStorage` holds a value; `verify_non_divergence` and several
//! `inclusion_proof_for` calls diverge in step with it.
//!
//! [finding 3] The fuzzed property below caught this defect reliably in
//! this session's own runs (5 of 5 at 24 cases -- see this file's own
//! committed `.proptest-regressions` seed, generated from exactly that
//! failure and replayed before any novel case on every future run), but an
//! unseeded proptest run's minimal, non-fixed-seed shape means a
//! differently-unlucky seed on a different machine or a different proptest
//! version could still miss it by chance, and no regression was previously
//! committed to guard against that. Closed three ways: the case count is
//! raised, this file's `.proptest-regressions` seed is committed (the root
//! `.gitignore`'s blanket exclusion is overridden for this directory by
//! `tests/.gitignore`, deliberately, since a fuzz test's failing case must
//! be reproducible for everyone rather than rediscovered by luck), and the
//! two deterministic scenarios below pin the add/remove/resume shape
//! without depending on proptest's random engine running at all.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
use proptest::prelude::*;
use storage_git::GitStorage;

fn hasher_pairs(ids: impl IntoIterator<Item = u64>) -> Vec<(u64, Box<dyn Hasher>)> {
    ids.into_iter()
        .map(|id| (id, Box::new(WideHasher) as Box<dyn Hasher>))
        .collect()
}

/// Every leaf and node key `mem` holds must read back identically from
/// `git` -- the exact dropped-node-detecting oracle
/// (`tip_tree_contract.rs::assert_completeness`), an independent copy here
/// since each `tests/*.rs` file compiles as its own binary.
async fn assert_every_key_matches(git: &GitStorage, mem: &MemoryStorage, context: &str) {
    for (i, expected) in mem.leaves.iter().enumerate() {
        let got = git.get_leaf(i as u64).await.unwrap_or_else(|e| {
            panic!("{context}: get_leaf({i}) errored where MemoryStorage holds a value: {e}")
        });
        assert_eq!(
            &got, expected,
            "{context}: get_leaf({i}) diverged from MemoryStorage"
        );
    }
    for (&(alg, left, height), expected) in &mem.nodes {
        let got = git.get_node(alg, left, height).await.unwrap();
        assert_eq!(
            got.as_ref(),
            Some(expected),
            "{context}: EVERY KEY PERSISTED: get_node(alg={alg}, left={left}, height={height}) \
             diverged from MemoryStorage (git={got:?})"
        );
    }
}

/// Reopen from disk, then `git gc --prune=now`, then reopen again -- every
/// key `mem` holds must still match at each stage ("live, after
/// reopen, and after gc").
async fn assert_survives_reopen_and_gc(
    dir: &std::path::Path,
    staging: &str,
    arity: u64,
    mem: &MemoryStorage,
    context: &str,
) {
    let reopened = GitStorage::open(dir, staging, arity).expect("reopen after write");
    assert_every_key_matches(&reopened, mem, &format!("{context}: after reopen")).await;
    drop(reopened);

    let out = std::process::Command::new("git")
        .arg("--git-dir")
        .arg(dir)
        .args(["gc", "--prune=now", "-q"])
        .output()
        .expect("run git gc");
    assert!(
        out.status.success(),
        "{context}: git gc failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let reopened2 = GitStorage::open(dir, staging, arity).expect("reopen after gc");
    assert_every_key_matches(&reopened2, mem, &format!("{context}: after gc and reopen")).await;
}

/// The exact failing scenario: k=2, `add_algorithm(1)` at size 4,
/// `remove_algorithm(0)` at size 7, append to 8, `resume_algorithm(0)` at
/// 8, append 5 more (to 13).
#[test]
fn gate_scenario_k2_merge_into_existing_peak_persists_every_node() {
    smol::block_on(async {
        let arity = 2u64;
        let (dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/completeness-gate/staging";
        let git_storage = GitStorage::new(repo, staging, arity).unwrap();
        let mut git_log =
            NaryMerkleLog::new(git_storage, Box::new(WideHasher), TreeConfig { arity })
                .await
                .unwrap();
        let mut mem_log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(WideHasher),
            TreeConfig { arity },
        )
        .await
        .unwrap();

        for i in 0..4u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            git_log.append_leaf(&leaf).await.unwrap();
            mem_log.append_leaf(&leaf).await.unwrap();
        }
        git_log
            .add_algorithm(1, Box::new(WideHasher))
            .await
            .unwrap();
        mem_log
            .add_algorithm(1, Box::new(WideHasher))
            .await
            .unwrap();

        for i in 4..7u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            git_log.append_leaf(&leaf).await.unwrap();
            mem_log.append_leaf(&leaf).await.unwrap();
        }
        git_log.remove_algorithm(0).await.unwrap();
        mem_log.remove_algorithm(0).await.unwrap();

        git_log.append_leaf(b"leaf-7").await.unwrap();
        mem_log.append_leaf(b"leaf-7").await.unwrap();

        git_log.resume_algorithm(0).await.unwrap();
        mem_log.resume_algorithm(0).await.unwrap();

        for i in 8..13u32 {
            let leaf = format!("leaf-{i}").into_bytes();
            git_log.append_leaf(&leaf).await.unwrap();
            mem_log.append_leaf(&leaf).await.unwrap();
        }

        assert_eq!(git_log.size(), mem_log.size());
        assert_eq!(git_log.root_for(0).ok(), mem_log.root_for(0).ok());

        // The two coordinates the underlying finding names by hand, checked directly first for
        // a legible failure if they alone are wrong.
        for &(left, height) in &[(4u64, 2u32), (6u64, 1u32)] {
            let g = git_log.storage().get_node(0, left, height).await.unwrap();
            let m = mem_log.storage().get_node(0, left, height).await.unwrap();
            assert!(
                m.is_some(),
                "fixture sanity: MemoryStorage must hold ({left},{height})"
            );
            assert_eq!(
                g, m,
                "get_node(alg=0, left={left}, height={height}) diverged: git={g:?} mem={m:?} -- \
                 this is the dropped-node scenario"
            );
        }

        // The broader claim: every key MemoryStorage holds, live.
        assert_every_key_matches(git_log.storage(), mem_log.storage(), "live").await;

        // Inclusion proofs at every index, algorithm 0, tree size 13: an earlier
        // probe reported 6 of 13 diverging in exactly this scenario.
        let size = git_log.size();
        for i in 0..size {
            let g = git_log.inclusion_proof_for(0, i, size).await;
            let m = mem_log.inclusion_proof_for(0, i, size).await;
            match (&g, &m) {
                (Ok(gv), Ok(mv)) => assert_eq!(
                    gv, mv,
                    "inclusion_proof_for(0, {i}, {size}) value diverged between git and memory"
                ),
                (Err(ge), Err(_)) => {
                    panic!("inclusion_proof_for(0, {i}, {size}) errored on BOTH backends: {ge:?}")
                },
                _ => panic!(
                    "inclusion_proof_for(0, {i}, {size}) success diverged: git={g:?} mem={m:?}"
                ),
            }
        }

        // verify_non_divergence, full replay from genesis -- an earlier probe:
        // `CorruptedMetadata` on git, `Ok(true)` on memory, in this exact
        // scenario.
        let g = git_log.verify_non_divergence(None, &[]).await;
        let m = mem_log.verify_non_divergence(None, &[]).await;
        match (&g, &m) {
            (Ok(gv), Ok(mv)) => assert_eq!(
                gv, mv,
                "verify_non_divergence(None, &[]) value diverged between git and memory"
            ),
            (Err(_), Err(_)) => {},
            _ => panic!("verify_non_divergence(None, &[]) success diverged: git={g:?} mem={m:?}"),
        }

        drop(git_log);
        assert_survives_reopen_and_gc(dir.path(), staging, arity, mem_log.storage(), "gate").await;
    });
}

// ============================================================================
// Fuzzed property: random append/add/remove/resume sequences at arities 2,
// 3 and 4, weighted so an add-then-remove-then-resume cycle (the shape that
// revisits an already-sealed, multi-algorithm coordinate) shows up often
// rather than being crowded out by plain appends.
// ============================================================================

#[derive(Debug, Clone)]
enum Op {
    Append(Vec<u8>),
    Add(u64),
    Remove(u64),
    Resume(u64),
}

fn arb_ops() -> impl Strategy<Value = Vec<Op>> {
    let leaf = prop::collection::vec(any::<u8>(), 0..12).prop_map(Op::Append);
    let add = (0u64..4).prop_map(Op::Add);
    let remove = (0u64..4).prop_map(Op::Remove);
    let resume = (0u64..4).prop_map(Op::Resume);
    // Weighted so a remove-then-resume cycle on the same algorithm --
    // The exact shape this file's own gate scenario pins: a digest merging back into an existing,
    // already-sealed peak -- shows up often within a short sequence,
    // rather than being crowded out by the many sequences that never
    // happen to line the two up (the gate scenario test above pins one
    // hand-picked instance deterministically; this property's job is to
    // find others).
    prop::collection::vec(
        prop_oneof![3 => leaf, 3 => add, 4 => remove, 4 => resume],
        1..24,
    )
}

async fn apply<S: Storage>(log: &mut NaryMerkleLog<S>, op: &Op)
where
    S::Error: std::fmt::Debug,
{
    match op {
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

async fn run_property(ops: &[Op], arity: u64, tag: &str) {
    let (dir, repo) = init_repo(HashKind::Sha1);
    let staging = format!("refs/eml/storage/completeness-fuzz/{tag}/staging");
    let git_storage = GitStorage::new(repo, &staging, arity).unwrap();
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
        assert_eq!(
            git_log.size(),
            mem_log.size(),
            "{tag}: size diverged after {op:?}"
        );
    }

    assert_every_key_matches(
        git_log.storage(),
        mem_log.storage(),
        &format!("{tag}: live"),
    )
    .await;

    let ids: Vec<u64> = mem_log
        .storage()
        .load_algorithm_metas()
        .await
        .unwrap()
        .into_iter()
        .map(|(id, _)| id)
        .collect();
    drop(git_log);
    assert_survives_reopen_and_gc(dir.path(), &staging, arity, mem_log.storage(), tag).await;

    // Reconstruct via `from_storage_with_config` too -- reopening a raw
    // `GitStorage` handle (above) proves the bytes survive; reconstructing
    // the log proves `polydigest`'s own reload path sees the identical
    // state `MemoryStorage` does.
    let reopened = GitStorage::open(dir.path(), &staging, arity).expect("reopen for reconstruct");
    let reconstructed =
        NaryMerkleLog::from_storage_with_config(reopened, hasher_pairs(ids), TreeConfig { arity })
            .await
            .unwrap_or_else(|e| panic!("{tag}: from_storage_with_config failed: {e:?}"));
    assert_eq!(
        reconstructed.size(),
        mem_log.size(),
        "{tag}: reconstructed size diverged"
    );
    assert_every_key_matches(
        reconstructed.storage(),
        mem_log.storage(),
        &format!("{tag}: reconstructed"),
    )
    .await;
}

proptest! {
    // [finding 3] Raised from 24: more cases per run means a wider sample of
    // the add/remove/resume placements this defect can hide at, on top of
    // (not instead of) the committed regression seed and the two
    // deterministic scenarios below, which no case count can make
    // unreliable.
    #![proptest_config(ProptestConfig::with_cases(96))]

    #[test]
    fn every_key_persisted_arity_2(ops in arb_ops()) {
        smol::block_on(run_property(&ops, 2, "a2"));
    }

    #[test]
    fn every_key_persisted_arity_3(ops in arb_ops()) {
        smol::block_on(run_property(&ops, 3, "a3"));
    }

    #[test]
    fn every_key_persisted_arity_4(ops in arb_ops()) {
        smol::block_on(run_property(&ops, 4, "a4"));
    }
}

/// [finding 3] Deterministic regression, independent of proptest's random
/// engine entirely: the exact minimal failing sequence this file's own
/// fuzz property found in this session's runs (also pinned as this file's
/// committed `.proptest-regressions` seed, so proptest itself replays it
/// first on every future run too) -- register a second algorithm, append
/// three empty leaves, remove it, append once more, then resume it. The
/// resume's merge crosses back into an already-sealed, multi-algorithm
/// coordinate and drops the digest.
#[test]
fn deterministic_add_remove_resume_across_a_sealed_coordinate_arity_2() {
    smol::block_on(run_property(
        &[
            Op::Add(3),
            Op::Append(Vec::new()),
            Op::Remove(3),
            Op::Append(Vec::new()),
            Op::Append(Vec::new()),
            Op::Append(Vec::new()),
            Op::Resume(3),
        ],
        2,
        "deterministic-a2",
    ));
}

/// [finding 3] The same add/remove/resume shape at a non-binary arity, with
/// non-empty leaf payloads and a different algorithm id -- a second,
/// independently hand-picked scenario so this file's deterministic
/// coverage is not just the one instance the fuzzer's own shrink happened
/// to find.
#[test]
fn deterministic_add_remove_resume_across_a_sealed_coordinate_arity_3() {
    smol::block_on(run_property(
        &[
            Op::Append(b"a".to_vec()),
            Op::Append(b"b".to_vec()),
            Op::Add(1),
            Op::Append(b"c".to_vec()),
            Op::Append(b"d".to_vec()),
            Op::Remove(1),
            Op::Append(b"e".to_vec()),
            Op::Resume(1),
            Op::Append(b"f".to_vec()),
        ],
        3,
        "deterministic-a3",
    ));
}
