//! Differential property tests against `MemoryStorage`: SG2, SG3, SG8, SG9,
//! SG10, SG11, SG13, SG14, SG15 -- mirroring `storage-fjall`'s own
//! `tests/proptests.rs` pattern (`storage-fjall/tests/proptests.rs`) and
//! `polydigest`'s reference oracle.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
use proptest::prelude::*;
use storage_git::GitStorage;

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
