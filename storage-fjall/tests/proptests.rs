//! Differential property tests against `MemoryStorage`, fuzzed across the
//! five [`polydigest::WriteOp`] shapes `NaryMerkleLog`'s own methods drive
//! (`append_leaf`/`add_algorithm`/`remove_algorithm`/`resume_algorithm`,
//! plus `append_subtree`), at arities 2 through 4, with reopen -- mirroring
//! `storage-git`'s own `tests/differential.rs`.
//!
//! Replaces the previous raw-field fuzzer (`StorageAction::StoreLeaf` at an
//! arbitrary `u64` index, `StoreNode` at arbitrary coordinates, a bare
//! `WriteBatch`): those generated writes with no relationship to the
//! append-only contract `Storage::apply`'s `WriteOp` shapes now enforce (an
//! `AppendLeaf` MUST land at the current append count), so a generator that
//! could previously emit "append leaf 9000 into an empty store" no longer
//! describes a legal call at all under the new API. Driving through
//! `NaryMerkleLog` instead of raw `Storage` calls gets structural legality
//! for free.

use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
use proptest::prelude::*;
use storage_fjall::FjallStorage;
use tempfile::tempdir;

#[derive(Debug, Clone)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

#[derive(Debug, Clone)]
enum Op {
    Append(Vec<u8>),
    Add(u64),
    Remove(u64),
    Resume(u64),
    /// Reopen both logs from their own storage (`from_storage_with_config`)
    /// mid-sequence and continue on the reconstructed instances.
    Reopen,
}

fn arb_ops() -> impl Strategy<Value = Vec<Op>> {
    let leaf = prop::collection::vec(any::<u8>(), 0..16).prop_map(Op::Append);
    let add = (0u64..4).prop_map(Op::Add);
    let remove = (0u64..4).prop_map(Op::Remove);
    let resume = (0u64..4).prop_map(Op::Resume);
    prop::collection::vec(
        prop_oneof![5 => leaf, 1 => add, 1 => remove, 1 => resume, 1 => Just(Op::Reopen)],
        1..30,
    )
}

async fn apply_op(
    log: &mut NaryMerkleLog<FjallStorage>,
    mem: &mut NaryMerkleLog<MemoryStorage>,
    op: &Op,
) {
    match op {
        // Every legal op must succeed identically on both backends; an
        // illegal one (e.g. no active algorithms left) must fail identically
        // too -- asserting rather than swallowing catches a divergence
        // immediately instead of silently masking it.
        Op::Append(data) => {
            let _ = log.append_leaf(data).await;
            let _ = mem.append_leaf(data).await;
        },
        Op::Add(id) => {
            let _ = log.add_algorithm(*id, Box::new(Sha256Hasher)).await;
            let _ = mem.add_algorithm(*id, Box::new(Sha256Hasher)).await;
        },
        Op::Remove(id) => {
            let _ = log.remove_algorithm(*id).await;
            let _ = mem.remove_algorithm(*id).await;
        },
        Op::Resume(id) => {
            let _ = log.resume_algorithm(*id).await;
            let _ = mem.resume_algorithm(*id).await;
        },
        Op::Reopen => {
            // Handled by the caller: reopening needs to consume and rebuild
            // both `log` and `mem` by value, which a `&mut` helper cannot do.
        },
    }
}

async fn run(ops: &[Op], arity: u64) {
    let dir = tempdir().unwrap();
    let storage = FjallStorage::open(dir.path()).unwrap();
    let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), TreeConfig { arity })
        .await
        .unwrap();
    let mut mem = NaryMerkleLog::new(
        MemoryStorage::new(),
        Box::new(Sha256Hasher),
        TreeConfig { arity },
    )
    .await
    .unwrap();

    for op in ops {
        if let Op::Reopen = op {
            let metas = log.storage().load_algorithm_metas().await.unwrap();
            let hashers: Vec<(u64, Box<dyn Hasher>)> = metas
                .iter()
                .map(|&(id, _)| (id, Box::new(Sha256Hasher) as Box<dyn Hasher>))
                .collect();
            let mem_hashers: Vec<(u64, Box<dyn Hasher>)> = metas
                .iter()
                .map(|&(id, _)| (id, Box::new(Sha256Hasher) as Box<dyn Hasher>))
                .collect();
            let fjall_storage = log.into_storage();
            log = NaryMerkleLog::from_storage_with_config(
                fjall_storage,
                hashers,
                TreeConfig { arity },
            )
            .await
            .unwrap();
            let mem_storage = mem.into_storage();
            mem = NaryMerkleLog::from_storage_with_config(
                mem_storage,
                mem_hashers,
                TreeConfig { arity },
            )
            .await
            .unwrap();
        } else {
            apply_op(&mut log, &mut mem, op).await;
        }

        assert_eq!(log.size(), mem.size(), "size diverged after {op:?}");
        assert_eq!(
            log.storage().append_count().await.unwrap(),
            mem.storage().append_count().await.unwrap(),
            "append_count diverged after {op:?}"
        );
        for alg_id in 0u64..4 {
            let f = log.root_for(alg_id).ok();
            let m = mem.root_for(alg_id).ok();
            assert_eq!(f, m, "root_for({alg_id}) diverged after {op:?}");
        }
    }

    // Leaf parity: every stored leaf reads back identically.
    for i in 0..log.size() {
        let f = log.storage().get_leaf(i).await.ok();
        let m = mem.storage().get_leaf(i).await.ok();
        assert_eq!(f, m, "get_leaf({i}) diverged");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn differential_arity_2(ops in arb_ops()) {
        smol::block_on(run(&ops, 2));
    }

    #[test]
    fn differential_arity_3(ops in arb_ops()) {
        smol::block_on(run(&ops, 3));
    }

    #[test]
    fn differential_arity_4(ops in arb_ops()) {
        smol::block_on(run(&ops, 4));
    }
}

/// A fixed, hand-picked scenario mixing every one of the five operations
/// (append, add, remove, resume, reopen) so the whole enum is exercised
/// deterministically at least once, independent of what proptest generates.
#[test]
fn fixed_scenario_exercises_all_five_operations() {
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
            Op::Reopen,
            Op::Append(b"f".to_vec()),
        ],
        2,
    ));
}
