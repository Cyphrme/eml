//! Scope isolation for [`FjallStorage::scoped`]: many logical logs share
//! one fixed keyspace triplet, separated only by a length-prefixed key
//! prefix. Checked differentially against one plain in-memory model per
//! scope, over scope sets chosen so that byte-prefix relations are common
//! (the failure a naive concatenated prefix would have).

use std::collections::{BTreeMap, BTreeSet};

use fjall::Database;
use polydigest::{NodeWrite, Storage, WriteOp};
use proptest::prelude::*;
use storage_fjall::{FjallStorage, LogKeyspaces};
use tempfile::tempdir;

#[derive(Debug, Clone, Default, PartialEq)]
struct Model {
    leaves: Vec<Vec<u8>>,
    nodes: BTreeMap<(u64, u64, u32), Vec<u8>>,
    algs: BTreeMap<u64, Vec<(u64, u64)>>,
}

#[derive(Debug, Clone)]
enum Op {
    Append {
        scope: usize,
        data: Vec<u8>,
        node: (u64, u64, u32),
    },
    AddAlg {
        scope: usize,
        alg: u64,
        epochs: Vec<(u64, u64)>,
    },
}

fn op_strategy(n_scopes: usize) -> impl Strategy<Value = Op> {
    prop_oneof![
        (
            0..n_scopes,
            prop::collection::vec(any::<u8>(), 0..8),
            (0u64..3, 0u64..4, 0u32..3)
        )
            .prop_map(|(scope, data, node)| Op::Append { scope, data, node }),
        (
            0..n_scopes,
            0u64..3,
            prop::collection::vec((any::<u64>(), any::<u64>()), 0..3)
        )
            .prop_map(|(scope, alg, epochs)| Op::AddAlg { scope, alg, epochs }),
    ]
}

/// Scopes over a two-letter alphabet, length 0..=3: dense in byte-prefix
/// pairs ([] < [0] < [0,0] < [0,0,1] ...), and including the empty scope.
fn scopes_strategy() -> impl Strategy<Value = Vec<Vec<u8>>> {
    prop::collection::btree_set(prop::collection::vec(0u8..2, 0..4), 2..6)
        .prop_map(|s| s.into_iter().collect())
}

async fn assert_scope_matches(storage: &FjallStorage, model: &Model) {
    assert_eq!(storage.len().await.unwrap(), model.leaves.len() as u64);
    assert_eq!(
        storage.append_count().await.unwrap(),
        model.leaves.len() as u64
    );
    for (i, leaf) in model.leaves.iter().enumerate() {
        assert_eq!(&storage.get_leaf(i as u64).await.unwrap(), leaf);
    }
    assert!(
        storage.get_leaf(model.leaves.len() as u64).await.is_err(),
        "a leaf past this scope's end must not be visible"
    );
    for a in 0u64..3 {
        for l in 0u64..4 {
            for h in 0u32..3 {
                assert_eq!(
                    storage.get_node(a, l, h).await.unwrap(),
                    model.nodes.get(&(a, l, h)).cloned()
                );
            }
        }
    }
    let metas: BTreeMap<u64, Vec<(u64, u64)>> = storage
        .load_algorithm_metas()
        .await
        .unwrap()
        .into_iter()
        .collect();
    assert_eq!(metas, model.algs);
}

async fn run(scopes: Vec<Vec<u8>>, ops: Vec<Op>, drop_idx: usize) {
    let dir = tempdir().unwrap();
    let db = Database::builder(dir.path()).open().unwrap();
    let keyspaces = LogKeyspaces::open(db).unwrap();
    let mut storages: Vec<FjallStorage> = scopes
        .iter()
        .map(|s| FjallStorage::scoped(&keyspaces, s).unwrap())
        .collect();
    let mut models = vec![Model::default(); scopes.len()];

    for op in &ops {
        match op {
            Op::Append { scope, data, node } => {
                let m = &mut models[*scope];
                let at = m.leaves.len() as u64;
                let hash = vec![*scope as u8, node.0 as u8, node.1 as u8, node.2 as u8];
                storages[*scope]
                    .apply(&[WriteOp::AppendLeaf {
                        at,
                        data,
                        nodes: &[NodeWrite {
                            alg_id: node.0,
                            left: node.1,
                            height: node.2,
                            hash: &hash,
                        }],
                    }])
                    .await
                    .unwrap();
                m.leaves.push(data.clone());
                m.nodes.insert(*node, hash);
            },
            Op::AddAlg { scope, alg, epochs } => {
                let m = &mut models[*scope];
                if m.algs.contains_key(alg) {
                    continue;
                }
                storages[*scope]
                    .apply(&[WriteOp::AddAlgorithm {
                        alg_id: *alg,
                        epochs,
                    }])
                    .await
                    .unwrap();
                m.algs.insert(*alg, epochs.clone());
            },
        }
    }

    for (s, m) in storages.iter().zip(&models) {
        assert_scope_matches(s, m).await;
    }

    // Dropping one scope empties exactly that scope.
    let d = drop_idx % scopes.len();
    FjallStorage::scoped(&keyspaces, &scopes[d])
        .unwrap()
        .drop_scope()
        .unwrap();
    models[d] = Model::default();
    for (s, m) in storages.iter().zip(&models) {
        assert_scope_matches(s, m).await;
    }

    // The dropped scope is reusable from position 0.
    storages[d]
        .apply(&[WriteOp::AppendLeaf {
            at: 0,
            data: b"again",
            nodes: &[],
        }])
        .await
        .unwrap();
    assert_eq!(storages[d].get_leaf(0).await.unwrap(), b"again");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn scopes_never_observe_each_other(
        (scopes, ops, drop_idx) in scopes_strategy().prop_flat_map(|s| {
            let n = s.len();
            (Just(s), prop::collection::vec(op_strategy(n), 0..40), 0usize..8)
        })
    ) {
        smol::block_on(run(scopes, ops, drop_idx));
    }
}

/// Opening scoped storages is a handle constructor: the database's keyspace
/// count is the same whether zero or many scopes exist.
#[test]
fn keyspace_count_is_independent_of_scope_count() {
    smol::block_on(async {
        let dir = tempdir().unwrap();
        let db = Database::builder(dir.path()).open().unwrap();
        let keyspaces = LogKeyspaces::open(db.clone()).unwrap();
        let baseline = db.keyspace_count();

        let mut seen = BTreeSet::new();
        for i in 0u32..40 {
            let mut s =
                FjallStorage::scoped(&keyspaces, format!("principal-{i}").as_bytes()).unwrap();
            if i % 3 == 0 {
                s.apply(&[WriteOp::AppendLeaf {
                    at: 0,
                    data: b"x",
                    nodes: &[],
                }])
                .await
                .unwrap();
            }
            seen.insert(db.keyspace_count());
        }
        assert_eq!(seen, BTreeSet::from([baseline]));
    });
}

#[test]
fn oversized_scope_is_rejected() {
    let dir = tempdir().unwrap();
    let db = Database::builder(dir.path()).open().unwrap();
    let keyspaces = LogKeyspaces::open(db).unwrap();
    assert!(FjallStorage::scoped(&keyspaces, &vec![0u8; 65_535]).is_ok());
    assert!(FjallStorage::scoped(&keyspaces, &vec![0u8; 65_536]).is_err());
}
