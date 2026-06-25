use std::collections::BTreeMap;

use polydigest::Storage;
use proptest::prelude::*;
use storage_fjall::FjallStorage;
use tempfile::tempdir;

#[derive(Debug, Clone)]
enum StorageAction {
    StoreLeaf {
        index: u64,
        data: Vec<u8>,
    },
    StoreNode {
        alg_id: u64,
        left: u64,
        height: u32,
        hash: Vec<u8>,
    },
    StoreAlgorithmMeta {
        alg_id: u64,
        epochs: Vec<(u64, u64)>,
    },
    WriteBatch {
        leaves: Vec<(u64, Vec<u8>)>,
        nodes: Vec<(u64, u64, u32, Vec<u8>)>,
    },
}

fn arb_action() -> impl Strategy<Value = StorageAction> {
    prop_oneof![
        (any::<u64>(), prop::collection::vec(any::<u8>(), 0..64))
            .prop_map(|(index, data)| StorageAction::StoreLeaf { index, data }),
        (
            any::<u64>(),
            any::<u64>(),
            any::<u32>(),
            prop::collection::vec(any::<u8>(), 0..32)
        )
            .prop_map(|(alg_id, left, height, hash)| StorageAction::StoreNode {
                alg_id,
                left,
                height,
                hash
            }),
        (
            any::<u64>(),
            prop::collection::vec((any::<u64>(), any::<u64>()), 0..4)
        )
            .prop_map(|(alg_id, epochs)| StorageAction::StoreAlgorithmMeta { alg_id, epochs }),
        (
            prop::collection::vec(
                (any::<u64>(), prop::collection::vec(any::<u8>(), 0..64)),
                0..5
            ),
            prop::collection::vec(
                (
                    any::<u64>(),
                    any::<u64>(),
                    any::<u32>(),
                    prop::collection::vec(any::<u8>(), 0..32)
                ),
                0..5
            )
        )
            .prop_map(|(leaves, nodes)| StorageAction::WriteBatch { leaves, nodes }),
    ]
}

struct StorageOracle {
    leaves: BTreeMap<u64, Vec<u8>>,
    nodes: BTreeMap<(u64, u64, u32), Vec<u8>>,
    metadata: BTreeMap<u64, Vec<(u64, u64)>>,
}

impl StorageOracle {
    fn new() -> Self {
        Self {
            leaves: BTreeMap::new(),
            nodes: BTreeMap::new(),
            metadata: BTreeMap::new(),
        }
    }

    fn apply(&mut self, action: &StorageAction) {
        match action {
            StorageAction::StoreLeaf { index, data } => {
                self.leaves.insert(*index, data.clone());
            },
            StorageAction::StoreNode {
                alg_id,
                left,
                height,
                hash,
            } => {
                self.nodes.insert((*alg_id, *left, *height), hash.clone());
            },
            StorageAction::StoreAlgorithmMeta { alg_id, epochs } => {
                self.metadata.insert(*alg_id, epochs.clone());
            },
            StorageAction::WriteBatch { leaves, nodes } => {
                for &(index, ref data) in leaves {
                    self.leaves.insert(index, data.clone());
                }
                for &(alg_id, left, height, ref hash) in nodes {
                    self.nodes.insert((alg_id, left, height), hash.clone());
                }
            },
        }
    }

    fn expected_len(&self) -> u64 {
        self.leaves
            .keys()
            .next_back()
            .map(|&index| index + 1)
            .unwrap_or(0)
    }
}

async fn run_differential_test(actions: Vec<StorageAction>) {
    let dir = tempdir().unwrap();
    let mut storage = FjallStorage::open(dir.path()).unwrap();
    let mut oracle = StorageOracle::new();

    for action in &actions {
        oracle.apply(action);
        match action {
            StorageAction::StoreLeaf { index, data } => {
                storage.store_leaf(*index, data).await.unwrap();
            },
            StorageAction::StoreNode {
                alg_id,
                left,
                height,
                hash,
            } => {
                storage
                    .store_node(*alg_id, *left, *height, hash)
                    .await
                    .unwrap();
            },
            StorageAction::StoreAlgorithmMeta { alg_id, epochs } => {
                storage.store_algorithm_meta(*alg_id, epochs).await.unwrap();
            },
            StorageAction::WriteBatch { leaves, nodes } => {
                let leaves_ref: Vec<(u64, &[u8])> = leaves
                    .iter()
                    .map(|(index, data)| (*index, data.as_slice()))
                    .collect();
                let nodes_ref: Vec<(u64, u64, u32, &[u8])> = nodes
                    .iter()
                    .map(|(alg_id, left, height, hash)| (*alg_id, *left, *height, hash.as_slice()))
                    .collect();
                storage
                    .write_batch(&leaves_ref, &nodes_ref, &[], None, &[])
                    .await
                    .unwrap();
            },
        }
    }

    // Assert parity
    assert_eq!(storage.len().await.unwrap(), oracle.expected_len());

    for (&index, expected_data) in &oracle.leaves {
        let actual_data = storage.get_leaf(index).await.unwrap();
        assert_eq!(&actual_data, expected_data);
    }

    for &index in oracle.leaves.keys() {
        if index > 0 && !oracle.leaves.contains_key(&(index - 1)) {
            assert!(storage.get_leaf(index - 1).await.is_err());
        }
        if !oracle.leaves.contains_key(&(index + 1)) {
            assert!(storage.get_leaf(index + 1).await.is_err());
        }
    }

    for (&(alg_id, left, height), expected_hash) in &oracle.nodes {
        let actual_hash = storage
            .get_node(alg_id, left, height)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(&actual_hash, expected_hash);
    }

    for &(alg_id, left, height) in oracle.nodes.keys() {
        if !oracle.nodes.contains_key(&(alg_id, left, height + 1)) {
            assert!(
                storage
                    .get_node(alg_id, left, height + 1)
                    .await
                    .unwrap()
                    .is_none()
            );
        }
    }

    let mut actual_metas = storage.load_algorithm_metas().await.unwrap();
    actual_metas.sort_by_key(|&(id, _)| id);

    let mut expected_metas: Vec<(u64, Vec<(u64, u64)>)> = oracle
        .metadata
        .iter()
        .map(|(&id, epochs)| (id, epochs.clone()))
        .collect();
    expected_metas.sort_by_key(|&(id, _)| id);

    assert_eq!(actual_metas, expected_metas);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]
    #[test]
    fn test_fjall_differential(ref actions in prop::collection::vec(arb_action(), 1..30)) {
        smol::block_on(run_differential_test(actions.clone()));
    }
}
