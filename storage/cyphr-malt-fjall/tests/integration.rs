use cyphr_malt::{Hasher, NaryMerkleLog, Storage, TreeConfig};
use cyphr_malt_storage_fjall::FjallStorage;
use sha2::{Digest, Sha256};
use tempfile::tempdir;

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children {
            h.update(child);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(Sha256Hasher)
    }
}

#[test]
fn test_fjall_storage_basic_ops() {
    let dir = tempdir().unwrap();
    let mut storage = FjallStorage::open(dir.path()).unwrap();

    // Init
    assert_eq!(storage.len(), 0);

    // Leaf ops
    storage.store_leaf(0, b"leaf0").unwrap();
    storage.store_leaf(1, b"leaf1").unwrap();
    assert_eq!(storage.len(), 2);
    assert_eq!(storage.get_leaf(0).unwrap(), b"leaf0");
    assert_eq!(storage.get_leaf(1).unwrap(), b"leaf1");

    // Node ops
    storage.store_node(0, 100, b"hash100").unwrap();
    assert_eq!(storage.get_node(0, 100).unwrap().unwrap(), b"hash100");
    assert!(storage.get_node(0, 999).unwrap().is_none());

    // Metadata ops
    let epochs = vec![(0, 10), (15, 20)];
    storage.store_algorithm_meta(0, &epochs).unwrap();
    let loaded = storage.load_algorithm_metas().unwrap();
    assert_eq!(loaded.len(), 1);
    assert_eq!(loaded[0].0, 0);
    assert_eq!(loaded[0].1, epochs);
}

#[test]
fn test_fjall_log_integration_and_recovery() {
    let dir = tempdir().unwrap();

    // Step 1: Build a log and write elements
    let root0;
    let root1;
    {
        let storage = FjallStorage::open(dir.path()).unwrap();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config);

        log.add_algorithm(1, Box::new(Sha256Hasher)).unwrap();

        log.append_leaf(b"hello").unwrap();
        log.append_leaf(b"world").unwrap();

        log.remove_algorithm(1).unwrap();

        log.append_leaf(b"rust").unwrap();

        root0 = log.root_for(0).unwrap();
        root1 = log.root_for(1).unwrap();

        assert_eq!(log.size(), 3);
    }

    // Step 2: Open a new log with the same storage and check recovery
    {
        let storage = FjallStorage::open(dir.path()).unwrap();
        let reconstructed = NaryMerkleLog::from_storage(
            storage,
            vec![(0, Box::new(Sha256Hasher)), (1, Box::new(Sha256Hasher))],
        )
        .unwrap();

        assert_eq!(reconstructed.size(), 3);
        assert_eq!(reconstructed.root_for(0).unwrap(), root0);
        assert_eq!(reconstructed.root_for(1).unwrap(), root1);
    }
}
