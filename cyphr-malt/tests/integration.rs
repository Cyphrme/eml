use cyphr_malt::{Hasher, MemoryStorage, NaryMerkleLog, Subtree, TreeConfig};
use sha2::{Digest, Sha256};

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
fn test_vector_1_single_leaf() {
    let hasher = Sha256Hasher;
    let storage = MemoryStorage::new();
    let config = TreeConfig { log_arity: 2 };
    let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config);

    log.append_leaf(b"hello").unwrap();
    let root = log.root();
    let expected = vec![
        0x2c, 0xf2, 0x4d, 0xba, 0x5f, 0xb0, 0xa3, 0x0e, 0x26, 0xe8, 0x3b, 0x2a, 0xc5, 0xb9, 0xe2,
        0x9e, 0x1b, 0x16, 0x1e, 0x5c, 0x1f, 0xa7, 0x42, 0x5e, 0x73, 0x04, 0x33, 0x62, 0x93, 0x8b,
        0x98, 0x24,
    ];
    assert_eq!(root, expected);
}

#[test]
fn test_vector_2_two_leaves_k2() {
    let hasher = Sha256Hasher;
    let storage = MemoryStorage::new();
    let config = TreeConfig { log_arity: 2 };
    let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config);

    log.append_leaf(b"a").unwrap();
    log.append_leaf(b"b").unwrap();
    let root = log.root();

    let h_a = Sha256::digest(b"a");
    let h_b = Sha256::digest(b"b");
    let mut h = Sha256::new();
    h.update(h_a);
    h.update(h_b);
    let expected = h.finalize().to_vec();

    assert_eq!(root, expected);
}

#[test]
fn test_vector_3_three_leaves_k2() {
    let hasher = Sha256Hasher;
    let storage = MemoryStorage::new();
    let config = TreeConfig { log_arity: 2 };
    let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config);

    log.append_leaf(b"a").unwrap();
    log.append_leaf(b"b").unwrap();
    log.append_leaf(b"c").unwrap();
    let root = log.root();

    let h_a = Sha256::digest(b"a");
    let h_b = Sha256::digest(b"b");
    let h_ab = Sha256::digest([h_a.as_slice(), h_b.as_slice()].concat());
    let h_c = Sha256::digest(b"c");

    let mut h = Sha256::new();
    h.update(h_ab);
    h.update(h_c);
    let expected = h.finalize().to_vec();

    assert_eq!(root, expected);
}

#[test]
fn test_vector_4_singleton_promotion() {
    let hasher = Sha256Hasher;
    let tree = Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())]);
    let evaluated = cyphr_malt::evaluate(&hasher, &tree);
    let expected = Sha256::digest(b"x").to_vec();
    assert_eq!(evaluated, expected);
}

#[test]
fn test_vector_5_nested_promotion() {
    let hasher = Sha256Hasher;
    let tree = Subtree::Node(vec![Subtree::Node(vec![Subtree::Leaf(b"x".to_vec())])]);
    let evaluated = cyphr_malt::evaluate(&hasher, &tree);
    let expected = Sha256::digest(b"x").to_vec();
    assert_eq!(evaluated, expected);
}

#[test]
fn test_vector_6_subtree_append_k2() {
    let hasher = Sha256Hasher;
    let storage = MemoryStorage::new();
    let config = TreeConfig { log_arity: 2 };
    let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config);

    let subtree0 = Subtree::Node(vec![
        Subtree::Leaf(b"a".to_vec()),
        Subtree::Leaf(b"b".to_vec()),
    ]);
    let subtree1 = Subtree::Node(vec![Subtree::Leaf(b"c".to_vec())]);

    log.append_subtree(&subtree0).unwrap();
    log.append_subtree(&subtree1).unwrap();
    let root = log.root();

    let h_a = Sha256::digest(b"a");
    let h_b = Sha256::digest(b"b");
    let h_ab = Sha256::digest([h_a.as_slice(), h_b.as_slice()].concat());
    let h_c = Sha256::digest(b"c");

    let mut h = Sha256::new();
    h.update(h_ab);
    h.update(h_c);
    let expected = h.finalize().to_vec();

    assert_eq!(root, expected);
}

#[test]
fn test_vector_7_null_constant() {
    let hasher = Sha256Hasher;
    let null = hasher.null();
    let expected = vec![
        0xdb, 0xc1, 0xb4, 0xc9, 0x00, 0xff, 0xe4, 0x8d, 0x57, 0x5b, 0x5d, 0xa5, 0xc6, 0x38, 0x04,
        0x01, 0x25, 0xf6, 0x5d, 0xb0, 0xfe, 0x3e, 0x24, 0x49, 0x4b, 0x76, 0xea, 0x98, 0x64, 0x57,
        0xd9, 0x86,
    ];
    assert_eq!(null, expected);
}

#[test]
fn test_vector_8_three_leaves_k3_ternary() {
    let hasher = Sha256Hasher;
    let storage = MemoryStorage::new();
    let config = TreeConfig { log_arity: 3 };
    let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config);

    log.append_leaf(b"a").unwrap();
    log.append_leaf(b"b").unwrap();
    log.append_leaf(b"c").unwrap();
    let root = log.root();

    let h_a = Sha256::digest(b"a");
    let h_b = Sha256::digest(b"b");
    let h_c = Sha256::digest(b"c");

    let mut h = Sha256::new();
    h.update(h_a);
    h.update(h_b);
    h.update(h_c);
    let expected = h.finalize().to_vec();

    assert_eq!(root, expected);
}

// Prefix-free binary MTH helper
fn manual_prefix_free_mth(hasher: &dyn Hasher, leaves: &[Vec<u8>]) -> Vec<u8> {
    if leaves.is_empty() {
        return hasher.empty();
    }
    if leaves.len() == 1 {
        return leaves[0].clone();
    }
    let n = leaves.len();
    let k = n.next_power_of_two() / 2;
    let k = if k == n { k / 2 } else { k };

    let left = manual_prefix_free_mth(hasher, &leaves[0..k]);
    let right = manual_prefix_free_mth(hasher, &leaves[k..n]);
    hasher.node(&[&left, &right])
}

#[test]
fn test_binary_compatibility_random_sizes() {
    for size in 1..=16 {
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config);

        let mut leaves = Vec::new();
        for i in 0..size {
            let data = format!("leaf_{}", i).into_bytes();
            log.append_leaf(&data).unwrap();
            leaves.push(Sha256Hasher.leaf(&data));
        }

        let mth_root = manual_prefix_free_mth(&Sha256Hasher, &leaves);
        assert_eq!(log.root(), mth_root, "binary MTH mismatch at size {}", size);
    }
}
