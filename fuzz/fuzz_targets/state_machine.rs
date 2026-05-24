#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use std::cell::Cell;
use std::rc::Rc;
use eml::{Hasher, Log, MemoryStorage, Storage};

#[derive(Debug)]
enum FuzzStorageErrorEnum {
    Inner(eml::MemoryStorageError),
    Injected(String),
}

impl std::fmt::Display for FuzzStorageErrorEnum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inner(e) => write!(f, "inner storage error: {}", e),
            Self::Injected(s) => write!(f, "injected storage error: {}", s),
        }
    }
}

impl std::error::Error for FuzzStorageErrorEnum {}

struct FaultyStorage {
    inner: MemoryStorage,
    decisions: Vec<bool>,
    decision_idx: Rc<Cell<usize>>,
    inject_faults: Rc<Cell<bool>>,
}

impl FaultyStorage {
    fn should_fail(&self) -> bool {
        if !self.inject_faults.get() {
            return false;
        }
        let idx = self.decision_idx.get();
        if idx >= self.decisions.len() {
            return false;
        }
        let res = self.decisions[idx];
        self.decision_idx.set(idx + 1);
        res
    }
}

impl Storage for FaultyStorage {
    type Error = FuzzStorageErrorEnum;

    fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        if self.should_fail() {
            return Err(FuzzStorageErrorEnum::Injected("store_leaf failed".to_string()));
        }
        self.inner.store_leaf(index, data).map_err(FuzzStorageErrorEnum::Inner)
    }

    fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.inner.get_leaf(index).map_err(FuzzStorageErrorEnum::Inner)
    }

    fn len(&self) -> u64 {
        self.inner.len()
    }

    fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: usize,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        if self.should_fail() {
            return Err(FuzzStorageErrorEnum::Injected("store_node failed".to_string()));
        }
        self.inner.store_node(alg_id, left, height, hash).map_err(FuzzStorageErrorEnum::Inner)
    }

    fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: usize,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner.get_node(alg_id, left, height).map_err(FuzzStorageErrorEnum::Inner)
    }

    fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        if self.should_fail() {
            return Err(FuzzStorageErrorEnum::Injected("store_algorithm_meta failed".to_string()));
        }
        self.inner.store_algorithm_meta(alg_id, epochs).map_err(FuzzStorageErrorEnum::Inner)
    }

    fn load_algorithm_metas(&self) -> Result<Vec<(u64, Vec<(u64, u64)>)>, Self::Error> {
        self.inner.load_algorithm_metas().map_err(FuzzStorageErrorEnum::Inner)
    }
}

#[derive(Debug)]
struct HasherA;
impl Hasher for HasherA {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00, 0x0A]);
        h.update(data);
        h.finalize().to_vec()
    }
    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0x0A]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest([0x0A]).to_vec()
    }
    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02, 0x0A]).to_vec()
    }
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
}

#[derive(Debug)]
struct HasherB;
impl Hasher for HasherB {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00, 0x0B]);
        h.update(data);
        h.finalize().to_vec()
    }
    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0x0B]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest([0x0B]).to_vec()
    }
    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02, 0x0B]).to_vec()
    }
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
}

#[derive(Debug)]
struct HasherC;
impl Hasher for HasherC {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00, 0x0C]);
        h.update(data);
        h.finalize().to_vec()
    }
    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0x0C]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest([0x0C]).to_vec()
    }
    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02, 0x0C]).to_vec()
    }
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
}

fn get_hasher(alg_id: u64) -> Box<dyn Hasher> {
    match alg_id % 3 {
        0 => Box::new(HasherA),
        1 => Box::new(HasherB),
        2 => Box::new(HasherC),
        _ => unreachable!(),
    }
}

fn largest_pow2_lt(n: u64) -> u64 {
    1u64 << (63 - (n - 1).leading_zeros())
}

fn mth(hasher: &dyn Hasher, leaves: &[Vec<u8>]) -> Vec<u8> {
    match leaves.len() {
        0 => hasher.empty(),
        1 => leaves[0].clone(),
        n => {
            let k = largest_pow2_lt(n as u64) as usize;
            let left = mth(hasher, &leaves[..k]);
            let right = mth(hasher, &leaves[k..]);
            hasher.node(&left, &right)
        }
    }
}

#[derive(Debug, Arbitrary)]
enum FuzzCommand {
    Append { data: Vec<u8> },
    AddAlgorithm { alg_id: u8 },
    RemoveAlgorithm { alg_id: u8 },
    ResumeAlgorithm { alg_id: u8 },
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    commands: Vec<FuzzCommand>,
    decisions: Vec<bool>,
}

fuzz_target!(|input: FuzzInput| {
    let decisions = input.decisions;
    let decision_idx = Rc::new(Cell::new(0));
    let inject_faults = Rc::new(Cell::new(true));

    let storage = FaultyStorage {
        inner: MemoryStorage::new(),
        decisions,
        decision_idx: decision_idx.clone(),
        inject_faults: inject_faults.clone(),
    };

    let mut log = Log::new(storage);
    let mut reference_leaves = Vec::new();
    let mut registered_algs = std::collections::BTreeSet::new();

    for command in input.commands {
        let res = match &command {
            FuzzCommand::Append { data } => {
                let res = log.append(data);
                if res.is_ok() {
                    reference_leaves.push(data.clone());
                }
                res.map(|_| ())
            }
            FuzzCommand::AddAlgorithm { alg_id } => {
                let id = *alg_id as u64;
                if registered_algs.contains(&id) {
                    continue;
                }
                let hasher = get_hasher(id);
                let res = log.add_algorithm(id, hasher);
                if res.is_ok() {
                    registered_algs.insert(id);
                }
                res
            }
            FuzzCommand::RemoveAlgorithm { alg_id } => {
                let id = *alg_id as u64;
                log.remove_algorithm(id)
            }
            FuzzCommand::ResumeAlgorithm { alg_id } => {
                let id = *alg_id as u64;
                log.resume_algorithm(id)
            }
        };

        if let Err(eml::Error::Storage(_)) = res {
            // Write failure! Discard and reconstruct.
            inject_faults.set(false);

            let storage = log.into_storage();
            let hashers: Vec<(u64, Box<dyn Hasher>)> = registered_algs
                .iter()
                .map(|&id| (id, get_hasher(id)))
                .collect();

            let reconstructed = Log::from_storage(storage, hashers)
                .expect("Failed to reconstruct Log from storage after write error");

            log = reconstructed;
            inject_faults.set(true);
        }

        // Verify invariants on the current state.
        let global_size = log.size();
        assert_eq!(global_size, reference_leaves.len() as u64);

        for &alg_id in &registered_algs {
            let has_active = log.is_active(alg_id).unwrap();
            let ts = log.tree_size(alg_id).unwrap();

            if has_active {
                assert_eq!(ts, global_size);
            } else {
                assert!(ts <= global_size);
            }

            let root = log.root(alg_id).unwrap();
            let epochs = log.epochs(alg_id).unwrap();

            // Construct projection.
            let hasher = get_hasher(alg_id);
            let mut projected = Vec::with_capacity(ts as usize);
            for i in 0..ts {
                let active = epochs.iter().any(|&(start, end)| {
                    start <= i && end.map_or(true, |e| i < e)
                });
                let h = if active {
                    hasher.leaf(&reference_leaves[i as usize])
                } else {
                    hasher.null()
                };
                projected.push(h);
            }

            let expected_root = mth(hasher.as_ref(), &projected);
            assert_eq!(root, expected_root);
        }
    }
});
