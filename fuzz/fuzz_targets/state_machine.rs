#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use eml::{AlgorithmMetas, Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};

// ---------------------------------------------------------------------------
// Faulty storage wrapper
// ---------------------------------------------------------------------------

#[derive(Debug)]
enum FuzzStorageError {
    Inner(<MemoryStorage as Storage>::Error),
    Injected(String),
}

impl std::fmt::Display for FuzzStorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inner(e) => write!(f, "inner storage error: {}", e),
            Self::Injected(s) => write!(f, "injected storage error: {}", s),
        }
    }
}

impl std::error::Error for FuzzStorageError {}

struct FaultyStorage {
    inner: MemoryStorage,
    decisions: Vec<bool>,
    decision_idx: Arc<AtomicUsize>,
    inject_faults: Arc<AtomicBool>,
}

impl FaultyStorage {
    fn should_fail(&self) -> bool {
        if !self.inject_faults.load(Ordering::SeqCst) {
            return false;
        }
        let idx = self.decision_idx.fetch_add(1, Ordering::SeqCst);
        if idx >= self.decisions.len() {
            return false;
        }
        self.decisions[idx]
    }
}

impl Storage for FaultyStorage {
    type Error = FuzzStorageError;

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        if self.should_fail() {
            return Err(FuzzStorageError::Injected("store_leaf failed".to_string()));
        }
        self.inner.store_leaf(index, data).await.map_err(FuzzStorageError::Inner)
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        self.inner.get_leaf(index).await.map_err(FuzzStorageError::Inner)
    }

    async fn len(&self) -> Result<u64, Self::Error> {
        self.inner.len().await.map_err(FuzzStorageError::Inner)
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        if self.should_fail() {
            return Err(FuzzStorageError::Injected("store_node failed".to_string()));
        }
        self.inner.store_node(alg_id, left, height, hash).await.map_err(FuzzStorageError::Inner)
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        self.inner.get_node(alg_id, left, height).await.map_err(FuzzStorageError::Inner)
    }

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        if self.should_fail() {
            return Err(FuzzStorageError::Injected("store_algorithm_meta failed".to_string()));
        }
        self.inner.store_algorithm_meta(alg_id, epochs).await.map_err(FuzzStorageError::Inner)
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        self.inner.load_algorithm_metas().await.map_err(FuzzStorageError::Inner)
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        self.inner.load_log_meta().await.map_err(FuzzStorageError::Inner)
    }

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        self.inner.load_checkpoint_roots().await.map_err(FuzzStorageError::Inner)
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
        algorithm_metas: &[(u64, &[(u64, u64)])],
        log_meta: Option<(u64, u8)>,
        checkpoint_roots: &[(u64, &[u8])],
    ) -> Result<(), Self::Error> {
        // Top-level fault injection: fail the whole batch before any write.
        if self.should_fail() {
            return Err(FuzzStorageError::Injected("write_batch failed".to_string()));
        }
        self.inner
            .write_batch(leaves, nodes, algorithm_metas, log_meta, checkpoint_roots)
            .await
            .map_err(FuzzStorageError::Inner)
    }
}

// ---------------------------------------------------------------------------
// Hashers
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct HasherA;
impl Hasher for HasherA {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00, 0x0A]);
        h.update(data);
        h.finalize().to_vec()
    }
    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0x0A]);
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest([0x0A]).to_vec()
    }
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(HasherA)
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
    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0x0B]);
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest([0x0B]).to_vec()
    }
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(HasherB)
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
    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0x0C]);
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest([0x0C]).to_vec()
    }
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(HasherC)
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

// ---------------------------------------------------------------------------
// Reference root computation
// ---------------------------------------------------------------------------

fn largest_pow2_lt(n: u64) -> u64 {
    1u64 << (63 - (n - 1).leading_zeros())
}

/// RFC-9162 MTH over pre-hashed leaves (each entry is already leaf-hashed).
fn mth(hasher: &dyn Hasher, leaves: &[Vec<u8>]) -> Vec<u8> {
    match leaves.len() {
        0 => hasher.empty(),
        1 => leaves[0].clone(),
        n => {
            let k = largest_pow2_lt(n as u64) as usize;
            let left = mth(hasher, &leaves[..k]);
            let right = mth(hasher, &leaves[k..]);
            hasher.node(&[&left, &right])
        }
    }
}

// ---------------------------------------------------------------------------
// Fuzz commands
// ---------------------------------------------------------------------------

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
    smol::block_on(async {
        let decisions = input.decisions;
        let decision_idx = Arc::new(AtomicUsize::new(0));
        let inject_faults = Arc::new(AtomicBool::new(true));

        let storage = FaultyStorage {
            inner: MemoryStorage::new(),
            decisions,
            decision_idx: decision_idx.clone(),
            inject_faults: inject_faults.clone(),
        };

        // NaryMerkleLog::new registers algorithm 0 (HasherA) automatically.
        let mut log = match NaryMerkleLog::new(
            storage,
            get_hasher(0),
            TreeConfig::default(),
        )
        .await
        {
            Ok(l) => l,
            Err(_) => return,
        };

        let mut reference_leaves: Vec<Vec<u8>> = Vec::new();
        // Track registered alg ids (alg 0 is always registered by new()).
        let mut registered_algs = std::collections::BTreeSet::new();
        registered_algs.insert(0u64);

        for command in input.commands {
            let res = match &command {
                FuzzCommand::Append { data } => {
                    let res = log.append_leaf(data).await;
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
                    let res = log.add_algorithm(id, hasher).await;
                    if res.is_ok() {
                        registered_algs.insert(id);
                    }
                    res
                }
                FuzzCommand::RemoveAlgorithm { alg_id } => {
                    let id = *alg_id as u64;
                    log.remove_algorithm(id).await
                }
                FuzzCommand::ResumeAlgorithm { alg_id } => {
                    let id = *alg_id as u64;
                    log.resume_algorithm(id).await
                }
            };

            if let Err(eml::Error::Storage(_)) = res {
                // Write failure! Verify that the log is consistent.
                inject_faults.store(false, Ordering::SeqCst);
                let len = log.size();
                assert_eq!(len, reference_leaves.len() as u64);
                inject_faults.store(true, Ordering::SeqCst);
            }

            // Verify invariants on the current state.
            let global_size = log.size();
            assert_eq!(global_size, reference_leaves.len() as u64);

            // Use committed_epochs_at to get per-alg epoch info.
            let epochs_at = log.committed_epochs_at(global_size);

            for &alg_id in &registered_algs {
                // Determine whether alg is active (last epoch is open).
                let epochs: Option<&Vec<(u64, u64)>> = epochs_at
                    .iter()
                    .find(|(id, _)| *id == alg_id)
                    .map(|(_, e)| e);

                let Some(alg_epochs) = epochs else { continue };

                let is_active = alg_epochs
                    .last()
                    .is_some_and(|&(_, end)| end == u64::MAX);

                let ts: u64 = if is_active {
                    global_size
                } else {
                    alg_epochs.last().map_or(0, |&(_, end)| end)
                };

                // root_for gives the raw member root for an alg.
                let root = match log.root_for(alg_id) {
                    Ok(r) => r,
                    Err(_) => continue,
                };

                // Construct the reference projection.
                let hasher = get_hasher(alg_id);
                let mut projected = Vec::with_capacity(ts as usize);
                for i in 0..ts {
                    let active = alg_epochs.iter().any(|&(start, end)| {
                        start <= i && (end == u64::MAX || i < end)
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
});
