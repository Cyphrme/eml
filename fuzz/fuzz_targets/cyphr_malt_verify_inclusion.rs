#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use neml::{verify_inclusion, ProofStep};

#[derive(Debug)]
struct FuzzHasher;

impl neml::Hasher for FuzzHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01]);
        for child in children {
            h.update(child);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        neml::null_digest(self)
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn neml::Hasher> {
        Box::new(FuzzHasher)
    }
}

#[derive(Debug, Arbitrary)]
struct FuzzProofStep {
    siblings: Vec<Vec<u8>>,
    position: usize,
}

#[derive(Debug, Arbitrary)]
struct Input {
    index: u64,
    tree_size: u64,
    arity: u64,
    path: Vec<FuzzProofStep>,
    leaf_hash: Vec<u8>,
    root: Vec<u8>,
}

fuzz_target!(|input: Input| {
    let path: Vec<ProofStep> = input.path.into_iter().map(|step| ProofStep {
        siblings: step.siblings,
        position: step.position,
    }).collect();

    let _ = verify_inclusion(
        &FuzzHasher,
        &input.leaf_hash,
        input.index,
        input.tree_size,
        input.arity,
        &path,
        &input.root,
    );
});
