#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use cyphr_malt::{verify_inclusion, InclusionProof, ProofStep};

#[derive(Debug)]
struct FuzzHasher;

impl cyphr_malt::Hasher for FuzzHasher {
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
        Sha256::digest([0x02]).to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn cyphr_malt::Hasher> {
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
    path: Vec<FuzzProofStep>,
    leaf_hash: Vec<u8>,
    root: Vec<u8>,
}

fuzz_target!(|input: Input| {
    let path = input.path.into_iter().map(|step| ProofStep {
        siblings: step.siblings,
        position: step.position,
    }).collect();

    let proof = InclusionProof {
        index: input.index,
        tree_size: input.tree_size,
        path,
    };
    
    let _ = verify_inclusion(&FuzzHasher, &input.leaf_hash, &proof, &input.root);
});
