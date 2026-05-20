//! Shared test hashers for EML unit tests.
//!
//! Provides domain-separated hash implementations across three distinct
//! algorithm families (SHA-256, SHA3-256, BLAKE2b-256) for property-based
//! and unit testing.

use blake2::Blake2b;
use blake2::digest::consts::U32;
use sha2::{Digest, Sha256};
use sha3::Sha3_256;

use crate::Hasher;

/// SHA-256 hasher (32-byte digest).
#[derive(Debug)]
pub(crate) struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
    }
}

/// SHA3-256 hasher (32-byte digest, Keccak-based).
#[derive(Debug)]
pub(crate) struct Sha3Hasher;

impl Hasher for Sha3Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha3_256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha3_256::new();
        h.update([0x01]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha3_256::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        Sha3_256::digest([0x02]).to_vec()
    }
}

/// BLAKE2b-256 hasher (32-byte digest).
#[derive(Debug)]
pub(crate) struct Blake2bHasher;

impl Hasher for Blake2bHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Blake2b::<U32>::new();
        Digest::update(&mut h, [0x00]);
        Digest::update(&mut h, data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Blake2b::<U32>::new();
        Digest::update(&mut h, [0x01]);
        Digest::update(&mut h, left);
        Digest::update(&mut h, right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        <Blake2b<U32> as Digest>::digest(b"").to_vec()
    }

    fn null(&self) -> Vec<u8> {
        <Blake2b<U32> as Digest>::digest([0x02]).to_vec()
    }
}

/// Second hasher for multi-algorithm tests (uses a different prefix to
/// produce distinct outputs — simulates SHA-384 without importing it).
#[derive(Debug)]
pub(crate) struct AltHasher;

impl Hasher for AltHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00, 0xFF]); // extra byte distinguishes from Sha256Hasher
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01, 0xFF]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0xFF]);
        h.finalize().to_vec()
    }

    fn null(&self) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x02, 0xFF]);
        h.finalize().to_vec()
    }
}

/// Three-way hasher dispatch by algorithm ID: 0→SHA-256, 1→SHA3-256, 2→BLAKE2b.
pub(crate) fn new_hasher_for(alg_id: u64) -> Box<dyn Hasher> {
    match alg_id % 3 {
        0 => Box::new(Sha256Hasher),
        1 => Box::new(Sha3Hasher),
        2 => Box::new(Blake2bHasher),
        _ => unreachable!(),
    }
}
