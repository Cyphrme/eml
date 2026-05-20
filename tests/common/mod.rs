//! Shared test utilities for EML integration tests.
//!
//! This duplicates `src/test_hashers::Sha256Hasher` because Rust's
//! compilation model prevents integration tests from accessing
//! `#[cfg(test)]` or `pub(crate)` items in the library crate.

use eml::Hasher;
use sha2::{Digest, Sha256};

/// SHA-256 implementation of the EML Hasher trait.
#[derive(Debug)]
pub struct Sha256Hasher;

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
