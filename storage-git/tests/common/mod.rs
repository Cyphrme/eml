//! Shared test fixtures: repository setup and two `Hasher` implementations
//! of different digest widths (SG26), used across this crate's structural,
//! differential, and parametric tests.

use gix::ThreadSafeRepository;
use gix::create::{Kind as CreateKind, Options as CreateOptions};
use gix::hash::Kind as HashKind;
use sha2::{Digest, Sha256};
use spine::Hasher;
use tempfile::TempDir;

/// Initialize a fresh bare repository under the requested object-hash
/// format (SG27).
#[must_use]
pub fn init_repo(hash: HashKind) -> (TempDir, ThreadSafeRepository) {
    let dir = tempfile::tempdir().unwrap();
    let opts = CreateOptions {
        object_hash: Some(hash),
        ..Default::default()
    };
    let repo =
        ThreadSafeRepository::init_opts(dir.path(), CreateKind::Bare, opts, Default::default())
            .expect("init bare repository");
    (dir, repo)
}

/// A 32-byte SHA-256 hasher, the same shape `storage-fjall`'s own tests use.
///
/// `allow(dead_code)`: this module is compiled once per integration test
/// binary, and not every binary that uses one hasher also uses the other.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct WideHasher;

impl Hasher for WideHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(WideHasher)
    }
}

/// An 8-byte hasher (SHA-256 truncated), deliberately a different width
/// than [`WideHasher`] so SG26's width-parametricity claim is exercised by
/// at least two distinct widths, never assumed to be 32.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct NarrowHasher;

impl Hasher for NarrowHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data)[..8].to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize()[..8].to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"")[..8].to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data)[..8].to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(NarrowHasher)
    }
}
