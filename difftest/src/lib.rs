//! Shared hashers for the differential harness.
//!
//! The current side (`eml`) and the frozen baseline (`neml_baseline`)
//! each define their own `Hasher` trait. A differential case drives both with the
//! *same* hashing behavior, so the structs below implement both traits with
//! byte-identical logic. The two `node` implementations concatenate children
//! and hash; the two `leaf`/`hash`/`empty`/`null` paths are identical.
//!
//! Multiple algorithms are exercised via three distinct hash functions
//! (SHA-256, "tagged" SHA-256, and byte-reversed SHA-256). They are *not*
//! cryptographically meaningful — they only need to be distinct, deterministic,
//! and identical across the two crates so the binding-root machinery sees a
//! genuine multi-algorithm registry.

use sha2::{Digest, Sha256};

/// Plain SHA-256 hasher (algorithm 0).
#[derive(Debug, Clone, Copy)]
pub struct Sha256Hasher;

/// SHA-256 over a fixed domain tag, giving a second distinct algorithm.
#[derive(Debug, Clone, Copy)]
pub struct TaggedSha256Hasher;

/// SHA-256 with the digest byte-reversed, giving a third distinct algorithm.
#[derive(Debug, Clone, Copy)]
pub struct RevSha256Hasher;

const TAG: &[u8] = b"difftest/tagged";

fn tagged(data: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(TAG);
    h.update(data);
    h.finalize().to_vec()
}

fn reversed(data: &[u8]) -> Vec<u8> {
    let mut out = Sha256::digest(data).to_vec();
    out.reverse();
    out
}

// A macro keeps the two trait impls byte-identical: any divergence between the
// `eml` and `neml_baseline` impls would be a harness bug, so they are
// generated from one source.
macro_rules! impl_hasher {
    ($trait_path:path) => {
        impl $trait_path for Sha256Hasher {
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

            fn hash(&self, data: &[u8]) -> Vec<u8> {
                Sha256::digest(data).to_vec()
            }

            fn clone_box(&self) -> Box<dyn $trait_path> {
                Box::new(Sha256Hasher)
            }
        }

        impl $trait_path for TaggedSha256Hasher {
            fn leaf(&self, data: &[u8]) -> Vec<u8> {
                tagged(data)
            }

            fn node(&self, children: &[&[u8]]) -> Vec<u8> {
                let mut buf = Vec::new();
                for child in children {
                    buf.extend_from_slice(child);
                }
                tagged(&buf)
            }

            fn empty(&self) -> Vec<u8> {
                tagged(b"")
            }

            fn hash(&self, data: &[u8]) -> Vec<u8> {
                tagged(data)
            }

            fn clone_box(&self) -> Box<dyn $trait_path> {
                Box::new(TaggedSha256Hasher)
            }
        }

        impl $trait_path for RevSha256Hasher {
            fn leaf(&self, data: &[u8]) -> Vec<u8> {
                reversed(data)
            }

            fn node(&self, children: &[&[u8]]) -> Vec<u8> {
                let mut buf = Vec::new();
                for child in children {
                    buf.extend_from_slice(child);
                }
                reversed(&buf)
            }

            fn empty(&self) -> Vec<u8> {
                reversed(b"")
            }

            fn hash(&self, data: &[u8]) -> Vec<u8> {
                reversed(data)
            }

            fn clone_box(&self) -> Box<dyn $trait_path> {
                Box::new(RevSha256Hasher)
            }
        }
    };
}

impl_hasher!(eml::Hasher);
impl_hasher!(neml_baseline::Hasher);
