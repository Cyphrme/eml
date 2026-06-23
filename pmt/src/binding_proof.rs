//! Cross-algorithm binding proof — a first-class, named proof API.
//!
//! A **binding proof** is the peer of inclusion / consistency / leaf / snapshot
//! proofs. It proves that a set of per-algorithm **binding roots** are mutually
//! consistent: that every algorithm has committed to the *same* logical
//! structure (the same member-root tuple and the same committed epoch timeline).
//!
//! # The per-algorithm binding root (no security mixing)
//!
//! Each algorithm `i` has its own binding root `BR_i`, the top-level node of
//! that algorithm's tree, computed with **that algorithm's own hash** `H_i` over
//! the canonical preimage of the shared member roots and committed epoch
//! timeline ([`crate::proof::combined_root_preimage`]):
//!
//! ```text
//! BR_i = H_i( combined_root_preimage(member_roots, alg_epochs) )
//! ```
//!
//! The member roots `MR₀, MR₁, …` enter the preimage as **opaque digests** —
//! plain bytes that `H_i` hashes without interpretation. No algorithm's hash is
//! ever applied to another algorithm's *security*: `BR_i`'s collision resistance
//! rests **solely** on `H_i`. There is no single mixed commitment; each `BR_i`
//! is an independent commitment under its own hash to the identical opaque
//! material. This is exactly what lets distinct algorithms agree on a structure
//! without any one's break weakening another (design decision D9).
//!
//! # What the proof establishes (and what it assumes)
//!
//! A binding proof proves **consistency given trusted binding roots**. The
//! binding roots `BR_i` are *trusted inputs* — the verifier never learns their
//! origin from the proof. (A consumer establishes that trust out of band, via an
//! optional attestation carried on the opaque metadata channel; the kernel is
//! agnostic to how.) Given trusted `BR_i, BR_j, …`, the verifier recomputes
//! `H_i(preimage) == BR_i` for **every** algorithm over the **same** member
//! roots and timeline. If all check, the algorithms provably commit to the same
//! structure: `BR_i ≘ BR_j`. A client must support every algorithm involved.
//!
//! Verification reads **digests only** — the binding roots and the member roots
//! are all hashes; no leaf payloads or proof paths are consulted.

use crate::hasher::Hasher;
use crate::proof::{combined_root_preimage, constant_time_eq, validate_committed_epochs};

/// A trusted per-algorithm binding root presented to a binding proof.
///
/// `root` is `BR_i`, an opaque digest the verifier treats as trusted; `hasher`
/// is that algorithm's own `H_i`, used to recompute the binding root from the
/// shared member roots. The pair is bound to `alg_id`.
pub struct TrustedBindingRoot<'a> {
    /// The algorithm this binding root belongs to.
    pub alg_id: u64,
    /// That algorithm's own hash `H_i` — used only on the opaque member-root
    /// preimage, never on another algorithm's material.
    pub hasher: &'a dyn Hasher,
    /// The trusted binding root `BR_i` (an opaque digest).
    pub root: &'a [u8],
}

/// A cross-algorithm binding proof.
///
/// Carries the shared structure every algorithm commits to: the member roots
/// `MR₀, MR₁, …` (the active per-algorithm roots, opaque digests) and the
/// committed epoch timeline they were bound under. The trusted binding roots
/// `BR_i` are *not* stored here — they are supplied to [`Self::verify`] as
/// trusted inputs, because their origin is established out of band.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BindingProof {
    /// The shared member roots: `(alg_id, MR)` for each algorithm active at the
    /// committed tree size, sorted by algorithm ID. Opaque digests.
    pub member_roots: Vec<(u64, Vec<u8>)>,
    /// The committed epoch timeline these roots were bound under: `(alg_id,
    /// epochs)` for every registered algorithm, sorted by algorithm ID. Part of
    /// the canonical binding-root preimage.
    pub alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

impl BindingProof {
    /// Assemble a binding proof from the shared structure committed by every
    /// algorithm: the member roots and the committed epoch timeline.
    ///
    /// This is the *produce* half: a holder of the shared structure packages it
    /// for a verifier. Producing the proof does not require any binding root —
    /// the binding roots are the verifier's trusted inputs, recomputed from this
    /// shared material at verification time.
    #[must_use]
    pub fn produce(
        member_roots: Vec<(u64, Vec<u8>)>,
        alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    ) -> Self {
        Self {
            member_roots,
            alg_epochs,
        }
    }

    /// The shared canonical preimage every algorithm's binding root commits to.
    ///
    /// Both halves of the binding proof — the member roots and the committed
    /// epoch timeline — feed [`combined_root_preimage`]. Every algorithm hashes
    /// this *same* opaque byte string with its own `H_i`; agreement on the
    /// preimage is what "the algorithms agree on the structure" means.
    #[must_use]
    fn preimage(&self) -> Vec<u8> {
        combined_root_preimage(&self.member_roots, &self.alg_epochs)
    }

    /// Verify cross-algorithm binding-root consistency against trusted binding
    /// roots, reading **digests only**.
    ///
    /// For **each** trusted binding root `(alg_id, H_i, BR_i)`, recomputes
    /// `H_i(preimage) == BR_i` over the shared member-root/timeline preimage. The
    /// proof succeeds iff every algorithm's recomputation matches its trusted
    /// `BR_i`. Success proves the algorithms are mutually bound (`BR_i ≘ BR_j`):
    /// each independently commits, under its own hash, to the identical shared
    /// structure.
    ///
    /// # No security mixing (D9)
    ///
    /// Each algorithm's `H_i` is applied **only** to the shared opaque preimage;
    /// the binding roots `BR_i` of other algorithms are never fed into `H_i`. A
    /// break of `H_j` cannot forge agreement under `H_i`.
    ///
    /// # Trust contract
    ///
    /// `trusted` carries **trusted** binding roots: the verifier proves
    /// consistency *given* them, never their origin. Supplying an unauthenticated
    /// `BR_i` makes the guarantee vacuous, exactly as for a forged `root` in
    /// [`crate::proof::verify_inclusion`].
    ///
    /// # Well-formedness
    ///
    /// Returns `false` for an empty trusted set (nothing to bind), for a
    /// structurally malformed committed timeline at `tree_size`, for member
    /// roots not strictly sorted by algorithm ID, or for any trusted binding
    /// root whose algorithm has no member root in the proof. These reject
    /// ill-formed inputs before any hashing.
    #[must_use]
    pub fn verify(&self, trusted: &[TrustedBindingRoot<'_>], tree_size: u64) -> bool {
        // An empty trusted set binds nothing; reject rather than vacuously
        // accept.
        if trusted.is_empty() {
            return false;
        }

        // The committed timeline must be well-formed at the claimed size; a
        // malformed timeline has no canonical preimage to bind.
        if !validate_committed_epochs(&self.alg_epochs, tree_size) {
            return false;
        }

        // Member roots must be canonically sorted by algorithm ID so the
        // preimage is unambiguous (and free of duplicate-ID malleability).
        if self.member_roots.windows(2).any(|w| w[0].0 >= w[1].0) {
            return false;
        }

        // Every trusted binding root must name an algorithm that has a member
        // root in this proof — otherwise the trusted set and the shared
        // structure disagree on which algorithms are bound.
        for t in trusted {
            if !self.member_roots.iter().any(|(id, _)| *id == t.alg_id) {
                return false;
            }
        }

        // The single shared preimage every algorithm commits to.
        let preimage = self.preimage();

        // Each algorithm independently recomputes its own binding root with its
        // own hash over the shared opaque preimage. No algorithm's hash ever
        // touches another's binding root: no security mixing.
        trusted
            .iter()
            .all(|t| constant_time_eq(&t.hasher.hash(&preimage), t.root))
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest as _, Sha256};

    use super::*;

    const MAX: u64 = u64::MAX;

    /// A SHA-256 hasher (`H_i` for algorithm A).
    #[derive(Debug)]
    struct Sha256Hasher;
    impl Hasher for Sha256Hasher {
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
            Box::new(Sha256Hasher)
        }
    }

    /// A second, genuinely different hash `H_j` for algorithm B: SHA-256 over a
    /// domain-separation prefix, so it never agrees with [`Sha256Hasher`] on any
    /// input. Avoids pulling in a second hash crate purely for the tests while
    /// still modelling two distinct algorithms.
    #[derive(Debug)]
    struct PrefixedSha256Hasher;
    impl PrefixedSha256Hasher {
        const PREFIX: &'static [u8] = b"alg-B:";
    }
    impl Hasher for PrefixedSha256Hasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            self.hash(data)
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut buf = Vec::new();
            for c in children {
                buf.extend_from_slice(c);
            }
            self.hash(&buf)
        }

        fn empty(&self) -> Vec<u8> {
            self.hash(b"")
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update(Self::PREFIX);
            h.update(data);
            h.finalize().to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(PrefixedSha256Hasher)
        }
    }

    /// Two algorithms (IDs 0 and 1) committing to the same two member roots and
    /// timeline, with each binding root computed honestly under its own hash.
    fn honest_setup() -> (
        BindingProof,
        Sha256Hasher,
        PrefixedSha256Hasher,
        Vec<u8>,
        Vec<u8>,
        u64,
    ) {
        let member_roots = vec![(0u64, vec![0xAA; 32]), (1u64, vec![0xBB; 32])];
        let alg_epochs = vec![(0u64, vec![(0u64, MAX)]), (1u64, vec![(0u64, MAX)])];
        let tree_size = 4;

        let proof = BindingProof::produce(member_roots.clone(), alg_epochs.clone());
        let preimage = combined_root_preimage(&member_roots, &alg_epochs);

        let h_a = Sha256Hasher;
        let h_b = PrefixedSha256Hasher;
        let br_a = h_a.hash(&preimage);
        let br_b = h_b.hash(&preimage);

        (proof, h_a, h_b, br_a, br_b, tree_size)
    }

    #[test]
    fn consistent_trusted_set_verifies() {
        let (proof, h_a, h_b, br_a, br_b, sz) = honest_setup();
        let trusted = vec![
            TrustedBindingRoot {
                alg_id: 0,
                hasher: &h_a,
                root: &br_a,
            },
            TrustedBindingRoot {
                alg_id: 1,
                hasher: &h_b,
                root: &br_b,
            },
        ];
        assert!(proof.verify(&trusted, sz));
    }

    #[test]
    fn single_algorithm_verifies() {
        // The degenerate one-algorithm case is a well-formed binding proof.
        let (proof, h_a, _h_b, br_a, _br_b, sz) = honest_setup();
        let trusted = vec![TrustedBindingRoot {
            alg_id: 0,
            hasher: &h_a,
            root: &br_a,
        }];
        assert!(proof.verify(&trusted, sz));
    }

    #[test]
    fn forged_binding_root_rejected() {
        // BR_b is replaced with garbage: B never committed to this structure.
        let (proof, h_a, h_b, br_a, _br_b, sz) = honest_setup();
        let forged = vec![0xFFu8; 32];
        let trusted = vec![
            TrustedBindingRoot {
                alg_id: 0,
                hasher: &h_a,
                root: &br_a,
            },
            TrustedBindingRoot {
                alg_id: 1,
                hasher: &h_b,
                root: &forged,
            },
        ];
        assert!(!proof.verify(&trusted, sz));
    }

    #[test]
    fn inconsistent_member_root_rejected() {
        // Algorithm B's binding root was computed over a *different* member-root
        // tuple than the one in the proof; the algorithms do not agree.
        let (proof, h_a, h_b, br_a, _br_b, sz) = honest_setup();
        let other_roots = vec![(0u64, vec![0xAA; 32]), (1u64, vec![0xCC; 32])];
        let other_epochs = vec![(0u64, vec![(0u64, MAX)]), (1u64, vec![(0u64, MAX)])];
        let br_b_other = h_b.hash(&combined_root_preimage(&other_roots, &other_epochs));
        let trusted = vec![
            TrustedBindingRoot {
                alg_id: 0,
                hasher: &h_a,
                root: &br_a,
            },
            TrustedBindingRoot {
                alg_id: 1,
                hasher: &h_b,
                root: &br_b_other,
            },
        ];
        assert!(!proof.verify(&trusted, sz));
    }

    #[test]
    fn wrong_hasher_rejected() {
        // BR_a is genuinely committed, but the verifier is handed the wrong H
        // for it (B's hash). H_b(preimage) != BR_a, so verification fails: no
        // algorithm's security is borrowed for another's check.
        let (proof, _h_a, h_b, br_a, _br_b, sz) = honest_setup();
        let trusted = vec![TrustedBindingRoot {
            alg_id: 0,
            hasher: &h_b,
            root: &br_a,
        }];
        assert!(!proof.verify(&trusted, sz));
    }

    #[test]
    fn empty_trusted_set_rejected() {
        let (proof, _h_a, _h_b, _br_a, _br_b, sz) = honest_setup();
        assert!(!proof.verify(&[], sz));
    }

    #[test]
    fn malformed_timeline_rejected() {
        // An overlapping committed epoch timeline has no canonical preimage.
        let member_roots = vec![(0u64, vec![0xAA; 32])];
        let bad_epochs = vec![(0u64, vec![(0u64, 5u64), (4u64, MAX)])];
        let proof = BindingProof::produce(member_roots.clone(), bad_epochs.clone());
        let h_a = Sha256Hasher;
        let br_a = h_a.hash(&combined_root_preimage(&member_roots, &bad_epochs));
        let trusted = vec![TrustedBindingRoot {
            alg_id: 0,
            hasher: &h_a,
            root: &br_a,
        }];
        assert!(!proof.verify(&trusted, 10));
    }

    #[test]
    fn unsorted_member_roots_rejected() {
        // Member roots out of canonical ID order are rejected before hashing.
        let member_roots = vec![(1u64, vec![0xBB; 32]), (0u64, vec![0xAA; 32])];
        let alg_epochs = vec![(0u64, vec![(0u64, MAX)]), (1u64, vec![(0u64, MAX)])];
        let proof = BindingProof::produce(member_roots.clone(), alg_epochs.clone());
        let h_a = Sha256Hasher;
        let br_a = h_a.hash(&combined_root_preimage(&member_roots, &alg_epochs));
        let trusted = vec![TrustedBindingRoot {
            alg_id: 0,
            hasher: &h_a,
            root: &br_a,
        }];
        assert!(!proof.verify(&trusted, 4));
    }

    #[test]
    fn trusted_root_without_member_root_rejected() {
        // A trusted BR for algorithm 2, which has no member root in the proof.
        let (proof, h_a, _h_b, br_a, _br_b, sz) = honest_setup();
        let trusted = vec![TrustedBindingRoot {
            alg_id: 2,
            hasher: &h_a,
            root: &br_a,
        }];
        assert!(!proof.verify(&trusted, sz));
    }

    #[test]
    fn verify_reads_only_digests() {
        // Structural witness of "digests only": the proof carries no leaf
        // payloads, no proof paths, no preimages — only the member-root and
        // binding-root digests plus the integer timeline. Mutating any member
        // digest flips the result, while there is no payload field to consult.
        let (mut proof, h_a, h_b, br_a, br_b, sz) = honest_setup();
        let trusted = vec![
            TrustedBindingRoot {
                alg_id: 0,
                hasher: &h_a,
                root: &br_a,
            },
            TrustedBindingRoot {
                alg_id: 1,
                hasher: &h_b,
                root: &br_b,
            },
        ];
        assert!(proof.verify(&trusted, sz));
        // Flip one byte of a member digest: the recomputed roots no longer match.
        proof.member_roots[0].1[0] ^= 0x01;
        assert!(!proof.verify(&trusted, sz));
    }
}
