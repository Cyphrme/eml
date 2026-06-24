//! Snapshot proof — the aggregate proof over a sealed [`Sealed`].
//!
//! A snapshot proof answers, in one self-contained witness, "are these leaves
//! legitimately in the sealed commitment?" — rooted in the commitment's
//! **trusted binding roots**. It is the aggregate peer of inclusion /
//! consistency / leaf / binding proofs, and its **base case is the PMT leaf
//! proof** ([`pmt::LeafProof`]).
//!
//! # The leaf-proof sequence ⇄ snapshot duality
//!
//! A snapshot froze, per active algorithm, a **member root** `MR_i` (the leaves
//! authenticate against it) and a **binding root** `BR_i` (the head the member
//! roots authenticate against). The two tiers compose:
//!
//! ```text
//! leaf  --(LeafProof::verify against MR_i)-->  MR_i
//! MR₀…  --(BR_i = head over the member roots)-->  BR_i   (trusted)
//! ```
//!
//! Verifying a *sequence* of leaf proofs against the member roots, then binding
//! those member roots to the trusted heads, regenerates exactly the structure
//! the snapshot committed — leaf proofs compose **into** the snapshot. The
//! composition is efficient: one head recomputation per algorithm binds *all*
//! the member roots at once, never a literal per-leaf recursion. The wire format
//! that carries the sequence is deliberately abstract; the duality is the design
//! intuition, not a binding encoding (D3).
//!
//! # Trust contract (security-critical)
//!
//! The binding roots `BR_i` are **trusted inputs**, supplied to [`verify`] as
//! [`TrustedBindingRoot`] values — the proof never establishes their origin. A
//! consumer establishes that trust **out of band**: an optional attestation over
//! the sealed snapshot rides on the snapshot's **opaque metadata channel**
//! ([`pmt::Sealed::meta`]), which this library never reads, validates, or
//! interprets. The library has no notion of who attested the head, only that the
//! caller presents heads it has chosen to trust — exactly the binding-proof
//! contract ([`pmt::BindingProof`]). Supplying an unauthenticated `BR_i` makes
//! the guarantee vacuous, just as a forged `root` does for
//! [`pmt::LeafProof::verify`].
//!
//! [`verify`]: SnapshotProof::verify

use pmt::{
    Hasher, LeafProof, Sealed, TrustedBindingRoot, combined_root, committed_active_algs,
    validate_committed_epochs,
};

/// One claimed leaf in a snapshot proof: a [`pmt::LeafProof`] paired with the
/// algorithm whose member root it verifies against.
///
/// The leaf proof's own trusted positional parameters
/// (`index`, `tree_size`, `arity`) pin the topology; `alg_id` selects which
/// of the snapshot's member roots is the authenticated root the proof reconstructs
/// to. This is the base-case unit the aggregate proof composes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClaimedLeaf {
    /// The algorithm whose member root this leaf proof verifies against.
    pub alg_id: u64,
    /// The base-case leaf proof, verified against that algorithm's member root.
    pub leaf_proof: LeafProof,
}

impl ClaimedLeaf {
    /// Pair a leaf proof with the algorithm whose member root it verifies
    /// against.
    #[must_use]
    pub fn new(alg_id: u64, leaf_proof: LeafProof) -> Self {
        Self { alg_id, leaf_proof }
    }
}

/// An aggregate proof over a sealed [`Sealed`].
///
/// It carries the commitment's frozen shared structure — the member roots `MR_i`
/// and the committed epoch timeline they were bound under, the same material a
/// [`pmt::BindingProof`] commits to — together with the sequence of claimed
/// leaves whose base-case [`pmt::LeafProof`]s verify against those member roots.
/// The trusted binding roots `BR_i` are **not** stored here; they are the
/// verifier's trusted inputs, supplied to [`Self::verify`], because their origin
/// is established out of band (see the module trust contract).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnapshotProof {
    /// The sealed member roots `(alg_id, MR_i)` of every algorithm active at the
    /// snapshot's size, sorted by algorithm ID. The leaves authenticate against
    /// these; the heads are built over them.
    member_roots: Vec<(u64, Vec<u8>)>,
    /// The sealed committed epoch timeline `(alg_id, epochs)` of every registered
    /// algorithm, sorted by algorithm ID — the rest of the canonical head
    /// preimage.
    alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
    /// The size the snapshot was sealed at; the topology the leaf proofs and the
    /// null runs are reconstructed against.
    tree_size: u64,
    /// The spine arity `k` the snapshot was sealed under; fixes the null-run
    /// geometry the head's coverage child commits.
    arity: u64,
    /// The claimed leaves, each a base-case leaf proof against an algorithm's
    /// member root.
    claims: Vec<ClaimedLeaf>,
}

impl SnapshotProof {
    /// Assemble a snapshot proof from a sealed [`Sealed`] and the leaves being
    /// claimed against it.
    ///
    /// The shared structure is read straight from the `Sealed`: the member roots
    /// are the *derived view* over its frozen frontier — each algorithm's peaks
    /// folded under its own hash (`hashers`) — paired with the committed timeline
    /// and sealed size. The caller supplies the base-case leaf proofs. This is
    /// the *produce* half — packaging the commitment's frozen material with the
    /// leaf-proof sequence for a verifier. Producing the proof requires no
    /// binding root: the heads are the verifier's trusted inputs, recomputed from
    /// this shared material at verification time.
    #[must_use]
    pub fn produce(
        sealed: &Sealed,
        hashers: &[(u64, &dyn Hasher)],
        claims: Vec<ClaimedLeaf>,
    ) -> Self {
        Self {
            member_roots: sealed.member_roots(hashers),
            alg_epochs: sealed.alg_epochs().to_vec(),
            tree_size: sealed.tree_size(),
            arity: sealed.arity(),
            claims,
        }
    }

    /// The member root of an algorithm in this proof, if it is one of the sealed
    /// active algorithms.
    fn member_root(&self, alg_id: u64) -> Option<&[u8]> {
        self.member_roots
            .iter()
            .find(|(id, _)| *id == alg_id)
            .map(|(_, r)| r.as_slice())
    }

    /// Recompute the head an algorithm's member roots bind to: the
    /// canonicalization fold ([`pmt::combined_root`]) over the member roots as
    /// children, plus a coverage child committing all algorithms' null runs iff
    /// the activation is non-trivial, under that algorithm's hash — exactly the
    /// head the log seals under
    /// ([`NaryMerkleLog::combined_root_at`](crate::tree::NaryMerkleLog::combined_root_at)).
    /// Genesis promotion is native: a single member root with no null run folds
    /// to itself, no special case. The returned bytes are compared, in constant
    /// time, against the trusted head.
    fn recompute_head(&self, hasher: &dyn Hasher) -> Vec<u8> {
        combined_root(
            hasher,
            &self.member_roots,
            &self.alg_epochs,
            self.tree_size,
            self.arity,
        )
    }

    /// Verify the snapshot proof against the snapshot's **trusted binding roots**.
    ///
    /// `trusted` carries the trusted heads `(alg_id, H_i, BR_i)` — one per
    /// algorithm whose leaves are claimed; `hashers` resolves an algorithm's own
    /// hash `H_i` for verifying its base-case leaf proofs against its member root.
    /// Verification has two composed tiers:
    ///
    /// 1. **Binding tier (aggregate).** For every trusted head, recompute the head over the proof's
    ///    shared member roots and committed timeline and require it equal `BR_i` (promotion-aware;
    ///    One head recomputation binds all the member roots at once.
    /// 2. **Base tier (leaf proofs).** Every claimed leaf proof must verify against *its
    ///    algorithm's member root* under that algorithm's hash. The member root is exactly the root
    ///    the binding tier just bound to a trusted head, so an accepted leaf chains leaf → member
    ///    root → trusted head.
    ///
    /// Returns `true` iff every well-formedness check passes, every trusted head
    /// is reproduced, and every claimed leaf proof verifies. The guarantee is
    /// **consistency given trusted heads**: the proof never learns a head's
    /// origin (established out of band over the opaque metadata channel).
    ///
    /// # Well-formedness
    ///
    /// Returns `false` for an empty trusted set (nothing to root trust in); for a
    /// committed timeline that is malformed at the sealed size, that disagrees on
    /// the active set, or whose member roots are not strictly sorted by algorithm
    /// ID; for any trusted head or claimed leaf naming an algorithm with no member
    /// root in the proof; or for any claim whose hasher is missing from `hashers`.
    /// These reject ill-formed inputs before trusting any result.
    #[must_use]
    pub fn verify(
        &self,
        trusted: &[TrustedBindingRoot<'_>],
        hashers: &[(u64, &dyn Hasher)],
    ) -> bool {
        // An empty trusted set roots trust in nothing; reject rather than
        // vacuously accept.
        if trusted.is_empty() {
            return false;
        }

        // The committed timeline must be well-formed at the sealed size and must
        // imply exactly the sealed active set — an algorithm cannot present a
        // member root without a covering epoch, nor a covering epoch without a
        // member root. This is the same active-set agreement the binding and
        // coupling proofs enforce.
        if !validate_committed_epochs(&self.alg_epochs, self.tree_size) {
            return false;
        }
        let derived = committed_active_algs(&self.alg_epochs, self.tree_size);
        if derived.len() != self.member_roots.len()
            || derived
                .iter()
                .zip(self.member_roots.iter())
                .any(|(&d, &(id, _))| d != id)
        {
            return false;
        }

        // Member roots must be canonically sorted by algorithm ID so the head
        // preimage is unambiguous (no duplicate-ID or ordering malleability).
        if self.member_roots.windows(2).any(|w| w[0].0 >= w[1].0) {
            return false;
        }

        // Every trusted head must name an algorithm that has a member root here,
        // else the trusted set and the sealed structure disagree on which
        // algorithms are bound.
        for t in trusted {
            if self.member_root(t.alg_id).is_none() {
                return false;
            }
        }

        // Tier 1 — bind every trusted head to the shared member roots. The head
        // is recomputed once per algorithm and bound to all member roots at once.
        for t in trusted {
            let head = self.recompute_head(t.hasher);
            if !pmt::constant_time_eq(&head, t.root) {
                return false;
            }
        }

        // Tier 2 — every claimed leaf proof verifies against its algorithm's
        // member root, under that algorithm's own hash. The member root is the
        // one the binding tier bound to a trusted head, so acceptance chains
        // leaf → member root → trusted head.
        for claim in &self.claims {
            let Some(member_root) = self.member_root(claim.alg_id) else {
                return false;
            };
            let Some(&(_, hasher)) = hashers.iter().find(|(id, _)| *id == claim.alg_id) else {
                return false;
            };
            if !claim.leaf_proof.verify(hasher, member_root) {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use pmt::Hasher;
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::storage::MemoryStorage;
    use crate::tree::{NaryMerkleLog, TreeConfig};

    /// A fixed-width (32-byte) test hasher.
    #[derive(Debug, Clone)]
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

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            Sha256::digest(data).to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(self.clone())
        }
    }

    /// A second, domain-separated 32-byte hasher modelling a distinct algorithm.
    #[derive(Debug, Clone)]
    struct PrefixedSha256Hasher;
    impl PrefixedSha256Hasher {
        const PREFIX: &'static [u8] = b"ALG1:";
    }
    impl Hasher for PrefixedSha256Hasher {
        fn leaf(&self, data: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update(Self::PREFIX);
            h.update(data);
            h.finalize().to_vec()
        }

        fn node(&self, children: &[&[u8]]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update(Self::PREFIX);
            for child in children {
                h.update(child);
            }
            h.finalize().to_vec()
        }

        fn empty(&self) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update(Self::PREFIX);
            h.update(b"");
            h.finalize().to_vec()
        }

        fn hash(&self, data: &[u8]) -> Vec<u8> {
            let mut h = Sha256::new();
            h.update(Self::PREFIX);
            h.update(data);
            h.finalize().to_vec()
        }

        fn clone_box(&self) -> Box<dyn Hasher> {
            Box::new(self.clone())
        }
    }

    async fn log_with(n: u64, k: usize) -> NaryMerkleLog<MemoryStorage> {
        let config = TreeConfig { arity: k as u64 };
        let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
            .await
            .unwrap();
        for i in 0..n {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log
    }

    /// Build the claimed leaves for every position of a single-algorithm log,
    /// reading the leaf proofs straight off the live log before it is sealed.
    async fn claims_for_all(log: &NaryMerkleLog<MemoryStorage>, n: u64) -> Vec<ClaimedLeaf> {
        let mut claims = Vec::new();
        for i in 0..n {
            let lp = log.leaf_proof(i, n).await.unwrap().expect("leaf proof");
            claims.push(ClaimedLeaf::new(0, lp));
        }
        claims
    }

    // ---------------------------------------------------------------------
    // Spec (acceptance): a valid snapshot verifies — every leaf chains to the
    // trusted binding root. Swept across sizes and arities. This is the
    // net-new property the IBC names; no difftest baseline exists (D7).
    // ---------------------------------------------------------------------

    #[test]
    fn valid_snapshot_verifies_across_sizes_and_arities() {
        smol::block_on(async {
            let h = Sha256Hasher;
            for k in [2usize, 3, 4] {
                for n in 1u64..18 {
                    let log = log_with(n, k).await;
                    let claims = claims_for_all(&log, n).await;
                    let br = log.combined_root_at(0, n).await.unwrap();
                    let sealed = log.seal().await.unwrap();

                    let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
                    let proof = SnapshotProof::produce(&sealed, &hashers, claims);
                    let trusted = [TrustedBindingRoot {
                        alg_id: 0,
                        hasher: &h,
                        root: &br,
                    }];
                    let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
                    assert!(
                        proof.verify(&trusted, &hashers),
                        "valid snapshot must verify (n={n}, k={k})"
                    );
                }
            }
        });
    }

    // ---------------------------------------------------------------------
    // The trusted head is the snapshot's binding root, and trust rides the
    // opaque metadata channel — the library never reads it. A snapshot with an
    // arbitrary metadata attestation verifies identically to one without; the
    // proof is agnostic to the channel's contents.
    // ---------------------------------------------------------------------

    #[test]
    fn trust_rides_opaque_metadata_untouched() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let log = log_with(6, 2).await;
            let claims = claims_for_all(&log, 6).await;
            let br = log.combined_root_at(0, 6).await.unwrap();
            // An arbitrary attestation payload rides the opaque channel; the
            // library never interprets it, so verification ignores it entirely.
            let sealed = log
                .seal_with_meta(pmt::Meta::new(vec![0xAB; 64]))
                .await
                .unwrap();

            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            let trusted = [TrustedBindingRoot {
                alg_id: 0,
                hasher: &h,
                root: &br,
            }];
            assert!(proof.verify(&trusted, &hashers));
            // The proof carries nothing derived from the metadata payload.
            assert_eq!(
                sealed.meta().map(pmt::Meta::as_bytes),
                Some([0xAB; 64].as_slice())
            );
        });
    }

    // ---------------------------------------------------------------------
    // Soundness — an untrusted (forged) binding root makes the guarantee fail:
    // the binding tier rejects a head the member roots do not reconstruct.
    // ---------------------------------------------------------------------

    #[test]
    fn forged_binding_root_is_rejected() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let log = log_with(7, 2).await;
            let claims = claims_for_all(&log, 7).await;
            let sealed = log.seal().await.unwrap();

            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            let forged = vec![0x00; 32];
            let trusted = [TrustedBindingRoot {
                alg_id: 0,
                hasher: &h,
                root: &forged,
            }];
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            assert!(
                !proof.verify(&trusted, &hashers),
                "a head the member roots do not reconstruct must be rejected"
            );
        });
    }

    // ---------------------------------------------------------------------
    // Soundness — a forged leaf (wrong payload at a claimed position) cannot
    // produce an accepting snapshot proof, even with the genuine binding root.
    // ---------------------------------------------------------------------

    #[test]
    fn forged_leaf_breaks_the_proof() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let log = log_with(8, 2).await;
            let mut claims = claims_for_all(&log, 8).await;
            let br = log.combined_root_at(0, 8).await.unwrap();
            let sealed = log.seal().await.unwrap();

            // Tamper with one claimed leaf's hash; the genuine head is unchanged.
            claims[3].leaf_proof.leaf_hash = h.leaf(b"forged-payload");

            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            let trusted = [TrustedBindingRoot {
                alg_id: 0,
                hasher: &h,
                root: &br,
            }];
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            assert!(
                !proof.verify(&trusted, &hashers),
                "a forged leaf must break the aggregate proof"
            );
        });
    }

    // ---------------------------------------------------------------------
    // Multi-algorithm: each algorithm's leaves bind to its own per-algorithm
    // binding root, computed under its own hash (no security mixing, D9).
    // ---------------------------------------------------------------------

    #[test]
    fn multi_algorithm_snapshot_verifies() {
        smol::block_on(async {
            let config = TreeConfig { arity: 2 };
            let mut log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(Sha256Hasher), config)
                .await
                .unwrap();
            log.add_algorithm(1, Box::new(PrefixedSha256Hasher))
                .await
                .unwrap();
            for i in 0..4u64 {
                log.append_leaf(&i.to_be_bytes()).await.unwrap();
            }
            let n = log.count();

            // A leaf proof under each algorithm at a couple of positions.
            let mut claims = Vec::new();
            for &(alg, idx) in &[(0u64, 0u64), (0, 3), (1, 1), (1, 2)] {
                let lp = log
                    .leaf_proof_for(alg, idx, n)
                    .await
                    .unwrap()
                    .expect("leaf proof");
                claims.push(ClaimedLeaf::new(alg, lp));
            }
            let br0 = log.combined_root_at(0, n).await.unwrap();
            let br1 = log.combined_root_at(1, n).await.unwrap();
            let sealed = log.seal().await.unwrap();

            let h0 = Sha256Hasher;
            let h1 = PrefixedSha256Hasher;
            let hashers: [(u64, &dyn Hasher); 2] = [(0, &h0), (1, &h1)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            let trusted = [
                TrustedBindingRoot {
                    alg_id: 0,
                    hasher: &h0,
                    root: &br0,
                },
                TrustedBindingRoot {
                    alg_id: 1,
                    hasher: &h1,
                    root: &br1,
                },
            ];
            assert!(proof.verify(&trusted, &hashers));

            // Wrong hash on a trusted head (alg 1 verified with alg 0's hash):
            // the head no longer reconstructs — rejected. No security mixing.
            let bad = [
                TrustedBindingRoot {
                    alg_id: 0,
                    hasher: &h0,
                    root: &br0,
                },
                TrustedBindingRoot {
                    alg_id: 1,
                    hasher: &h0,
                    root: &br1,
                },
            ];
            assert!(!proof.verify(&bad, &hashers));
        });
    }

    // ---------------------------------------------------------------------
    // Well-formedness rejections.
    // ---------------------------------------------------------------------

    #[test]
    fn empty_trusted_set_is_rejected() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let log = log_with(4, 2).await;
            let claims = claims_for_all(&log, 4).await;
            let sealed = log.seal().await.unwrap();
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            assert!(!proof.verify(&[], &hashers));
        });
    }

    #[test]
    fn trusted_head_for_unknown_algorithm_is_rejected() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let log = log_with(4, 2).await;
            let claims = claims_for_all(&log, 4).await;
            let br = log.combined_root_at(0, 4).await.unwrap();
            let sealed = log.seal().await.unwrap();
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            // Algorithm 9 has no member root in the snapshot.
            let trusted = [TrustedBindingRoot {
                alg_id: 9,
                hasher: &h,
                root: &br,
            }];
            let hashers: [(u64, &dyn Hasher); 1] = [(9, &h)];
            assert!(!proof.verify(&trusted, &hashers));
        });
    }

    #[test]
    fn claim_with_missing_hasher_is_rejected() {
        smol::block_on(async {
            let h = Sha256Hasher;
            let log = log_with(5, 2).await;
            let claims = claims_for_all(&log, 5).await;
            let br = log.combined_root_at(0, 5).await.unwrap();
            let sealed = log.seal().await.unwrap();
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, claims);
            let trusted = [TrustedBindingRoot {
                alg_id: 0,
                hasher: &h,
                root: &br,
            }];
            // No hasher provided for algorithm 0's claims.
            let hashers: [(u64, &dyn Hasher); 0] = [];
            assert!(!proof.verify(&trusted, &hashers));
        });
    }

    #[test]
    fn no_claims_still_binds_the_head() {
        smol::block_on(async {
            // A snapshot proof with zero claimed leaves degenerates to a binding
            // assertion: the head reconstructs from the sealed member roots. This
            // is well-formed and accepts (the leaf tier is vacuously satisfied).
            let h = Sha256Hasher;
            let log = log_with(6, 2).await;
            let br = log.combined_root_at(0, 6).await.unwrap();
            let sealed = log.seal().await.unwrap();
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            let proof = SnapshotProof::produce(&sealed, &hashers, vec![]);
            let trusted = [TrustedBindingRoot {
                alg_id: 0,
                hasher: &h,
                root: &br,
            }];
            let hashers: [(u64, &dyn Hasher); 1] = [(0, &h)];
            assert!(proof.verify(&trusted, &hashers));
        });
    }
}
