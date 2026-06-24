import EMLProof.LeafProof

/-!
# Snapshot-proof soundness (EML, over `Foundations`)

The **snapshot proof** is the aggregate proof over a sealed snapshot
(`eml/src/snapshot_proof.rs`): it answers "are these leaves legitimately in the
snapshot?" in one witness, rooted in the snapshot's **trusted binding root**. Its
**base case is the PMT leaf proof** (`LeafProof.lean`, N13), and this module
discharges its soundness *over* that base case — adding **no new axiom** beyond
`Foundations`' four.

## The two composed tiers

The Rust `SnapshotProof::verify` chains two tiers; both are modelled here over
the same `Kary`/`Foundations` machinery the leaf proof uses:

1. **Binding tier (head).** Each algorithm's member root binds to the trusted
   head `BR`. For the registry-singleton, default-timeline case the seal commits
   the *raw* member root as the head (genesis promotion: `BR = MR`), which is the
   case modelled here — the head the verifier trusts **is** the genuine
   `karyRoot L k cells` the leaf proofs verify against.
2. **Base tier (leaf proofs).** Every claimed leaf's base-case `LeafVerifies`
   (`LeafProof.lean`) must hold against that member root.

A snapshot proof is **valid** when the head equals the genuine root *and* every
claimed leaf verifies against it. Soundness is then exactly the statement the
acceptance/soundness spec tests witness operationally: a valid snapshot proof's
claimed leaves are the committed cells — equivalently, a forged leaf cannot
appear in a valid snapshot proof unless a hash assumption breaks.

## What "valid" means

A snapshot proof over level `L`, arity `k`, and committed cells `cells` carries a
list of `claims`, each a `(leaf, index, path)` triple whose verify relation is
`LeafVerifies L k leaf index cells.length root path` against the head `root`. The
proof is `SnapshotValid` when `root = karyRoot L k cells` (the binding tier on the
promoted head) and every claim's `LeafVerifies` holds.

## No new axiom

This module imports only `EMLProof.LeafProof` (hence `Kary`/`Foundations`); every
theorem is proved by composing `leaf_proof_flat_sound`. `#print axioms` therefore
reports a subset of `{Digest, Digest.nonempty, H, digestToBytes}` plus the Lean
built-ins `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no new axiom.
-/

namespace NEML

/-- One claimed leaf in a snapshot proof: the leaf hash, its trusted log
    position, and its inclusion path — the base-case `LeafProof` payload. -/
structure SnapshotClaim where
  /-- The claimed leaf hash. -/
  leaf : Digest
  /-- The trusted log position of the leaf. -/
  index : Nat
  /-- The base-case inclusion path verified against the member root. -/
  path : List ProofStep

/-- The base-tier predicate for a single claim: its base-case leaf proof
    verifies against the head `root` (the member root the binding tier bound to
    the trusted head). This is `LeafVerifies` from `LeafProof.lean` — the N13
    base case the aggregate composes. -/
def ClaimVerifies (L k : Nat) (cells : List Digest) (root : Digest)
    (c : SnapshotClaim) : Prop :=
  LeafVerifies L k c.leaf c.index cells.length root c.path

/-- **A valid snapshot proof.** The binding tier fixes the trusted head to the
    genuine root over `cells` (`root = karyRoot L k cells`, the promoted-head
    case the seal commits), and the base tier requires every claim's leaf proof
    to verify against that head. `flat` records the flat-live-tree shape
    (`d = 0`) under which the base case pins the leaf exactly, exactly as in
    `leaf_proof_flat_sound`. -/
structure SnapshotValid (L k : Nat) (cells : List Digest)
    (root : Digest) (claims : List SnapshotClaim) : Prop where
  /-- Binding tier: the trusted head is the genuine root over the cells. -/
  headBinds : root = karyRoot L k cells
  /-- Base tier: every claimed leaf proof verifies against that head. -/
  claimsVerify : ∀ c ∈ claims, ClaimVerifies L k cells root c
  /-- The flat-live-tree shape for each claim's position: the honest proof
      carries no within-cell prefix, so an accepting proof pins the leaf. -/
  flatShape : ∀ c ∈ claims, ∀ skel,
    inclusionSkeleton k cells.length c.index = some skel →
    skel.length = c.path.length

/-- **Snapshot-proof soundness — every claimed leaf is the committed cell.**

    If a snapshot proof over `cells` is valid, then for **every** claimed leaf
    `(leaf, index, path)` either `leaf` equals the committed level-0 cell at
    `index` (`cells.getD index emptyHash`) or one of the standing hash
    assumptions broke. The proof composes the base case `leaf_proof_flat_sound`
    (N13) over each claim — the aggregate adds no machinery beyond the base case,
    so it inherits its trust base exactly.

    This is the soundness the API's spec tests witness: a valid snapshot
    verifies *and* the leaves it commits to are the genuine ones; a forged leaf
    cannot appear in a valid proof (corollary below). -/
theorem snapshot_proof_sound (L k : Nat) (cells : List Digest)
    (root : Digest) (claims : List SnapshotClaim)
    (hvalid : SnapshotValid L k cells root claims)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) :
    ∀ c ∈ claims,
      c.leaf = cells.getD c.index emptyHash ∨ NodeHashCollision ∨ CollapseAmbiguity L := by
  intro c hc
  exact leaf_proof_flat_sound L k cells c.leaf root c.index c.path
    (hvalid.claimsVerify c hc) hvalid.headBinds (hvalid.flatShape c hc) hH hN

/-- **Forged-leaf rejection (aggregate).** The contrapositive of
    `snapshot_proof_sound` at a single claim: under the standing hash
    assumptions, a claim whose `leaf` differs from the genuine committed cell at
    its `index` cannot have a verifying base-case proof inside a valid snapshot
    proof. This is the aggregate forgery-rejection the API's `forged_leaf_*`
    spec test witnesses operationally. -/
theorem snapshot_proof_forged_leaf_rejected (L k : Nat) (cells : List Digest)
    (root : Digest) (c : SnapshotClaim)
    (hroot : root = karyRoot L k cells)
    (hflat : ∀ skel, inclusionSkeleton k cells.length c.index = some skel →
      skel.length = c.path.length)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L)
    (hforged : c.leaf ≠ cells.getD c.index emptyHash) :
    ¬ ClaimVerifies L k cells root c := by
  exact leaf_proof_forged_rejected L k cells c.leaf root c.index c.path
    hroot hflat hH hN hforged

/-- **Snapshot-proof non-vacuity — a genuine snapshot proof is valid.** The
    honest aggregate: take, for each requested position, the genuine cell with
    its honest inclusion path; the resulting claims form a `SnapshotValid` proof
    against the genuine root. This witnesses that the accept set is inhabited
    (the acceptance spec test is not vacuous) and that the base-case
    completeness (`leaf_proof_complete`, N13) composes upward.

    Each requested `index` must be in range (`< cells.length`); the honest claim
    for it is `⟨cells.getD index emptyHash, index, honestInclusionPath …⟩`. -/
theorem snapshot_proof_complete (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (indices : List Nat) (hidx : ∀ i ∈ indices, i < cells.length)
    (hflat : ∀ i ∈ indices, ∀ skel,
      inclusionSkeleton k cells.length i = some skel →
      skel.length = (honestInclusionPath L k cells i).length) :
    SnapshotValid L k cells (karyRoot L k cells)
      (indices.map (fun i =>
        ⟨cells.getD i emptyHash, i, honestInclusionPath L k cells i⟩)) where
  headBinds := rfl
  claimsVerify := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    -- The honest claim at `i` is exactly `leaf_proof_complete`.
    exact leaf_proof_complete L k hk cells i (hidx i hi)
  flatShape := by
    intro c hc skel hskel
    simp only [List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact hflat i hi skel hskel

end NEML
