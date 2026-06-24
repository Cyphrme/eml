import EMLProof.LeafProof
import EMLProof.BindingProof

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
   `karyRoot k cells` the leaf proofs verify against.
2. **Base tier (leaf proofs).** Every claimed leaf's base-case `LeafVerifies`
   (`LeafProof.lean`) must hold against that member root.

A snapshot proof is **valid** when the head equals the genuine root *and* every
claimed leaf verifies against it. Soundness is then exactly the statement the
acceptance/soundness spec tests witness operationally: a valid snapshot proof's
claimed leaves are the committed cells — equivalently, a forged leaf cannot
appear in a valid snapshot proof unless a hash assumption breaks.

## What "valid" means

A snapshot proof over arity `k` and committed cells `cells` carries a
list of `claims`, each a `(leaf, index, path)` triple whose verify relation is
`LeafVerifies k leaf index cells.length root path` against the head `root`. The
proof is `SnapshotValid` when `root = karyRoot k cells` (the binding tier on the
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
def ClaimVerifies (k : Nat) (cells : List Digest) (root : Digest)
    (c : SnapshotClaim) : Prop :=
  LeafVerifies k c.leaf c.index cells.length root c.path

/-- **A valid snapshot proof.** The binding tier fixes the trusted head to the
    genuine root over `cells` (`root = karyRoot k cells`, the promoted-head
    case the seal commits), and the base tier requires every claim's leaf proof
    to verify against that head. `flat` records the flat-live-tree shape
    (`d = 0`) under which the base case pins the leaf exactly, exactly as in
    `leaf_proof_flat_sound`. -/
structure SnapshotValid (k : Nat) (cells : List Digest)
    (root : Digest) (claims : List SnapshotClaim) : Prop where
  /-- Binding tier: the trusted head is the genuine root over the cells. -/
  headBinds : root = karyRoot k cells
  /-- Base tier: every claimed leaf proof verifies against that head. -/
  claimsVerify : ∀ c ∈ claims, ClaimVerifies k cells root c
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
theorem snapshot_proof_sound (k : Nat) (cells : List Digest)
    (root : Digest) (claims : List SnapshotClaim)
    (hvalid : SnapshotValid k cells root claims)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    ∀ c ∈ claims,
      c.leaf = cells.getD c.index emptyHash ∨ NodeHashCollision ∨ CollapseAmbiguity := by
  intro c hc
  exact leaf_proof_flat_sound k cells c.leaf root c.index c.path
    (hvalid.claimsVerify c hc) hvalid.headBinds (hvalid.flatShape c hc) hH hN

/-- **A valid snapshot proof over a general (non-flat) live tree.** Identical to
    [`SnapshotValid`] but **without** the `flatShape` field: the trusted head is
    still the genuine root over `cells`, and every claim's base-case leaf proof
    verifies against it, but the tree need not be flat — a claimed leaf may sit
    *below* its level-0 cell, reached by some within-cell prefix. This is the
    general live-tree shape; `SnapshotValid` is its flat specialization
    (`flatShape` forcing within-cell depth `d = 0`). -/
structure SnapshotValidGeneral (k : Nat) (cells : List Digest)
    (root : Digest) (claims : List SnapshotClaim) : Prop where
  /-- Binding tier: the trusted head is the genuine root over the cells. -/
  headBinds : root = karyRoot k cells
  /-- Base tier: every claimed leaf proof verifies against that head. -/
  claimsVerify : ∀ c ∈ claims, ClaimVerifies k cells root c

/-- **Snapshot-proof soundness on a general live tree (depth-existential).**

    Drops the flat-tree restriction of `snapshot_proof_sound`. For a valid
    *general* snapshot proof, every claimed leaf `(leaf, index, path)` *hashes up
    to* the committed level-0 cell at `index` after some within-cell prefix of `d`
    steps — `foldNary leaf (path.take d) = cells.getD index emptyHash` — unless a
    standing hash assumption broke. The depth `d` is existential by design:
    implicit promotion makes a promoted digest equal its parent slot, so the proof
    binds the log *position*, never the within-cell depth (Cyphr SPEC §2.2.12). The
    proof composes the general base case `leaf_proof_sound` (N13) over each claim.

    This is the most a snapshot proof can bind on a general tree: the *equality*
    form `leaf = cells.getD index` (hence forged-leaf rejection by `leaf ≠ cell`)
    is recoverable only when the tree is flat (`d = 0`, the leaf *is* the cell) —
    that specialization is `snapshot_proof_sound` / `..._forged_leaf_rejected`,
    which carry the `flatShape` hypothesis exactly to pin `d = 0`. On a general
    tree a genuine leaf below its cell legitimately differs from the cell, so the
    equality form does not hold and is *not* a provable gap but a structural
    consequence of within-cell promotion. -/
theorem snapshot_proof_sound_general (k : Nat) (cells : List Digest)
    (root : Digest) (claims : List SnapshotClaim)
    (hvalid : SnapshotValidGeneral k cells root claims)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    ∀ c ∈ claims, ∃ d,
      foldNary c.leaf (c.path.take d) = cells.getD c.index emptyHash := by
  intro c hc
  obtain ⟨d, _skel, _hskel, _hsum, hfold⟩ :=
    leaf_proof_sound k cells c.leaf root c.index c.path
      (hvalid.claimsVerify c hc) hvalid.headBinds hH hN
  exact ⟨d, hfold⟩

/-- **Forged-leaf rejection (aggregate).** The contrapositive of
    `snapshot_proof_sound` at a single claim: under the standing hash
    assumptions, a claim whose `leaf` differs from the genuine committed cell at
    its `index` cannot have a verifying base-case proof inside a valid snapshot
    proof. This is the aggregate forgery-rejection the API's `forged_leaf_*`
    spec test witnesses operationally. -/
theorem snapshot_proof_forged_leaf_rejected (k : Nat) (cells : List Digest)
    (root : Digest) (c : SnapshotClaim)
    (hroot : root = karyRoot k cells)
    (hflat : ∀ skel, inclusionSkeleton k cells.length c.index = some skel →
      skel.length = c.path.length)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity)
    (hforged : c.leaf ≠ cells.getD c.index emptyHash) :
    ¬ ClaimVerifies k cells root c := by
  exact leaf_proof_forged_rejected k cells c.leaf root c.index c.path
    hroot hflat hH hN hforged

/-- **Snapshot-proof non-vacuity — a genuine snapshot proof is valid.** The
    honest aggregate: take, for each requested position, the genuine cell with
    its honest inclusion path; the resulting claims form a `SnapshotValid` proof
    against the genuine root. This witnesses that the accept set is inhabited
    (the acceptance spec test is not vacuous) and that the base-case
    completeness (`leaf_proof_complete`, N13) composes upward.

    Each requested `index` must be in range (`< cells.length`); the honest claim
    for it is `⟨cells.getD index emptyHash, index, honestInclusionPath …⟩`. -/
theorem snapshot_proof_complete (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (indices : List Nat) (hidx : ∀ i ∈ indices, i < cells.length)
    (hflat : ∀ i ∈ indices, ∀ skel,
      inclusionSkeleton k cells.length i = some skel →
      skel.length = (honestInclusionPath k cells i).length) :
    SnapshotValid k cells (karyRoot k cells)
      (indices.map (fun i =>
        ⟨cells.getD i emptyHash, i, honestInclusionPath k cells i⟩)) where
  headBinds := rfl
  claimsVerify := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    -- The honest claim at `i` is exactly `leaf_proof_complete`.
    exact leaf_proof_complete k hk cells i (hidx i hi)
  flatShape := by
    intro c hc skel hskel
    simp only [List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact hflat i hi skel hskel

/-! ## End-to-end multi-algorithm snapshot soundness

`snapshot_proof_sound` proves the **single-member promoted-head** case: the
trusted head *is* the genuine member root `karyRoot k cells` (genesis
promotion, `BR = MR`). A genuine multi-algorithm snapshot's trusted head is
instead the algorithm's **binding root** `BRᵢ = combinedRootWith Hᵢ ar tl`
(`BindingProof`), which over ≥ 2 members is a node hash, not the bare member
root. The two soundness tiers the Rust `SnapshotProof::verify` chains are:

1. **Binding tier** — the presented member-root tuple folds, under `Hᵢ` over the
   **raw** member-root bytes, to the trusted `BRᵢ`, recovering the committed
   member-root byte list (`BindingProof.binding_root_sound`, modulo an `Hᵢ`
   byte-hash collision, under the fixed-width contract).
2. **Base tier** — every claimed leaf proof verifies against *that algorithm's
   member root* `MRᵢ` (here `karyRoot k cells`), pinning the leaves to the
   committed cells (`snapshot_proof_sound`, modulo `NodeHashCollision` /
   `CollapseAmbiguity`).

The theorem below composes both into one end-to-end guarantee over a single
snapshot, closing the gap that the multi-alg binding tier was proven only *in
isolation*. The **bridge** between the tiers is the hypothesis `hbridge`: the
member root the binding tier authenticates for the snapshot's algorithm is the
*bytes of* `MRᵢ = karyRoot k cells` (`digestToBytes`) — exactly the head the
base-tier leaf proofs verify against. With that link the two independently-proven
tiers conjoin: an accepting multi-alg snapshot proof binds **both** the
cross-algorithm member-root agreement **and** the per-leaf cell membership, with
the bound member root being the very `MRᵢ` the leaves verify against. -/

/-- **End-to-end multi-algorithm snapshot soundness.** For a snapshot whose
    trusted head is algorithm `alg`'s **binding root** over a presented ≥ 2-member
    structure `(ar', tl')` (`haccept`), with `alg` genuinely committing `(ar_i,
    tl_i)` of the same length (`hcommit`, `hlen`); whose committed structure
    carries `MRᵢ = karyRoot k cells` as one member root via the head/base bridge
    `hbridge : alg's committed entry e_i ∈ ar_i` with `e_i.2 = digestToBytes
    (karyRoot k cells)`; and whose base-tier leaf proofs form a valid (flat)
    snapshot against that `MRᵢ` (`hbase`):

    * **(binding tier)** the presented member-root byte list equals the
      committed one (under `alg`'s fixed-width contract, `hw'`/`hw_i`), so in
      particular the presented structure carries the *raw* member root `MRᵢ` —
      `digestToBytes (karyRoot k cells) ∈ ar'.map (memberDigestWith alg.hash)`,
      `memberDigestWith` being the raw member bytes (D9, no per-member re-hash) —
      the member root the leaves verify against is the one cross-bound; and
    * **(base tier)** every claimed leaf is the committed level-0 cell,

    unless `alg`'s own byte-hash collides, or a tree-level hash assumption
    (`NodeHashCollision` / `CollapseAmbiguity`) broke. No new machinery: the
    binding tier is `BindingProof.binding_root_sound`, the base tier is
    `snapshot_proof_sound`, conjoined over one snapshot via the `hbridge` link. -/
theorem snapshot_proof_multialg_sound {w : Nat} (k : Nat)
    (alg : BindingProof.Algorithm) (cells : List Digest)
    (ar_i ar' : List (NEML.AlgId × List UInt8)) (tl_i tl' : NEML.Timeline)
    (e_i : NEML.AlgId × List UInt8) (claims : List SnapshotClaim)
    (hmulti_i : ar_i.length ≥ 2) (hmulti' : ar'.length ≥ 2)
    (hlen : ar'.length = ar_i.length)
    (hw' : NEML.EqWidth w (NEML.combinedChildrenWith alg.hash ar' tl'))
    (hw_i : NEML.EqWidth w (NEML.combinedChildrenWith alg.hash ar_i tl_i))
    (hclen : (NEML.combinedChildrenWith alg.hash ar' tl').length
      = (NEML.combinedChildrenWith alg.hash ar_i tl_i).length)
    (hcommit : BindingProof.bindingRoot alg ar_i tl_i = alg.root)
    (haccept : BindingProof.Verifies alg ar' tl')
    (hbridge_mem : e_i ∈ ar_i) (hbridge : e_i.2 = digestToBytes (karyRoot k cells))
    (hbase : SnapshotValid k cells (karyRoot k cells) claims)
    (hHnode : ¬ NEML.NodeHashCollisionFor alg.hash)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    (digestToBytes (karyRoot k cells)
        ∈ ar'.map (NEML.memberDigestWith alg.hash))
      ∧ (∀ c ∈ claims,
          c.leaf = cells.getD c.index emptyHash ∨ NodeHashCollision ∨ CollapseAmbiguity) := by
  refine ⟨?_, ?_⟩
  · -- Binding tier: the presented and committed member-byte lists agree
    -- (discharging the `Hᵢ`-collision disjunct with `hHnode`); `MRᵢ`'s committed
    -- raw member root is therefore present among the presented ones.
    have hagree : ar'.map (NEML.memberDigestWith alg.hash)
        = ar_i.map (NEML.memberDigestWith alg.hash) := by
      rcases BindingProof.binding_root_sound alg ar_i ar' tl_i tl'
          hmulti_i hmulti' hlen hw' hw_i hclen hcommit haccept with hagree | hcol
      · exact hagree
      · exact absurd hcol hHnode
    -- `MRᵢ`'s raw root is committed (via `e_i`), hence — by agreement — presented.
    have hmem_i : NEML.memberDigestWith alg.hash e_i ∈ ar_i.map (NEML.memberDigestWith alg.hash) :=
      List.mem_map.mpr ⟨e_i, hbridge_mem, rfl⟩
    have hbridge_dig : NEML.memberDigestWith alg.hash e_i
        = digestToBytes (karyRoot k cells) := by
      simp only [NEML.memberDigestWith, hbridge]
    rw [hagree]
    rw [hbridge_dig] at hmem_i
    exact hmem_i
  · -- Base tier: the leaf proofs against `MRᵢ = karyRoot k cells`.
    exact snapshot_proof_sound k cells (karyRoot k cells) claims hbase hH hN

end NEML
