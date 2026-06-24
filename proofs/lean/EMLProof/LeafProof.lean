import EMLProof.Kary

/-!
# Leaf-proof soundness (PMT, over `Foundations`)

The **leaf proof** is the peer of the inclusion proof: a self-contained
"is this a legitimate leaf?" witness over a live tree. In the shipped Rust
(`pmt/src/leaf_proof.rs`) `LeafProof::verify` *is* `verify_inclusion` — the
proof bundles the leaf hash with its trusted positional parameters
`(index, tree_size, log_arity)` and the path, and verification reconstructs the
spine topology exactly as inclusion does. So its verify relation is modeled here
as the very `AcceptsKary` relation that models `verify_inclusion`
(`Kary.lean`), and its soundness is the leaf-proof *specialization* of the k-ary
inclusion soundness already discharged over `Foundations`.

This module adds **no new axiom**: it builds entirely over `Kary.lean`'s
machinery (`AcceptsKary`, `karyRoot`, `honestInclusionPath`, `naryMr`,
`foldNary`), which sources its trust base from `Foundations`' four structural
axioms. `#print axioms` on the theorems below therefore reports a subset of
`{Digest, Digest.nonempty, H, digestToBytes}` plus the Lean built-ins.

## What "legitimate" and "forged" mean

A live tree is modeled by its level-0 cell digests `cells`; the genuine leaf at
log position `index` is `cells.getD index emptyHash`, and the genuine root is
`karyRoot k cells`. A **leaf proof for `leaf` at `index`** is a `LeafProof`
whose verify relation is `AcceptsKary k leaf index cells.length root path`.

* **Legitimate ⇒ accepted** (`leaf_proof_complete`): the genuine cell's honest
  proof verifies against the genuine root — the base-case completeness the
  snapshot proof (N14) composes.
* **Accepted ⇒ legitimate** (`leaf_proof_sound`): an accepting proof binds the
  leaf to the committed cell at `index` (existential in within-cell depth, as
  inclusion is — Cyphr SPEC §2.2.12). For a **flat** live tree, where the leaf
  *is* the level-0 cell, this collapses to depth `0`: the verified `leaf`
  equals the committed cell exactly (`leaf_proof_flat_sound`).
* **Forged ⇒ rejected** (`leaf_proof_forged_rejected`): the contrapositive on a
  flat tree — a `leaf` that differs from the genuine committed cell cannot
  produce an accepting proof unless a hash assumption breaks. This is the
  forgery-rejection half the API's spec tests exercise.
-/

namespace NEML

/-- The leaf-proof verify relation: identical to the inclusion accept relation,
    because `LeafProof::verify` delegates to `verify_inclusion`. `leaf` is the
    proven leaf hash, `(index, treeSize, k)` the trusted positional parameters,
    `root` the authenticated root, `path` the inclusion path. -/
def LeafVerifies (k : Nat) (leaf : Digest) (index treeSize : Nat)
    (root : Digest) (path : List ProofStep) : Prop :=
  AcceptsKary k leaf index treeSize root path

/-- **Leaf-proof completeness — a legitimate leaf verifies.** The genuine cell
    at log position `index`, with the honest inclusion path over `cells`,
    verifies against the genuine root `karyRoot k cells`. This is the base
    case the snapshot proof composes; it is also the non-vacuity witness for
    `LeafVerifies` (the accept set is provably inhabited). -/
theorem leaf_proof_complete (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    LeafVerifies k (cells.getD index emptyHash) index cells.length
      (karyRoot k cells) (honestInclusionPath k cells index) :=
  kary_completeness k hk cells index hidx

/-- **Leaf-proof soundness (existential in depth) — accept binds the committed
    cell.** If a leaf proof for `leaf` at `index` verifies against the genuine
    root over `cells`, then after some prefix of `d` within-cell steps `leaf`
    hashes to *the committed level-0 cell at position `index`* — unless a hash
    assumption breaks. Depth is existential by design (implicit promotion makes
    it unbindable); the forged-leaf rejection on flat trees follows below where
    `d = 0`. -/
theorem leaf_proof_sound (k : Nat) (cells : List Digest)
    (leaf root : Digest) (index : Nat) (path : List ProofStep)
    (hver : LeafVerifies k leaf index cells.length root path)
    (hroot : root = karyRoot k cells)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    ∃ (d : Nat) (skel : List (Nat × Nat)),
      inclusionSkeleton k cells.length index = some skel ∧
      d + skel.length = path.length ∧
      foldNary leaf (path.take d) = cells.getD index emptyHash :=
  kary_inclusion_soundness k cells leaf root index path hver hroot hH hN

/-- **Leaf-proof soundness on a flat live tree — accept forces leaf equality.**
    On a flat tree the leaf *is* the level-0 cell, so the honest proof carries no
    within-cell prefix (`d = 0`) and an accepting proof of that same shape pins
    the verified `leaf` to the committed cell exactly. Concretely: if `leaf`'s
    proof accepts *and* the honest proof for `index` has full skeleton length
    (the flat-tree shape, `d = 0`), then `leaf = cells.getD index emptyHash` or a
    hash assumption broke. -/
theorem leaf_proof_flat_sound (k : Nat) (cells : List Digest)
    (leaf root : Digest) (index : Nat) (path : List ProofStep)
    (hver : LeafVerifies k leaf index cells.length root path)
    (hroot : root = karyRoot k cells)
    (hflat : ∀ skel, inclusionSkeleton k cells.length index = some skel →
      skel.length = path.length)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    leaf = cells.getD index emptyHash ∨ NodeHashCollision ∨ CollapseAmbiguity := by
  obtain ⟨d, skel, hskel, hsum, hfold⟩ :=
    leaf_proof_sound k cells leaf root index path hver hroot hH hN
  -- The flat-tree shape forces `d = 0`: the skeleton already spans the path.
  have hflatlen := hflat skel hskel
  have hd0 : d = 0 := by omega
  -- With no prefix, `foldNary leaf [] = leaf`, which the binding equates to the
  -- committed cell.
  rw [hd0, List.take_zero, foldNary] at hfold
  simp only [List.foldl_nil] at hfold
  exact Or.inl hfold

/-- **Forged-leaf rejection (flat live tree).** The contrapositive of
    `leaf_proof_flat_sound`: under the standing hash assumptions, a `leaf` that
    differs from the genuine committed cell at `index` cannot produce an
    accepting leaf proof against the genuine root. This is the soundness half the
    API's `forged_leaf_is_rejected` / `proof_does_not_transfer_across_positions`
    spec tests witness operationally. -/
theorem leaf_proof_forged_rejected (k : Nat) (cells : List Digest)
    (leaf root : Digest) (index : Nat) (path : List ProofStep)
    (hroot : root = karyRoot k cells)
    (hflat : ∀ skel, inclusionSkeleton k cells.length index = some skel →
      skel.length = path.length)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity)
    (hforged : leaf ≠ cells.getD index emptyHash) :
    ¬ LeafVerifies k leaf index cells.length root path := by
  intro hver
  rcases leaf_proof_flat_sound k cells leaf root index path hver hroot hflat hH hN with
    heq | hcol
  · exact hforged heq
  · rcases hcol with hc | hc
    · exact hH hc
    · exact hN hc

end NEML
