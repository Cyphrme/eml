/-!
# Foundations — the minimal cryptographic trust base

This module is the **entire trusted computing base** of the authoritative
proof corpus: the four structural axioms that model an abstract collision-resistant
hash, the decidability/inhabitedness instances they license, and the few hash
constants every downstream layer shares.

It exists so the authoritative chain (`Spine → Kary → KaryConsistency`, plus the
polydigest theorems built over it in later nodes) depends on **these four axioms and
nothing else**. Lifting them here severs that chain from the CT-lineage
`Tree/Binary/Invariant/Bridge` proof material, which is retained only as
CT-build reference (see `Bridge.lean`'s header) and is no longer authoritative.

## The trust base

* `Digest` — an abstract digest type (the codomain of the hash).
* `Digest.nonempty` — digests exist (licenses `Inhabited`/`Classical` choice).
* `H` — the abstract hash, `List UInt8 → Digest`. Collision resistance is **not**
  an axiom: it is modeled wherever needed as a *hypothesis* `¬ HashCollision`
  (`Spine.lean`), so the trust base never assumes `H` injective.
* `digestToBytes` — the serialization a node hash folds its children through.

`#print axioms` on every downstream theorem must report a subset of
`{Digest, Digest.nonempty, H, digestToBytes}` together with the Lean built-ins
`{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no further axiom.

The API here is deliberately small and stable: net-new proof nodes (the leaf
proof, the snapshot proof, the binding-proof soundness theorem) build *over* this
module, so its surface must not churn.
-/

/-- Concrete hash abstract digest type. -/
axiom Digest : Type

/-- Digests exist. Licenses the `Inhabited` instance and `Classical` choice over
    `Digest` without assuming anything about `H`. -/
axiom Digest.nonempty : Nonempty Digest

noncomputable instance : DecidableEq Digest := Classical.typeDecidableEq _
noncomputable instance : Inhabited Digest :=
  ⟨Classical.choice Digest.nonempty⟩

/-- The abstract hash. Collision resistance is never assumed here; it is a
    discharged hypothesis at each use site. -/
axiom H : List UInt8 → Digest

/-- Domain-separation tags for the tagged construction. Retained as the canonical
    tag constants shared across layers. -/
def nodeTag : UInt8 := 0x01
def nullTag : UInt8 := 0x02

/-- The serialization a node hash folds its children through. -/
axiom digestToBytes : Digest → List UInt8

/-- The empty-node digest constant, `H []`. Shared by the k-ary tiling layer. -/
noncomputable def emptyHash : Digest := H []
