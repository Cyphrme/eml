import EMLProof.Spine
import EMLProof.Kary

/-!
# Mountain inclusion — instantiating the abstract spine inclusion layer

`EMLProof.Spine` proves the canonical inclusion theorems (`inclusion_soundness`,
`inclusion_proof_unique`) over an **abstract** skeleton predicate
`SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop` — topology-agnostic, so
they hold for whatever pinning a consumer's concrete topology enforces. This
module discharges the durability phase's reuse obligation: the append-only log's
**MMR mountain topology** is one such consumer, and the spine layer applies to it
**verbatim** — we instantiate `SkeletonValid`, we do not re-specify a spine
topology.

The concrete skeleton is `EMLProof.Kary`'s `inclusionSkeleton` — the single
topology authority shared by generator and verifier, a faithful transcription of
`spine/src/topology.rs` whose mountain form (`peakPath ++ bagPath`) is owned by
`cml/src/mountain.rs::mountain_skeleton`. The mountain `SkeletonValid` says only
that the trailing steps of a proof match that skeleton shape-for-shape; it pins
no digests, exactly as the spine's abstract predicate intends.

Instantiating an already-proven parametric theorem adds nothing to the trust
base: `#print axioms` on the corollaries below is the same subset of the four
`Foundations` axioms plus the Lean built-ins that the spine theorems carry.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace NEML

/-- **The cml mountain skeleton-validity predicate.** A proof's `path` is
    skeleton-valid for log position `index` in a size-`treeSize` arity-`k` tree
    iff the concrete mountain `inclusionSkeleton` exists and the path's per-step
    shape matches it. This is the consumer-supplied instance of the spine's
    abstract `SkeletonValid` — the mountain topology (`peakPath ++ bagPath`),
    never a new spine spec. -/
def MountainSkeletonValid (k index treeSize : Nat) (path : List ProofStep) : Prop :=
  ∃ skel, inclusionSkeleton k treeSize index = some skel ∧ path.map stepShape = skel

/-- **The mountain instance of the spine accept relation.** Spine's generic
    `Accepts` specialized to `MountainSkeletonValid`. -/
def MountainAccepts (k index treeSize : Nat) (leaf root : Digest) (path : List ProofStep) : Prop :=
  Accepts MountainSkeletonValid k index treeSize leaf root path

/-- **Mountain inclusion soundness — by instantiation.** The spine's abstract
    `inclusion_soundness`, with `SkeletonValid := MountainSkeletonValid`. An
    accepting canonical proof exhibits a within-mountain subtree root `R` at
    depth `d` (the peak the leaf hashes up to), with the trailing steps pinned by
    the mountain skeleton and folding `R` to the root. The spine theorem is
    reused verbatim — this is the cml topology slotting into it. -/
theorem mountain_inclusion_soundness
    (k index treeSize : Nat) (leaf root : Digest) (path : List ProofStep)
    (h : MountainAccepts k index treeSize leaf root path) :
    ∃ (R : Digest) (d : Nat), d ≤ path.length ∧
      foldCanonical leaf (path.take d) = R ∧
      MountainSkeletonValid k index treeSize (path.drop d) ∧
      foldCanonical R (path.drop d) = root :=
  inclusion_soundness MountainSkeletonValid k index treeSize leaf root path h

/-- **Mountain inclusion proof-encoding uniqueness — by instantiation.** The
    spine's abstract `inclusion_proof_unique`, with
    `SkeletonValid := MountainSkeletonValid`. With zero-sibling steps rejected and
    the mountain skeleton pinning length and per-step position, a fixed
    `(leaf, index, treeSize, root)` admits at most one accepting canonical path —
    modulo a `nodeHash` collision. Reused verbatim from the spine layer. -/
theorem mountain_inclusion_proof_unique
    (k index treeSize : Nat) (leaf root : Digest) (p₁ p₂ : List ProofStep)
    (h₁ : MountainAccepts k index treeSize leaf root p₁)
    (h₂ : MountainAccepts k index treeSize leaf root p₂)
    (hlen : p₁.length = p₂.length)
    (hpos : ∀ i : Nat, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position) :
    p₁ = p₂ ∨ NodeHashCollision :=
  inclusion_proof_unique MountainSkeletonValid k index treeSize leaf root p₁ p₂ h₁ h₂ hlen hpos

/-! ## Bag canonical-uniqueness — the "no size prefix" discharge

The peak bag is the **unprefixed** `nary_mr` fold over the frontier peaks
(`cml/src/mountain.rs::bag_peaks` over `bag_shape`), modelled by `karyRoot` (the
`foldFrontierRoot` over the per-peak `perfectRoot`s). Unlike OpenTimestamps/Grin's
`H(size ‖ peak ‖ acc)`, it carries **no size prefix**: `tree_size` is a trusted
verifier parameter, and the anti-confusion guarantee the prefix would provide is
discharged instead by *proven* injectivity of the fold over equal-length peak
sets — `karyRoot_inj_of_length`. The equal-length pinning is essential and
sufficient: all-null sets of differing length share a root (the
flat-null-promotion design), so injectivity holds exactly once `tree_size` is
pinned, which the trusted parameter does. -/

/-- **Bag canonical-uniqueness.** The unprefixed peak-bag fold is injective over
    equal-length cell sets: distinct size-pinned trees have distinct member
    roots (modulo a hash collision). This formally discharges the MMR "no size
    prefix" decision — re-exposed at the mountain layer from the structural
    `karyRoot_inj_of_length`. -/
theorem bag_canonical_unique (k : Nat) (hk : 2 ≤ k) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : karyRoot k xs = karyRoot k ys)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    xs = ys :=
  karyRoot_inj_of_length k hk xs ys hlen heq hH hN

end NEML

/-!
## Trust base (axiom inventory)

No new axiom. `mountain_inclusion_soundness` and `mountain_inclusion_proof_unique`
are the spine's `inclusion_soundness` / `inclusion_proof_unique` applied at
`SkeletonValid := MountainSkeletonValid`; their `#print axioms` is the same subset
of `{Digest, Digest.nonempty, H, digestToBytes}` ∪ `{propext, Classical.choice,
Quot.sound}` the spine theorems carry. The cml mountain topology reuses the
abstract inclusion layer rather than extending the trust base.
-/
