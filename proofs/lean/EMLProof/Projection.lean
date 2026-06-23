import EMLProof.Bridge
import EMLProof.Foundations

/-!
# EML Cryptographic Projection and Validation Theorems

This module instantiates the structural equivalence of the EML tree over concrete cryptographic 
digests, defines the activation-epoch projection, and establishes the security theorems from 
the whitepaper.

## Mathematical Formulations

1. **Epoch Projection**:
   An epoch is modeled as a half-open interval $[start, stop)$. The activation map `isActive`
   determines if leaf $i$ is within any active epoch. The projection function `project` maps
   inactive positions to `nullLeaf` and active positions to their payload leaf hashes.

2. **Theorem 1: Projection Equivalence**:
   For any payload sequence and set of activation epochs, the concrete ctoRoot digest equals
   the concrete mth digest:
   $$\text{ctoRootDigest}(\text{project}(\text{epochs}, \text{nullLeaf}, \text{payloads})) =
     \text{mthDigest}(\text{project}(\text{epochs}, \text{nullLeaf}, \text{payloads}))$$

   This is a genuine structural equivalence (it instantiates `bridge_lemma`).
   `generic_projection_equivalence` is its hash-agnostic version — `congrArg`
   applied to the underlying tree equality, holding for any evaluation function.

The previous "Temporal Binding" and "Algorithm Isolation" theorems were removed:
they were vacuous (an axiom echo, and two independent copies of Projection
Equivalence). Their intended security content — that inactivity is authenticated,
and that per-algorithm commitments do not interfere — is formalized properly in
`NEML.lean`'s committed-epoch (Design A+) layer, where activity is read from an
authenticated timeline bound into the combined-root metaroot.
-/

set_option linter.style.emptyLine false

/-- An activation epoch: a half-open interval [start, stop). -/
structure Epoch where
  start : Nat
  stop : Nat
  valid : start < stop

/-- Whether index i falls within any epoch in the activation map. -/
def isActive (epochs : List Epoch) (i : Nat) : Bool :=
  epochs.any (fun e => e.start ≤ i && i < e.stop)

/-- Auxiliary project helper that monotonically tracks the current leaf index. -/
def projectAux {α : Type} (epochs : List Epoch) (nullLeaf : α) (idx : Nat) : List α → List α
  | [] => []
  | hd :: tl =>
    let leaf_val := if isActive epochs idx then hd else nullLeaf
    leaf_val :: projectAux epochs nullLeaf (idx + 1) tl

/-- The projection function. -/
def project {α : Type} (epochs : List Epoch) (nullLeaf : α)
    (payloads : List α) : List α :=
  projectAux epochs nullLeaf 0 payloads

/- The four trust-base axioms (`Digest`, `Digest.nonempty`, `H`, `digestToBytes`),
   the digest instances, the domain-separation tags, and `emptyHash` now live in
   `EMLProof.Foundations`; this CT-build module consumes them from there. -/

/-- Tagged binary internal node hash (CT-lineage / binary construction). -/
noncomputable def nodeHash (l r : Digest) : Digest :=
  H (nodeTag :: digestToBytes l ++ digestToBytes r)

noncomputable def nullLeaf : Digest := H [nullTag]

/-- Maps a MerkleTree Digest to a single Digest. -/
noncomputable def eval : MerkleTree Digest → Digest
  | MerkleTree.empty => emptyHash
  | MerkleTree.leaf v => v
  | MerkleTree.node l r => nodeHash (eval l) (eval r)

/-- Concrete ctoRoot over Digest. -/
noncomputable def ctoRootDigest (leaves : List Digest) : Digest :=
  eval (ctoRoot (leaves.map MerkleTree.leaf))

/-- Concrete mth over Digest. -/
noncomputable def mthDigest (leaves : List Digest) : Digest :=
  eval (mth (leaves.map MerkleTree.leaf))

/-- Helper theorem showing that the tree height of leaf-mapped lists is zero. -/
theorem treeHeight_leaf_map {α : Type} (L : List α) :
    ∀ t ∈ L.map MerkleTree.leaf, treeHeight t = 0 := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨v, _, rfl⟩ := ht
  rfl

/-- **Generic Projection Equivalence.**
    For any type `β` representing a digest space and any evaluation function `eval_fn`
    (which maps a structural tree to `β`), the evaluated ctoRoot equals the evaluated mth
    over any list of leaves. The equivalence is independent of any concrete hash function
    or serialization format. Mechanically this is `congrArg eval_fn bridge_lemma` — the
    underlying trees are equal as data; no algebraic/homomorphism structure is involved. -/
theorem generic_projection_equivalence {α β : Type} (eval_fn : MerkleTree α → β)
    (leaves : List (MerkleTree α)) :
    eval_fn (ctoRoot leaves) = eval_fn (mth leaves) := by
  rw [bridge_lemma]

/-- **Theorem 1 (Projection Equivalence).**
    The concrete ctoRoot digest equals the concrete mth digest over any projected sequence. -/
theorem projection_equivalence (epochs : List Epoch) (payloads : List Digest) :
    ctoRootDigest (project epochs nullLeaf payloads) =
      mthDigest (project epochs nullLeaf payloads) := by
  simp only [ctoRootDigest, mthDigest]
  rw [bridge_lemma]

-- `temporal_binding` and `algorithm_isolation` were removed here. Both were
-- vacuous: `temporal_binding` ignored its inactivity hypothesis and merely
-- restated a domain-separation axiom (which itself secured only the tagged EML
-- construction and is information-theoretically false for a compressing hash),
-- and `algorithm_isolation` was two independent copies of `projection_equivalence`
-- with nothing modeling distinct algorithms or non-interference. The genuine
-- replacements live in `NEML.lean` (Design A+): inactivity is authenticated by
-- the committed epoch timeline bound into the combined-root metaroot, and the
-- metaroot binding is the real cross-algorithm non-interference statement.
-- Deleting `temporal_binding` left `domain_separation`, the tagged `leafHash`,
-- and `projectDigest` with no consumers, so they were removed too.
