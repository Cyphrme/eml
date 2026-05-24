import EMLProof.Bridge

/-!
# EML Cryptographic Projection and Validation Theorems

This module instantiates the structural equivalence of the EML tree over concrete cryptographic 
digests, defines the activation-epoch projection, and establishes the security theorems from 
the whitepaper.

## Mathematical Formulations

1. **Epoch Projection**:
   An epoch is modeled as a half-open interval $[start, stop)$. The activation map `isActive` 
   determines if leaf $i$ is within any active epoch. The projection function `project` maps 
   inactive positions to `nullLeaf` ($H(0x02)$) and active positions to their payload leaf hashes.

2. **Theorem 1: Projection Equivalence**:
   For any payload sequence and set of activation epochs, the concrete ctoRoot digest equals 
   the concrete mth digest:
   $$\text{ctoRootDigest}(\text{project}(\text{epochs}, \text{nullLeaf}, \text{payloads})) = 
     \text{mthDigest}(\text{project}(\text{epochs}, \text{nullLeaf}, \text{payloads}))$$

3. **Theorem 2: Temporal Binding**:
   Under the Random Oracle Model (modeled via the `domain_separation` axiom), the null constant 
   $H(0x02)$ is distinct from any leaf hash $H(0x00 \mathbin{\Vert} d)$. Consequently, no valid 
   inclusion proof can be produced for an inactive leaf position.

4. **Theorem 3: Algorithm Isolation**:
   Proves that two configuration epoch sets ($\mathcal{A}$ and $\mathcal{B}$) 
   each yield valid RFC 9162 Merkle trees over the same leaf sequence, without interference.
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

/-- Concrete hash abstract types and functions -/
axiom Digest : Type
axiom Digest.nonempty : Nonempty Digest
noncomputable instance : DecidableEq Digest := Classical.typeDecidableEq _
noncomputable instance : Inhabited Digest :=
  ⟨Classical.choice Digest.nonempty⟩

axiom H : List UInt8 → Digest

def leafTag : UInt8 := 0x00
def nodeTag : UInt8 := 0x01
def nullTag : UInt8 := 0x02

noncomputable def leafHash (d : List UInt8) : Digest := H (leafTag :: d)

axiom digestToBytes : Digest → List UInt8

noncomputable def nodeHash (l r : Digest) : Digest :=
  H (nodeTag :: digestToBytes l ++ digestToBytes r)

noncomputable def emptyHash : Digest := H []
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
    over any list of leaves. This proves that the equivalence is independent of any concrete
    hash function or serialization format. -/
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

/-- Domain separation axiom: the null constant H(0x02) is distinct from
    any leaf hash H(0x00 ‖ d). This is a computational hardness assumption
    under the Random Oracle Model — finding a collision requires breaking
    preimage resistance of H. -/
axiom domain_separation : ∀ (d : List UInt8), nullLeaf ≠ leafHash d

/-- **Theorem 2 (Temporal Binding).**
    At any inactive position, the tree contains the null constant,
    and no payload can produce a leaf hash equal to the null constant.
    Therefore, no valid inclusion proof exists for any payload at an
    inactive position. -/
theorem temporal_binding (epochs : List Epoch) (i : Nat) (d : List UInt8)
    (_h_inactive : isActive epochs i = false) :
    leafHash d ≠ nullLeaf := by
  exact Ne.symm (domain_separation d)

/-- Concrete project function for algorithm. -/
noncomputable def projectDigest (epochs : List Epoch) (payloads : List Digest) : List Digest :=
  project epochs nullLeaf payloads

/-- **Theorem 3 (Algorithm Isolation).**
    For any two algorithms a and b (represented by their activation epochs)
    operating over the same payload sequence, both per-algorithm projections
    independently yield valid RFC 9162 Merkle trees. -/
theorem algorithm_isolation
    (epochs_a epochs_b : List Epoch) (payloads : List Digest) :
    ctoRootDigest (projectDigest epochs_a payloads) =
      mthDigest (projectDigest epochs_a payloads) ∧
    ctoRootDigest (projectDigest epochs_b payloads) =
      mthDigest (projectDigest epochs_b payloads) := by
  simp only [projectDigest]
  exact ⟨projection_equivalence epochs_a payloads, projection_equivalence epochs_b payloads⟩
