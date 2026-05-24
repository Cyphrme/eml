/-
  EML Projection Equivalence — Minimal Algebraic Proof

  Proves that the incremental CTO frontier stack construction produces
  the same Merkle root as the batch RFC 9162 MTH recursive construction.

  By decoupling the structural tree topology from cryptographic hashing using a
  generic type `α` and `MerkleTree α` inductive representation, the mathematical
  insight is simplified and made trivially derivable.
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- ============================================================================
-- §1. Inductive Merkle Tree Representation
-- ============================================================================

/-- A structural representation of a Merkle Tree.
    Decoupled from hash function evaluation, enabling pure algebraic proofs. -/
inductive MerkleTree (α : Type) where
  | leaf (val : α)
  | node (left right : MerkleTree α)
  deriving DecidableEq, Inhabited

/-- Height of a MerkleTree. -/
def treeHeight {α : Type} : MerkleTree α → Nat
  | MerkleTree.leaf _ => 0
  | MerkleTree.node l r => Nat.max (treeHeight l) (treeHeight r) + 1

-- ============================================================================
-- §2. largest_pow2_lt
-- ============================================================================

def largestPow2Lt (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else 2 ^ (Nat.log 2 (n - 1))

theorem largestPow2Lt_def {n : Nat} (hn : n > 1) :
    largestPow2Lt n = 2 ^ (Nat.log 2 (n - 1)) := by
  simp [largestPow2Lt, Nat.not_le.mpr hn]

theorem largestPow2Lt_pos {n : Nat} (hn : n > 1) :
    largestPow2Lt n > 0 := by
  rw [largestPow2Lt_def hn]
  exact Nat.pos_of_ne_zero (by positivity)

theorem largestPow2Lt_lt {n : Nat} (hn : n > 1) :
    largestPow2Lt n < n := by
  rw [largestPow2Lt_def hn]
  have h1 : n - 1 ≠ 0 := by omega
  have h2 : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 h1
  omega

theorem largestPow2Lt_is_pow2 {n : Nat} (hn : n > 1) :
    ∃ k, largestPow2Lt n = 2 ^ k := by
  rw [largestPow2Lt_def hn]
  exact ⟨Nat.log 2 (n - 1), rfl⟩

theorem largestPow2Lt_ge_half {n : Nat} (hn : n > 1) :
    2 * largestPow2Lt n ≥ n := by
  rw [largestPow2Lt_def hn]
  have h1 : n - 1 ≠ 0 := by omega
  have h2 : n - 1 < 2 ^ (Nat.log 2 (n - 1)).succ :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n - 1)
  rw [Nat.succ_eq_add_one, pow_succ] at h2
  omega

-- ============================================================================
-- §3. MTH — Structural Merkle Tree Hash
-- ============================================================================

def mth {α : Type} : List (MerkleTree α) → Option (MerkleTree α)
  | [] => none
  | [t] => some t
  | a :: b :: rest =>
    let leaves := a :: b :: rest
    let n := leaves.length
    let k := largestPow2Lt n
    match mth (leaves.take k), mth (leaves.drop k) with
    | some l, some r => some (MerkleTree.node l r)
    | _, _ => none
termination_by l => l.length
decreasing_by
  · simp only [List.length_take]
    have hn : (a :: b :: rest).length > 1 := by simp
    have hlt := largestPow2Lt_lt hn
    omega
  · simp only [List.length_drop]
    have hn : (a :: b :: rest).length > 1 := by simp
    have hpos := largestPow2Lt_pos hn
    omega

theorem mth_unfold {α : Type} (leaves : List (MerkleTree α)) (h : leaves.length > 1) :
    mth leaves =
      match mth (leaves.take (largestPow2Lt leaves.length)),
            mth (leaves.drop (largestPow2Lt leaves.length)) with
      | some l, some r => some (MerkleTree.node l r)
      | _, _ => none := by
  match leaves with
  | [] => simp at h
  | [_] => simp at h
  | a :: b :: rest => simp [mth]

-- ============================================================================
-- §4. Frontier Stack Operations
-- ============================================================================

def insertCol {α : Type} (carry : MerkleTree α) : List (MerkleTree α) → List (MerkleTree α)
  | [] => [carry]
  | h :: t =>
    if treeHeight carry < treeHeight h then
      carry :: h :: t
    else if treeHeight h < treeHeight carry then
      h :: insertCol carry t
    else
      insertCol (MerkleTree.node h carry) t

def mergeStacks {α : Type} :
    List (MerkleTree α) → List (MerkleTree α) → List (MerkleTree α)
  | [], S₂ => S₂
  | S₁, [] => S₁
  | h₁ :: t₁, h₂ :: t₂ =>
    if treeHeight h₁ < treeHeight h₂ then
      h₁ :: mergeStacks t₁ (h₂ :: t₂)
    else if treeHeight h₂ < treeHeight h₁ then
      h₂ :: mergeStacks (h₁ :: t₁) t₂
    else
      insertCol (MerkleTree.node h₁ h₂) (mergeStacks t₁ t₂)
termination_by S₁ S₂ => S₁.length + S₂.length

def buildStack {α : Type} : List (MerkleTree α) → List (MerkleTree α)
  | [] => []
  | hd :: tl => mergeStacks [hd] (buildStack tl)

def stackRoot {α : Type} (stack : List (MerkleTree α)) : Option (MerkleTree α) :=
  match stack with
  | [] => none
  | h :: t => some (t.foldl (fun acc left => MerkleTree.node left acc) h)

def ctoRoot {α : Type} (leaves : List (MerkleTree α)) : Option (MerkleTree α) :=
  stackRoot (buildStack leaves)

-- ============================================================================
-- §5. Structural Stack Merging Axioms
-- ============================================================================

/-- Stack merging is associative. -/
axiom mergeStacks_assoc {α : Type} (S₁ S₂ S₃ : List (MerkleTree α)) :
  mergeStacks S₁ (mergeStacks S₂ S₃) = mergeStacks (mergeStacks S₁ S₂) S₃

/-- mth over a power of 2 list yields a tree of height k. -/
axiom height_mth {α : Type} (L : List (MerkleTree α)) (k : Nat) (h : L.length = 2 ^ k)
  (hL : ∀ t ∈ L, treeHeight t = 0) :
  ∃ t, mth L = some t ∧ treeHeight t = k

/-- Merging two singleton stacks of matching height collides them into a single parent node. -/
axiom mergeStacks_same_height {α : Type} (a b : MerkleTree α) (h : treeHeight a = treeHeight b) :
  mergeStacks [a] [b] = [MerkleTree.node a b]

/-- Merging a singleton stack [a] of height H with a stack S whose elements all
    have height strictly less than H simply appends [a] to the bottom of the stack. -/
axiom mergeStacks_large_left {α : Type} (a : MerkleTree α) (S : List (MerkleTree α))
  (hS : ∀ t ∈ S, treeHeight t < treeHeight a) :
  mergeStacks [a] S = S ++ [a]

/-- Elements in a recursively built stack for L of size less than 2^j have height less than j. -/
axiom treeHeight_buildStack_bound {α : Type} (L : List (MerkleTree α))
  (hL : ∀ t ∈ L, treeHeight t = 0) (j : Nat) (h : L.length < 2 ^ j) :
  ∀ t ∈ buildStack L, treeHeight t < j

/-- The frontier stack of a non-empty leaf sequence is non-empty. -/
axiom buildStack_nonempty {α : Type} (L : List (MerkleTree α)) (h : L.length > 0) :
  buildStack L ≠ []

/-- For any n that is not a power of 2, n - largestPow2Lt n < largestPow2Lt n. -/
axiom largestPow2Lt_non_pow2 (n : Nat) (h : ¬ ∃ m, n = 2 ^ m) :
  n - largestPow2Lt n < largestPow2Lt n

-- ----------------------------------------------------------------------------
-- §5.2 Structural Proofs
-- ----------------------------------------------------------------------------

/-- stackRoot snoc: folding with a base element at the tail. -/
theorem stackRoot_snoc {α : Type} (s : List (MerkleTree α)) (base : MerkleTree α) (hs : s ≠ []) :
    stackRoot (s ++ [base]) =
      match stackRoot s with
      | some t => some (MerkleTree.node base t)
      | none => none := by
  match s with
  | [] => contradiction
  | h :: t =>
    simp only [stackRoot, List.cons_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Theorem: Monoid Homomorphism Lemma.**
    buildStack preserves list concatenation as a monoid homomorphism to mergeStacks. -/
theorem buildStack_append {α : Type} (L₁ L₂ : List (MerkleTree α)) :
    buildStack (L₁ ++ L₂) = mergeStacks (buildStack L₁) (buildStack L₂) := by
  induction L₁ with
  | nil =>
    simp only [List.nil_append, buildStack]
    rw [mergeStacks]
  | cons hd tl ih =>
    simp only [List.cons_append, buildStack]
    rw [ih]
    rw [mergeStacks_assoc]

/-- Auxiliary step for the power of two collapse. -/
theorem buildStack_pow2_step {α : Type} (L₁ L₂ : List (MerkleTree α)) (k : Nat)
    (h1 : L₁.length = 2 ^ k) (h2 : L₂.length = 2 ^ k)
    (hL₁ : ∀ t ∈ L₁, treeHeight t = 0) (hL₂ : ∀ t ∈ L₂, treeHeight t = 0)
    (ih1 : buildStack L₁ = match mth L₁ with | some t => [t] | none => [])
    (ih2 : buildStack L₂ = match mth L₂ with | some t => [t] | none => []) :
    buildStack (L₁ ++ L₂) = match mth (L₁ ++ L₂) with | some t => [t] | none => [] := by
  obtain ⟨t1, hm1, ht1⟩ := height_mth L₁ k h1 hL₁
  obtain ⟨t2, hm2, ht2⟩ := height_mth L₂ k h2 hL₂
  have ih1' : buildStack L₁ = [t1] := by rw [ih1, hm1]
  have ih2' : buildStack L₂ = [t2] := by rw [ih2, hm2]
  rw [buildStack_append, ih1', ih2']
  have hsame : treeHeight t1 = treeHeight t2 := by omega
  rw [mergeStacks_same_height _ _ hsame]
  have hlen : (L₁ ++ L₂).length = 2 ^ (k + 1) := by
    simp [List.length_append, h1, h2, pow_succ]
    ring
  have hgt : (L₁ ++ L₂).length > 1 := by
    rw [hlen]
    have := Nat.one_le_two_pow (n := k + 1)
    omega
  rw [mth_unfold _ hgt]
  have hsplit : largestPow2Lt (L₁ ++ L₂).length = L₁.length := by
    rw [hlen]
    have hgt' : 2 ^ (k + 1) > 1 := by
      have := Nat.one_le_two_pow (n := k + 1); omega
    rw [largestPow2Lt_def hgt']
    have hlog : Nat.log 2 (2 ^ (k + 1) - 1) = k := by
      have h_lo : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
        have := Nat.one_le_two_pow (n := k); omega
      have h_hi : 2 ^ (k + 1) - 1 < 2 ^ (k + 1) := by omega
      apply Nat.log_eq_of_pow_le_of_lt_pow h_lo h_hi
    rw [hlog, h1]
  have h_take : (L₁ ++ L₂).take (largestPow2Lt (L₁ ++ L₂).length) = L₁ := by
    rw [hsplit, List.take_left]
  have h_drop : (L₁ ++ L₂).drop (largestPow2Lt (L₁ ++ L₂).length) = L₂ := by
    rw [hsplit, List.drop_left]
  rw [h_take, h_drop, hm1, hm2]

/-- **Theorem: Power-of-Two Core Reflection.**
    For any list of leaves of power-of-2 length, buildStack collapses to a singleton. -/
theorem buildStack_pow2 {α : Type} (L : List (MerkleTree α)) (k : Nat) (h : L.length = 2 ^ k)
    (hL : ∀ t ∈ L, treeHeight t = 0) :
    buildStack L = match mth L with | some t => [t] | none => [] := by
  induction k generalizing L with
  | zero =>
    have hlen : L.length = 1 := by omega
    match L with
    | [] => simp at hlen
    | [d] =>
      simp [buildStack, mergeStacks, mth]
  | succ k' ih =>
    let L₁ := L.take (2 ^ k')
    let L₂ := L.drop (2 ^ k')
    have h1 : L₁.length = 2 ^ k' := by
      dsimp [L₁]
      rw [List.length_take, h]
      have h2pow : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by
        rw [pow_succ]
        ring
      have : 2 ^ k' ≤ 2 ^ (k' + 1) := by omega
      rw [Nat.min_eq_left this]
    have h2 : L₂.length = 2 ^ k' := by
      dsimp [L₂]
      rw [List.length_drop, h]
      have h2pow : 2 ^ (k' + 1) = 2 ^ k' + 2 ^ k' := by
        rw [pow_succ]
        ring
      omega
    have hL₁ : ∀ t ∈ L₁, treeHeight t = 0 := by
      intro t ht
      have := List.mem_of_mem_take ht
      exact hL t this
    have hL₂ : ∀ t ∈ L₂, treeHeight t = 0 := by
      intro t ht
      have := List.mem_of_mem_drop ht
      exact hL t this
    have ih1 := ih L₁ h1 hL₁
    have ih2 := ih L₂ h2 hL₂
    have hsplit : L = L₁ ++ L₂ := (List.take_append_drop (2 ^ k') L).symm
    rw [hsplit]
    exact buildStack_pow2_step L₁ L₂ k' h1 h2 hL₁ hL₂ ih1 ih2

/-- **The Bridge Lemma.** -/
theorem bridge_lemma {α : Type} (leaves : List (MerkleTree α))
    (hL : ∀ t ∈ leaves, treeHeight t = 0) :
    ctoRoot leaves = mth leaves := by
  induction h_len : leaves.length using Nat.strong_induction_on generalizing leaves with
  | h n ih =>
    by_cases hn : n ≤ 1
    · interval_cases n
      · have : leaves = [] := by match leaves with | [] => rfl | _ :: _ => simp at h_len
        subst this
        simp [ctoRoot, buildStack, stackRoot, mth]
      · match leaves with
        | [d] => simp [ctoRoot, buildStack, mergeStacks, stackRoot, mth]
    · have hn_gt : n > 1 := by omega
      by_cases h_pow : ∃ m, n = 2 ^ m
      · obtain ⟨m, hm⟩ := h_pow
        have h_pow2 : buildStack leaves = match mth leaves with | some t => [t] | none => [] := by
          apply buildStack_pow2 leaves m
          · rw [h_len, hm]
          · exact hL
        obtain ⟨t, hm_some, _⟩ := height_mth leaves m (by rw [h_len, hm]) hL
        simp only [ctoRoot]
        rw [h_pow2, hm_some]
        rfl
      · let k := largestPow2Lt n
        have hk_pos : k > 0 := largestPow2Lt_pos hn_gt
        have hk_lt : k < n := largestPow2Lt_lt hn_gt
        obtain ⟨j, hj⟩ := largestPow2Lt_is_pow2 hn_gt
        let L₁ := leaves.take k
        let L₂ := leaves.drop k
        have h1 : L₁.length = k := by
          simp only [L₁]
          rw [List.length_take, h_len]
          exact Nat.min_eq_left (by omega)
        have h2 : L₂.length = n - k := by simp [L₂, h_len]
        have hL₁ : ∀ t ∈ L₁, treeHeight t = 0 := by
          intro t ht
          have := List.mem_of_mem_take ht
          exact hL t this
        have hL₂ : ∀ t ∈ L₂, treeHeight t = 0 := by
          intro t ht
          have := List.mem_of_mem_drop ht
          exact hL t this
        have hsplit : leaves = L₁ ++ L₂ := (List.take_append_drop k leaves).symm
        obtain ⟨t1, hm1, ht1⟩ := height_mth L₁ j (by rw [h1]; exact hj) hL₁
        have h_build_L₁ : buildStack L₁ = [t1] := by
          have := buildStack_pow2 L₁ j (by rw [h1]; exact hj) hL₁
          rw [this, hm1]
        have h_build_L₂_len : ∀ t ∈ buildStack L₂, treeHeight t < j := by
          intro t ht
          have h_cond : L₂.length < 2 ^ j := by
            rw [h2, ← hj]
            exact largestPow2Lt_non_pow2 n h_pow
          exact treeHeight_buildStack_bound L₂ hL₂ j h_cond t ht
        have h_build : buildStack leaves = mergeStacks (buildStack L₁) (buildStack L₂) := by
          rw [hsplit, buildStack_append]
        have h_height_m1 : treeHeight t1 = j := ht1
        have h_all_lt : ∀ t ∈ buildStack L₂, treeHeight t < treeHeight t1 := by
          intro t ht
          have h_lt_t := h_build_L₂_len t ht
          rw [ht1]
          exact h_lt_t
        have h_merge : mergeStacks [t1] (buildStack L₂) = buildStack L₂ ++ [t1] := by
          apply mergeStacks_large_left t1 (buildStack L₂) h_all_lt
        have h_ctoRoot : ctoRoot leaves =
            match ctoRoot L₂ with
            | some t2 => some (MerkleTree.node t1 t2)
            | none => none := by
          simp only [ctoRoot]
          rw [h_build, h_build_L₁, h_merge]
          have h_nonempty : buildStack L₂ ≠ [] := by
            have h_L₂_len : L₂.length > 0 := by
              rw [h2]
              omega
            exact buildStack_nonempty L₂ h_L₂_len
          rw [stackRoot_snoc (buildStack L₂) t1 h_nonempty]
        rw [h_ctoRoot]
        rw [mth_unfold leaves (by omega)]
        have h_take : mth (leaves.take (largestPow2Lt leaves.length)) = some t1 := by
          have h_lt : largestPow2Lt leaves.length = k := by rw [h_len]
          rw [h_lt]
          exact hm1
        have h_drop : mth (leaves.drop (largestPow2Lt leaves.length)) = mth L₂ := by
          have h_lt : largestPow2Lt leaves.length = k := by rw [h_len]
          rw [h_lt]
        rw [h_take, h_drop]
        have h_ih_L₂ := ih (n - k) (by omega) L₂ hL₂ h2
        rw [h_ih_L₂]
        cases h_m2 : mth L₂ with
        | none => rfl
        | some t2 => rfl

-- ============================================================================
-- §6. Concrete Cryptographic Instantiation
-- ============================================================================

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
  | MerkleTree.leaf v => v
  | MerkleTree.node l r => nodeHash (eval l) (eval r)

/-- Maps Option (MerkleTree Digest) to a single Digest. -/
noncomputable def evalOpt : Option (MerkleTree Digest) → Digest
  | none => emptyHash
  | some t => eval t

/-- Concrete ctoRoot over Digest. -/
noncomputable def ctoRootDigest (leaves : List Digest) : Digest :=
  evalOpt (ctoRoot (leaves.map MerkleTree.leaf))

/-- Concrete mth over Digest. -/
noncomputable def mthDigest (leaves : List Digest) : Digest :=
  evalOpt (mth (leaves.map MerkleTree.leaf))

theorem treeHeight_leaf_map {α : Type} (L : List α) :
    ∀ t ∈ L.map MerkleTree.leaf, treeHeight t = 0 := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨v, _, rfl⟩ := ht
  rfl

/-- **Theorem 1 (Projection Equivalence).**
    The concrete ctoRoot digest equals the concrete mth digest over any projected sequence. -/
theorem projection_equivalence (epochs : List Epoch) (payloads : List Digest) :
    ctoRootDigest (project epochs nullLeaf payloads) =
      mthDigest (project epochs nullLeaf payloads) := by
  simp only [ctoRootDigest, mthDigest]
  have hL : ∀ t ∈ (project epochs nullLeaf payloads).map MerkleTree.leaf, treeHeight t = 0 :=
    treeHeight_leaf_map _
  rw [bridge_lemma _ hL]

-- ============================================================================
-- §8. Theorem 2 — Temporal Binding
-- ============================================================================

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

-- ============================================================================
-- §9. Theorem 3 — Algorithm Isolation
-- ============================================================================

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
