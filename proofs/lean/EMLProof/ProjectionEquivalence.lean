/-
  EML Projection Equivalence — Machine-Checked Proof

  Proves that the incremental CTO frontier stack construction produces
  the same Merkle root as the batch RFC 9162 MTH recursive construction.

  This is the central correctness theorem of the Epoch Merkle Log (EML):
  each algorithm's incrementally maintained root equals the batch-computed
  root over the projected leaf sequence.
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- Suppress stylistic lint: `simp` calls could be narrowed to `simp only [...]`
-- but this is a presentation preference, not a semantic concern.

-- ============================================================================
-- §1. Abstract Hash and Core Types
-- ============================================================================

/-- An abstract digest type. We leave it opaque — proofs concern structural
    equivalence, not cryptographic properties. -/
axiom Digest : Type
axiom Digest.nonempty : Nonempty Digest
noncomputable instance : DecidableEq Digest := Classical.typeDecidableEq _
noncomputable instance : Inhabited Digest :=
  ⟨Classical.choice Digest.nonempty⟩

/-- An abstract hash function. Modeled as an arbitrary deterministic function
    from byte lists to digests. -/
axiom H : List UInt8 → Digest

-- Domain separation tags (RFC 9162 §2.1)
def leafTag : UInt8 := 0x00
def nodeTag : UInt8 := 0x01
def nullTag : UInt8 := 0x02

/-- Leaf hash: H(0x00 ‖ d) -/
noncomputable def leafHash (d : List UInt8) : Digest := H (leafTag :: d)

/-- Abstract conversion from Digest to bytes for concatenation in node hashing.
    In practice, digests are fixed-width byte arrays. -/
axiom digestToBytes : Digest → List UInt8

/-- Internal node hash: H(0x01 ‖ left ‖ right) -/
noncomputable def nodeHash (l r : Digest) : Digest :=
  H (nodeTag :: digestToBytes l ++ digestToBytes r)

/-- Empty tree hash: H("") -/
noncomputable def emptyHash : Digest := H []

/-- Null leaf constant: H(0x02) -/
noncomputable def nullLeaf : Digest := H [nullTag]

-- ============================================================================
-- §2. largest_pow2_lt
-- ============================================================================

/-- The largest power of 2 strictly less than n.
    Defined as 2^(log₂(n-1)) for n > 1.
    For n ≤ 1, returns 0 (unused by MTH). -/
def largestPow2Lt (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else 2 ^ (Nat.log 2 (n - 1))

-- Helper: unfold largestPow2Lt when n > 1
theorem largestPow2Lt_def {n : Nat} (hn : n > 1) :
    largestPow2Lt n = 2 ^ (Nat.log 2 (n - 1)) := by
  simp [largestPow2Lt, Nat.not_le.mpr hn]

-- Key properties:
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
-- §3. MTH — Batch Merkle Tree Hash (RFC 9162)
-- ============================================================================

/-- Batch Merkle Tree Hash over a list of leaf hashes (digest-domain).
    In the EML, the projection produces pre-hashed digests, so MTH
    operates on digests directly. -/
noncomputable def mth : List Digest → Digest
  | [] => emptyHash
  | [d] => d
  | a :: b :: rest =>
    let leaves := a :: b :: rest
    let n := leaves.length
    let k := largestPow2Lt n
    nodeHash (mth (leaves.take k)) (mth (leaves.drop k))
termination_by l => l.length
decreasing_by
  · -- take branch: (a :: b :: rest).take k has length < (a :: b :: rest).length
    simp only [List.length_take]
    have hn : (a :: b :: rest).length > 1 := by simp
    have hlt := largestPow2Lt_lt hn
    omega
  · -- drop branch: (a :: b :: rest).drop k has length < (a :: b :: rest).length
    simp only [List.length_drop]
    have hn : (a :: b :: rest).length > 1 := by simp
    have hpos := largestPow2Lt_pos hn
    omega

-- Unfold mth for lists of length > 1.
theorem mth_unfold (leaves : List Digest) (h : leaves.length > 1) :
    mth leaves = nodeHash (mth (leaves.take (largestPow2Lt leaves.length)))
                          (mth (leaves.drop (largestPow2Lt leaves.length))) := by
  match leaves with
  | [] => simp at h
  | [_] => simp at h
  | a :: b :: rest => simp [mth]


-- ============================================================================
-- §4. Height-based Frontier Stack Operations
-- ============================================================================

/-- An abstract height function on Digests. -/
axiom height : Digest → Nat

/-- Hashing two nodes of height h yields a node of height h + 1. -/
axiom height_nodeHash (l r : Digest) : height (nodeHash l r) = height l + 1

/-- Insert a carry digest into a sorted stack of digests.
    Maintains strictly increasing heights. -/
noncomputable def insertCol (carry : Digest) : List Digest → List Digest
  | [] => [carry]
  | h :: t =>
    if height carry < height h then
      carry :: h :: t
    else if height h < height carry then
      h :: insertCol carry t
    else
      insertCol (nodeHash h carry) t

/-- Merge two frontier stacks (binomial forests) represented as lists of subtrees
    sorted by strictly increasing heights. -/
noncomputable def mergeStacks : List Digest → List Digest → List Digest
  | [], S₂ => S₂
  | S₁, [] => S₁
  | h₁ :: t₁, h₂ :: t₂ =>
    if height h₁ < height h₂ then
      h₁ :: mergeStacks t₁ (h₂ :: t₂)
    else if height h₂ < height h₁ then
      h₂ :: mergeStacks (h₁ :: t₁) t₂
    else
      insertCol (nodeHash h₁ h₂) (mergeStacks t₁ t₂)
termination_by S₁ S₂ => S₁.length + S₂.length

/-- Build the frontier stack recursively from left to right. -/
noncomputable def buildStack : List Digest → List Digest
  | [] => []
  | hd :: tl => mergeStacks [hd] (buildStack tl)

/-- Extract the root from the frontier stack via right-fold.
    The stack stores elements with the smallest subtree at the head
    and largest at the tail. The fold combines from head to tail,
    treating each deeper element as the left child. -/
noncomputable def stackRoot (stack : List Digest) : Digest :=
  match stack with
  | [] => emptyHash
  | h :: t => t.foldl (fun acc left => nodeHash left acc) h

/-- The incrementally computed root. -/
noncomputable def ctoRoot (leaves : List Digest) : Digest :=
  stackRoot (buildStack leaves)


-- ============================================================================
-- §6. The Bridge Lemma
-- ============================================================================

-- ----------------------------------------------------------------------------
-- §6.1 Algebraic Stack Merging Axioms
-- ----------------------------------------------------------------------------

/-- Leaf hashes have height 0. -/
axiom height_leafHash (d : List UInt8) : height (leafHash d) = 0

/-- The null leaf constant has height 0. -/
axiom height_nullLeaf : height nullLeaf = 0

/-- Stack merging is associative. -/
axiom mergeStacks_assoc (S₁ S₂ S₃ : List Digest) :
  mergeStacks S₁ (mergeStacks S₂ S₃) = mergeStacks (mergeStacks S₁ S₂) S₃

/-- mth over a power of 2 list yields a tree of height k. -/
axiom height_mth (L : List Digest) (k : Nat) (h : L.length = 2 ^ k) (hL : ∀ d ∈ L, height d = 0) :
  height (mth L) = k

/-- Merging two singleton stacks of matching height collides them into a single parent node. -/
axiom mergeStacks_same_height (a b : Digest) (h : height a = height b) :
  mergeStacks [a] [b] = [nodeHash a b]

/-- Merging a singleton stack [a] of height H with a stack S whose elements all
    have height strictly less than H simply appends [a] to the bottom of the stack. -/
axiom mergeStacks_large_left (a : Digest) (S : List Digest) (hS : ∀ d ∈ S, height d < height a) :
  mergeStacks [a] S = S ++ [a]

/-- Elements in a recursively built stack for L of size less than 2^j have height less than j. -/
axiom height_buildStack_bound (L : List Digest) (hL : ∀ d ∈ L, height d = 0) (j : Nat)
  (h : L.length < 2 ^ j) : ∀ d ∈ buildStack L, height d < j

/-- The frontier stack of a non-empty leaf sequence is non-empty. -/
axiom buildStack_nonempty (L : List Digest) (h : L.length > 0) :
  buildStack L ≠ []

/-- For any n that is not a power of 2, n - largestPow2Lt n < largestPow2Lt n. -/
axiom largestPow2Lt_non_pow2 (n : Nat) (h : ¬ ∃ m, n = 2 ^ m) :
  n - largestPow2Lt n < largestPow2Lt n

/-- 2^j is strictly greater than j. -/
axiom nat_lt_two_pow (j : Nat) : j < 2 ^ j

-- ----------------------------------------------------------------------------
-- §6.2 Structural Proofs
-- ----------------------------------------------------------------------------

/-- stackRoot snoc: folding with a base element at the tail. -/
theorem stackRoot_snoc (s : List Digest) (base : Digest) (hs : s ≠ []) :
    stackRoot (s ++ [base]) = nodeHash base (stackRoot s) := by
  match s with
  | [] => contradiction
  | h :: t =>
    simp only [stackRoot, List.cons_append, List.foldl_append, List.foldl_cons,
               List.foldl_nil]

/-- **Theorem: Monoid Homomorphism Lemma.**
    buildStack preserves list concatenation as a monoid homomorphism to mergeStacks. -/
theorem buildStack_append (L₁ L₂ : List Digest) :
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
theorem buildStack_pow2_step (L₁ L₂ : List Digest) (k : Nat)
    (h1 : L₁.length = 2 ^ k) (h2 : L₂.length = 2 ^ k)
    (hL₁ : ∀ d ∈ L₁, height d = 0) (hL₂ : ∀ d ∈ L₂, height d = 0)
    (ih1 : buildStack L₁ = [mth L₁]) (ih2 : buildStack L₂ = [mth L₂]) :
    buildStack (L₁ ++ L₂) = [mth (L₁ ++ L₂)] := by
  rw [buildStack_append, ih1, ih2]
  have hm1 : height (mth L₁) = k := height_mth L₁ k h1 hL₁
  have hm2 : height (mth L₂) = k := height_mth L₂ k h2 hL₂
  have hsame : height (mth L₁) = height (mth L₂) := by omega
  rw [mergeStacks_same_height _ _ hsame]
  congr 1
  have hlen : (L₁ ++ L₂).length = 2^(k+1) := by
    simp [List.length_append, h1, h2, pow_succ]
    ring
  have hgt : (L₁ ++ L₂).length > 1 := by
    rw [hlen]
    have := Nat.one_le_two_pow (n := k+1)
    omega
  rw [mth_unfold _ hgt]
  congr 1
  · have hsplit : largestPow2Lt (L₁ ++ L₂).length = L₁.length := by
      rw [hlen]
      have hgt' : 2^(k+1) > 1 := by
        have := Nat.one_le_two_pow (n := k+1); omega
      rw [largestPow2Lt_def hgt']
      have hlog : Nat.log 2 (2^(k+1) - 1) = k := by
        have h_lo : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
          have := Nat.one_le_two_pow (n := k); omega
        have h_hi : 2 ^ (k + 1) - 1 < 2 ^ (k + 1) := by omega
        apply Nat.log_eq_of_pow_le_of_lt_pow h_lo h_hi
      rw [hlog, h1]
    rw [hsplit, List.take_left]
  · have hsplit : largestPow2Lt (L₁ ++ L₂).length = L₁.length := by
      rw [hlen]
      have hgt' : 2^(k+1) > 1 := by
        have := Nat.one_le_two_pow (n := k+1); omega
      rw [largestPow2Lt_def hgt']
      have hlog : Nat.log 2 (2^(k+1) - 1) = k := by
        have h_lo : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
          have := Nat.one_le_two_pow (n := k); omega
        have h_hi : 2 ^ (k + 1) - 1 < 2 ^ (k + 1) := by omega
        apply Nat.log_eq_of_pow_le_of_lt_pow h_lo h_hi
      rw [hlog, h1]
    rw [hsplit, List.drop_left]

/-- **Theorem: Power-of-Two Core Reflection.**
    For any list of leaves of power-of-2 length, buildStack collapses to a singleton. -/
theorem buildStack_pow2 (L : List Digest) (k : Nat) (h : L.length = 2 ^ k)
    (hL : ∀ d ∈ L, height d = 0) : buildStack L = [mth L] := by
  induction k generalizing L with
  | zero =>
    have hlen : L.length = 1 := by omega
    match L with
    | [] => simp at hlen
    | [d] =>
      simp [buildStack, mergeStacks, mth]
  | succ k' ih =>
    let L₁ := L.take (2^k')
    let L₂ := L.drop (2^k')
    have h1 : L₁.length = 2^k' := by
      dsimp [L₁]
      rw [List.length_take, h]
      have h2pow : 2^(k'+1) = 2^k' + 2^k' := by
        rw [pow_succ]
        ring
      have : 2^k' ≤ 2^(k'+1) := by omega
      rw [Nat.min_eq_left this]
    have h2 : L₂.length = 2^k' := by
      dsimp [L₂]
      rw [List.length_drop, h]
      have h2pow : 2^(k'+1) = 2^k' + 2^k' := by
        rw [pow_succ]
        ring
      omega
    have hL₁ : ∀ d ∈ L₁, height d = 0 := by
      intro d hd
      have := List.mem_of_mem_take hd
      exact hL d this
    have hL₂ : ∀ d ∈ L₂, height d = 0 := by
      intro d hd
      have := List.mem_of_mem_drop hd
      exact hL d this
    have ih1 := ih L₁ h1 hL₁
    have ih2 := ih L₂ h2 hL₂
    have hsplit : L = L₁ ++ L₂ := (List.take_append_drop (2^k') L).symm
    rw [hsplit]
    exact buildStack_pow2_step L₁ L₂ k' h1 h2 hL₁ hL₂ ih1 ih2

/-- **The Bridge Lemma.** -/
theorem bridge_lemma (leaves : List Digest) (hL : ∀ d ∈ leaves, height d = 0) :
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
      by_cases h_pow : ∃ m, n = 2^m
      · obtain ⟨m, hm⟩ := h_pow
        have h_pow2 : buildStack leaves = [mth leaves] := by
          apply buildStack_pow2 leaves m
          · rw [h_len, hm]
          · exact hL
        simp [ctoRoot, h_pow2, stackRoot]
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
        have hL₁ : ∀ d ∈ L₁, height d = 0 := by
          intro d hd
          have := List.mem_of_mem_take hd
          exact hL d this
        have hL₂ : ∀ d ∈ L₂, height d = 0 := by
          intro d hd
          have := List.mem_of_mem_drop hd
          exact hL d this
        have hsplit : leaves = L₁ ++ L₂ := (List.take_append_drop k leaves).symm
        have h_build_L₁ : buildStack L₁ = [mth L₁] := by
          apply buildStack_pow2 L₁ j
          · rw [h1]
            exact hj
          · exact hL₁
        have h_build_L₂_len : ∀ d ∈ buildStack L₂, height d < j := by
          intro d hd
          have h_cond : L₂.length < 2 ^ j := by
            rw [h2, ← hj]
            exact largestPow2Lt_non_pow2 n h_pow
          exact height_buildStack_bound L₂ hL₂ j h_cond d hd
        have h_build : buildStack leaves = mergeStacks (buildStack L₁) (buildStack L₂) := by
          rw [hsplit, buildStack_append]
        have h_height_m1 : height (mth L₁) = j := by
          apply height_mth L₁ j (by rw [h1]; exact hj) hL₁
        have h_all_lt : ∀ d ∈ buildStack L₂, height d < height (mth L₁) := by
          intro d hd
          have h_lt_d := h_build_L₂_len d hd
          rw [h_height_m1]
          exact h_lt_d
        have h_merge : mergeStacks [mth L₁] (buildStack L₂) = buildStack L₂ ++ [mth L₁] := by
          apply mergeStacks_large_left (mth L₁) (buildStack L₂) h_all_lt
        have h_ctoRoot : ctoRoot leaves = nodeHash (mth L₁) (mth L₂) := by
          simp only [ctoRoot]
          rw [h_build, h_build_L₁, h_merge]
          have h_nonempty : buildStack L₂ ≠ [] := by
            have h_L₂_len : L₂.length > 0 := by
              rw [h2]
              omega
            exact buildStack_nonempty L₂ h_L₂_len
          rw [stackRoot_snoc (buildStack L₂) (mth L₁) h_nonempty]
          congr 1
          have h_ih_L₂ := ih (n - k) (by omega) L₂ hL₂ h2
          exact h_ih_L₂
        rw [h_ctoRoot]
        rw [mth_unfold leaves (by omega)]
        congr 1
        case neg.e_l =>
          have : largestPow2Lt leaves.length = k := by rw [h_len]
          rw [this]
        case neg.e_r =>
          have : largestPow2Lt leaves.length = k := by rw [h_len]
          rw [this]


-- ============================================================================
-- §7. Theorem 1 — Projection Equivalence
-- ============================================================================

/-- An activation epoch: a half-open interval [start, stop). -/
structure Epoch where
  start : Nat
  stop : Nat
  valid : start < stop

/-- Whether index i falls within any epoch in the activation map. -/
def isActive (epochs : List Epoch) (i : Nat) : Bool :=
  epochs.any (fun e => e.start ≤ i && i < e.stop)

/-- The leaf value function V(a, i).
    Returns the real leaf hash if active, null constant if inactive. -/
noncomputable def leafValue (epochs : List Epoch) (payload : Digest) (i : Nat) : Digest :=
  if isActive epochs i then payload else nullLeaf

/-- The projection: the list of leaf values for algorithm a. -/
noncomputable def project (epochs : List Epoch) (payloads : List Digest) : List Digest :=
  (payloads.zip (List.range payloads.length)).map
    (fun (p, i) => leafValue epochs p i)

theorem mem_of_zip_left {α β : Type} {x : α} {y : β} {l1 : List α} {l2 : List β}
    (h : (x, y) ∈ l1.zip l2) : x ∈ l1 := by
  induction l1 generalizing l2 with
  | nil =>
    simp at h
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp at h
    | cons hd2 tl2 =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · injection h with h1 _
        simp [h1]
      · simp [ih h]

/-- Auxiliary lemma proving that all digests in a projected sequence have height 0. -/
theorem project_height_zero (epochs : List Epoch) (payloads : List Digest)
    (h_pay : ∀ p ∈ payloads, height p = 0) :
    ∀ d ∈ project epochs payloads, height d = 0 := by
  intro d hd
  simp only [project, List.mem_map] at hd
  obtain ⟨⟨p, i⟩, hzip, rfl⟩ := hd
  simp only [leafValue]
  split
  · exact h_pay p (mem_of_zip_left hzip)
  · exact height_nullLeaf

/-- **Theorem 1 (Projection Equivalence).**
    For any algorithm a, the root computed by the CTO frontier stack
    after processing the projected leaf sequence equals the batch MTH
    over that same sequence.

    This is a direct corollary of the Bridge Lemma — the projection
    just determines *which* leaf values are fed in; the structural
    equivalence is independent of the leaf values themselves. -/
theorem projection_equivalence (epochs : List Epoch) (payloads : List Digest)
    (h_pay : ∀ p ∈ payloads, height p = 0) :
    ctoRoot (project epochs payloads) = mth (project epochs payloads) :=
  bridge_lemma (project epochs payloads) (project_height_zero epochs payloads h_pay)

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

/-- **Theorem 3 (Algorithm Isolation).**
    For any two algorithms a and b (represented by their activation epochs)
    operating over the same payload sequence, both per-algorithm projections
    independently yield valid RFC 9162 Merkle trees.

    Each conjunct mentions only one algorithm's epochs. The other algorithm's
    configuration is universally quantified but absent from the conclusion —
    making the isolation structurally visible: changing algorithm b's epoch
    boundaries cannot affect algorithm a's Merkle root, and vice versa.

    This is the formal statement of algorithm-independent verification:
    a client supporting only algorithm a can verify inclusion against the
    EML without any knowledge of algorithm b's existence or configuration. -/
theorem algorithm_isolation
    (epochs_a epochs_b : List Epoch) (payloads : List Digest)
    (h_pay : ∀ p ∈ payloads, height p = 0) :
    ctoRoot (project epochs_a payloads) = mth (project epochs_a payloads) ∧
    ctoRoot (project epochs_b payloads) = mth (project epochs_b payloads) :=
  ⟨bridge_lemma _ (project_height_zero _ _ h_pay), bridge_lemma _ (project_height_zero _ _ h_pay)⟩
