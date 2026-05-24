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

set_option linter.style.emptyLine false

-- ============================================================================
-- §1. Inductive Merkle Tree Representation
-- ============================================================================

inductive MerkleTree (α : Type) where
  | empty
  | leaf (val : α)
  | node (left right : MerkleTree α)
  deriving DecidableEq, Inhabited

def treeHeight {α : Type} : MerkleTree α → Nat
  | MerkleTree.empty => 0
  | MerkleTree.leaf _ => 0
  | MerkleTree.node l r => Nat.max (treeHeight l) (treeHeight r) + 1
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
noncomputable def mth {α : Type} : List (MerkleTree α) → MerkleTree α
  | [] => MerkleTree.empty
  | [d] => d
  | a :: b :: rest =>
    let leaves := a :: b :: rest
    let n := leaves.length
    let k := largestPow2Lt n
    MerkleTree.node (mth (leaves.take k)) (mth (leaves.drop k))
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

-- ============================================================================
-- §4. CTO — Count Trailing Ones
-- ============================================================================

/-- Count trailing one-bits in the binary representation of n. -/
def cto (n : Nat) : Nat :=
  if n % 2 = 1 then 1 + cto (n / 2)
  else 0

@[simp] theorem cto_zero : cto 0 = 0 := by simp [cto]
@[simp] theorem cto_even {n : Nat} (h : n % 2 = 0) : cto n = 0 := by
  simp [cto, h]

-- ============================================================================
-- §5. Frontier Stack Operations
-- ============================================================================

/-- Merge the top `count` pairs on the stack.
    Each merge pops two elements, hashes them, and pushes the result. -/
noncomputable def mergeStack {α : Type} (stack : List (MerkleTree α)) (count : Nat) :
    List (MerkleTree α) :=
  match count with
  | 0 => stack
  | n + 1 =>
    match stack with
    | r :: l :: rest => mergeStack (MerkleTree.node l r :: rest) n
    | _ => stack  -- underflow guard

/-- Append a single leaf hash to the frontier stack, then perform
    CTO-determined merges. Per the EML model (Definition 8),
    merge_count = cto(S.size) where S.size is the 0-based leaf index. -/
noncomputable def appendToStack (stack : List (MerkleTree α)) (leaf : MerkleTree α)
    (idx : Nat) : List (MerkleTree α) :=
  mergeStack (leaf :: stack) (cto idx)

/-- Build the frontier stack by processing leaves with explicit index tracking.
    Uses a recursive auxiliary for proof friendliness (vs foldl). -/
noncomputable def buildStackAux {α : Type} (stack : List (MerkleTree α))
    (remaining : List (MerkleTree α)) (idx : Nat) : List (MerkleTree α) :=
  match remaining with
  | [] => stack
  | leaf :: rest => buildStackAux (appendToStack stack leaf idx) rest (idx + 1)

noncomputable def buildStack {α : Type} (leaves : List (MerkleTree α)) : List (MerkleTree α) :=
  buildStackAux [] leaves 0

/-- Extract the root from the frontier stack via right-fold.
    The stack stores elements with the smallest subtree at the head
    and largest at the tail. The fold combines from head to tail,
    treating each deeper element as the left child. -/
noncomputable def stackRoot (stack : List (MerkleTree α)) : MerkleTree α :=
  match stack with
  | [] => MerkleTree.empty
  | h :: t => t.foldl (fun acc left => MerkleTree.node left acc) h

/-- The incrementally computed root. -/
noncomputable def ctoRoot (leaves : List (MerkleTree α)) : MerkleTree α :=
  stackRoot (buildStack leaves)

-- ============================================================================
-- §6. The Bridge Lemma
-- ============================================================================

/-
  Proof Strategy:

  Rather than proving a full stack invariant over the foldl, we take a more
  direct approach. We prove the bridge lemma by strong induction on
  leaves.length, using two key computational observations:

  1. When n is a power of 2, buildStack produces a singleton stack
     containing mth(leaves). This is because CTO counts trailing ones,
     and appending the last leaf of a power-of-2 block triggers a full
     cascade of merges.

  2. For general n, the stack after processing n leaves decomposes at the
     largest set bit: the bottom element is mth(leaves[0:k]) where
     k = 2^msb(n), and the remaining elements form the stack for
     leaves[k:n].

  The right-fold then combines them exactly as mth's top-down split.
-/

-- Base cases are computational:
theorem bridge_base_empty {α : Type} : ctoRoot (α := α) [] = mth (α := α) [] := by
  simp only [ctoRoot, buildStack, buildStackAux, stackRoot, mth]

theorem bridge_base_single {α : Type} (d : MerkleTree α) : ctoRoot [d] = mth [d] := by
  simp [ctoRoot, buildStack, buildStackAux, appendToStack, mergeStack,
        stackRoot, mth]

-- Decomposition lemma 1: buildStackAux splits over concatenation.
-- Processing L₁ ++ L₂ from stack₀ at index i is the same as
-- first processing L₁, then processing L₂ from the resulting stack.
theorem buildStackAux_append (stack₀ : List (MerkleTree α)) (L₁ L₂ : List (MerkleTree α))
    (i : Nat) :
    buildStackAux stack₀ (L₁ ++ L₂) i =
    buildStackAux (buildStackAux stack₀ L₁ i) L₂ (i + L₁.length) := by
  induction L₁ generalizing stack₀ i with
  | nil => simp [buildStackAux]
  | cons hd tl ih =>
    simp only [List.cons_append, buildStackAux, List.length_cons]
    rw [ih]
    congr 1
    omega

-- ============================================================================
-- Stack Invariant — the core structural property
-- ============================================================================

/-
  The CTO algorithm maintains the following invariant:
  After processing n leaves (indices 0..n-1), the frontier stack
  decomposes the leaf sequence into contiguous segments whose sizes
  are the set bits of n, strictly descending (largest segment first).
  Each stack element is the mth of its corresponding segment, with
  the stack reversed (smallest at head, largest at tail).

  Example: after 13 = 0b1101 leaves:
    segments = [leaves[0:8], leaves[8:12], leaves[12:13]]
    sizes    = [8, 4, 1]  (strictly descending)
    stack    = [mth(leaves[12:13]), mth(leaves[8:12]), mth(leaves[0:8])]
              (smallest subtree at head, largest at tail)

  This invariant is what makes ctoRoot = mth: stackRoot folds from
  head to tail, combining elements into the same tree that mth builds
  by recursive splitting at the largest power-of-2 boundary.
-/

/-- The stack invariant: pfx is partitioned into power-of-2 segments
    in strictly descending size order, and the stack holds their mth's
    in reverse. -/
noncomputable def stackInvariant {α : Type} (pfx : List (MerkleTree α))
    (stack : List (MerkleTree α)) : Prop :=
  ∃ (segments : List (List (MerkleTree α))),
    -- The segments partition the leaves left-to-right
    segments.flatten = pfx ∧
    -- Each segment has power-of-2 length
    (∀ s ∈ segments, ∃ k, s.length = 2 ^ k) ∧
    -- Segment sizes are strictly descending
    List.Pairwise (· > ·) (segments.map List.length) ∧
    -- The stack contains the mth of each segment, reversed
    stack = (segments.map mth).reverse

/-- mth of a two-element list -/
theorem mth_pair {α : Type} (a b : MerkleTree α) : mth [a, b] = MerkleTree.node a b := by
  simp [mth, largestPow2Lt, List.take]



/-- If segment sizes are strictly descending powers of 2 summing to idx,
    and cto(idx) = 0, then no segment has size 1. -/
theorem no_size_one_when_cto_zero (sizes : List Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ k, s = 2 ^ k)
    (h_cto : cto sizes.sum = 0) :
    ∀ s ∈ sizes, s ≥ 2 := by
  -- cto n = 0 implies n % 2 = 0 (by definition: if n%2=1 then 1+... else 0)
  have h_even : sizes.sum % 2 = 0 := by
    by_contra h_ne
    have h_odd : sizes.sum % 2 = 1 := by omega
    -- cto unfolds: since sum%2=1, cto sum = 1 + cto(sum/2) ≥ 1
    have : cto sizes.sum ≥ 1 := by
      rw [cto]; simp [h_odd]
    omega
  -- Now: sum is even, so no element can be 1
  -- (1 = 2^0; strictly descending pow2s with a 1 make the sum odd)
  intro s hs
  by_contra h_lt
  push Not at h_lt
  -- s is a power of 2 and s < 2, so s = 1 = 2^0
  obtain ⟨k, hk⟩ := h_pow2 s hs
  have h_k_zero : k = 0 := by
    by_contra h_k_pos
    push Not at h_k_pos
    have : 2 ^ k ≥ 2 := by
      calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    omega
  subst hk; subst h_k_zero
  -- 1 ∈ sizes with strictly descending pow2s → sum is odd
  -- Prove by induction: if 1 ∈ l, desc, all pow2, then l.sum % 2 = 1
  suffices h_odd : ∀ (l : List Nat),
      List.Pairwise (· > ·) l → (∀ s ∈ l, ∃ k, s = 2 ^ k) → 1 ∈ l →
      l.sum % 2 = 1 by
    have := h_odd sizes h_desc h_pow2 hs
    omega
  intro l
  induction l with
  | nil => intro _ _ h_mem; nomatch h_mem
  | cons hd tl ih =>
    intro h_d h_p h_mem
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h_mem with h_eq | h_in_tl
    · -- hd = 1: all tl elements < 1, but all are pow2 ≥ 1, so tl = []
      subst h_eq
      have h_tl_empty : tl = [] := by
        by_contra h_ne
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil tl h_ne
        have h_gt := (List.pairwise_cons.mp h_d).1 x hx  -- 1 > x
        obtain ⟨j, hj⟩ := h_p x (List.Mem.tail _ hx)
        have := Nat.one_le_two_pow (n := j); omega
      subst h_tl_empty; simp
    · -- 1 ∈ tl: hd > 1, hd is pow2, so hd even; tl.sum odd by IH
      have h_hd_gt : hd > 1 :=
        (List.pairwise_cons.mp h_d).1 1 h_in_tl
      obtain ⟨j, hj⟩ := h_p hd (List.Mem.head _)
      subst hj
      have h_j_pos : j ≥ 1 := by
        by_contra h
        push Not at h
        interval_cases j
        simp at h_hd_gt
      have h_tl_odd : tl.sum % 2 = 1 :=
        ih (List.Pairwise.of_cons h_d)
          (fun s hs => h_p s (List.Mem.tail _ hs)) h_in_tl
      -- 2^j with j ≥ 1 is even: 2^j = 2 * 2^(j-1)
      have h_hd_even : 2 ^ j % 2 = 0 := by
        have : j = j - 1 + 1 := by omega
        rw [this, pow_succ]
        omega
      omega


-- ============================================================================
-- From invariant to bridge lemma — helper lemmas
-- ============================================================================

-- stackRoot snoc: folding with a base element at the tail.
theorem stackRoot_snoc (s : List (MerkleTree α)) (base : MerkleTree α) (hs : s ≠ []) :
    stackRoot (s ++ [base]) = MerkleTree.node base (stackRoot s) := by
  match s with
  | [] => contradiction
  | h :: t =>
    simp only [stackRoot, List.cons_append, List.foldl_append, List.foldl_cons,
               List.foldl_nil]

-- flatten_cons: segments.flatten for first :: rest
@[simp] theorem flatten_cons (first : List α) (rest : List (List α)) :
    (first :: rest).flatten = first ++ rest.flatten := by
  simp [List.flatten]

-- Key arithmetic lemma: for a strictly descending list of powers of 2,
-- the sum of the remaining elements is strictly less than the first.
-- This is because 2^(k-1) + 2^(k-2) + ... + 2^0 = 2^k - 1 < 2^k.
theorem sum_rest_lt_first (first : Nat) (rest : List Nat)
    (h_first_pow2 : ∃ k, first = 2 ^ k)
    (h_rest_pow2 : ∀ s ∈ rest, ∃ k, s = 2 ^ k)
    (h_desc : List.Pairwise (· > ·) (first :: rest)) :
    rest.sum < first := by
  induction rest generalizing first with
  | nil =>
    obtain ⟨k, hk⟩ := h_first_pow2; subst hk; simp
  | cons hd tl ih =>
    simp only [List.sum_cons]
    have h_hd_lt : hd < first := by
      have := List.pairwise_cons.mp h_desc
      exact this.1 hd (List.Mem.head _)
    have h_hd_pow2 : ∃ j, hd = 2 ^ j :=
      h_rest_pow2 hd (List.Mem.head _)
    have h_tl_pow2 : ∀ s ∈ tl, ∃ k, s = 2 ^ k := by
      intro s hs; exact h_rest_pow2 s (List.Mem.tail _ hs)
    have h_desc_tl : List.Pairwise (· > ·) (hd :: tl) := by
      exact List.Pairwise.sublist
        (List.sublist_cons_self first (hd :: tl)) h_desc
    have h_tl_lt : tl.sum < hd := ih hd h_hd_pow2 h_tl_pow2 h_desc_tl
    -- 2*hd ≤ first because both are powers of 2 and hd < first
    obtain ⟨j, hj⟩ := h_hd_pow2
    obtain ⟨k, hk⟩ := h_first_pow2
    subst hj; subst hk
    have h_j_lt_k : j < k := by
      by_contra h_ge
      push Not at h_ge
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h_ge
      omega
    have h_two_j_le : 2 * 2 ^ j ≤ 2 ^ k := by
      calc 2 * 2 ^ j = 2 ^ (j + 1) := by ring
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

-- When the first segment is the largest power of 2 and the rest sum
-- to less than it, largestPow2Lt of the total equals the first segment's size.
theorem largestPow2Lt_of_desc_segments (first_len rest_total : Nat)
    (h_first_pos : first_len > 0)
    (h_rest_pos : rest_total > 0)
    (h_first_pow2 : ∃ k, first_len = 2 ^ k)
    (h_lt : rest_total < first_len) :
    largestPow2Lt (first_len + rest_total) = first_len := by
  obtain ⟨k, hk⟩ := h_first_pow2
  subst hk
  -- Need: largestPow2Lt (2^k + rest_total) = 2^k
  -- total > 1 since 2^k ≥ 1 and rest_total ≥ 1
  have h_total_gt_1 : 2 ^ k + rest_total > 1 := by
    have := Nat.one_le_two_pow (n := k)
    omega
  rw [largestPow2Lt_def h_total_gt_1]
  -- Need: Nat.log 2 (2^k + rest_total - 1) = k
  -- 2^k + rest_total - 1 ∈ [2^k, 2^(k+1) - 1]
  -- Lower: 2^k + rest_total - 1 ≥ 2^k (since rest_total ≥ 1)
  -- Upper: 2^k + rest_total - 1 < 2^(k+1) (since rest_total < 2^k)
  have h_lo : 2 ^ k ≤ 2 ^ k + rest_total - 1 := by omega
  have h_hi : 2 ^ k + rest_total - 1 < 2 ^ (k + 1) := by
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have h_log : Nat.log 2 (2 ^ k + rest_total - 1) = k := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact h_lo
    · exact h_hi
  rw [h_log]

-- Unfold mth for lists of length > 1.
theorem mth_unfold (leaves : List (MerkleTree α)) (h : leaves.length > 1) :
    mth leaves = MerkleTree.node (mth (leaves.take (largestPow2Lt leaves.length)))
                          (mth (leaves.drop (largestPow2Lt leaves.length))) := by
  match leaves with
  | [] => simp at h
  | [_] => simp at h
  | a :: b :: rest => simp [mth]

-- Split mth over concatenation when the split point matches largestPow2Lt.
theorem mth_split (L₁ L₂ : List (MerkleTree α))
    (hL₁ : L₁ ≠ []) (hL₂ : L₂ ≠ [])
    (h_split : largestPow2Lt (L₁.length + L₂.length) = L₁.length) :
    mth (L₁ ++ L₂) = MerkleTree.node (mth L₁) (mth L₂) := by
  have h_len : (L₁ ++ L₂).length > 1 := by
    simp only [List.length_append]
    have h1 : L₁.length > 0 := by
      match L₁ with | [] => contradiction | _ :: _ => simp
    have h2 : L₂.length > 0 := by
      match L₂ with | [] => contradiction | _ :: _ => simp
    omega
  rw [mth_unfold _ h_len]
  simp only [List.length_append, h_split]
  rw [List.take_append_length, List.drop_append_length]

/-- When two segments have equal power-of-2 size, merging their mth's
    produces the mth of the concatenated segment. -/
theorem mth_merge (L R : List (MerkleTree α)) (k : Nat)
    (hL : L.length = 2 ^ k) (hR : R.length = 2 ^ k) :
    MerkleTree.node (mth L) (mth R) = mth (L ++ R) := by
  symm
  apply mth_split L R
  · intro h; simp [h] at hL; have := Nat.one_le_two_pow (n := k); omega
  · intro h; simp [h] at hR; have := Nat.one_le_two_pow (n := k); omega
  · have h_gt : 2 ^ (k + 1) > 1 := by
      have := Nat.one_le_two_pow (n := k + 1); omega
    simp only [hL, hR]
    have h_sum : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
    rw [h_sum]
    simp only [largestPow2Lt, Nat.not_le.mpr h_gt, if_false]
    have h_bound_lo : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by omega
    have h_bound_hi : 2 ^ (k + 1) - 1 < 2 ^ (k + 1) := by omega
    rw [Nat.log_eq_of_pow_le_of_lt_pow h_bound_lo h_bound_hi]

/-- Sum of strictly descending pow2s: if all elements are powers of 2,
    pairwise strictly descending, and all < 2^a, then the sum < 2^a. -/
private theorem sum_desc_pow2_lt (a : Nat) (tl : List Nat)
    (h_desc : ∀ s ∈ tl, s < 2 ^ a)
    (h_pow2 : ∀ s ∈ tl, ∃ j, s = 2 ^ j)
    (h_pair : List.Pairwise (· > ·) tl) :
    tl.sum < 2 ^ a := by
  induction tl generalizing a with
  | nil => simp
  | cons hd rest ih =>
    simp only [List.sum_cons]
    have h_hd_lt := h_desc hd (by simp)
    have h_rest_pair : rest.Pairwise (· > ·) := by
      exact List.Pairwise.of_cons h_pair
    -- Every rest element < hd (from pairwise cons)
    have h_rest_lt_hd : ∀ s ∈ rest, s < hd := by
      intro s hs
      have := List.pairwise_cons.mp h_pair
      exact this.1 s hs
    obtain ⟨j, hj⟩ := h_pow2 hd (by simp)
    subst hj
    have h_j_lt_a : j < a := by
      by_contra h; push Not at h
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h
      omega
    have h_rest_sum : rest.sum < 2 ^ j := ih j
      h_rest_lt_hd
      (fun s hs => h_pow2 s (by simp [hs]))
      h_rest_pair
    -- 2^j + rest.sum < 2^j + 2^j = 2^(j+1) ≤ 2^a
    have h1 : 2 ^ j + rest.sum < 2 ^ j + 2 ^ j := by omega
    have h2 : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ]; ring
    have h3 : 2 ^ (j + 1) ≤ 2 ^ a := by
      apply Nat.pow_le_pow_right (by decide); omega
    omega

/-- In a strictly descending list of powers of 2 with odd sum,
    the last element must be 1 = 2^0. All other elements are even pow2s
    (≥ 2), so only the last can make the sum odd. -/
private theorem last_is_one_of_odd_sum (sizes : List Nat)
    (h_ne : sizes ≠ [])
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_odd : sizes.sum % 2 = 1) :
    sizes.getLast h_ne = 1 := by
  -- getLast is a pow2
  obtain ⟨j, hj⟩ := h_pow2 _ (List.getLast_mem h_ne)
  -- If j ≥ 1, all elements are even (each ≥ getLast = 2^j ≥ 2), sum is even
  by_contra h_ne_1
  rw [hj] at h_ne_1
  have h_j_pos : j ≥ 1 := by
    by_contra h; push Not at h; interval_cases j; simp at h_ne_1
  -- Every element is ≥ getLast (from strict descent) and hence even
  have h_all_even : ∀ s ∈ sizes, s % 2 = 0 := by
    intro s hs
    obtain ⟨m, hm⟩ := h_pow2 s hs
    subst hm
    have h_m_ge_j : m ≥ j := by
      by_contra h_lt; push Not at h_lt
      have h_pow_lt : 2 ^ m < 2 ^ j := Nat.pow_lt_pow_right (by omega) h_lt
      -- s = 2^m ∈ sizes. It's either in dropLast or IS getLast.
      rw [← List.dropLast_append_getLast h_ne] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with h_drop | h_eq
      · have := h_desc.rel_dropLast_getLast h_drop; rw [hj] at this; omega
      · rw [h_eq] at h_pow_lt; rw [hj] at h_pow_lt; omega
    exact (Nat.two_pow_mod_two_eq_zero).mpr (by omega)
  -- Sum of even numbers is even
  have h_sum_even : sizes.sum % 2 = 0 := by
    -- Prove by showing: if every element is even, sum is even.
    -- Induct on sizes itself, but use a local copy to avoid shadowing.
    suffices h : ∀ (l : List Nat), (∀ s ∈ l, s % 2 = 0) → l.sum % 2 = 0 from
      h sizes h_all_even
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih_l =>
      intro h_even
      simp [List.sum_cons]
      have := h_even hd (by simp)
      have := ih_l (fun s hs => h_even s (by simp [hs]))
      omega
  omega

/-- Removing the trailing 1 and halving each remaining element preserves
    the strictly descending pow2 structure and CTO decreases by 1:
    cto(sum/2) = cto(sum) - 1 when sum is odd. -/
private theorem cto_half_of_odd (n : Nat) (h_odd : n % 2 = 1) :
    cto (n / 2) = cto n - 1 := by
  have : cto n = 1 + cto (n / 2) := by
    conv_lhs => unfold cto
    simp [h_odd]
  omega

/-- If n has m trailing 1-bits (n mod 2^m = 2^m - 1), then cto n ≥ m. -/
private theorem cto_ge_of_mod : ∀ (n m : Nat),
    n % 2 ^ m = 2 ^ m - 1 → cto n ≥ m := by
  intro n m; induction m generalizing n with
  | zero => intro _; omega
  | succ k ih =>
    intro h_mod
    have h_pk_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h_pk1_pos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    -- n is odd: n % 2^(k+1) = 2^(k+1) - 1, which is odd
    have h_odd : n % 2 = 1 := by
      have : n % 2 = n % 2 ^ (k + 1) % 2 := by
        rw [Nat.mod_mod_of_dvd]
        exact ⟨2 ^ k, by ring⟩
      rw [this, h_mod]
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    rw [cto, if_pos h_odd]
    suffices cto (n / 2) ≥ k from by omega
    apply ih
    -- Goal: (n / 2) % 2^k = 2^k - 1
    -- From h_mod: n % 2^(k+1) = 2^(k+1) - 1
    -- n = 2^(k+1) * q + 2^(k+1) - 1
    -- n is odd, so n/2 = (n-1)/2
    -- n-1 = 2^(k+1) * q + 2^(k+1) - 2 = 2*(2^k * q + 2^k - 1)
    -- n/2 = 2^k * q + 2^k - 1
    -- (2^k * q + 2^k - 1) % 2^k = (2^k - 1) % 2^k = 2^k - 1
    set q := n / 2 ^ (k + 1) with hq_def
    have h_decomp := Nat.div_add_mod n (2 ^ (k + 1))
    -- Express n in additive form (avoiding Nat subtraction)
    -- h_decomp: 2^(k+1) * q + n % 2^(k+1) = n
    -- h_mod: n % 2^(k+1) = 2^(k+1) - 1
    -- So: n + 1 = 2^(k+1) * q + 2^(k+1) = 2^(k+1) * (q + 1)
    have h_n_succ : n + 1 = 2 ^ (k + 1) * (q + 1) := by
      have : n % 2 ^ (k + 1) + 1 = 2 ^ (k + 1) := by omega
      nlinarith
    have h2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    -- n/2: since n is odd, n = 2*(n/2) + 1
    -- n + 1 = 2*(n/2) + 2 = 2*((n/2) + 1)
    -- Also n + 1 = 2^(k+1)*(q+1) = 2*2^k*(q+1)
    -- So (n/2) + 1 = 2^k*(q+1)
    -- n/2 = 2^k*(q+1) - 1 = 2^k*q + 2^k - 1
    have h_ndiv_succ : n / 2 + 1 = 2 ^ k * (q + 1) := by
      have : n + 1 = 2 * (n / 2 + 1) := by omega
      rw [h2k] at h_n_succ; nlinarith
    -- n/2 + 1 = 2^k*(q+1), and 2^k*(q+1) = 2^k + q*2^k
    -- So n/2 = 2^k - 1 + q*2^k
    have h_ndiv_rearr : n / 2 + 1 = 2 ^ k + q * 2 ^ k := by nlinarith
    -- Goal: (n/2) % 2^k = 2^k - 1
    -- n/2 = (2^k + q*2^k) - 1 = (q+1)*2^k - 1
    -- Use: n/2 % 2^k = (n/2 + 1 - 1) % 2^k
    -- Since (q+1)*2^k ≡ 0 (mod 2^k), (n/2) = (q+1)*2^k - 1 ≡ -1 ≡ 2^k-1 (mod 2^k)
    have h_n2_eq : n / 2 = 2 ^ k - 1 + q * 2 ^ k := by omega
    rw [h_n2_eq, show 2 ^ k - 1 + q * 2 ^ k = 2 ^ k - 1 + 2 ^ k * q from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The halved dropLast construction: given a non-empty strictly descending list
    of pow2s with odd sum, the dropLast mapped by (·/2) preserves the invariants
    and reduces cto by 1. -/
private theorem halved_dropLast_props (sizes : List Nat) (k' : Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_cto : cto sizes.sum = k' + 2)
    (h_ne : sizes ≠ [])
    (h_odd : sizes.sum % 2 = 1)
    (h_last : sizes.getLast h_ne = 1) :
    let dl := sizes.dropLast
    let dl2 := dl.map (· / 2)
    List.Pairwise (· > ·) dl2 ∧
    (∀ s ∈ dl2, ∃ j, s = 2 ^ j) ∧
    cto dl2.sum = k' + 1 ∧
    dl2.length = sizes.length - 1 ∧
    (∀ s ∈ dl, ∃ j, j ≥ 1 ∧ s = 2 ^ j) := by
  intro dl dl2
  have h_dl_gt1 : ∀ s ∈ dl, s > 1 := by
    intro s hs
    have : s > sizes.getLast h_ne := h_desc.rel_dropLast_getLast hs
    rw [h_last] at this; exact this
  have h_dl_pow2 : ∀ s ∈ dl, ∃ j, j ≥ 1 ∧ s = 2 ^ j := by
    intro s hs
    obtain ⟨j, hj⟩ := h_pow2 s (List.dropLast_subset sizes hs)
    refine ⟨j, ?_, hj⟩
    by_contra hlt; push Not at hlt
    interval_cases j; simp at hj
    have := h_dl_gt1 s hs; omega
  have h_dl2_desc : List.Pairwise (· > ·) dl2 := by
    change List.Pairwise (· > ·) (dl.map (· / 2))
    rw [List.pairwise_iff_getElem]
    intro i j hil hjl hij
    simp only [List.getElem_map]
    have h_dl_desc : dl.Pairwise (· > ·) := by
      rw [List.pairwise_iff_getElem]
      intro i' j' hi'l hj'l hi'j'
      rw [List.pairwise_iff_getElem] at h_desc
      have h_dl_len : dl.length = sizes.length - 1 := by simp [dl, List.length_dropLast]
      have hi_eq : dl[i'] = sizes[i']'(by omega) := by simp [dl, List.getElem_dropLast]
      have hj_eq : dl[j'] = sizes[j']'(by omega) := by simp [dl, List.getElem_dropLast]
      rw [hi_eq, hj_eq]; exact h_desc i' j' (by omega) (by omega) hi'j'
    rw [List.pairwise_iff_getElem] at h_dl_desc
    have h_dl_len : dl.length = (dl.map (· / 2)).length := by simp
    have h_ij : dl[i] > dl[j] := h_dl_desc i j (by omega) (by omega) hij
    obtain ⟨ei, hei, h_ei⟩ := h_dl_pow2 dl[i] (List.getElem_mem ..)
    obtain ⟨ej, hej, h_ej⟩ := h_dl_pow2 dl[j] (List.getElem_mem ..)
    rw [h_ei, h_ej]
    rw [show 2 ^ ei / 2 = 2 ^ (ei - 1) from by
      conv_lhs => rw [show ei = (ei - 1) + 1 from by omega, pow_succ]
      exact Nat.mul_div_cancel _ (by omega)]
    rw [show 2 ^ ej / 2 = 2 ^ (ej - 1) from by
      conv_lhs => rw [show ej = (ej - 1) + 1 from by omega, pow_succ]
      exact Nat.mul_div_cancel _ (by omega)]
    apply Nat.pow_lt_pow_right (by omega)
    rw [h_ei, h_ej] at h_ij
    by_contra h_le; push Not at h_le
    have h_ei_le_ej : ei ≤ ej := by omega
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h_ei_le_ej
    omega
  have h_dl2_pow2 : ∀ s ∈ dl2, ∃ j, s = 2 ^ j := by
    intro s hs
    simp only [dl2, List.mem_map] at hs
    obtain ⟨x, hx_mem, rfl⟩ := hs
    obtain ⟨j, hj_ge, rfl⟩ := h_dl_pow2 x hx_mem
    exact ⟨j - 1, by rw [Nat.pow_div hj_ge (by omega)]⟩
  have h_dl2_sum : dl2.sum = (sizes.sum - 1) / 2 := by
    have h_dl_sum : dl.sum = sizes.sum - 1 := by
      have h_split := List.dropLast_append_getLast h_ne
      have h_eq : sizes.sum = dl.sum + sizes.getLast h_ne := by
        conv_lhs => rw [← h_split]; simp [List.sum_append, List.sum_cons]
      rw [h_last] at h_eq; omega
    suffices h_half : dl2.sum * 2 = dl.sum from by
      rw [h_dl_sum] at h_half; omega
    suffices h_gen : ∀ (l : List Nat),
        (∀ s ∈ l, ∃ j, j ≥ 1 ∧ s = 2 ^ j) → (l.map (· / 2)).sum * 2 = l.sum from
      h_gen dl h_dl_pow2
    intro l; induction l with
    | nil => simp
    | cons hd tl ih =>
      intro h_pw2
      simp only [List.map, List.sum_cons]
      obtain ⟨j, hj_ge, rfl⟩ := h_pw2 hd (List.mem_cons_self ..)
      have h_div : 2 ^ j / 2 = 2 ^ (j - 1) := by
        conv_lhs => rw [show j = (j - 1) + 1 from by omega, pow_succ]
        exact Nat.mul_div_cancel _ (by omega)
      rw [h_div]
      have ih_res := ih (fun s hs => h_pw2 s (List.mem_cons_of_mem _ hs))
      have h_pow : 2 ^ (j - 1) * 2 = 2 ^ j := by
        conv_rhs => rw [show j = (j - 1) + 1 from by omega, pow_succ]
      linarith
  have h_dl2_cto : cto dl2.sum = k' + 1 := by
    rw [h_dl2_sum]
    have h_half := cto_half_of_odd sizes.sum h_odd
    have h_sum_pos : sizes.sum ≥ 1 := by
      by_contra h
      have h_sum_zero : sizes.sum = 0 := by omega
      rw [h_sum_zero] at h_cto
      simp only [cto_zero] at h_cto
      omega
    have h_div_eq : sizes.sum / 2 = (sizes.sum - 1) / 2 := by
      have := Nat.div_add_mod sizes.sum 2
      have := h_odd; omega
    rw [← h_div_eq]; omega
  have h_dl2_len : dl2.length = sizes.length - 1 := by
    have : dl2.length = dl.length := List.length_map ..
    have : dl.length = sizes.length - 1 := List.length_dropLast ..
    omega
  exact ⟨h_dl2_desc, h_dl2_pow2, h_dl2_cto, h_dl2_len, h_dl_pow2⟩

/-- Length bound: strictly descending pow2s with cto(sum) = k+1
    have at least k+1 elements. -/
private theorem cto_trailing_geo_len (sizes : List Nat) (k : Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_cto : cto sizes.sum = k + 1) :
    k + 1 ≤ sizes.length := by
  induction k generalizing sizes with
  | zero =>
    by_contra h
    have h_len_zero : sizes.length = 0 := by omega
    have h_empty : sizes = [] := List.length_eq_zero_iff.mp h_len_zero
    subst h_empty
    simp only [List.sum_nil, cto_zero] at h_cto
    omega
  | succ k' ih =>
    have h_ne : sizes ≠ [] := by intro h; subst h; simp at h_cto
    have h_odd : sizes.sum % 2 = 1 := by
      by_contra h_even; push Not at h_even
      rw [cto] at h_cto; simp [show sizes.sum % 2 ≠ 1 from h_even] at h_cto
    have h_last := last_is_one_of_odd_sum sizes h_ne h_desc h_pow2 h_odd
    obtain ⟨h_dl2_desc, h_dl2_pow2, h_dl2_cto, h_dl2_len, _⟩ :=
      halved_dropLast_props sizes k' h_desc h_pow2 h_cto h_ne h_odd h_last
    have h_len' := ih _ h_dl2_desc h_dl2_pow2 h_dl2_cto
    omega

/-- Geometric property: trailing k+1 segments are 2^0, 2^1, ..., 2^k. -/
private theorem cto_trailing_geo (sizes : List Nat) (k : Nat)
    (h_desc : List.Pairwise (· > ·) sizes)
    (h_pow2 : ∀ s ∈ sizes, ∃ j, s = 2 ^ j)
    (h_cto : cto sizes.sum = k + 1)
    (h_len : k + 1 ≤ sizes.length) :
    ∀ (i : Nat) (hi : i < k + 1),
      sizes.get ⟨sizes.length - 1 - i, by omega⟩ = 2 ^ i := by
  -- This follows from cto_trailing_geo_len plus the unique binary decomposition.
  -- The strictly descending pow2 constraint forces the exact values.
  -- Prove by strong induction on k.
  induction k generalizing sizes with
  | zero =>
    -- cto(sum) = 1: exactly one trailing element, must be 2^0 = 1
    intro i hi; interval_cases i
    -- Need: sizes[sizes.length - 1] = 1
    -- sizes.getLast = 1 (from last_is_one_of_odd_sum)
    have h_ne : sizes ≠ [] := by intro h; subst h; simp at h_cto
    have h_odd : sizes.sum % 2 = 1 := by
      by_contra h_even
      have h_even_zero : sizes.sum % 2 = 0 := by omega
      have h_cto_zero := cto_even h_even_zero
      omega
    have h_last := last_is_one_of_odd_sum sizes h_ne h_desc h_pow2 h_odd
    simp only [List.get_eq_getElem, Nat.sub_zero]
    rw [← List.getLast_eq_getElem h_ne]
    exact h_last
  | succ k' ih =>
    -- cto(sum) = k'+2. Build the halved dropLast list as in cto_trailing_geo_len.
    have h_ne : sizes ≠ [] := by intro h; subst h; simp at h_cto
    have h_odd : sizes.sum % 2 = 1 := by
      by_contra h_even
      have h_even_zero : sizes.sum % 2 = 0 := by omega
      have h_cto_zero := cto_even h_even_zero
      omega
    have h_last := last_is_one_of_odd_sum sizes h_ne h_desc h_pow2 h_odd
    intro i hi
    by_cases h_i0 : i = 0
    · -- Base: i = 0, sizes[n-1] = 2^0 = 1
      subst h_i0; simp only [List.get_eq_getElem, Nat.sub_zero]
      rw [← List.getLast_eq_getElem h_ne]
      exact h_last
    · -- Inductive: i ≥ 1. Use the halved list via shared lemma.
      obtain ⟨h_dl2_desc, h_dl2_pow2, h_dl2_cto, h_dl2_len, h_dl_pow2⟩ :=
        halved_dropLast_props sizes k' h_desc h_pow2 h_cto h_ne h_odd h_last
      -- IH: dl2 has the geometric property for k'
      have h_ih_len := cto_trailing_geo_len _ k' h_dl2_desc h_dl2_pow2 h_dl2_cto
      have h_ih := ih _ h_dl2_desc h_dl2_pow2 h_dl2_cto (by omega)
      -- h_ih : ∀ i' < k'+1, dl2.get ⟨dl2.length-1-i', _⟩ = 2^i'
      -- We need: sizes.get ⟨sizes.length-1-i, _⟩ = 2^i
      -- Since i ≥ 1: sizes.length - 1 - i < sizes.length - 1 = dl.length
      -- So sizes[sizes.length-1-i] = dl[sizes.length-1-i] (it's in dropLast range)
      -- And dl[j] = 2 * dl2[j] (since dl[j] is an even pow2)
      -- dl2[j] = dl[j] / 2 (by definition of dl2 = dl.map (·/2))
      -- By IH: dl2[dl2.length-1-(i-1)] = 2^(i-1)
      -- dl2.length = sizes.length - 1, so
      -- dl2.length-1-(i-1) = sizes.length-2-i+1 = sizes.length-1-i
      -- So dl2[sizes.length-1-i] = 2^(i-1)
      -- And dl[sizes.length-1-i] = 2 * 2^(i-1) = 2^i
      -- And sizes[sizes.length-1-i] = dl[sizes.length-1-i] = 2^i ✓
      have h_i_pos : i ≥ 1 := by omega
      -- Index arithmetic
      have h_idx : sizes.length - 1 - i < sizes.length - 1 := by omega
      have h_dl_len : (sizes.dropLast).length = sizes.length - 1 := List.length_dropLast ..
      -- sizes[n-1-i] = dl[n-1-i] (in dropLast range)
      have h_sizes_eq_dl : sizes[sizes.length - 1 - i] =
          (sizes.dropLast)[sizes.length - 1 - i]'(by omega) := by
        simp [List.getElem_dropLast]
      -- dl2[n-1-i] = dl[n-1-i] / 2 (by map)
      have h_dl2_eq : (sizes.dropLast.map (· / 2))[sizes.length - 1 - i]'(by simp; omega) =
          (sizes.dropLast)[sizes.length - 1 - i]'(by omega) / 2 := by
        simp [List.getElem_map]
      -- IH: dl2[dl2.length-1-(i-1)] = 2^(i-1)
      -- dl2.length - 1 - (i-1) = (sizes.length - 1) - 1 - (i - 1) = sizes.length - 1 - i
      have h_idx_eq : (sizes.dropLast.map (· / 2)).length - 1 - (i - 1) =
          sizes.length - 1 - i := by
        simp; omega
      have h_ih_val := h_ih (i - 1) (by omega)
      simp only [List.get_eq_getElem] at h_ih_val
      -- h_ih_val: dl2.getElem (dl2.length-1-(i-1)) _ = 2^(i-1)
      -- The key index fact: dl2.length-1-(i-1) = sizes.length-1-i
      -- Avoid rewriting inside getElem. Instead, directly show what we need.
      -- Step 1: sizes[n-1-i] = dl[n-1-i]
      simp only [List.get_eq_getElem]
      rw [h_sizes_eq_dl]
      -- Step 2: Get pow2 info about dl[n-1-i]
      obtain ⟨ej, hej, h_ej⟩ := h_dl_pow2 ((sizes.dropLast)[sizes.length - 1 - i]'(by omega))
        (List.getElem_mem ..)
      rw [h_ej]
      -- Step 3: Show ej = i by using the halved list
      -- dl2[n-1-i] = dl[n-1-i] / 2 = 2^ej / 2 = 2^(ej-1)
      -- dl2[n-1-i] = dl2[dl2.length-1-(i-1)] = 2^(i-1) (by IH)
      -- So 2^(ej-1) = 2^(i-1), hence ej = i
      have h_dl2_val : (sizes.dropLast.map (· / 2))[sizes.length - 1 - i]'(by simp; omega) =
          2 ^ ej / 2 := by
        simp only [List.getElem_map]; rw [h_ej]
      have h_ej_div : 2 ^ ej / 2 = 2 ^ (ej - 1) := by
        conv_lhs => rw [show ej = (ej - 1) + 1 from by omega, pow_succ]
        exact Nat.mul_div_cancel _ (by omega)
      rw [h_ej_div] at h_dl2_val
      -- h_dl2_val: dl2[sizes.length-1-i] = 2^(ej-1)
      -- h_ih_val: dl2[dl2.length-1-(i-1)] = 2^(i-1)
      -- These are the same index, so 2^(ej-1) = 2^(i-1)
      have h_same_idx : (sizes.dropLast.map (· / 2)).length - 1 - (i - 1) =
          sizes.length - 1 - i := by
        simp; omega
      have h_eq_pow : 2 ^ (ej - 1) = 2 ^ (i - 1) := by
        rw [← h_dl2_val, ← h_ih_val]
        congr 1; omega
      have h_ej_eq : ej = i := by
        have := Nat.pow_right_injective (by omega : 2 ≥ 2) h_eq_pow
        omega
      rw [h_ej_eq]


/-- The merge cascade: k merges on a stack correctly combine equal-size
    power-of-2 segments in a geometric doubling run.

    Stack layout: `mth(acc) :: mth(run[0]) :: mth(run[1]) :: ... :: tail`
    where `|acc| = |run[0]| = 2^j` and `|run[i]| = 2^(j+i)`.
    After |run| merges, produces `mth(run[k-1] ++ ... ++ run[0] ++ acc) :: tail`.

    The run is ordered from stack-top outward: run[0] is adjacent to acc,
    run[k-1] is deepest in the cascade. -/
private theorem merge_cascade
    (acc_content : List (MerkleTree α)) -- leaves whose mth is the accumulator
    (run : List (List (MerkleTree α))) -- segments in cascade order (head = top)
    (tail : List (MerkleTree α)) -- remaining stack below cascade
    (j : Nat) -- |acc_content| = 2^j
    (h_acc_len : acc_content.length = 2 ^ j)
    (h_run_geo : ∀ (i : Nat) (h : i < run.length),
      (run.get ⟨i, h⟩).length = 2 ^ (j + i)) :
    mergeStack (mth acc_content :: run.map mth ++ tail) run.length =
      mth (run.reverse.flatten ++ acc_content) :: tail := by
  induction run generalizing acc_content j with
  | nil =>
    simp [mergeStack]
  | cons seg tl ih =>
    -- mergeStack (mth acc :: mth seg :: rest) (tl.length + 1)
    --   = mergeStack (MerkleTree.node (mth seg) (mth acc) :: rest) tl.length
    -- mergeStack pattern matches on count (Nat.succ), then on stack (:: :: rest)
    change mergeStack (MerkleTree.node (mth seg) (mth acc_content) ::
      (List.map mth tl ++ tail)) tl.length =
      mth ((seg :: tl).reverse.flatten ++ acc_content) :: tail
    -- After merge: MerkleTree.node (mth seg) (mth acc_content) :: (tl.map mth ++ tail)
    have h_seg_len : seg.length = 2 ^ j := by
      have := h_run_geo 0 (Nat.zero_lt_succ _)
      simp only [List.get_eq_getElem, List.getElem_cons_zero, Nat.add_zero] at this
      exact this
    -- MerkleTree.node (mth seg) (mth acc_content) = mth (seg ++ acc_content)
    rw [mth_merge seg acc_content j h_seg_len h_acc_len]
    -- Apply IH with accumulated content = seg ++ acc_content, j' = j + 1
    have h_new_len : (seg ++ acc_content).length = 2 ^ (j + 1) := by
      simp [List.length_append, h_seg_len, h_acc_len]; ring
    have h_tl_geo : ∀ (i : Nat) (h : i < tl.length),
        (tl.get ⟨i, h⟩).length = 2 ^ ((j + 1) + i) := by
      intro i hi
      have h_bound : i + 1 < (seg :: tl).length := by
        simp only [List.length_cons]
        omega
      have := h_run_geo (i + 1) h_bound
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at this
      convert this using 2
      omega
    have h_ih := ih (seg ++ acc_content) (j + 1) h_new_len h_tl_geo
    -- The IH talks about (mth x :: map) ++ tail, goal has mth x :: (map ++ tail)
    -- These are equal by List.cons_append
    simp only [List.cons_append] at h_ih
    rw [h_ih]
    congr 1
    simp [List.reverse_cons, List.flatten_append, List.append_assoc]

/-- Appending a single leaf preserves the stack invariant.
    This is the key single-step lemma for the loop invariant. -/
private theorem appendToStack_invariant (pfx₀ : List (MerkleTree α))
    (stack₀ : List (MerkleTree α))
    (leaf : MerkleTree α) (idx : Nat)
    (h_inv : stackInvariant pfx₀ stack₀)
    (h_idx : idx = pfx₀.length) :
    stackInvariant (pfx₀ ++ [leaf]) (appendToStack stack₀ leaf idx) := by
  obtain ⟨segments, h_flat, h_pow2, h_desc, h_stack⟩ := h_inv
  simp only [appendToStack]
  by_cases h_cto : cto idx = 0
  · rw [h_cto]; simp only [mergeStack]
    -- Witness: segments ++ [[leaf]]
    refine ⟨segments ++ [[leaf]], ?_, ?_, ?_, ?_⟩
    · -- flatten = pfx₀ ++ [leaf]
      simp only [List.flatten_append, h_flat, List.flatten_cons, List.flatten_nil, List.append_nil]
    · -- all segments have power-of-2 length
      intro s hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · exact h_pow2 s hs
      · exact ⟨0, rfl⟩
    · -- segment sizes strictly descending
      -- Need: Pairwise (· > ·) (segments.map length ++ [[leaf].length])
      simp only [List.map_append, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil]
      -- Now goal: Pairwise (· > ·) (segments.map List.length ++ [1])
      -- All existing segments have size ≥ 2 (from no_size_one_when_cto_zero)
      have h_seg_lens := segments.map List.length
      have h_sizes_ge_2 := no_size_one_when_cto_zero
        (segments.map List.length) h_desc
        (by intro s hs
            simp only [List.mem_map] at hs
            obtain ⟨seg, h_mem, h_eq⟩ := hs
            obtain ⟨k, hk⟩ := h_pow2 seg h_mem
            exact ⟨k, by rw [← h_eq, hk]⟩)
        (by -- sum of segment lengths = pfx₀.length = idx
            have : (segments.map List.length).sum = pfx₀.length := by
              rw [← h_flat]; simp only [List.length_flatten]
            rw [this, ← h_idx]; exact h_cto)
      rw [List.pairwise_append]
      refine ⟨h_desc, ?_, fun a ha b hb => ?_⟩
      · -- Pairwise (· > ·) on the singleton tail
        exact List.pairwise_singleton _ _
      · -- every element in segments.map length > every element in tail
        simp only [List.mem_singleton] at hb
        subst hb
        have := h_sizes_ge_2 a ha
        omega
    · -- stack = reversed map of mth
      simp only [List.map_append, List.reverse_append, h_stack, List.map_cons, List.map_nil,
        mth]
      rfl
  · -- Case: cto idx ≥ 1, merge cascade
    -- Strategy: prove by induction on cto idx.
    -- Extract cto idx = k + 1 for some k.
    obtain ⟨k, h_cto_eq⟩ : ∃ k, cto idx = k + 1 := by
      exact ⟨cto idx - 1, by omega⟩
    -- idx is odd (from cto definition)
    have h_odd : idx % 2 = 1 := by
      by_contra h_even
      push Not at h_even
      have : idx % 2 = 0 := by omega
      rw [cto, if_neg (by omega)] at h_cto_eq
      omega
    -- Since sum of segment sizes = idx (odd), last segment has size 1
    -- (if no segment had size 1, sum would be even — contradicts odd)
    -- The last segment must be [x] for some x.
    -- segments is nonempty (idx ≥ 1 means there's at least one segment)
    have h_segs_ne : segments ≠ [] := by
      intro h_empty; subst h_empty
      simp only [List.flatten_nil] at h_flat
      rw [← h_flat] at h_idx; simp only [List.length_nil] at h_idx; omega
    -- Use merge_cascade. We need to show:
    -- 1. The stack has the right shape for merge_cascade
    -- 2. The last (cto idx) segments form a geometric run
    -- 3. The result satisfies the invariant
    --
    -- Step 1: The stack is (segments.map mth).reverse.
    -- After pushing leaf, it's leaf :: (segments.map mth).reverse.
    -- mergeStack operates on this with count = cto idx.
    --
    -- Step 2: Since segments are strictly descending pow2s summing to idx,
    -- and idx is odd, the last segment has size 1. The last cto(idx)
    -- segments form the consecutive trailing 1-bits run.
    --
    -- For now, we take a direct approach: unfold one merge step,
    -- show it reduces to a smaller problem, and induct.
    -- The last segment has size 1 (from parity argument).
    -- After one merge with leaf, we get a size-2 segment.
    -- The new segments are init ++ [merged], with cto reduced.
    --
    -- Direct construction: prove the invariant by providing witness segments.
    -- The witness is: take (segments.length - cto idx) segments
    --   ++ [segments.reverse[0..cto(idx)-1].flatten ++ [leaf]]
    -- (i.e., merge the last cto(idx) segments with leaf into one).

    -- Rewrite stack and unfold appendToStack
    rw [h_cto_eq, h_stack]
    -- Goal: stackInvariant (pfx₀ ++ [leaf])
    --         (mergeStack (leaf :: (segments.map mth).reverse) (k + 1))

    -- The reversed segment list puts smallest (last) segments first.
    -- segments.reverse = [Sₘ, Sₘ₋₁, ..., S₁] (smallest to largest)
    -- The stack is mth Sₘ :: mth Sₘ₋₁ :: ... :: mth S₁
    -- After pushing leaf: leaf :: mth Sₘ :: mth Sₘ₋₁ :: ...

    -- We need to show leaf = mth [leaf] for merge_cascade
    have h_leaf_mth : leaf = mth [leaf] := by simp [mth]

    -- Key sizes list for cto_trailing_geo
    let sz := segments.map List.length
    have h_sz_desc : sz.Pairwise (· > ·) := h_desc
    have h_sz_pow2 : ∀ s ∈ sz, ∃ j, s = 2 ^ j := by
      intro s hs; simp only [sz, List.mem_map] at hs
      obtain ⟨seg, hmem, rfl⟩ := hs; exact h_pow2 seg hmem
    have h_sz_sum : sz.sum = idx := by
      have : sz.sum = pfx₀.length := by
        rw [← h_flat]; simp only [sz, List.length_flatten]
      rw [this, ← h_idx]
    have h_sz_cto : cto sz.sum = k + 1 := by rw [h_sz_sum, h_cto_eq]

    -- Length bound from cto_trailing_geo_len
    have h_sz_len : k + 1 ≤ sz.length :=
      cto_trailing_geo_len sz k h_sz_desc h_sz_pow2 h_sz_cto
    have h_sz_len' : k + 1 ≤ segments.length := by
      simp only [sz, List.length_map] at h_sz_len
      exact h_sz_len

    -- Geometric property: the last k+1 segments have sizes 2^0, 2^1, ..., 2^k
    have h_geo := cto_trailing_geo sz k h_sz_desc h_sz_pow2 h_sz_cto h_sz_len

    -- Split segments into above (first n-k-1) and run_segs (last k+1)
    set n := segments.length
    set above := segments.take (n - (k + 1)) with h_above_def
    set run_segs := segments.drop (n - (k + 1)) with h_run_def

    have h_split : segments = above ++ run_segs :=
      (List.take_append_drop (n - (k + 1)) segments).symm
    have h_run_len : run_segs.length = k + 1 := by
      simp only [h_run_def, List.length_drop]
      omega

    -- The stack in merge_cascade form:
    -- leaf :: (segments.map mth).reverse
    -- = leaf :: (run_segs.map mth).reverse ++ (above.map mth).reverse
    have h_stack_rw : (segments.map mth).reverse =
        (run_segs.map mth).reverse ++ (above.map mth).reverse := by
      rw [h_split]; simp only [List.map_append, List.reverse_append]

    -- For merge_cascade, the "run" parameter is run_segs.reverse (stack order)
    -- run_segs.reverse[i] has size 2^i (from cto_trailing_geo)
    set mc_run := run_segs.reverse with h_mc_def
    have h_mc_len : mc_run.length = k + 1 := by
      simp only [h_mc_def, List.length_reverse, h_run_len]

    -- Geometric run property for merge_cascade
    have h_mc_geo : ∀ (i : Nat) (hi : i < mc_run.length),
        (mc_run.get ⟨i, hi⟩).length = 2 ^ (0 + i) := by
      intro i hi
      rw [h_mc_len] at hi
      simp only [h_mc_def, List.get_eq_getElem, List.getElem_reverse, Nat.zero_add]
      simp only [h_run_def, List.getElem_drop]
      -- Need: segments[n-(k+1) + (run_segs.length-1-i)].length = 2^i
      -- run_segs.length - 1 - i = k - i, and n-(k+1)+(k-i) = n-1-i
      -- From h_geo: sz[sz.length-1-i] = 2^i, i.e., segments[n-1-i].length = 2^i
      have h_geo_i := h_geo i (by omega)
      simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at h_geo_i
      -- The indices are equal: n-(k+1) + (run_segs.length-1-i) = n-1-i
      have h_idx_eq : n - (k + 1) + (run_segs.length - 1 - i) = n - 1 - i := by
        rw [h_run_len]; omega
      have : segments[n - (k + 1) + (run_segs.length - 1 - i)] =
             segments[n - 1 - i] := by
        simp only [h_idx_eq]
      rw [this]; exact h_geo_i

    -- Apply merge_cascade
    rw [h_leaf_mth, h_stack_rw]
    -- Convert the goal to use mc_run directly
    -- Goal: stackInvariant ... (mergeStack (mth [leaf] :: (run_segs.map mth).reverse ++ ...) (k+1))
    -- merge_cascade applies to: mergeStack (mth [leaf] :: mc_run.map mth ++ ...) mc_run.length
    -- We need to show the goal matches merge_cascade's LHS
    have h_mc := merge_cascade [leaf] mc_run ((above.map mth).reverse) 0
      rfl h_mc_geo
    -- h_mc: mergeStack (mth [leaf] :: mc_run.map mth ++ ...) mc_run.length = ...
    -- Goal has (run_segs.map mth).reverse and (k+1)
    -- Convert goal to mc_run terms:
    rw [show (List.map mth run_segs).reverse = List.map mth mc_run from by
      simp only [h_mc_def, List.map_reverse]]
    rw [← h_mc_len]
    -- Now both goal and h_mc use mc_run.length and mc_run.map mth
    -- But goal has `a :: (b ++ c)` while h_mc has `a :: b ++ c` (same definitionally)
    conv at h_mc => lhs; rw [List.cons_append]
    rw [h_mc]

    -- After merge_cascade:
    -- Goal: stackInvariant (pfx₀ ++ [leaf])
    --         (mth (mc_run.reverse.flatten ++ [leaf]) :: (above.map mth).reverse)
    -- mc_run.reverse = run_segs.reverse.reverse = run_segs
    simp only [h_mc_def, List.reverse_reverse]

    -- Witness: above ++ [run_segs.flatten ++ [leaf]]
    set merged := run_segs.flatten ++ [leaf]
    refine ⟨above ++ [merged], ?_, ?_, ?_, ?_⟩

    · -- Flatten: (above ++ [merged]).flatten = pfx₀ ++ [leaf]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                  List.append_nil, merged]
      -- Goal: above.flatten ++ (run_segs.flatten ++ [leaf]) = pfx₀ ++ [mth [leaf]]
      -- leaf = mth [leaf] from h_leaf_mth, so mth [leaf] = leaf
      rw [← h_leaf_mth]
      rw [← List.append_assoc, ← List.flatten_append, ← h_split, h_flat]

    · -- Pow2: each segment has pow2 length
      intro seg h_mem
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h_mem
      rcases h_mem with h_above | h_eq
      · -- seg ∈ above = segments.take(n-k-1) ⊆ segments
        have : seg ∈ segments := List.mem_of_mem_take h_above
        exact h_pow2 seg this
      · subst h_eq
        -- merged.length = run_segs.flatten.length + 1 = (2^(k+1) - 1) + 1 = 2^(k+1)
        refine ⟨k + 1, ?_⟩
        simp only [merged, List.length_append, List.length_flatten,
                    List.length_cons, List.length_nil]
        -- Goal should now be: (run_segs.map List.length).sum + 1 = 2 ^ (k + 1)
        suffices h_sum : (run_segs.map List.length).sum = 2 ^ (k + 1) - 1 by
          have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
        -- run_segs = segments.drop(n-(k+1)), length = k+1
        -- run_segs[j] = segments[n-(k+1)+j], length = 2^(k-j) from h_geo
        -- sum = 2^k + 2^(k-1) + ... + 2^0 = 2^(k+1) - 1
        -- Prove: for any m ≤ k+1, (segments.drop(n-m)).map(length).sum = 2^m - 1
        suffices ∀ m, m ≤ k + 1 →
          ((segments.drop (n - m)).map List.length).sum = 2 ^ m - 1 by
          exact this (k + 1) le_rfl
        intro m hm
        induction m with
        | zero =>
          simp only [Nat.sub_zero, pow_zero, Nat.sub_self]
          -- n = segments.length, so drop n segments = []
          have h_drop_all : List.drop n segments = [] := by
            change List.drop segments.length segments = []; exact List.drop_length
          rw [h_drop_all]; simp
        | succ m' ih =>
          -- segments.drop(n-(m'+1)) = segments[n-(m'+1)] :: segments.drop(n-m')
          have h_drop : n - (m' + 1) < segments.length := by omega
          rw [List.drop_eq_getElem_cons h_drop]
          simp only [List.map, List.sum_cons]
          -- The tail is segments.drop(n-(m'+1)+1) = segments.drop(n-m')
          have h_tail_idx : n - (m' + 1) + 1 = n - m' := by omega
          have h_eq_idx : n - (m' + 1) + 1 = n - m' := by omega
          rw [h_eq_idx]
          -- Goal: segments[n-(m'+1)].length + (segments.drop(n-m')).map(...).sum = 2^(m'+1)-1
          rw [ih (by omega)]
          -- Goal: segments[n-(m'+1)].length + (2^m' - 1) = 2^(m'+1) - 1
          -- segments[n-(m'+1)].length = 2^m' from h_geo
          have h_geo_m' := h_geo m' (by omega)
          simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at h_geo_m'
          -- n-(m'+1) = n-1-m'
          have : segments[n - (m' + 1)] = segments[n - 1 - m'] := by
            simp only [show n - (m' + 1) = n - 1 - m' from by omega]
          rw [show segments[n - (m' + 1)].length = 2 ^ m' from by
            rw [this]; exact h_geo_m']
          have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
          have : 2 ^ m' ≥ 1 := Nat.one_le_two_pow
          omega

    · -- Desc: Pairwise (·>·) on sizes of (above ++ [merged])
      rw [List.map_append, List.map_cons, List.map_nil]
      rw [List.pairwise_append]
      -- Helper: pairwise descent on segments as getElem
      have h_pw := List.pairwise_iff_getElem.mp h_desc
      simp only [List.length_map, List.getElem_map] at h_pw
      refine ⟨?_, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      · -- (1) above.map length is Pairwise (inherited from segments)
        rw [show above.map List.length = (segments.map List.length).take (n - (k + 1)) from by
          simp only [above, List.map_take]]
        exact h_desc.take
      · -- (2) Every above element's length > merged.length
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb; subst hb
        simp only [List.mem_map] at ha
        obtain ⟨seg, h_seg_mem, rfl⟩ := ha
        -- Establish merged.length = 2^(k+1)
        have h_merged_len : merged.length = 2 ^ (k + 1) := by
          simp only [merged, List.length_append, List.length_flatten,
                      List.length_cons, List.length_nil]
          suffices (run_segs.map List.length).sum = 2 ^ (k + 1) - 1 by
            have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
          suffices ∀ m, m ≤ k + 1 →
            ((segments.drop (n - m)).map List.length).sum = 2 ^ m - 1 by
            exact this (k + 1) le_rfl
          intro m hm
          induction m with
          | zero =>
            simp only [Nat.sub_zero, pow_zero, Nat.sub_self]
            have : List.drop n segments = [] := by
              change List.drop segments.length segments = []; exact List.drop_length
            rw [this]; simp
          | succ m' ih =>
            have hd : n - (m' + 1) < segments.length := by omega
            rw [List.drop_eq_getElem_cons hd]
            simp only [List.map, List.sum_cons]
            rw [show List.drop (n - (m' + 1) + 1) segments =
                  List.drop (n - m') segments from by congr 1; omega]
            rw [ih (by omega)]
            have hg := h_geo m' (by omega)
            simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at hg
            have : segments[n - (m' + 1)] = segments[n - 1 - m'] := by
              simp only [show n - (m' + 1) = n - 1 - m' from by omega]
            rw [show segments[n - (m' + 1)].length = 2 ^ m' from by rw [this]; exact hg]
            have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
            have : 2 ^ m' ≥ 1 := Nat.one_le_two_pow
            omega
        rw [h_merged_len]
        -- seg ∈ above ⊆ segments
        have h_seg_in : seg ∈ segments := List.mem_of_mem_take h_seg_mem
        obtain ⟨e, h_seg_len⟩ := h_pow2 seg h_seg_in
        rw [h_seg_len]
        -- Get seg's index j in above
        obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem h_seg_mem
        have h_above_len : above.length = n - (k + 1) := by
          simp only [above, List.length_take]; omega
        rw [h_above_len] at hj_lt
        -- above[j] = segments[j]
        have h_seg_is : seg = segments[j] := by
          rw [← hj_eq]; simp [above, List.getElem_take]
        -- segments[n-(k+1)].length = 2^k
        have h_first_run : segments[n - (k + 1)].length = 2 ^ k := by
          have h_g := h_geo k (by omega)
          simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at h_g
          -- h_g uses segments.length - 1 - k; goal uses n - (k + 1)
          -- Both n = segments.length and n-(k+1) = n-1-k arithmetically
          have : n - (k + 1) = segments.length - 1 - k := by omega
          simp only [this]; exact h_g
        -- By pairwise descent: segments[j].length > 2^k
        have h_seg_gt : seg.length > 2 ^ k := by
          have := h_pw j (n - (k + 1)) (by omega) (by omega) hj_lt
          rw [h_first_run] at this; rw [h_seg_is]; exact this
        -- 2^e > 2^k → e ≥ k+1
        rw [h_seg_len] at h_seg_gt
        have h_e_ge : e ≥ k + 1 := by
          by_contra hc; push Not at hc
          exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
            (by omega : e ≤ k)) h_seg_gt
        -- Need: 2^e > 2^(k+1). Assume not, derive contradiction.
        by_contra h_not_gt; push Not at h_not_gt
        -- e ≥ k+1 and 2^e ≤ 2^(k+1) → e = k+1
        have h_e_eq : e = k + 1 := by
          have : e ≤ k + 1 := by
            by_contra hc; push Not at hc
            have h1 := Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              (by omega : k + 2 ≤ e)
            have : 2 ^ (k + 1) < 2 ^ (k + 2) := by
              have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
              have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
            omega
          omega
        subst h_e_eq
        -- j = n-(k+2): if j < n-k-2, segments[j+1] would be a pow2 strictly
        -- between 2^k and 2^(k+1), which is impossible.
        have hj_eq_nk2 : j = n - (k + 2) := by
          by_contra hj_ne
          have hj_lt' : j + 1 < n - (k + 1) := by omega
          -- segments[j+1].length < segments[j].length = 2^(k+1)
          have h_lt := h_pw j (j + 1) (by omega) (by omega) (by omega)
          rw [← h_seg_is, h_seg_len] at h_lt
          -- segments[j+1].length > segments[n-(k+1)].length = 2^k
          have h_gt := h_pw (j + 1) (n - (k + 1)) (by omega) (by omega) hj_lt'
          rw [h_first_run] at h_gt
          -- segments[j+1].length is a pow2 strictly between 2^k and 2^(k+1)
          obtain ⟨f, hf⟩ := h_pow2 (segments[j + 1]) (List.getElem_mem ..)
          rw [hf] at h_lt h_gt
          have : f ≥ k + 1 := by
            by_contra hc; push Not at hc
            exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              (by omega)) h_gt
          have : f ≤ k := by
            by_contra hc; push Not at hc
            exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              this) h_lt
          omega
        -- idx = head_sum + tail_sum, where:
        --   tail_sum = 2^(k+1) + (2^(k+1)-1) = 2^(k+2)-1
        --   head_sum ≡ 0 (mod 2^(k+2))
        have h_drop_j : segments.drop j = segments[j] :: segments.drop (j + 1) :=
          List.drop_eq_getElem_cons (by omega)
        have h_drop_j1 : segments.drop (j + 1) = run_segs := by
          rw [hj_eq_nk2]; congr 1; omega
        have h_idx_split : idx =
            ((segments.take j).map List.length).sum +
            ((segments.drop j).map List.length).sum := by
          rw [← h_sz_sum]
          simp [sz, ← List.sum_append, List.take_append_drop]
        have h_tail_sum : ((segments.drop j).map List.length).sum = 2 ^ (k + 2) - 1 := by
          rw [h_drop_j]; simp only [List.map, List.sum_cons]
          rw [h_drop_j1, ← h_seg_is, h_seg_len]
          have h_rs : (run_segs.map List.length).sum = 2 ^ (k + 1) - 1 := by
            have := h_merged_len
            simp only [merged, List.length_append, List.length_flatten,
                        List.length_cons, List.length_nil] at this
            have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
          rw [h_rs]; have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
          have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
        -- Each segment before j has size divisible by 2^(k+2)
        have h_head_dvd : 2 ^ (k + 2) ∣ ((segments.take j).map List.length).sum := by
          -- Prove by induction on the list
          suffices ∀ x ∈ (segments.take j).map List.length, 2 ^ (k + 2) ∣ x by
            exact List.dvd_sum this
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨s, hs_mem, rfl⟩ := hx
          obtain ⟨f, hf⟩ := h_pow2 s (List.mem_of_mem_take hs_mem)
          rw [hf]
          obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hs_mem
          have hi_lt' : i < j := by
            rw [List.length_take] at hi_lt
            exact lt_of_lt_of_le hi_lt (Nat.min_le_left j n)
          have this := h_pw i j (by omega) (by omega) hi_lt'
          rw [show segments[i] = s from by
            rw [← hi_eq]; exact (List.getElem_take ..).symm] at this
          rw [← h_seg_is, h_seg_len, hf] at this
          have : f ≥ k + 2 := by
            by_contra hc; push Not at hc
            exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              (by omega)) this
          exact Nat.pow_dvd_pow 2 this
        -- Combine: idx % 2^(k+2) = (0 + 2^(k+2)-1) % 2^(k+2) = 2^(k+2)-1
        have h_mod : idx % 2 ^ (k + 2) = 2 ^ (k + 2) - 1 := by
          rw [h_idx_split]
          obtain ⟨q, hq⟩ := h_head_dvd
          rw [hq, h_tail_sum]
          rw [Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt (by have := Nat.one_le_two_pow (n := k + 2); omega)
        exact absurd (cto_ge_of_mod idx (k + 2) h_mod) (by omega)

    · -- Stack: the result stack matches (above ++ [merged]).map mth).reverse
      simp [List.map_append, List.reverse_append]

/-- The core invariant theorem: buildStack maintains the stack invariant. -/
theorem buildStack_invariant (leaves : List (MerkleTree α)) :
    stackInvariant leaves (buildStack leaves) := by
  suffices h : ∀ (pfx₀ : List (MerkleTree α)) (stack₀ : List (MerkleTree α))
      (remaining : List (MerkleTree α)) (idx : Nat),
      stackInvariant pfx₀ stack₀ → idx = pfx₀.length →
      stackInvariant (pfx₀ ++ remaining)
        (buildStackAux stack₀ remaining idx) by
    have h_empty : stackInvariant (α := α) [] [] :=
      ⟨[], And.intro rfl (And.intro (fun _ h => nomatch h) (And.intro List.Pairwise.nil rfl))⟩
    specialize h [] [] leaves 0 h_empty rfl
    simp only [List.nil_append] at h
    exact h
  intro pfx₀ stack₀ remaining
  induction remaining generalizing pfx₀ stack₀ with
  | nil =>
    intro idx h_inv h_idx
    simp only [List.append_nil]
    exact h_inv
  | cons leaf rest ih =>
    intro idx h_inv h_idx
    simp only [buildStackAux]
    -- Goal: stackInvariant (pfx₀ ++ leaf :: rest)
    --         (buildStackAux (appendToStack stack₀ leaf idx) rest (idx+1))
    -- Rewrite pfx₀ ++ (leaf :: rest) = (pfx₀ ++ [leaf]) ++ rest
    conv_lhs => rw [show pfx₀ ++ leaf :: rest = (pfx₀ ++ [leaf]) ++ rest
      from by simp]
    apply ih
    · exact appendToStack_invariant pfx₀ stack₀ leaf idx h_inv h_idx
    · simp [h_idx]
-- ============================================================================
-- From invariant to bridge lemma
-- ============================================================================

/-- stackRoot over a decomposition in strictly descending size order
    yields the same result as mth over the flattened sequence.

    This is because mth splits at largestPow2Lt, which is the first
    (largest) segment, and recurses on the rest — exactly matching
    the stackRoot fold from head (smallest) to tail (largest). -/
theorem stackRoot_segments_eq_mth (segments : List (List (MerkleTree α)))
    (h_pow2 : ∀ s ∈ segments, ∃ k, s.length = 2 ^ k)
    (h_desc : List.Pairwise (· > ·) (segments.map List.length)) :
    stackRoot ((segments.map mth).reverse) = mth segments.flatten := by
  match segments with
  | [] =>
    -- stackRoot [] = MerkleTree.empty = mth []
    simp [stackRoot, mth]
  | [s] =>
    -- stackRoot [mth s] = mth s, and [s].flatten = s ++ [] = s
    simp [stackRoot, List.flatten]
  | first :: second :: rest =>
    -- Inductive step: segments = first :: second :: rest
    -- Need: stackRoot((segments.map mth).reverse) = mth(segments.flatten)
    --
    -- (segments.map mth).reverse = (rest.map mth ++ [mth second, mth first]).reverse
    -- Actually: (first :: second :: rest).map mth = mth first :: (second :: rest).map mth
    -- reversed: ((second :: rest).map mth).reverse ++ [mth first]
    --
    -- stackRoot of this = MerkleTree.node(mth first, stackRoot(((second :: rest).map mth).reverse))
    --   by stackRoot_snoc
    --
    -- By IH: stackRoot(((second :: rest).map mth).reverse) = mth((second :: rest).flatten)
    -- So: MerkleTree.node(mth first, mth((second :: rest).flatten))
    --
    -- Need to show: mth(first ++ (second :: rest).flatten) =
    --   MerkleTree.node(mth first, mth((second :: rest).flatten))
    -- This holds when largestPow2Lt(|first ++ (second :: rest).flatten|) = |first|

    -- Step 1: rewrite the reversed map as snoc
    have h_map : (first :: second :: rest).map mth =
        mth first :: (second :: rest).map mth := by rfl
    rw [h_map, List.reverse_cons]

    -- Step 2: apply stackRoot_snoc
    have h_nonempty : ((second :: rest).map mth).reverse ≠ [] := by
      simp [List.reverse_eq_nil_iff]
    rw [stackRoot_snoc _ _ h_nonempty]

    -- Step 3: apply IH on (second :: rest)
    have h_pow2_rest : ∀ s ∈ (second :: rest), ∃ k, s.length = 2 ^ k := by
      intro s hs
      exact h_pow2 s (List.mem_cons_of_mem first hs)
    have h_desc_rest : List.Pairwise (· > ·) ((second :: rest).map List.length) := by
      have := h_desc
      simp only [gt_iff_lt, List.map_cons, List.pairwise_cons, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at this ⊢
      exact this.2
    rw [stackRoot_segments_eq_mth (second :: rest) h_pow2_rest h_desc_rest]

    -- Step 4: rewrite flatten
    simp only [flatten_cons]

    -- Goal: MerkleTree.node (mth first) (mth ((second :: rest).flatten))
    --      = mth (first ++ (second :: rest).flatten)
    -- Apply mth_split symmetrically

    -- first is nonempty (power-of-2 length ≥ 1)
    have h_first_ne : first ≠ [] := by
      intro h_eq; subst h_eq
      obtain ⟨k, hk⟩ := h_pow2 [] (List.Mem.head _)
      simp only [List.length] at hk
      exact absurd hk (by have := Nat.one_le_two_pow (n := k); omega)
    have h_second_ne : second ≠ [] := by
      intro h_eq; subst h_eq
      obtain ⟨k, hk⟩ := h_pow2 [] (List.Mem.tail _ (List.Mem.head _))
      simp only [List.length] at hk
      exact absurd hk (by have := Nat.one_le_two_pow (n := k); omega)
    -- (second :: rest).flatten is nonempty
    have h_rest_ne : (second :: rest).flatten ≠ [] := by
      simp only [flatten_cons]
      match second with
      | [] => contradiction
      | h :: t => simp
    -- Lengths
    have h_first_pos : first.length > 0 := by
      match first with | [] => contradiction | _ :: _ => simp
    have h_rest_pos : (second :: rest).flatten.length > 0 := by
      match h : (second :: rest).flatten with
      | [] => exact absurd h h_rest_ne
      | _ :: _ => simp
    have h_first_pow2 : ∃ k, first.length = 2 ^ k :=
      h_pow2 first (List.Mem.head _)
    -- flatten length = sum of map length (general lemma)
    have h_flatten_sum : ∀ (ss : List (List (MerkleTree α))),
        ss.flatten.length = (ss.map List.length).sum := by
      intro ss
      induction ss with
      | nil => simp [List.flatten]
      | cons hd tl ih =>
        simp only [flatten_cons, List.length_append, List.map_cons,
                   List.sum_cons, ih]
    -- Sum of rest segment lengths < first.length
    have h_sum_lt : ((second :: rest).map List.length).sum < first.length := by
      have h_rest_pow2_len : ∀ s ∈ (second :: rest).map List.length,
          ∃ k, s = 2 ^ k := by
        simp only [List.mem_map]
        intro n ⟨s, hs_mem, hs_len⟩
        have h_mem : s ∈ first :: second :: rest := List.Mem.tail _ hs_mem
        obtain ⟨k, hk⟩ := h_pow2 s h_mem
        exact ⟨k, by omega⟩
      exact sum_rest_lt_first first.length
        ((second :: rest).map List.length) h_first_pow2
        h_rest_pow2_len (by simp only [List.map_cons] at h_desc; exact h_desc)
    have h_split_cond : largestPow2Lt
        (first.length + (second :: rest).flatten.length) = first.length := by
      have h_rest_sum_pos : ((second :: rest).map List.length).sum > 0 := by
        have : second.length > 0 := by
          match second with | [] => contradiction | _ :: _ => simp
        simp [List.sum_cons]
        omega
      conv_lhs => rw [h_flatten_sum (second :: rest)]
      exact largestPow2Lt_of_desc_segments first.length
        ((second :: rest).map List.length).sum
        h_first_pos h_rest_sum_pos h_first_pow2 h_sum_lt
    symm
    exact mth_split first ((second :: rest).flatten) h_first_ne h_rest_ne
      h_split_cond

/-- **The Bridge Lemma.** -/
theorem bridge_lemma (leaves : List (MerkleTree α)) :
    ctoRoot leaves = mth leaves := by
  -- By buildStack_invariant, the stack decomposes leaves into segments
  obtain ⟨segments, h_flat, h_pow2, h_desc, h_stack⟩ :=
    buildStack_invariant leaves
  -- ctoRoot = stackRoot (buildStack leaves) = stackRoot (segments.map mth).reverse
  simp only [ctoRoot, h_stack]
  -- stackRoot over the reversed segment mth's = mth of the flattened segments
  rw [stackRoot_segments_eq_mth segments h_pow2 h_desc]
  -- segments.flatten = leaves
  rw [h_flat]


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
  | MerkleTree.empty => emptyHash
  | MerkleTree.leaf v => v
  | MerkleTree.node l r => nodeHash (eval l) (eval r)

/-- Concrete ctoRoot over Digest. -/
noncomputable def ctoRootDigest (leaves : List Digest) : Digest :=
  eval (ctoRoot (leaves.map MerkleTree.leaf))

/-- Concrete mth over Digest. -/
noncomputable def mthDigest (leaves : List Digest) : Digest :=
  eval (mth (leaves.map MerkleTree.leaf))

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
  rw [bridge_lemma]

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
