import EMLProof.Tree

/-!
# EML Generalized split policies and merge schedules

This module defines the abstract interface for generalized Merkle tree topologies.
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

/-- A SplitPolicy determines the size of the left child for a tree of size n. -/
def SplitPolicy := Nat → Nat

/-- A SplitPolicy is valid if for all n > 1, the split point k satisfies 0 < k < n. -/
def ValidSplitPolicy (f : SplitPolicy) : Prop :=
  ∀ n > 1, 0 < f n ∧ f n < n

/-- A MergeSchedule determines how many reductions to perform at step idx. -/
def MergeSchedule := Nat → Nat

/-- Helper to get the i-th element of a list of Nat with a default value. -/
def getD (L : List Nat) (i : Nat) (default : Nat) : Nat :=
  match L with
  | [] => default
  | x :: xs =>
    match i with
    | 0 => x
    | i + 1 => getD xs i default

/-- Generalized stack sizes decomposition.
    Returns the sizes of the completed subtrees in the forest from top to bottom
    (head of list is the top/smallest tree, tail of list is the bottom/largest tree). -/
def forestSizes (f : SplitPolicy) (n : Nat) : List Nat :=
  if n = 0 then []
  else if n = 1 then [1]
  else
    let k := f n
    if h : k > 0 ∧ k < n then
      forestSizes f (n - k) ++ [k]
    else
      [n]
termination_by n
decreasing_by
  have h_pos : f n > 0 := h.1
  omega

/-- AppendConsistent states that the merge schedule `s` correctly transitions
    forestSizes from n to n + 1, and that intermediate splits match the policy. -/
def AppendConsistent (f : SplitPolicy) (s : MergeSchedule) : Prop :=
  ∀ n,
    let S_n := forestSizes f n
    let c := s n
    (forestSizes f (n + 1) = (1 + (S_n.take c).sum) :: S_n.drop c) ∧
    (∀ i < c, f (1 + (S_n.take (i + 1)).sum) = getD S_n i 0)

/-- Generalized Batch Merkle Tree Hash (MTH) under a split policy `f`. -/
noncomputable def generalized_mth {α : Type} (f : SplitPolicy) (leaves : List (MerkleTree α)) :
    MerkleTree α :=
  match leaves with
  | [] => MerkleTree.empty
  | [d] => d
  | a :: b :: rest =>
    let L := a :: b :: rest
    let n := L.length
    let k := f n
    if h : k > 0 ∧ k < n then
      MerkleTree.node (generalized_mth f (L.take k)) (generalized_mth f (L.drop k))
    else
      -- Fallback if the policy is invalid (should not happen for ValidSplitPolicy)
      MerkleTree.empty
termination_by leaves.length
decreasing_by
  · simp only [List.length_take]
    change Nat.min (f L.length) L.length < L.length
    have h_le : Nat.min (f L.length) L.length ≤ f L.length := Nat.min_le_left _ _
    have h_lt : f L.length < L.length := h.2
    omega
  · simp only [List.length_drop]
    change L.length - k < L.length
    omega

/-- Generalized mergeStack: merges the top `count` elements of the stack. -/
noncomputable def generalized_mergeStack {α : Type} (stack : List (MerkleTree α)) (count : Nat) :
    List (MerkleTree α) :=
  match count with
  | 0 => stack
  | n + 1 =>
    match stack with
    | r :: l :: rest => generalized_mergeStack (MerkleTree.node l r :: rest) n
    | _ => stack

/-- Generalized appendToStack: appends a leaf and runs the merge schedule. -/
noncomputable def generalized_appendToStack {α : Type} (s : MergeSchedule)
    (stack : List (MerkleTree α)) (leaf : MerkleTree α) (idx : Nat) : List (MerkleTree α) :=
  generalized_mergeStack (leaf :: stack) (s idx)

/-- Generalized buildStackAux: runs the stack machine over a list of remaining leaves. -/
noncomputable def generalized_buildStackAux {α : Type} (s : MergeSchedule)
    (stack : List (MerkleTree α)) (remaining : List (MerkleTree α)) (idx : Nat) :
    List (MerkleTree α) :=
  match remaining with
  | [] => stack
  | leaf :: rest =>
    generalized_buildStackAux s (generalized_appendToStack s stack leaf idx) rest (idx + 1)

/-- Generalized buildStack starting from index 0. -/
noncomputable def generalized_buildStack {α : Type} (s : MergeSchedule)
    (leaves : List (MerkleTree α)) : List (MerkleTree α) :=
  generalized_buildStackAux s [] leaves 0

/-- Generalized ctoRoot: extracts the root from the generalized buildStack. -/
noncomputable def generalized_ctoRoot {α : Type} (s : MergeSchedule)
    (leaves : List (MerkleTree α)) : MerkleTree α :=
  stackRoot (generalized_buildStack s leaves)

/-- Counts how many elements of L we need to take to sum to target. -/
def countToSum (L : List Nat) (target : Nat) : Nat :=
  match L with
  | [] => 0
  | x :: xs =>
    if target = 0 then 0
    else if x ≥ target then 1
    else 1 + countToSum xs (target - x)

/-- The canonical lazy merge schedule for a SplitPolicy f. -/
def lazy_schedule (f : SplitPolicy) (n : Nat) : Nat :=
  let S_n := forestSizes f n
  let S_next := forestSizes f (n + 1)
  match S_next with
  | [] => 0
  | target :: _ => countToSum S_n (target - 1)
