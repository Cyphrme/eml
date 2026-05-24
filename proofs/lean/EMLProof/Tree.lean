import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# EML Merkle Tree Data Structures and State Machine

This module defines the structural components of the Epoch Merkle Log (EML) proof. 
To ensure modularity and ease of review, the structural topology of the Merkle Tree is decoupled 
from concrete cryptographic hashing via a generic type parameter `α`.

## Mathematical Definitions

1. **Merkle Tree Topology**:
   We model a Merkle tree as an inductive type:
   $$\text{MerkleTree } \alpha ::= \text{empty} \mid \text{leaf}(v) \mid \text{node}(l, r)$$
   The structural height is defined recursively:
   $$\text{treeHeight}(\text{empty}) = 0, \quad \text{treeHeight}(\text{leaf}(v)) = 0$$
   $$\text{treeHeight}(\text{node}(l, r)) = \max(\text{treeHeight}(l), \text{treeHeight}(r)) + 1$$

2. **Batch Merkle Tree Hash (MTH) Split Point**:
   Following RFC 9162, the split boundary $k$ for a list of length $n > 1$
   is the largest power of 2 strictly less than $n$:
   $$\text{largestPow2Lt}(n) = 2^{\lfloor \log_2(n - 1) \rfloor}$$

3. **Frontier Stack State Machine**:
   - `cto(n)`: Counts the trailing one-bits of $n$, determining the cascade merge count.
   - `mergeStack(stack, count)`: Merges the top `count` pairs on the stack.
   - `appendToStack(stack, leaf, idx)`: Appends a leaf and applies `cto(idx)` merges.
   - `buildStack(leaves)`: Sequentially accumulates leaves starting from index 0.
   - `stackRoot(stack)`: Folds the stack from head (smallest) to tail (largest) to extract the root.
-/

set_option linter.style.emptyLine false

/-- Inductive Merkle Tree topology decoupled from cryptographic digest types. -/
inductive MerkleTree (α : Type) where
  | empty
  | leaf (val : α)
  | node (left right : MerkleTree α)
  deriving DecidableEq, Inhabited

/-- Structural height of a Merkle Tree. Leaves have height 0. -/
def treeHeight {α : Type} : MerkleTree α → Nat
  | MerkleTree.empty => 0
  | MerkleTree.leaf _ => 0
  | MerkleTree.node l r => Nat.max (treeHeight l) (treeHeight r) + 1

/-- The largest power of 2 strictly less than n.
    Defined as 2^(log₂(n-1)) for n > 1.
    For n ≤ 1, returns 0 (unused by MTH). -/
def largestPow2Lt (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else 2 ^ (Nat.log 2 (n - 1))

/-- Unfold lemma for largestPow2Lt when n > 1. -/
theorem largestPow2Lt_def {n : Nat} (hn : n > 1) :
    largestPow2Lt n = 2 ^ (Nat.log 2 (n - 1)) := by
  simp [largestPow2Lt, Nat.not_le.mpr hn]

/-- Strict positivity of largestPow2Lt for n > 1. -/
theorem largestPow2Lt_pos {n : Nat} (hn : n > 1) :
    largestPow2Lt n > 0 := by
  rw [largestPow2Lt_def hn]
  exact Nat.pos_of_ne_zero (by positivity)

/-- Strict upper bound: largestPow2Lt n < n. -/
theorem largestPow2Lt_lt {n : Nat} (hn : n > 1) :
    largestPow2Lt n < n := by
  rw [largestPow2Lt_def hn]
  have h1 : n - 1 ≠ 0 := by omega
  have h2 : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 h1
  omega

/-- Expressibility as a power of 2. -/
theorem largestPow2Lt_is_pow2 {n : Nat} (hn : n > 1) :
    ∃ k, largestPow2Lt n = 2 ^ k := by
  rw [largestPow2Lt_def hn]
  exact ⟨Nat.log 2 (n - 1), rfl⟩

/-- Lower bound: 2 * largestPow2Lt n ≥ n. -/
theorem largestPow2Lt_ge_half {n : Nat} (hn : n > 1) :
    2 * largestPow2Lt n ≥ n := by
  rw [largestPow2Lt_def hn]
  have h1 : n - 1 ≠ 0 := by omega
  have h2 : n - 1 < 2 ^ (Nat.log 2 (n - 1)).succ :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n - 1)
  rw [Nat.succ_eq_add_one, pow_succ] at h2
  omega

/-- Batch Merkle Tree Hash over structural trees (RFC 9162). -/
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
  · simp only [List.length_take]
    have hn : (a :: b :: rest).length > 1 := by simp
    have hlt := largestPow2Lt_lt hn
    omega
  · simp only [List.length_drop]
    have hn : (a :: b :: rest).length > 1 := by simp
    have hpos := largestPow2Lt_pos hn
    omega

/-- Count trailing one-bits in the binary representation of n. -/
def cto (n : Nat) : Nat :=
  if n % 2 = 1 then 1 + cto (n / 2)
  else 0

@[simp] theorem cto_zero : cto 0 = 0 := by simp [cto]

@[simp] theorem cto_even {n : Nat} (h : n % 2 = 0) : cto n = 0 := by
  simp [cto, h]

/-- Merge the top `count` pairs on the stack.
    Each merge pops two elements, creates a node, and pushes the result. -/
noncomputable def mergeStack {α : Type} (stack : List (MerkleTree α)) (count : Nat) :
    List (MerkleTree α) :=
  match count with
  | 0 => stack
  | n + 1 =>
    match stack with
    | r :: l :: rest => mergeStack (MerkleTree.node l r :: rest) n
    | _ => stack  -- underflow guard

/-- Append a single leaf hash to the frontier stack, then perform
    CTO-determined merges. merge_count = cto(idx). -/
noncomputable def appendToStack (stack : List (MerkleTree α)) (leaf : MerkleTree α)
    (idx : Nat) : List (MerkleTree α) :=
  mergeStack (leaf :: stack) (cto idx)

/-- Build the frontier stack by processing leaves with index tracking. -/
noncomputable def buildStackAux {α : Type} (stack : List (MerkleTree α))
    (remaining : List (MerkleTree α)) (idx : Nat) : List (MerkleTree α) :=
  match remaining with
  | [] => stack
  | leaf :: rest => buildStackAux (appendToStack stack leaf idx) rest (idx + 1)

/-- Build the frontier stack from a leaf list. -/
noncomputable def buildStack {α : Type} (leaves : List (MerkleTree α)) : List (MerkleTree α) :=
  buildStackAux [] leaves 0

/-- Extract the root from the frontier stack via right-fold. -/
noncomputable def stackRoot (stack : List (MerkleTree α)) : MerkleTree α :=
  match stack with
  | [] => MerkleTree.empty
  | h :: t => t.foldl (fun acc left => MerkleTree.node left acc) h

/-- The incrementally computed root. -/
noncomputable def ctoRoot (leaves : List (MerkleTree α)) : MerkleTree α :=
  stackRoot (buildStack leaves)

/-- Base case: ctoRoot of empty list. -/
theorem bridge_base_empty {α : Type} : ctoRoot (α := α) [] = mth (α := α) [] := by
  simp only [ctoRoot, buildStack, buildStackAux, stackRoot, mth]

/-- Base case: ctoRoot of singleton list. -/
theorem bridge_base_single {α : Type} (d : MerkleTree α) : ctoRoot [d] = mth [d] := by
  simp [ctoRoot, buildStack, buildStackAux, appendToStack, mergeStack,
        stackRoot, mth]

/-- Decomposes buildStackAux over list concatenation. -/
theorem buildStackAux_append {α : Type} (stack₀ : List (MerkleTree α))
    (L₁ L₂ : List (MerkleTree α)) (i : Nat) :
    buildStackAux stack₀ (L₁ ++ L₂) i =
    buildStackAux (buildStackAux stack₀ L₁ i) L₂ (i + L₁.length) := by
  induction L₁ generalizing stack₀ i with
  | nil => simp [buildStackAux]
  | cons hd tl ih =>
    simp only [List.cons_append, buildStackAux, List.length_cons]
    rw [ih]
    congr 1
    omega

/-- Helper for folding stackRoot with an appended base element. -/
theorem stackRoot_snoc {α : Type} (s : List (MerkleTree α)) (base : MerkleTree α) (hs : s ≠ []) :
    stackRoot (s ++ [base]) = MerkleTree.node base (stackRoot s) := by
  match s with
  | [] => contradiction
  | h :: t =>
    simp only [stackRoot, List.cons_append, List.foldl_append, List.foldl_cons,
               List.foldl_nil]
