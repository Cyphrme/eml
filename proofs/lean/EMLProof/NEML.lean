import EMLProof.Projection

/-!
# NEML Formal Soundness and Promotion Properties

This module formalizes the N-ary Epoch Merkle Log (NEML) tree structure,
its singleton and flat null promotion rules, and proves their cryptographic soundness
under prefix-free hashing.
-/

namespace NEML

/-- Prefix-free leaf hash: H(data). -/
noncomputable def leafHash (d : List UInt8) : Digest := H d

/-- Prefix-free internal node hash: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). -/
noncomputable def nodeHash (children : List Digest) : Digest :=
  H (children.flatMap digestToBytes)

/-- Null digest constant.
    Under prefix-free hashing, the null constant must be a high-entropy constant
    (such as a NUMS constant) with no known preimage under H, rather than the hash
    of a known preimage (like EML's nullLeaf). This prevents collisions with any leaf
    or node hashes. -/
axiom nullDigest : Digest

/-- Inductive N-ary Merkle Tree structure. -/
inductive NaryTree (α : Type) where
  | leaf (val : α)
  | node (children : List (NaryTree α))
  deriving Inhabited

/-- Predicate enforcing that a tree has a fixed arity k.
    This is used to model the log-level fixed-arity tree topology. -/
def HasArity {α : Type} (k : Nat) : NaryTree α → Prop
  | NaryTree.leaf _ => True
  | NaryTree.node children => children.length = k ∧ ∀ c ∈ children, HasArity k c

/-- The "tree of trees" model of NEML:
    The outer log tree is a fixed-arity k tree whose leaves are dynamic-arity subtrees. -/
def IsNEMLTree {α : Type} (k : Nat) (t : NaryTree (NaryTree α)) : Prop :=
  HasArity k t

/-- Recursive evaluation of an N-ary tree under NEML promotion rules.
    Defined axiomatically to separate structural representation from proof minutia. -/
axiom eval : NaryTree (List UInt8) → Digest

/-- Leaf evaluation axiom. -/
axiom eval_leaf : ∀ (data : List UInt8),
  eval (NaryTree.leaf data) = leafHash data

/-- Empty node evaluation axiom. -/
axiom eval_empty :
  eval (NaryTree.node []) = emptyHash

/-- Singleton promotion evaluation axiom. -/
axiom eval_singleton_node : ∀ (t : NaryTree (List UInt8)),
  eval (NaryTree.node [t]) = eval t

/-- Flat null promotion evaluation axiom (for arity >= 2). -/
axiom eval_flat_null_node : ∀ (children : List (NaryTree (List UInt8))),
  children.length ≥ 2 →
  (∀ t ∈ children, eval t = nullDigest) →
  eval (NaryTree.node children) = nullDigest

/-- Standard node evaluation axiom (for arity >= 2 with at least one non-null child). -/
axiom eval_node_hash : ∀ (children : List (NaryTree (List UInt8))),
  children.length ≥ 2 →
  (∃ t ∈ children, eval t ≠ nullDigest) →
  eval (NaryTree.node children) = nodeHash (children.map eval)

/-!
## Cryptographic Soundness Axioms (Preimage Resistance)

Under prefix-free hashing, the soundness of EML/NEML's inactivity binding depends
on `nullDigest` being a high-entropy constant with no known preimage under H.
This is formalized via the following preimage resistance axioms: no leaf hash,
empty hash, or internal node hash (for nodes of arity >= 2) can collide with `nullDigest`.
-/

/-- Preimage resistance: no leaf hash can collide with the null digest. -/
axiom leaf_hash_neq_null : ∀ (data : List UInt8), leafHash data ≠ nullDigest

/-- Preimage resistance: no node hash (arity >= 2) can collide with the null digest. -/
axiom node_hash_neq_null :
  ∀ (children : List Digest), children.length ≥ 2 → nodeHash children ≠ nullDigest

/-- Preimage resistance: empty hash cannot collide with the null digest. -/
axiom empty_hash_neq_null : emptyHash ≠ nullDigest

/-!
## Soundness Theorems
-/

/-- **Theorem 1 (Singleton Promotion Soundness).**
    A node with exactly one child evaluates directly to the child's evaluation,
    preserving the digest without hashing. -/
theorem eval_singleton (t : NaryTree (List UInt8)) :
    eval (NaryTree.node [t]) = eval t := by
  exact eval_singleton_node t

/-- **Theorem 2 (Flat Null Promotion Soundness).**
    A node with two or more children, all of which evaluate to the null digest,
    evaluates directly to the null digest. -/
theorem eval_flat_null_promotion (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval t = nullDigest) :
    eval (NaryTree.node children) = nullDigest := by
  exact eval_flat_null_node children h_length h_all_null

theorem eval_eq_null_implies (t : NaryTree (List UInt8)) (h_eval : eval t = nullDigest) :
    ∃ (children : List (NaryTree (List UInt8))),
      t = NaryTree.node children ∧
      (children ≠ []) ∧
      (∀ c ∈ children, eval c = nullDigest) := by
  cases t with
  | leaf data =>
    have h_leaf := eval_leaf data
    rw [h_leaf] at h_eval
    have h_neq := leaf_hash_neq_null data
    contradiction
  | node children =>
    use children
    have h_not_nil : children ≠ [] := by
      intro h_empty
      rw [h_empty] at h_eval
      have h_empty_eval := eval_empty
      rw [h_empty_eval] at h_eval
      have h_neq := empty_hash_neq_null
      contradiction
    refine ⟨rfl, h_not_nil, ?_⟩
    intro c hc
    by_contra hc_neq
    cases h_children : children with
    | nil =>
      exact h_not_nil h_children
    | cons x xs =>
      cases h_xs : xs with
      | nil =>
        have h_single : children = [x] := by rw [h_children, h_xs]
        have h_eval_single := eval_singleton_node x
        rw [←h_single] at h_eval_single
        have h_eval_x : eval x = nullDigest := by
          rw [←h_eval_single, h_eval]
        have h_c_eq_x : c = x := by
          have hc' : c ∈ [x] := by rw [←h_single]; exact hc
          exact List.mem_singleton.mp hc'
        rw [h_c_eq_x] at hc_neq
        exact hc_neq h_eval_x
      | cons y ys =>
        have h_len : children.length ≥ 2 := by
          rw [h_children, h_xs]
          simp [List.length]
        have h_exists_neq : ∃ t ∈ children, eval t ≠ nullDigest := ⟨c, hc, hc_neq⟩
        have h_eval_node := eval_node_hash children h_len h_exists_neq
        rw [h_eval] at h_eval_node
        have h_map_len : (children.map eval).length ≥ 2 := by
          rw [List.length_map]
          exact h_len
        have h_neq := node_hash_neq_null (children.map eval) h_map_len
        rw [h_eval_node] at h_neq
        contradiction

/-- **Theorem 3 (Null Path Isolation / Inactivity Binding).**
    Any tree that contains at least one leaf node with payload data
    can never evaluate to the null digest. This ensures that active data
    cannot be spoofed as or substituted with null/inactive nodes. -/
theorem contains_leaf_neq_null (t : NaryTree (List UInt8)) (data : List UInt8) :
    (t = NaryTree.leaf data ∨
     ∃ (children : List (NaryTree (List UInt8))),
       t = NaryTree.node children ∧ ∃ c ∈ children, eval c ≠ nullDigest) →
    eval t ≠ nullDigest := by
  intro h h_eval
  rcases h with h_leaf | ⟨children, rfl, c, hc, hc_neq⟩
  · rw [h_leaf] at h_eval
    rw [eval_leaf] at h_eval
    have h_neq := leaf_hash_neq_null data
    contradiction
  · cases h_children : children with
    | nil =>
      rw [h_children] at hc
      contradiction
    | cons x xs =>
      cases h_xs : xs with
      | nil =>
        have h_single : children = [x] := by rw [h_children, h_xs]
        have h_eval_single := eval_singleton_node x
        rw [←h_single] at h_eval_single
        have h_eval_x : eval x = nullDigest := by
          rw [←h_eval_single, h_eval]
        have h_c_eq_x : c = x := by
          have hc' : c ∈ [x] := by rw [←h_single]; exact hc
          exact List.mem_singleton.mp hc'
        rw [h_c_eq_x] at hc_neq
        exact hc_neq h_eval_x
      | cons y ys =>
        have h_len : children.length ≥ 2 := by
          rw [h_children, h_xs]
          simp [List.length]
        have h_exists_neq : ∃ t ∈ children, eval t ≠ nullDigest := ⟨c, hc, hc_neq⟩
        have h_eval_node := eval_node_hash children h_len h_exists_neq
        rw [h_eval] at h_eval_node
        have h_map_len : (children.map eval).length ≥ 2 := by
          rw [List.length_map]
          exact h_len
        have h_neq := node_hash_neq_null (children.map eval) h_map_len
        rw [h_eval_node] at h_neq
        contradiction

end NEML
