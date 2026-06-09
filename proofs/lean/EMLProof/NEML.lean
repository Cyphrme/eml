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

/-- Master Nothing-Up-My-Sleeve seed constant. -/
axiom numsSeed : List UInt8

/-- Extendable-Output Function (XOF) expanding a seed to a digest of length L. -/
axiom xof : List UInt8 → Nat → Digest

/-- The null digest is derived by expanding the master seed to length L. -/
noncomputable def nullDigest (L : Nat) : Digest := xof numsSeed L

/-- Inductive N-ary Merkle Tree structure. -/
inductive NaryTree (α : Type) where
  | leaf (val : α)
  | node (children : List (NaryTree α))
  deriving Inhabited

/-- Inductive predicate representing that an NaryTree contains at least one leaf node. -/
inductive ContainsLeaf {α : Type} : NaryTree α → Prop where
  | leaf (val : α) : ContainsLeaf (NaryTree.leaf val)
  | node (children : List (NaryTree α)) (c : NaryTree α) (h_mem : c ∈ children)
      (h_cont : ContainsLeaf c) : ContainsLeaf (NaryTree.node children)


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
    L represents the digest length of the active hash algorithm. -/
axiom eval (L : Nat) : NaryTree (List UInt8) → Digest

/-- Leaf evaluation axiom. -/
axiom eval_leaf : ∀ (L : Nat) (data : List UInt8),
  eval L (NaryTree.leaf data) = leafHash data

/-- Empty node evaluation axiom. -/
axiom eval_empty : ∀ (L : Nat),
  eval L (NaryTree.node []) = emptyHash

/-- Singleton promotion evaluation axiom. -/
axiom eval_singleton_node : ∀ (L : Nat) (t : NaryTree (List UInt8)),
  eval L (NaryTree.node [t]) = eval L t

/-- Flat null promotion evaluation axiom (for arity >= 2). -/
axiom eval_flat_null_node : ∀ (L : Nat) (children : List (NaryTree (List UInt8))),
  children.length ≥ 2 →
  (∀ t ∈ children, eval L t = nullDigest L) →
  eval L (NaryTree.node children) = nullDigest L

/-- Standard node evaluation axiom (for arity >= 2 with at least one non-null child). -/
axiom eval_node_hash : ∀ (L : Nat) (children : List (NaryTree (List UInt8))),
  children.length ≥ 2 →
  (∃ t ∈ children, eval L t ≠ nullDigest L) →
  eval L (NaryTree.node children) = nodeHash (children.map (eval L))

/-!
## Cryptographic Soundness Axioms (Preimage Resistance)

Under prefix-free hashing, the soundness of EML/NEML's inactivity binding depends
on `nullDigest L` being a high-entropy constant with no known preimage under H.
This is formalized via the following preimage resistance axioms: no leaf hash,
empty hash, or internal node hash (for nodes of arity >= 2) can collide with `nullDigest L`.
-/

/-- Preimage resistance: no leaf hash can collide with the null digest. -/
axiom leaf_hash_neq_null : ∀ (L : Nat) (data : List UInt8), leafHash data ≠ nullDigest L

/-- Preimage resistance: no node hash (arity >= 2) can collide with the null digest. -/
axiom node_hash_neq_null :
  ∀ (L : Nat) (children : List Digest), children.length ≥ 2 → nodeHash children ≠ nullDigest L

/-- Preimage resistance: empty hash cannot collide with the null digest. -/
axiom empty_hash_neq_null : ∀ (L : Nat), emptyHash ≠ nullDigest L

/-!
## Soundness Theorems
-/

/-- **Theorem 1 (Singleton Promotion Soundness).**
    A node with exactly one child evaluates directly to the child's evaluation,
    preserving the digest without hashing. -/
theorem eval_singleton (L : Nat) (t : NaryTree (List UInt8)) :
    eval L (NaryTree.node [t]) = eval L t := by
  exact eval_singleton_node L t

/-- **Theorem 2 (Flat Null Promotion Soundness).**
    A node with two or more children, all of which evaluate to the null digest,
    evaluates directly to the null digest. -/
theorem eval_flat_null_promotion (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L := by
  exact eval_flat_null_node L children h_length h_all_null

theorem eval_eq_null_implies (L : Nat) (t : NaryTree (List UInt8))
    (h_eval : eval L t = nullDigest L) :
    ∃ (children : List (NaryTree (List UInt8))),
      t = NaryTree.node children ∧
      (children ≠ []) ∧
      (∀ c ∈ children, eval L c = nullDigest L) := by
  cases t with
  | leaf data =>
    have h_leaf := eval_leaf L data
    rw [h_leaf] at h_eval
    have h_neq := leaf_hash_neq_null L data
    contradiction
  | node children =>
    use children
    have h_not_nil : children ≠ [] := by
      intro h_empty
      rw [h_empty] at h_eval
      have h_empty_eval := eval_empty L
      rw [h_empty_eval] at h_eval
      have h_neq := empty_hash_neq_null L
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
        have h_eval_single := eval_singleton_node L x
        rw [←h_single] at h_eval_single
        have h_eval_x : eval L x = nullDigest L := by
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
        have h_exists_neq : ∃ t ∈ children, eval L t ≠ nullDigest L := ⟨c, hc, hc_neq⟩
        have h_eval_node := eval_node_hash L children h_len h_exists_neq
        rw [h_eval] at h_eval_node
        have h_map_len : (children.map (eval L)).length ≥ 2 := by
          rw [List.length_map]
          exact h_len
        have h_neq := node_hash_neq_null L (children.map (eval L)) h_map_len
        rw [h_eval_node] at h_neq
        contradiction

/-- **Theorem 3 (Null Path Isolation / Inactivity Binding).**
    Any tree that recursively contains at least one leaf node with payload data
    can never evaluate to the null digest. This ensures that active data
    cannot be spoofed as or substituted with null/inactive nodes. -/
theorem contains_leaf_neq_null (L : Nat) (t : NaryTree (List UInt8)) (h : ContainsLeaf t) :
    eval L t ≠ nullDigest L := by
  induction h with
  | leaf data =>
    rw [eval_leaf L data]
    exact leaf_hash_neq_null L data
  | node children c h_mem h_cont ih =>
    intro h_eval
    cases h_children : children with
    | nil =>
      rw [h_children] at h_mem
      contradiction
    | cons x xs =>
      cases h_xs : xs with
      | nil =>
        have h_single : children = [x] := by rw [h_children, h_xs]
        have h_eval_single := eval_singleton_node L x
        rw [←h_single] at h_eval_single
        have h_eval_x : eval L x = nullDigest L := by
          rw [←h_eval_single, h_eval]
        have h_c_eq_x : c = x := by
          have hc' : c ∈ [x] := by rw [←h_single]; exact h_mem
          exact List.mem_singleton.mp hc'
        rw [h_c_eq_x] at ih
        exact ih h_eval_x
      | cons y ys =>
        have h_len : children.length ≥ 2 := by
          rw [h_children, h_xs]
          simp [List.length]
        have h_exists_neq : ∃ t ∈ children, eval L t ≠ nullDigest L := ⟨c, h_mem, ih⟩
        have h_eval_node := eval_node_hash L children h_len h_exists_neq
        rw [h_eval] at h_eval_node
        have h_map_len : (children.map (eval L)).length ≥ 2 := by
          rw [List.length_map]
          exact h_len
        have h_neq := node_hash_neq_null L (children.map (eval L)) h_map_len
        rw [h_eval_node] at h_neq
        contradiction

end NEML
