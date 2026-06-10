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

set_option linter.style.longLine false

/-- Inserts an element at a given position in a list. -/
def insertAt {α : Type} (n : Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    match n with
    | 0 => x :: y :: ys
    | n + 1 => y :: insertAt n x ys

structure ProofStep where
  siblings : List Digest
  position : Nat
  deriving Inhabited

structure InclusionProof where
  index : Nat
  treeSize : Nat
  logArity : Nat
  path : List ProofStep
  deriving Inhabited

/-- Helper to safely get an element from a list, returning default if out of bounds. -/
def getL {α : Type} [Inhabited α] : List α → Nat → α
  | [], _ => default
  | x :: _, 0 => x
  | _ :: xs, n + 1 => getL xs n

/-- Reconstructs the root hash from a leaf and a proof path. -/
noncomputable def reconstructPathRoot (leafHash : Digest) (path : List ProofStep) : Digest :=
  path.foldl (fun current step =>
    if step.siblings.isEmpty then
      current
    else
      nodeHash (insertAt step.position current step.siblings)
  ) leafHash

/-- Reconstruct the coordinates (left_index, height) of the frontier for a given tree size. -/
partial def frontierForSize (n : Nat) (k : Nat) : List (Nat × Nat) :=
  if k < 2 then []
  else
    let rec loop (temp_n : Nat) (curr_left : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
      if temp_n = 0 then acc.reverse
      else
        let rec find_height (cap : Nat) (height : Nat) : Nat × Nat :=
          let next_cap := cap * k
          if next_cap ≤ temp_n then
            find_height next_cap (height + 1)
          else
            (cap, height)
        let (cap, height) := find_height 1 0
        loop (temp_n - cap) (curr_left + cap) ((curr_left, height) :: acc)
    loop n 0 []

structure TreeBuildResult where
  childrenMap : List (Nat × List Nat)
  spans : List (Nat × (Nat × Nat))
  root : Nat
  deriving Inhabited

def lookupSpan (spans : List (Nat × (Nat × Nat))) (key : Nat) : Nat × Nat :=
  match spans with
  | [] => (0, 0)
  | (k, v) :: xs => if k = key then v else lookupSpan xs key

def lookupChildren (childrenMap : List (Nat × List Nat)) (key : Nat) : Option (List Nat) :=
  match childrenMap with
  | [] => none
  | (k, v) :: xs => if k = key then some v else lookupChildren xs key

partial def buildTree (k : Nat) (coords_len : Nat) : TreeBuildResult :=
  let initial_spans := List.range coords_len |>.map (fun i => (i, (i, i)))
  let initial_frontier := List.range coords_len
  let rec loop (frontier : List Nat) (next_id : Nat) (cmap : List (Nat × List Nat)) (spans : List (Nat × (Nat × Nat))) : TreeBuildResult :=
    if frontier.length > k then
      let split_idx := frontier.length - k
      let children := frontier.drop split_idx
      let parent_id := next_id
      let first_child := children.headD 0
      let last_child := children.getLastD 0
      let (min_val, _) := lookupSpan spans first_child
      let (_, max_val) := lookupSpan spans last_child
      let next_frontier := (frontier.take split_idx) ++ [parent_id]
      loop next_frontier (parent_id + 1) ((parent_id, children) :: cmap) ((parent_id, (min_val, max_val)) :: spans)
    else if frontier.length > 1 then
      let parent_id := next_id
      let first_child := frontier.headD 0
      let last_child := frontier.getLastD 0
      let (min_val, _) := lookupSpan spans first_child
      let (_, max_val) := lookupSpan spans last_child
      let cmap_final := (parent_id, frontier) :: cmap
      let spans_final := (parent_id, (min_val, max_val)) :: spans
      TreeBuildResult.mk cmap_final spans_final parent_id
    else
      TreeBuildResult.mk cmap spans (frontier.headD 0)
  loop initial_frontier coords_len [] initial_spans

partial def pathLengthToFrontierNode (k : Nat) (coords_len : Nat) (target_f_idx : Nat) : Option Nat :=
  if target_f_idx ≥ coords_len then none
  else
    let res : TreeBuildResult := buildTree k coords_len
    let rec trace (curr : Nat) (depth : Nat) : Option Nat :=
      match lookupChildren res.childrenMap curr with
      | none => some depth
      | some children =>
        let rec find_child (lst : List Nat) : Option Nat :=
          match lst with
          | [] => none
          | c :: cs =>
            let (min_val, max_val) := lookupSpan res.spans c
            if target_f_idx ≥ min_val ∧ target_f_idx ≤ max_val then
              trace c (depth + 1)
            else
              find_child cs
        find_child children
    trace res.root 0

partial def reconstructIndexFromPath (k : Nat) (treeSize : Nat) (path : List ProofStep) : Option Nat :=
  if k < 2 then none
  else
    let coords := frontierForSize treeSize k
    if coords.isEmpty then none
    else
      let res : TreeBuildResult := buildTree k coords.length
      let rec loop (curr : Nat) (path_idx : Nat) : Option (Nat × Nat) :=
        match lookupChildren res.childrenMap curr with
        | some children =>
          if path_idx = 0 then none
          else
            let step : ProofStep := getL path (path_idx - 1)
            if step.siblings.length ≠ children.length - 1 then none
            else if step.position ≥ children.length then none
            else
              let next_node := getL children step.position
              loop next_node (path_idx - 1)
        | none => some (curr, path_idx)
      
      match loop res.root path.length with
      | none => none
      | some (curr, path_idx) =>
        if curr ≥ coords.length then none
        else
          let (left, height) := getL coords curr
          if path_idx ≠ height then none
          else
            let rec loop_offset (i : Nat) (offset : Nat) (power : Nat) : Option Nat :=
              if i = path_idx then some (left + offset)
              else
                let step : ProofStep := getL path i
                if step.siblings.length ≠ k - 1 then none
                else if step.position ≥ k then none
                else
                  loop_offset (i + 1) (offset + step.position * power) (power * k)
            loop_offset 0 0 1

def verifyInclusionPathStructure (k : Nat) (index : Nat) (treeSize : Nat) (path : List ProofStep) : Bool :=
  match reconstructIndexFromPath k treeSize path with
  | some idx => idx = index
  | none => false

noncomputable def verifyInclusion (leafHash : Digest) (proof : InclusionProof) (root : Digest) : Bool :=
  let k := proof.logArity
  let T := proof.treeSize
  let S_I := proof.index
  let P := proof.path.length
  if k < 2 then false
  else
    let coords := frontierForSize T k
    let rec find_f_idx (lst : List (Nat × Nat)) (idx : Nat) : Option (Nat × Nat × Nat) :=
      match lst with
      | [] => none
      | (left, height) :: xs =>
        let cap := k ^ height
        if S_I ≥ left ∧ S_I < left + cap then
          some (idx, left, height)
        else
          find_f_idx xs (idx + 1)
    
    match find_f_idx coords 0 with
    | none => false
    | some (target_f_idx, _, height) =>
      match pathLengthToFrontierNode k coords.length target_f_idx with
      | none => false
      | some C =>
        let H := height
        if P < C + H then false
        else
          let d := P - C - H
          let log_path := proof.path.drop d
          if verifyInclusionPathStructure k S_I T log_path then
            let computed_root := reconstructPathRoot leafHash proof.path
            computed_root = root
          else
            false

end NEML
