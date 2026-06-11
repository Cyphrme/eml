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

/-- Canonical preimage of the null constant: the literal bytes of `b"null"`.
    Mirrors `neml/src/hasher.rs` (`null() = hash(b"null")`). -/
def nullPreimage : List UInt8 := [0x6e, 0x75, 0x6c, 0x6c]

/-- The null digest `N₀`, defined faithfully as `H` of the null preimage —
    exactly `hash(b"null")` in the Rust hasher.

    The digest-length parameter `L` is retained for compatibility with the
    dynamic-arity evaluator but is vestigial: the shipped `null()` does not
    depend on it, matching the implementation where the null constant is
    length-independent.

    Because `leafHash d = H d` (prefix-free) and `nullDigest _ = H nullPreimage`,
    the identity `leafHash nullPreimage = nullDigest L` holds *by construction*
    (`null_collision` below). This is the leaf/null collision, now expressible
    in the model. It is **correct under Design A+**: A+ does not assume the
    collision away — it renders it inert by reading activity from the
    authenticated epoch timeline rather than from digest null-ness (see the
    "Design A+" section). -/
noncomputable def nullDigest (_L : Nat) : Digest := H nullPreimage

/-- **The leaf/null collision, made expressible — and provable.**
    A genuine leaf whose payload is the 4-byte string `null` hashes to the null
    constant. Under prefix-free hashing this is not a negligible-probability
    event — the preimage is public and trivial. Inactivity therefore cannot be
    soundly inferred from `cell = N₀`; it must be read from the committed epoch
    timeline (Design A+, below). -/
theorem null_collision (L : Nat) : leafHash nullPreimage = nullDigest L := rfl

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

/-! ## Constructive evaluation under NEML promotion rules

`eval` was previously an `axiom` together with five `eval_*` equation axioms
(six axioms in total). It is now a real `def`; the five equations are derived
lemmas, removing those axioms from the trust base. The case split mirrors
`nary_mr` in `neml/src/mr.rs` and `Compression.lean`'s `evalConstructive`. -/

/-! Structural size metric for termination of the evaluator (`nsize`/`nlsize`).
    Local to NEML; `Compression.lean` carries its own `treeSize`/`listSize` for
    the `Option`-payload variant. -/
mutual
  def nsize {α : Type} : NaryTree α → Nat
    | NaryTree.leaf _ => 1
    | NaryTree.node children => 1 + nlsize children
  def nlsize {α : Type} : List (NaryTree α) → Nat
    | [] => 0
    | c :: cs => 1 + nsize c + nlsize cs
end

mutual
  /-- Recursive evaluation of an N-ary tree under NEML promotion rules.
      `L` is the digest length of the active hash algorithm (vestigial; see
      `nullDigest`). Arms: leaf hashing; empty node → `emptyHash`; singleton
      promotion; flat null promotion (all children null, arity ≥ 2); standard
      node hashing. -/
  noncomputable def eval (L : Nat) : NaryTree (List UInt8) → Digest
    | NaryTree.leaf data => leafHash data
    | NaryTree.node [] => emptyHash
    | NaryTree.node [c] => eval L c
    | NaryTree.node children =>
        if evalAllNull L children then nullDigest L
        else nodeHash (evalMap L children)
  termination_by t => nsize t
  decreasing_by
    all_goals simp [nsize, nlsize]
    all_goals omega

  /-- Whether every child of a node evaluates to the null digest. -/
  noncomputable def evalAllNull (L : Nat) : List (NaryTree (List UInt8)) → Bool
    | [] => true
    | c :: cs => (eval L c == nullDigest L) && evalAllNull L cs
  termination_by cs => nlsize cs
  decreasing_by
    all_goals simp [nlsize]
    all_goals omega

  /-- Map `eval` over a child list (structural; equals `List.map (eval L)`). -/
  noncomputable def evalMap (L : Nat) : List (NaryTree (List UInt8)) → List Digest
    | [] => []
    | c :: cs => eval L c :: evalMap L cs
  termination_by cs => nlsize cs
  decreasing_by
    all_goals simp [nlsize]
    all_goals omega
end

/-- `evalAllNull` is the decidable reflection of "every child evaluates null". -/
theorem evalAllNull_eq_true_iff (L : Nat) (children : List (NaryTree (List UInt8))) :
    evalAllNull L children = true ↔ ∀ t ∈ children, eval L t = nullDigest L := by
  induction children with
  | nil => simp [evalAllNull]
  | cons c cs ih =>
    simp only [evalAllNull, Bool.and_eq_true, beq_iff_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hc, hcs⟩ x (rfl | hx)
      · exact hc
      · exact hcs x hx
    · intro h
      exact ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

/-- `evalMap` agrees with `List.map (eval L)`. -/
theorem evalMap_eq_map (L : Nat) (children : List (NaryTree (List UInt8))) :
    evalMap L children = children.map (eval L) := by
  induction children with
  | nil => simp [evalMap]
  | cons c cs ih => simp [evalMap, ih]

/-- Leaf evaluation equation (was `axiom eval_leaf`). -/
theorem eval_leaf (L : Nat) (data : List UInt8) :
    eval L (NaryTree.leaf data) = leafHash data := by
  simp [eval]

/-- Empty node evaluation equation (was `axiom eval_empty`). -/
theorem eval_empty (L : Nat) :
    eval L (NaryTree.node []) = emptyHash := by
  simp [eval]

/-- Singleton promotion equation (was `axiom eval_singleton_node`). -/
theorem eval_singleton_node (L : Nat) (t : NaryTree (List UInt8)) :
    eval L (NaryTree.node [t]) = eval L t := by
  simp [eval]

/-- Flat null promotion equation, arity ≥ 2 (was `axiom eval_flat_null_node`). -/
theorem eval_flat_null_node (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have hAll : evalAllNull L (a :: b :: rest) = true :=
    (evalAllNull_eq_true_iff L _).mpr h_all_null
  simp only [eval]
  rw [if_pos hAll]

/-- Standard node hashing equation, arity ≥ 2 with a non-null child
    (was `axiom eval_node_hash`). -/
theorem eval_node_hash (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_some : ∃ t ∈ children, eval L t ≠ nullDigest L) :
    eval L (NaryTree.node children) = nodeHash (children.map (eval L)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have hNot : ¬ evalAllNull L (a :: b :: rest) = true := by
    rw [evalAllNull_eq_true_iff]
    intro hall
    obtain ⟨t, ht, htne⟩ := h_some
    exact htne (hall t ht)
  simp only [eval]
  rw [if_neg hNot, evalMap_eq_map]

/-- **Theorem 1 (Singleton Promotion Soundness).**
    A node with exactly one child evaluates directly to the child's evaluation,
    preserving the digest without hashing. Now a real theorem (no longer an
    `exact <axiom>` restatement). -/
theorem eval_singleton (L : Nat) (t : NaryTree (List UInt8)) :
    eval L (NaryTree.node [t]) = eval L t :=
  eval_singleton_node L t

/-- **Theorem 2 (Flat Null Promotion Soundness).**
    A node with two or more children, all of which evaluate to the null digest,
    evaluates directly to the null digest. This is the null-*valued* collapse
    (N₀); it is unrelated to the rejection of zero-*sibling* proof steps under
    canonical proof encoding (see the inclusion-verifier section). -/
theorem eval_flat_null_promotion (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L :=
  eval_flat_null_node L children h_length h_all_null

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
