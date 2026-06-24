import EMLProof.Foundations
import Mathlib.Tactic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Merkle Spine — structural canonicalization and canonical inclusion proofs

The **structural core** of the proof corpus. This module formalizes the n-ary
Merkle tree, its canonicalizing evaluator (`eval`: leaf hashing, singleton
promotion, general same-value collapse, node hashing), and the canonical
inclusion proofs (`inclusion_soundness`, `inclusion_proof_unique`,
`not_canonical_of_promoted`). Every definition here is **epoch-free**: it carries
no activation timeline, no binding root, no null-run-extent — it operates purely
over the positional topology and consumes nothing from the combinator.

The epoch combinator — the committed activation timeline (Design A+), the combined
root, the per-algorithm binding root, and coupling-verifier soundness — moved to
`EMLProof.Epoch`, which imports *this* module (the arrow runs epoch → spine only).
Splitting it out makes the boundary explicit: the structural injectivity guarantee
(distinct canonical structures ⇒ distinct roots) stands alone here, and the
timeline-binding guarantee composes on top in `EMLProof.Epoch`.

Same-value collapse (the null run included) is structural and reduces here without
being counted; only the per-tree-divergent null-run-extent is counted, and that
lives at the combinator (`EMLProof.Epoch`), never in this module.
-/

namespace NEML

/-- Prefix-free leaf hash: H(data). -/
noncomputable def leafHash (d : List UInt8) : Digest := H d

/-- Prefix-free internal node hash: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). -/
noncomputable def nodeHash (children : List Digest) : Digest :=
  H (children.flatMap digestToBytes)

/-- A collision on the internal node hash: distinct child lists, equal digest.
    A `nodeHash` collision is in particular an `H` collision. (Defined here, by
    `nodeHash`, so both the combined-root fold and the inclusion layer share it.) -/
def NodeHashCollision : Prop := ∃ a b : List Digest, a ≠ b ∧ nodeHash a = nodeHash b

/-- A collision on the hash `H`: distinct preimages with equal digest. The
    structural `H`-collision lever, shared by the canonical-uniqueness layer
    (`EMLProof.Canonical`) and the epoch combinator (`EMLProof.Epoch`); kept here in
    the spine because it speaks only of the bare hash `H`, no epoch concept. -/
def HashCollision : Prop := ∃ a b : List UInt8, a ≠ b ∧ H a = H b

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
  /-- Recursive evaluation of an N-ary tree under NEML canonicalization rules.
      `L` is the digest length of the active hash algorithm (vestigial; see
      `nullDigest`). Arms: leaf hashing; empty node → `emptyHash`; singleton
      promotion; **general same-value collapse** (all children evaluate to one
      value, arity ≥ 2 → that value); standard node hashing. The all-null
      collapse is the dominant instance of the same-value collapse, not a
      separate rule — `evalAllNull` is its `value = nullDigest` specialization,
      retained because activity is read against `nullDigest`. -/
  noncomputable def eval (L : Nat) : NaryTree (List UInt8) → Digest
    | NaryTree.leaf data => leafHash data
    | NaryTree.node [] => emptyHash
    | NaryTree.node [c] => eval L c
    | NaryTree.node (a :: b :: rest) =>
        let ds := evalMap L (a :: b :: rest)
        if ds.all (· == eval L a) then eval L a
        else nodeHash ds
  termination_by t => nsize t
  decreasing_by
    all_goals simp [nsize, nlsize]
    all_goals omega

  /-- Whether every child of a node evaluates to the null digest — the
      `value = nullDigest` instance of same-value collapse, kept because
      activity is read against the null constant. -/
  noncomputable def evalAllNull (L : Nat) : List (NaryTree (List UInt8)) → Bool
    | [] => true
    | c :: cs => (eval L c == nullDigest L) && evalAllNull L cs
  termination_by cs => nlsize cs
  decreasing_by
    all_goals simp [nlsize]

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

/-- The same-value collapse guard, reflected: every child of a node (arity ≥ 2)
    evaluates to the head child's digest. The boolean the `eval` collapse arm
    branches on. -/
theorem evalAllEq_iff (L : Nat) (a b : NaryTree (List UInt8))
    (rest : List (NaryTree (List UInt8))) :
    ((evalMap L (a :: b :: rest)).all (· == eval L a) = true)
      ↔ ∀ t ∈ (a :: b :: rest), eval L t = eval L a := by
  rw [evalMap_eq_map]
  constructor
  · intro h t ht
    have := (List.all_eq_true.mp h) (eval L t) (by
      rw [List.mem_map]; exact ⟨t, ht, rfl⟩)
    simpa using this
  · intro h
    rw [List.all_eq_true]
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    simpa using h t ht

/-- **General same-value collapse equation, arity ≥ 2.** A node all of whose
    children evaluate to one value `v` evaluates to `v`. The all-null collapse
    (`v = nullDigest`) is the dominant instance. -/
theorem eval_collapse_node (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2) {v : Digest}
    (h_all_eq : ∀ t ∈ children, eval L t = v) :
    eval L (NaryTree.node children) = v := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have ha : eval L a = v := h_all_eq a (by simp)
  have hall : ∀ t ∈ (a :: b :: rest), eval L t = eval L a := by
    intro t ht; rw [h_all_eq t ht, ha]
  have hguard : (evalMap L (a :: b :: rest)).all (· == eval L a) = true :=
    (evalAllEq_iff L a b rest).mpr hall
  simp only [eval]
  rw [if_pos hguard, ha]

/-- Flat null promotion equation, arity ≥ 2 (was `axiom eval_flat_null_node`).
    The `value = nullDigest` instance of the general collapse. -/
theorem eval_flat_null_node (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_all_null : ∀ t ∈ children, eval L t = nullDigest L) :
    eval L (NaryTree.node children) = nullDigest L :=
  eval_collapse_node L children h_length h_all_null

/-- Standard node hashing equation, arity ≥ 2 with two children of different
    value (was `axiom eval_node_hash`, generalized: hashing fires whenever the
    children are *not* all equal, of which "a non-null child amid nulls" is one
    instance). -/
theorem eval_node_hash (L : Nat) (children : List (NaryTree (List UInt8)))
    (h_length : children.length ≥ 2)
    (h_some : ∃ t ∈ children, ∃ u ∈ children, eval L t ≠ eval L u) :
    eval L (NaryTree.node children) = nodeHash (children.map (eval L)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, children = a :: b :: rest := by
    match children, h_length with
    | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
  have hNot : ¬ ((evalMap L (a :: b :: rest)).all (· == eval L a) = true) := by
    rw [evalAllEq_iff]
    intro hall
    obtain ⟨t, ht, u, hu, hne⟩ := h_some
    exact hne ((hall t ht).trans (hall u hu).symm)
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

/-! ## Canonical inclusion proofs (structural — Merkle Spine)

The inclusion-proof material below is structural: it pins the proof *shape* over
the positional topology and binds a leaf to its log position. It carries no epoch
hypothesis (the combined-root / binding-root / timeline material that once sat
between the evaluator and this section now lives in `EMLProof.Epoch`). Its only
collision lever is `NodeHashCollision` on the structural `nodeHash`, defined at the
top of this module. -/

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

/-- Reconstructs the root hash from a leaf and a proof path.

    This is the legacy transcription of the Rust verifier's fold. Under
    **canonical proof encoding** the `step.siblings.isEmpty` (promoted/zero-
    sibling) branch is dead: such steps are rejected, not passed through. The
    canonical model with its proved properties is `foldCanonical` /
    `CanonicalPath` in the "Canonical inclusion proofs" section below. -/
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

/-! ## Canonical inclusion proofs — soundness and non-malleability

Under **canonical proof encoding**, zero-sibling ("promoted") steps are
*rejected*: honest provers omit them, because implicit promotion elevates a
digest to its parent slot without hashing, so a promoted step is a hash no-op.
Every step of an accepted proof therefore strictly hashes.

This is distinct from flat null promotion (`eval_flat_null_promotion`), a
null-*valued* collapse (N₀) that appears as null-*valued* siblings; here we
reject zero-*sibling* steps. The two mechanisms are independent.

The log skeleton pinned by `(k, index, tree_size)` is the security boundary
(exact length, per-step position, per-level sibling count). Its concrete
computation is the shared topology module (`neml/src/topology.rs`); the theorems
below take it as an abstract predicate `SkeletonValid`, so they hold for whatever
pinning that module enforces. -/

/-- A step strictly hashes iff it carries at least one sibling. -/
def StrictStep (s : ProofStep) : Prop := s.siblings ≠ []

/-- A canonical path contains no zero-sibling (promoted) steps. -/
def CanonicalPath (path : List ProofStep) : Prop := ∀ s ∈ path, StrictStep s

/-- One strictly-hashing fold step: hash the path node into its slot among the
    siblings. Under `CanonicalPath` this is the only behavior that occurs (the
    `reconstructPathRoot` pass-through branch is dead). -/
noncomputable def applyStep (cur : Digest) (s : ProofStep) : Digest :=
  nodeHash (insertAt s.position cur s.siblings)

/-- Reconstruct the root by strictly hashing along a canonical path. -/
noncomputable def foldCanonical (leaf : Digest) (path : List ProofStep) : Digest :=
  path.foldl applyStep leaf

/-- **Canonical encoding rejects promoted steps.** Any path containing a
    zero-sibling step is non-canonical, hence rejected. This closes the
    prepend-a-promoted-step malleability: padded proofs are no longer accepted. -/
theorem not_canonical_of_promoted (path : List ProofStep)
    (h : ∃ s ∈ path, s.siblings = []) : ¬ CanonicalPath path := by
  obtain ⟨s, hmem, hs⟩ := h
  intro hcanon
  exact (hcanon s hmem) hs

/-- The canonical inclusion verifier's accept relation. Trusted parameters
    `(k, index, tree_size)` come from a signed tree head. The path splits at
    `boundary`: the leading steps are the subtree prefix (hashing `leaf` up to
    its log-position subtree root) and the trailing steps are the log skeleton,
    pinned to log position `index` by `SkeletonValid`. The whole path is
    canonical and strictly hashes `leaf` to `root`. -/
def Accepts (SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop)
    (k index treeSize : Nat) (leaf root : Digest) (path : List ProofStep) : Prop :=
  CanonicalPath path ∧
  foldCanonical leaf path = root ∧
  ∃ boundary, boundary ≤ path.length ∧ SkeletonValid k index treeSize (path.drop boundary)

/-- **Inclusion soundness (existential).** An accepting canonical proof for
    `(leaf, index, tree_size, root)` exhibits a subtree root `R` at log position
    `index` such that `leaf` hashes up to `R` at some depth `d`, and `R` folds
    through the pinned log skeleton to `root`. Depth is existential: implicit
    promotion makes a promoted digest equal its parent slot, so the claim binds
    the log *position*, never the depth (Cyphr SPEC §2.2.12). -/
theorem inclusion_soundness
    (SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop)
    (k index treeSize : Nat) (leaf root : Digest) (path : List ProofStep)
    (h : Accepts SkeletonValid k index treeSize leaf root path) :
    ∃ (R : Digest) (d : Nat), d ≤ path.length ∧
      foldCanonical leaf (path.take d) = R ∧
      SkeletonValid k index treeSize (path.drop d) ∧
      foldCanonical R (path.drop d) = root := by
  obtain ⟨_hcanon, hfolds, boundary, hble, hskel⟩ := h
  refine ⟨foldCanonical leaf (path.take boundary), boundary, hble, rfl, hskel, ?_⟩
  have hsplit : foldCanonical leaf (path.take boundary ++ path.drop boundary) = root := by
    rw [List.take_append_drop]; exact hfolds
  rw [foldCanonical, List.foldl_append] at hsplit
  exact hsplit

/-! Helper lemmas for `inclusion_proof_unique`: injectivity of `insertAt`,
    back-decomposition of lists, indexing across appends, and the
    fold-append step. -/

theorem insertAt_ne_nil {α : Type} (n : Nat) (x : α) (xs : List α) :
    insertAt n x xs ≠ [] := by
  induction xs generalizing n with
  | nil =>
    simp [insertAt]
  | cons y ys ih =>
    cases n with
    | zero =>
      simp [insertAt]
    | succ m =>
      simp [insertAt]

theorem insertAt_injective {α : Type} (n : Nat) (x y : α) (xs ys : List α)
    (h : insertAt n x xs = insertAt n y ys) : x = y ∧ xs = ys := by
  induction n generalizing xs ys with
  | zero =>
    have hxs : insertAt 0 x xs = x :: xs := by
      cases xs <;> rfl
    have hys : insertAt 0 y ys = y :: ys := by
      cases ys <;> rfl
    rw [hxs, hys] at h
    injection h with hxy hxsys
    exact ⟨hxy, hxsys⟩
  | succ m ih =>
    cases xs with
    | nil =>
      have hx : insertAt (m + 1) x [] = [x] := rfl
      rw [hx] at h
      cases ys with
      | nil =>
        have hy : insertAt (m + 1) y [] = [y] := rfl
        rw [hy] at h
        injection h with hxy
        exact ⟨hxy, rfl⟩
      | cons z zs =>
        have hy : insertAt (m + 1) y (z :: zs) = z :: insertAt m y zs := rfl
        rw [hy] at h
        injection h with _ h2
        have hne := insertAt_ne_nil m y zs
        rw [← h2] at hne
        contradiction
    | cons z zs =>
      have hx : insertAt (m + 1) x (z :: zs) = z :: insertAt m x zs := rfl
      rw [hx] at h
      cases ys with
      | nil =>
        have hy : insertAt (m + 1) y [] = [y] := rfl
        rw [hy] at h
        injection h with _ h2
        have hne := insertAt_ne_nil m x zs
        rw [h2] at hne
        contradiction
      | cons w ws =>
        have hy : insertAt (m + 1) y (w :: ws) = w :: insertAt m y ws := rfl
        rw [hy] at h
        injection h with hzw h2
        have ih_res := ih zs ws h2
        obtain ⟨hxy, hzs⟩ := ih_res
        rw [hzw, hzs]
        exact ⟨hxy, rfl⟩

theorem list_decomp_last {α : Type} {m : Nat} (l : List α) (h : l.length = m + 1) :
    ∃ l' x, l = l' ++ [x] ∧ l'.length = m := by
  induction l generalizing m with
  | nil =>
    contradiction
  | cons y ys ih =>
    cases m with
    | zero =>
      cases ys with
      | nil =>
        refine ⟨[], y, rfl, rfl⟩
      | cons z zs =>
        simp only [List.length_cons] at h
        omega
    | succ k =>
      have hlen : ys.length = k + 1 := by
        simp only [List.length_cons] at h
        omega
      obtain ⟨ys', x, hys_eq, hys'_len⟩ := ih hlen
      rw [hys_eq]
      refine ⟨y :: ys', x, rfl, ?_⟩
      simp [hys'_len]

theorem get?_append_left {α : Type} (xs : List α) (ys : List α) (i : Nat) (h : i < xs.length) :
    (xs ++ ys)[i]? = xs[i]? := by
  induction xs generalizing i with
  | nil =>
    contradiction
  | cons z zs ih =>
    cases i with
    | zero =>
      rfl
    | succ j =>
      have h2 : j < zs.length := by
        simp only [List.length_cons] at h
        omega
      exact ih j h2

theorem get?_append_last {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  induction xs with
  | nil =>
    rfl
  | cons z zs ih =>
    exact ih

theorem foldCanonical_append_last (leaf : Digest) (p' : List ProofStep) (s : ProofStep) :
    foldCanonical leaf (p' ++ [s]) = applyStep (foldCanonical leaf p') s := by
  simp [foldCanonical]

theorem foldCanonical_unique_of_len (n : Nat) (leaf : Digest) (p₁ p₂ : List ProofStep)
    (hlen1 : p₁.length = n)
    (hlen2 : p₂.length = n)
    (hpos : ∀ i < n, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position)
    (heq : foldCanonical leaf p₁ = foldCanonical leaf p₂)
    (hcol : ¬ NodeHashCollision) :
    p₁ = p₂ := by
  induction n generalizing leaf p₁ p₂ with
  | zero =>
    have hp1 : p₁ = [] := by
      cases p₁ with
      | nil => rfl
      | cons x xs =>
        simp only [List.length_cons] at hlen1
        omega
    have hp2 : p₂ = [] := by
      cases p₂ with
      | nil => rfl
      | cons x xs =>
        simp only [List.length_cons] at hlen2
        omega
    rw [hp1, hp2]
  | succ m ih =>
    obtain ⟨p₁', s₁, hp1_eq, hp1'_len⟩ := list_decomp_last p₁ hlen1
    obtain ⟨p₂', s₂, hp2_eq, hp2'_len⟩ := list_decomp_last p₂ hlen2
    rw [hp1_eq, hp2_eq] at heq
    rw [foldCanonical_append_last, foldCanonical_append_last] at heq
    simp only [applyStep] at heq
    have h_node_eq : insertAt s₁.position (foldCanonical leaf p₁') s₁.siblings = insertAt s₂.position (foldCanonical leaf p₂') s₂.siblings := by
      by_contra hc
      apply hcol
      refine ⟨insertAt s₁.position (foldCanonical leaf p₁') s₁.siblings, insertAt s₂.position (foldCanonical leaf p₂') s₂.siblings, hc, heq⟩
    have hpos_last : (p₁[m]?).map ProofStep.position = (p₂[m]?).map ProofStep.position := by
      apply hpos
      omega
    rw [hp1_eq, hp2_eq] at hpos_last
    have hp1_last_eq : (p₁' ++ [s₁])[p₁'.length]? = some s₁ := get?_append_last p₁' s₁
    have hp2_last_eq : (p₂' ++ [s₂])[p₂'.length]? = some s₂ := get?_append_last p₂' s₂
    rw [hp1'_len] at hp1_last_eq
    rw [hp2'_len] at hp2_last_eq
    rw [hp1_last_eq, hp2_last_eq] at hpos_last
    simp only [Option.map, Option.some.injEq] at hpos_last
    rw [hpos_last] at h_node_eq
    have h_inj := insertAt_injective s₂.position (foldCanonical leaf p₁') (foldCanonical leaf p₂') s₁.siblings s₂.siblings h_node_eq
    obtain ⟨h_fold_eq, h_sib_eq⟩ := h_inj
    have h_step_eq : s₁ = s₂ := by
      cases s₁
      cases s₂
      simp only [ProofStep.mk.injEq] at *
      exact ⟨h_sib_eq, hpos_last⟩
    have hpos' : ∀ i < m, (p₁'[i]?).map ProofStep.position = (p₂'[i]?).map ProofStep.position := by
      intro i hi
      have hpos_i := hpos i (by omega)
      rw [hp1_eq, hp2_eq] at hpos_i
      have h_i_len1 : i < p₁'.length := by omega
      have h_i_len2 : i < p₂'.length := by omega
      have hp1'_i : (p₁' ++ [s₁])[i]? = p₁'[i]? := get?_append_left p₁' [s₁] i h_i_len1
      have hp2'_i : (p₂' ++ [s₂])[i]? = p₂'[i]? := get?_append_left p₂' [s₂] i h_i_len2
      rw [hp1'_i, hp2'_i] at hpos_i
      exact hpos_i
    have hp_eq : p₁' = p₂' := ih leaf p₁' p₂' hp1'_len hp2'_len hpos' h_fold_eq
    rw [hp1_eq, hp2_eq, hp_eq, h_step_eq]

/-- **Inclusion proof-encoding uniqueness (non-malleability).** With zero-sibling
    steps rejected, every remaining step strictly hashes, and the shared topology
    module pins the proof *shape* from `(k, index, tree_size)`: the accepted
    path's length and its per-step position are determined (hypotheses `hlen`,
    `hpos` — what `topology.rs` guarantees, modeled as premises until that module
    is ported to Lean). The only remaining freedom is the sibling *values*, which
    the fold pins to `root`. Hence for a fixed `(leaf, index, tree_size, root)`
    there is at most one accepting canonical path — modulo a `nodeHash` collision
    (where the path could be rerouted by colliding an internal node hash).

    Without `hlen`/`hpos` the claim is false (two paths of different lengths can
    both fold to a fixed point, and a fixed `position` is what makes the
    per-step `insertAt` recoverable); they encode the injective child-ordering
    the canonical-encoding decision relies on.

    Proved by back-to-front induction (`foldCanonical_unique_of_len`): each final
    `nodeHash` is equal, so its preimages either collide or, with `position`
    pinned, `insertAt` injectivity forces the steps and the running digests
    equal, recursing on the prefixes. -/
theorem inclusion_proof_unique
    (SkeletonValid : Nat → Nat → Nat → List ProofStep → Prop)
    (k index treeSize : Nat) (leaf root : Digest) (p₁ p₂ : List ProofStep)
    (h₁ : Accepts SkeletonValid k index treeSize leaf root p₁)
    (h₂ : Accepts SkeletonValid k index treeSize leaf root p₂)
    (hlen : p₁.length = p₂.length)
    (hpos : ∀ i : Nat, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position) :
    p₁ = p₂ ∨ NodeHashCollision := by
  by_cases hcol : NodeHashCollision
  · exact Or.inr hcol
  · have hf₁ := h₁.2.1
    have hf₂ := h₂.2.1
    have hpos_lim : ∀ i < p₁.length, (p₁[i]?).map ProofStep.position = (p₂[i]?).map ProofStep.position := by
      intro i _
      exact hpos i
    have heq : p₁ = p₂ := foldCanonical_unique_of_len p₁.length leaf p₁ p₂ rfl hlen.symm hpos_lim (hf₁.trans hf₂.symm) hcol
    exact Or.inl heq

end NEML

/-!
## Trust base (axiom inventory)

The structural Merkle Spine declares **no new axiom**: its entire trust base is the
four `Foundations` axioms — `Digest`, `Digest.nonempty`, `H`, `digestToBytes` —
plus the Lean built-ins `propext`, `Classical.choice`, `Quot.sound`. `#print axioms`
on every theorem in this module reports a subset of those.

Collision resistance is never assumed: `null_collision` makes the
`leaf(b"null") = N₀` identity provable, and the inclusion theorems carry their hash
assumptions as explicit *hypotheses* (`¬ NodeHashCollision`), not axioms. The
combinator half — the combined root, the binding root, and the timeline-binding
non-equivocation that consume these structural roots as opaque digests — lives in
`EMLProof.Epoch` over the same four axioms; it too adds none.

Every theorem in this file is now fully proved and sorry-free.
-/
