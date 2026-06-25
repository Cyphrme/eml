import EMLProof.Spine

namespace NEML

mutual
  def treeSize {α : Type} : NaryTree α → Nat
    | NaryTree.leaf _ => 1
    | NaryTree.node children => 1 + listSize children

  def listSize {α : Type} : List (NaryTree α) → Nat
    | [] => 0
    | c :: cs => 1 + treeSize c + listSize cs
end

lemma treeSize_lt_listSize {α : Type} (children : List (NaryTree α)) (c : NaryTree α)
    (hc : c ∈ children) : treeSize c < listSize children := by
  induction children with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.mem_cons] at hc
    rcases hc with rfl | h_mem
    · -- c = hd
      simp [listSize]
      omega
    · -- c ∈ tl
      have ih_tl := ih h_mem
      simp [listSize]
      omega

mutual
  noncomputable def evalConstructive (L : Nat) : NaryTree (Option (List UInt8)) → Digest
    | NaryTree.leaf none => nullDigest L
    | NaryTree.leaf (some data) => leafHash data
    | NaryTree.node [] => emptyHash
    | NaryTree.node [c] => evalConstructive L c
    | NaryTree.node (a :: b :: rest) =>
        -- General same-value collapse: a node all of whose children evaluate to
        -- one value folds to that value; the all-null run is its dominant
        -- instance. `evalConstructiveAllNull` is the `value = nullDigest`
        -- specialization (activity is read against the null constant).
        if evalConstructiveAllEq L (a :: b :: rest) (evalConstructive L a) then
          evalConstructive L a
        else
          nodeHash (evalConstructiveMap L (a :: b :: rest))
  termination_by t => treeSize t
  decreasing_by
    all_goals
      simp [treeSize, listSize]
      try omega

  /-- Whether every child of a node evaluates to the given value `v` — the guard
      of the general same-value collapse. -/
  noncomputable def evalConstructiveAllEq (L : Nat) :
      List (NaryTree (Option (List UInt8))) → Digest → Bool
    | [], _ => true
    | c :: cs, v => (evalConstructive L c == v) && evalConstructiveAllEq L cs v
  termination_by children => listSize children
  decreasing_by
    all_goals
      simp [listSize]
      try omega

  noncomputable def evalConstructiveAllNull (L : Nat) :
      List (NaryTree (Option (List UInt8))) → Bool
    | [] => true
    | c :: cs => evalConstructive L c == nullDigest L && evalConstructiveAllNull L cs
  termination_by children => listSize children
  decreasing_by
    all_goals
      simp [listSize]
      try omega

  noncomputable def evalConstructiveMap (L : Nat) :
      List (NaryTree (Option (List UInt8))) → List Digest
    | [] => []
    | c :: cs => evalConstructive L c :: evalConstructiveMap L cs
  termination_by children => listSize children
  decreasing_by
    all_goals
      simp [listSize]
      try omega
end

/-- The all-null guard is the `value = nullDigest` instance of the all-equal
    guard: every child null ⟺ every child equals `nullDigest`. -/
theorem evalConstructiveAllNull_eq_allEq (L : Nat)
    (children : List (NaryTree (Option (List UInt8)))) :
    evalConstructiveAllNull L children
      = evalConstructiveAllEq L children (nullDigest L) := by
  induction children with
  | nil => simp only [evalConstructiveAllNull, evalConstructiveAllEq]
  | cons c cs ih => simp only [evalConstructiveAllNull, evalConstructiveAllEq, ih]

/-- **All-null collapse equation** (the dominant instance of same-value collapse).
    A node of arity ≥ 2 whose every child evaluates to the null digest evaluates
    to the null digest. -/
theorem evalConstructive_null_collapse (L : Nat) (a b : NaryTree (Option (List UInt8)))
    (rest : List (NaryTree (Option (List UInt8))))
    (h_all : evalConstructiveAllNull L (a :: b :: rest) = true) :
    evalConstructive L (NaryTree.node (a :: b :: rest)) = nullDigest L := by
  have ha : evalConstructive L a = nullDigest L := by
    rw [evalConstructiveAllNull] at h_all
    exact (beq_iff_eq.mp (Bool.and_elim_left h_all))
  have hguard : evalConstructiveAllEq L (a :: b :: rest) (evalConstructive L a) = true := by
    rw [ha, ← evalConstructiveAllNull_eq_allEq]; exact h_all
  simp only [evalConstructive]
  rw [if_pos hguard, ha]

/-- **Node hashing equation.** A node of arity ≥ 2 that is not an all-equal
    collapse (some child differs from the head) hashes its children. -/
theorem evalConstructive_node_hash (L : Nat) (a b : NaryTree (Option (List UInt8)))
    (rest : List (NaryTree (Option (List UInt8))))
    (h_not : evalConstructiveAllEq L (a :: b :: rest) (evalConstructive L a) = false) :
    evalConstructive L (NaryTree.node (a :: b :: rest))
      = nodeHash (evalConstructiveMap L (a :: b :: rest)) := by
  simp only [evalConstructive]
  rw [if_neg (by rw [h_not]; simp)]

/-- `evalConstructiveMap` agrees with `List.map (evalConstructive L)`. -/
theorem evalConstructiveMap_eq_map (L : Nat)
    (children : List (NaryTree (Option (List UInt8)))) :
    evalConstructiveMap L children = children.map (evalConstructive L) := by
  induction children with
  | nil => simp [evalConstructiveMap]
  | cons c cs ih => simp [evalConstructiveMap, ih]

/-- The digest-list image of `evalConstructiveAllEq`: a node's children all
    evaluate to `v` ⟺ the digest list is all-`v`. -/
theorem evalConstructiveAllEq_map (L : Nat)
    (children : List (NaryTree (Option (List UInt8)))) (v : Digest) :
    evalConstructiveAllEq L children v
      = (children.map (evalConstructive L)).all (· == v) := by
  induction children with
  | nil => simp [evalConstructiveAllEq]
  | cons c cs ih => simp only [evalConstructiveAllEq, List.map_cons, List.all_cons, ih]

/-- The node-combining function on digest lists, mirroring the `evalConstructive`
    node arms exactly (including the general same-value collapse). -/
noncomputable def combineC : List Digest → Digest
  | [] => emptyHash
  | [d] => d
  | a :: b :: zs => if (a :: b :: zs).all (· == a) then a else nodeHash (a :: b :: zs)

/-- **`evalConstructive` factors through `combineC`.** A node's digest depends on
    its children only through their evaluated digests. This is what makes the
    compression-preserves-eval and decompression proofs recurse on the child
    digest list rather than the tree structure. -/
theorem evalConstructive_node_combine (L : Nat)
    (children : List (NaryTree (Option (List UInt8)))) :
    evalConstructive L (NaryTree.node children)
      = combineC (children.map (evalConstructive L)) := by
  match children with
  | [] => simp only [evalConstructive, combineC, List.map_nil]
  | [c] => simp only [evalConstructive, combineC, List.map_cons, List.map_nil]
  | a :: b :: rest =>
    have hmap : (a :: b :: rest).map (evalConstructive L)
        = evalConstructive L a :: evalConstructive L b
            :: rest.map (evalConstructive L) := by simp
    by_cases hcol : evalConstructiveAllEq L (a :: b :: rest) (evalConstructive L a) = true
    · rw [evalConstructive, if_pos hcol, hmap]
      rw [combineC, if_pos]
      · rw [← hmap, ← evalConstructiveAllEq_map]; exact hcol
    · simp only [Bool.not_eq_true] at hcol
      rw [evalConstructive_node_hash L a b rest hcol, evalConstructiveMap_eq_map, hmap]
      rw [combineC, if_neg]
      rw [← hmap, ← evalConstructiveAllEq_map, hcol]; simp

noncomputable def compress (L : Nat) (t : NaryTree (Option (List UInt8))) :
    NaryTree (Option (List UInt8)) :=
  if evalConstructive L t == nullDigest L then
    NaryTree.leaf none
  else
    match t with
    | NaryTree.leaf val => NaryTree.leaf val
    | NaryTree.node children => NaryTree.node (children.map (compress L))
termination_by treeSize t
decreasing_by
  rename_i c hc
  have h_c_lt := treeSize_lt_listSize children c hc
  simp [treeSize]
  omega

/-- Nested induction principle for NaryTree. -/
theorem NaryTree.ind {α : Type} {P : NaryTree α → Prop}
    (h_leaf : ∀ val, P (NaryTree.leaf val))
    (h_node : ∀ children, (∀ c ∈ children, P c) → P (NaryTree.node children))
    (t : NaryTree α) : P t := by
  have h_wf (n : Nat) (t : NaryTree α) (h : treeSize t < n) : P t := by
    induction n generalizing t with
    | zero => contradiction
    | succ n' ih =>
      cases t with
      | leaf val => exact h_leaf val
      | node children =>
        apply h_node
        intro c hc
        apply ih c
        have h_c_lt := treeSize_lt_listSize children c hc
        have h_node_lt : listSize children < treeSize (NaryTree.node children) := by
          simp [treeSize]
        omega
  exact h_wf (treeSize t + 1) t (by omega)

/-- Theorem: A compressed tree always evaluates to the exact same digest as the original tree. -/
theorem eval_compress (L : Nat) (t : NaryTree (Option (List UInt8))) :
    evalConstructive L (compress L t) = evalConstructive L t := by
  induction t using NaryTree.ind with
  | h_leaf val =>
    simp only [compress]
    split
    · rename_i h_eval
      rw [beq_iff_eq] at h_eval
      simp only [evalConstructive]
      exact h_eval.symm
    · rfl
  | h_node children ih =>
    simp only [compress]
    split
    · rename_i h_eval
      rw [beq_iff_eq] at h_eval
      simp only [evalConstructive]
      exact h_eval.symm
    · -- The else-branch: compress recurses on children. `evalConstructive`
      -- factors through `combineC` of the child digests, and compressing the
      -- children preserves that digest list (per-child IH), so the node digest
      -- is unchanged — no case split on the (now general) collapse guard needed.
      rename_i h_eval
      rw [evalConstructive_node_combine, evalConstructive_node_combine, List.map_map]
      congr 1
      apply List.map_congr_left
      intro c hc
      simpa using ih c hc

/-- Predicate enforcing that a tree is a perfect k-ary tree of height h. -/
def IsPerfectKary (k : Nat) : Nat → NaryTree (Option (List UInt8)) → Prop
  | 0, NaryTree.leaf _ => True
  | 0, NaryTree.node _ => False
  | _ + 1, NaryTree.leaf _ => False
  | h + 1, NaryTree.node children => children.length = k ∧ ∀ c ∈ children, IsPerfectKary k h c

/-- The expansion function: expands a compressed leaf representing all-null subtrees
    back into a perfect k-ary tree of height h consisting entirely of null leaves. -/
def expand (k : Nat) : Nat → NaryTree (Option (List UInt8)) → NaryTree (Option (List UInt8))
  | 0, t => t
  | h + 1, NaryTree.leaf none =>
      NaryTree.node (List.replicate k (expand k h (NaryTree.leaf none)))
  | _ + 1, NaryTree.leaf (some data) =>
      NaryTree.leaf (some data)
  | h + 1, NaryTree.node children =>
      NaryTree.node (children.map (expand k h))

/-- Helper lemma: List.all over a replicated list. -/
lemma all_replicate (L : Nat) (k : Nat) (x : NaryTree (Option (List UInt8)))
    (h_x : evalConstructive L x = nullDigest L) :
    evalConstructiveAllNull L (List.replicate k x) = true := by
  induction k with
  | zero =>
    simp [List.replicate, evalConstructiveAllNull]
  | succ k' ih =>
    simp only [List.replicate_succ, evalConstructiveAllNull, h_x, ih, beq_self_eq_true,
      Bool.true_and]

/-- Helper lemma: eval of a perfect all-null tree of height h is always nullDigest L. -/
theorem eval_perfect_null (L : Nat) (k : Nat) (h : Nat) (_hk : k ≥ 1) :
    evalConstructive L (expand k h (NaryTree.leaf none)) = nullDigest L := by
  induction h with
  | zero =>
    simp [expand, evalConstructive]
  | succ h' ih =>
    cases k with
    | zero => contradiction
    | succ k' =>
      cases k' with
      | zero =>
        simp only [expand, List.replicate_succ, List.replicate_zero, evalConstructive, ih]
      | succ k'' =>
        -- k >= 2: expand produces a node of `k''+2` null children — the all-null
        -- collapse (the dominant instance of same-value collapse) yields null.
        have h_all : evalConstructiveAllNull L
          (List.replicate (k'' + 2) (expand (k'' + 2) h' (NaryTree.leaf none))) = true := by
          exact all_replicate L (k'' + 2) (expand (k'' + 2) h' (NaryTree.leaf none)) ih
        simp only [expand]
        -- Expose the `a :: b :: rest` shape of the replicate (length ≥ 2).
        rw [show List.replicate (k'' + 2) (expand (k'' + 2) h' (NaryTree.leaf none))
              = expand (k'' + 2) h' (NaryTree.leaf none)
                :: expand (k'' + 2) h' (NaryTree.leaf none)
                :: List.replicate k'' (expand (k'' + 2) h' (NaryTree.leaf none)) from by
          rw [show k'' + 2 = (k'' + 1) + 1 from rfl, List.replicate_succ,
            show k'' + 1 = k'' + 1 from rfl, List.replicate_succ]]
        apply evalConstructive_null_collapse
        rw [show expand (k'' + 2) h' (NaryTree.leaf none)
              :: expand (k'' + 2) h' (NaryTree.leaf none)
              :: List.replicate k'' (expand (k'' + 2) h' (NaryTree.leaf none))
            = List.replicate (k'' + 2) (expand (k'' + 2) h' (NaryTree.leaf none)) from by
          rw [show k'' + 2 = (k'' + 1) + 1 from rfl, List.replicate_succ, List.replicate_succ]]
        exact h_all

lemma all_null_eq_true_iff (L : Nat) (children : List (NaryTree (Option (List UInt8)))) :
    evalConstructiveAllNull L children = true ↔
    ∀ c ∈ children, evalConstructive L c = nullDigest L := by
  induction children with
  | nil =>
    simp [evalConstructiveAllNull]
  | cons c cs ih =>
    simp only [evalConstructiveAllNull, Bool.and_eq_true, beq_iff_eq, ih, List.mem_cons]
    constructor
    · intro ⟨hc, hcs⟩ x hx
      rcases hx with rfl | h_mem
      · exact hc
      · exact hcs x h_mem
    · intro h
      constructor
      · exact h c (Or.inl rfl)
      · intro x hx
        exact h x (Or.inr hx)

lemma map_length (L : Nat) (children : List (NaryTree (Option (List UInt8)))) :
    (evalConstructiveMap L children).length = children.length := by
  induction children with
  | nil =>
    simp [evalConstructiveMap]
  | cons c cs ih =>
    simp [evalConstructiveMap, ih]

/-- Helper lemma: if a node evaluates to nullDigest L, all of its children
    must evaluate to nullDigest L. -/
lemma eval_node_eq_null_implies_all_null (L : Nat)
    (empty_hash_neq_null : emptyHash ≠ nullDigest L)
    (node_hash_neq_null : ∀ (children : List Digest),
      children.length ≥ 2 → nodeHash children ≠ nullDigest L)
    (children : List (NaryTree (Option (List UInt8))))
    (h_eval : evalConstructive L (NaryTree.node children) = nullDigest L) :
    ∀ c ∈ children, evalConstructive L c = nullDigest L := by
  cases h_children : children with
  | nil =>
    rw [h_children] at h_eval
    simp only [evalConstructive] at h_eval
    have h_neq := empty_hash_neq_null
    contradiction
  | cons x xs =>
    cases h_xs : xs with
    | nil =>
      have h_single : children = [x] := by rw [h_children, h_xs]
      rw [h_single] at h_eval
      simp only [evalConstructive] at h_eval
      intro c hc
      have : c = x := List.mem_singleton.mp hc
      rw [this]
      exact h_eval
    | cons y ys =>
      have h_len : children.length ≥ 2 := by
        rw [h_children, h_xs]
        simp [List.length]
      have h_all : evalConstructiveAllNull L children = true := by
        by_contra h_not_all
        have h_children_eq : children = x :: y :: ys := by rw [h_children, h_xs]
        -- Under general collapse, a node evaluating to null is either (a) an
        -- all-equal collapse whose common value is null (⟹ every child null), or
        -- (b) a genuine `nodeHash` equal to null (collapse ambiguity, ruled out by
        -- `node_hash_neq_null`). The hypothesis says the node is null, so we case
        -- on the collapse guard via the `combineC` factoring.
        rw [h_children_eq, evalConstructive_node_combine] at h_eval
        have hmap : (x :: y :: ys).map (evalConstructive L)
            = evalConstructive L x :: evalConstructive L y :: ys.map (evalConstructive L) := by
          simp
        rw [hmap] at h_eval
        by_cases hcol : (evalConstructive L x :: evalConstructive L y
            :: ys.map (evalConstructive L)).all (· == evalConstructive L x) = true
        · -- collapse fired: combineC = evalConstructive x = null, so every child
          -- evaluates to null, contradicting `h_not_all`.
          rw [combineC, if_pos hcol] at h_eval
          apply h_not_all
          rw [h_children_eq]
          have hxnull : evalConstructive L x = nullDigest L := h_eval
          have hall_eq : ∀ d ∈ (evalConstructive L x :: evalConstructive L y
              :: ys.map (evalConstructive L)), d = evalConstructive L x := by
            intro d hd
            have := List.all_eq_true.mp hcol d hd
            simpa using this
          rw [all_null_eq_true_iff]
          intro c hc
          have hcd : evalConstructive L c ∈ (x :: y :: ys).map (evalConstructive L) :=
            List.mem_map.mpr ⟨c, hc, rfl⟩
          rw [hmap] at hcd
          rw [hall_eq (evalConstructive L c) hcd, hxnull]
        · -- not a collapse: it hashes; node_hash_neq_null contradicts null.
          simp only [Bool.not_eq_true] at hcol
          rw [combineC, if_neg (by rw [hcol]; simp)] at h_eval
          have h_map_len : (evalConstructive L x :: evalConstructive L y
              :: ys.map (evalConstructive L)).length ≥ 2 := by simp
          exact node_hash_neq_null _ h_map_len h_eval
      have h_children_eq : children = x :: y :: ys := by rw [h_children, h_xs]
      have h_all_prop := h_all
      rw [h_children_eq] at h_all_prop
      rw [all_null_eq_true_iff] at h_all_prop
      exact h_all_prop

/-- Helper lemma: List.replicate is equal to l if l has length k and all elements are x. -/
lemma list_eq_replicate {α : Type} {x : α} (l : List α) (h_all : ∀ y ∈ l, y = x) :
    l = List.replicate l.length x := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have h_y : y = x := h_all y List.mem_cons_self
    have h_ys : ∀ z ∈ ys, z = x := fun z hz => h_all z (List.mem_cons_of_mem y hz)
    simp only [List.length_cons, List.replicate]
    rw [h_y, ih h_ys]
    simp only [List.length_replicate]

/-- Helper lemma: list map of identity is identity. -/
lemma map_id_of_all {α : Type} (l : List α) (f : α → α) (h : ∀ y ∈ l, f y = y) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons]
    have h_y : f y = y := h y List.mem_cons_self
    have h_ys : ∀ z ∈ ys, f z = z := fun z hz => h z (List.mem_cons_of_mem y hz)
    rw [h_y, ih h_ys]

/-- Theorem: A compressed perfect k-ary tree of height h can be expanded
    back to its exact original topology. -/
theorem expand_compress (L : Nat) (k : Nat) (h : Nat)
    (leaf_hash_neq_null : ∀ (data : List UInt8), leafHash data ≠ nullDigest L)
    (empty_hash_neq_null : emptyHash ≠ nullDigest L)
    (node_hash_neq_null : ∀ (children : List Digest),
      children.length ≥ 2 → nodeHash children ≠ nullDigest L)
    (t : NaryTree (Option (List UInt8)))
    (_hk : k ≥ 1) (h_perf : IsPerfectKary k h t) :
    expand k h (compress L t) = t := by
  induction h generalizing t with
  | zero =>
    cases t with
    | leaf val =>
      simp only [compress]
      split
      · rename_i h_eval
        rw [beq_iff_eq] at h_eval
        have h_eq : evalConstructive L (NaryTree.leaf val) = nullDigest L := h_eval
        cases val with
        | none => rfl
        | some data =>
          simp only [evalConstructive] at h_eq
          have h_neq := leaf_hash_neq_null data
          contradiction
      · rfl
    | node children =>
      contradiction
  | succ h' ih =>
    cases t with
    | leaf val =>
      contradiction
    | node children =>
      simp only [IsPerfectKary] at h_perf
      obtain ⟨h_len, h_all_perf⟩ := h_perf
      simp only [compress]
      split
      · rename_i h_eval
        rw [beq_iff_eq] at h_eval
        have h_eq : evalConstructive L (NaryTree.node children) = nullDigest L := h_eval
        have h_children_null := eval_node_eq_null_implies_all_null L
          empty_hash_neq_null node_hash_neq_null children h_eq
        simp only [expand]
        have h_map_eq : children = List.replicate k (expand k h' (NaryTree.leaf none)) := by
          have h_c_eq : ∀ c ∈ children, c = expand k h' (NaryTree.leaf none) := by
            intro c hc
            have h_c_null := h_children_null c hc
            have h_c_perf := h_all_perf c hc
            have ih_c := ih c h_c_perf
            have h_comp : compress L c = NaryTree.leaf none := by
              unfold compress
              rw [h_c_null]
              simp
            rw [← ih_c, h_comp]
          have h_repl := list_eq_replicate children h_c_eq
          rw [h_len] at h_repl
          exact h_repl
        rw [h_map_eq]
      · rename_i h_eval
        simp only [expand]
        have h_map_eq : (children.map (compress L)).map (expand k h') = children := by
          rw [List.map_map]
          have h_id : children.map (fun c => expand k h' (compress L c)) = children := by
            apply map_id_of_all
            intro c hc
            have h_perf_c := h_all_perf c hc
            exact ih c h_perf_c
          exact h_id
        rw [h_map_eq]

end NEML
