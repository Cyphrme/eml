import EMLProof.General.Policy

/-!
# EML Generalized Stack Root to MTH Equivalence

This module establishes that under any valid SplitPolicy, folding a stack of
completed subtrees whose sizes match `forestSizes f n` yields the same root as the
batch `generalized_mth f` over the flattened leaves.
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

/-- If n > 1 and f is a valid split policy, then forestSizes f n ends with f n. -/
theorem forestSizes_last {f : SplitPolicy} (hf : ValidSplitPolicy f) {n : Nat} (hn : n > 1) :
    forestSizes f n = forestSizes f (n - f n) ++ [f n] := by
  conv_lhs => unfold forestSizes
  have h_ne : n ≠ 0 := by omega
  have h_ne2 : n ≠ 1 := by omega
  rw [if_neg h_ne, if_neg h_ne2]
  have h_guard : f n > 0 ∧ f n < n := hf n hn
  rw [dif_pos h_guard]

/-- The elements of forestSizes are always positive. -/
theorem forestSizes_pos {f : SplitPolicy} (hf : ValidSplitPolicy f) (n : Nat) :
    ∀ x ∈ forestSizes f n, x > 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [forestSizes]
    · by_cases hn1 : n = 1
      · subst hn1; simp [forestSizes]
      · have hn : n > 1 := by omega
        rw [forestSizes_last hf hn]
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx_left | rfl
        · have h_guard : f n > 0 ∧ f n < n := hf n hn
          have h_lt : n - f n < n := by omega
          exact ih (n - f n) h_lt x hx_left
        · exact (hf n hn).1

/-- Unfolds generalized_mth definition when list length > 1. -/
theorem generalized_mth_unfold {α : Type} (f : SplitPolicy) (leaves : List (MerkleTree α))
    (h : leaves.length > 1) :
    generalized_mth f leaves =
      let k := f leaves.length
      if h_guard : k > 0 ∧ k < leaves.length then
        MerkleTree.node (generalized_mth f (leaves.take k)) (generalized_mth f (leaves.drop k))
      else
        MerkleTree.empty := by
  match leaves with
  | [] => simp at h
  | [_] => simp at h
  | a :: b :: rest =>
    conv_lhs => unfold generalized_mth

/-- Splits generalized_mth over concatenation when the split point matches the policy. -/
theorem generalized_mth_split {α : Type} (f : SplitPolicy) [hf : Fact (ValidSplitPolicy f)]
    (first second : List (MerkleTree α)) (h1 : first ≠ []) (h2 : second ≠ [])
    (h_split : f (first.length + second.length) = first.length) :
    generalized_mth f (first ++ second) =
      MerkleTree.node (generalized_mth f first) (generalized_mth f second) := by
  have h_len : (first ++ second).length > 1 := by
    have h1_len : first.length > 0 := by match first with | [] => contradiction | _ :: _ => simp
    have h2_len : second.length > 0 := by match second with | [] => contradiction | _ :: _ => simp
    simp; omega
  rw [generalized_mth_unfold f (first ++ second) h_len]
  simp only [List.length_append, h_split]
  have h_guard : first.length > 0 ∧ first.length < first.length + second.length := by
    have h1_len : first.length > 0 := by match first with | [] => contradiction | _ :: _ => simp
    have h2_len : second.length > 0 := by match second with | [] => contradiction | _ :: _ => simp
    omega
  rw [dif_pos h_guard]
  rw [List.take_append_length, List.drop_append_length]

/-- The generalized stackRoot equivalence: for any list of segments whose reversed
    lengths match the forestSizes of the flattened length, folding the stack is
    topologically isomorphic to generalized_mth. -/
theorem stackRoot_segments_eq_generalized_mth {α : Type} (f : SplitPolicy)
    [hf : Fact (ValidSplitPolicy f)] (segments : List (List (MerkleTree α)))
    (h_sizes : (segments.map List.length).reverse = forestSizes f segments.flatten.length) :
    stackRoot ((segments.map (generalized_mth f)).reverse) =
      generalized_mth f segments.flatten := by
  match segments with
  | [] =>
    simp [stackRoot, generalized_mth]
  | [s] =>
    simp [stackRoot, List.flatten]
  | first :: second :: rest =>
    have h_flatten_eq : (first :: second :: rest).flatten =
        first ++ (second :: rest).flatten := by simp
    have h_len_eq : (first :: second :: rest).flatten.length =
        first.length + (second :: rest).flatten.length := by
      rw [h_flatten_eq, List.length_append]

    have h_map : (first :: second :: rest).map (generalized_mth f) =
        generalized_mth f first :: (second :: rest).map (generalized_mth f) := rfl
    rw [h_map, List.reverse_cons]
    have h_nonempty : ((second :: rest).map (generalized_mth f)).reverse ≠ [] := by
      simp [List.reverse_eq_nil_iff]
    rw [stackRoot_snoc _ _ h_nonempty]

    have h_N_pos : (first :: second :: rest).flatten.length > 1 := by
      have h_sz := h_sizes
      rw [List.map_cons, List.reverse_cons] at h_sz
      match h_N : (first :: second :: rest).flatten.length with
      | 0 =>
        rw [h_N] at h_sz
        unfold forestSizes at h_sz
        change ((second :: rest).map List.length).reverse ++ [first.length] = [] at h_sz
        have h_len_eq :
            (((second :: rest).map List.length).reverse ++ [first.length]).length = 0 :=
          congr_arg List.length h_sz
        simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons]
          at h_len_eq
        omega
      | 1 =>
        rw [h_N] at h_sz
        unfold forestSizes at h_sz
        change ((second :: rest).map List.length).reverse ++ [first.length] = [1] at h_sz
        have h_len_eq :
            (((second :: rest).map List.length).reverse ++ [first.length]).length = 1 :=
          congr_arg List.length h_sz
        simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons]
          at h_len_eq
        omega
      | n + 2 => omega

    have h_fs_last := forestSizes_last hf.elim h_N_pos
    have h_sz_rw := h_sizes
    rw [h_fs_last] at h_sz_rw
    rw [List.map_cons, List.reverse_cons] at h_sz_rw

    have h_len_eq_fs : ((second :: rest).map List.length).reverse.length =
        (forestSizes f ((first :: second :: rest).flatten.length -
          f (first :: second :: rest).flatten.length)).length := by
      have h_len_eq_app : (((second :: rest).map List.length).reverse ++ [first.length]).length =
          (forestSizes f ((first :: second :: rest).flatten.length -
            f (first :: second :: rest).flatten.length) ++
              [f (first :: second :: rest).flatten.length]).length := by
        rw [h_sz_rw]
      simp only [List.length_append, List.length_singleton] at h_len_eq_app
      omega

    have h_last_eq : first.length = f (first :: second :: rest).flatten.length := by
      have h_last := List.append_inj_right h_sz_rw h_len_eq_fs
      injection h_last

    have h_append_eq : ((second :: rest).map List.length).reverse =
        forestSizes f ((first :: second :: rest).flatten.length -
          f (first :: second :: rest).flatten.length) :=
      List.append_inj_left' h_sz_rw rfl

    have h_sizes_rest : ((second :: rest).map List.length).reverse =
        forestSizes f (second :: rest).flatten.length := by
      rw [h_append_eq]
      have h_arg_eq : (first :: second :: rest).flatten.length -
          f (first :: second :: rest).flatten.length =
            (second :: rest).flatten.length := by
        omega
      rw [h_arg_eq]

    rw [stackRoot_segments_eq_generalized_mth f (second :: rest) h_sizes_rest]

    have h_first_ne : first ≠ [] := by
      intro h_nil
      have h_len_zero : first.length = 0 := by rw [h_nil, List.length_nil]
      rw [h_len_zero] at h_last_eq
      have h_f_pos := (hf.elim (first :: second :: rest).flatten.length h_N_pos).1
      omega

    have h_rest_len_pos : (second :: rest).flatten.length > 0 := by
      have h_sz_rest := h_sizes_rest
      by_contra hc
      have hc' : (second :: rest).flatten.length = 0 := by omega
      rw [hc'] at h_sz_rest
      unfold forestSizes at h_sz_rest
      have h_len_eq : ((second :: rest).map List.length).reverse.length = 0 :=
        congr_arg List.length h_sz_rest
      simp only [List.length_reverse, List.length_map, List.length_cons] at h_len_eq
      omega

    have h_second_len_pos : second.length > 0 := by
      have h_mem : second.length ∈ ((second :: rest).map List.length).reverse := by
        simp only [List.map_cons, List.reverse_cons, List.mem_append, List.mem_singleton]
        right; trivial
      rw [h_sizes_rest] at h_mem
      exact forestSizes_pos hf.elim (second :: rest).flatten.length second.length h_mem

    have h_rest_ne : (second :: rest).flatten ≠ [] := by
      intro h_nil
      rw [h_nil] at h_rest_len_pos
      contradiction

    have h_last_eq_rw : f (first.length + (second :: rest).flatten.length) = first.length := by
      have h_last_eq_symm := h_last_eq.symm
      have h_flat_len : (first :: second :: rest).flatten.length =
          first.length + (second :: rest).flatten.length := by
        simp only [List.flatten_cons, List.length_append]
      rw [←h_flat_len]
      exact h_last_eq_symm

    symm
    rw [h_flatten_eq]
    exact generalized_mth_split f first ((second :: rest).flatten) h_first_ne h_rest_ne h_last_eq_rw

/-- Merges the top segments at the index level. -/
def mergeSegmentsRev {α : Type} (L_rev : List (List α)) (c : Nat) : List (List α) :=
  match c with
  | 0 => L_rev
  | c + 1 =>
    match L_rev with
    | r :: l :: rest => mergeSegmentsRev ((l ++ r) :: rest) c
    | _ => L_rev

/-- Merges the top sizes at the numeric level. -/
def mergeSizes (S : List Nat) (c : Nat) : List Nat :=
  match c with
  | 0 => S
  | c + 1 =>
    match S with
    | r :: l :: rest => mergeSizes ((l + r) :: rest) c
    | _ => S

/-- mergeSizes preserves the sum of take/drop structure. -/
theorem mergeSizes_formula (c : Nat) (w : Nat) (S : List Nat) :
    mergeSizes (w :: S) c = (w + (S.take c).sum) :: S.drop c := by
  induction c generalizing w S with
  | zero => simp [mergeSizes]
  | succ c ih =>
    match S with
    | [] => simp [mergeSizes]
    | x :: xs =>
      simp only [mergeSizes, ih (x + w) xs, List.take_succ_cons, List.sum_cons, List.drop_succ_cons]
      congr 1
      omega

/-- mergeSegmentsRev preserves flatten. -/
theorem flatten_mergeSegmentsRev {α : Type} (c : Nat) (L_rev : List (List α)) :
    (mergeSegmentsRev L_rev c).reverse.flatten = L_rev.reverse.flatten := by
  induction c generalizing L_rev with
  | zero => simp [mergeSegmentsRev]
  | succ c ih =>
    match L_rev with
    | [] => simp [mergeSegmentsRev]
    | [s] => simp [mergeSegmentsRev]
    | r :: l :: rest =>
      simp only [mergeSegmentsRev]
      rw [ih ((l ++ r) :: rest)]
      simp only [List.reverse_cons, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.append_assoc]

/-- mergeSegmentsRev and mergeSizes are homomorphic under map length. -/
theorem length_mergeSegmentsRev {α : Type} (c : Nat) (L_rev : List (List α)) :
    (mergeSegmentsRev L_rev c).map List.length = mergeSizes (L_rev.map List.length) c := by
  induction c generalizing L_rev with
  | zero => simp [mergeSegmentsRev, mergeSizes]
  | succ c ih =>
    match L_rev with
    | [] => simp [mergeSegmentsRev, mergeSizes]
    | [s] => simp [mergeSegmentsRev, mergeSizes]
    | r :: l :: rest =>
      simp only [mergeSegmentsRev, mergeSizes, List.map_cons]
      have ih_val := ih ((l ++ r) :: rest)
      simp only [List.map_cons, List.length_append] at ih_val
      exact ih_val

/-- mergeSegmentsRev and generalized_mergeStack are homomorphic. -/
theorem generalized_mergeStack_eq_mergeSegmentsRev {α : Type} (f : SplitPolicy)
    [hf : Fact (ValidSplitPolicy f)] (c : Nat) (S_rev : List (List (MerkleTree α)))
    (h_nonempty : ∀ s ∈ S_rev, s ≠ [])
    (h_split : ∀ i < c, ∀ (r l : List (MerkleTree α)) rest,
      mergeSegmentsRev S_rev i = r :: l :: rest →
      f (l.length + r.length) = l.length) :
    generalized_mergeStack (S_rev.map (generalized_mth f)) c =
      (mergeSegmentsRev S_rev c).map (generalized_mth f) := by
  induction c generalizing S_rev with
  | zero => simp [generalized_mergeStack, mergeSegmentsRev]
  | succ c ih =>
    match S_rev with
    | [] => simp [generalized_mergeStack, mergeSegmentsRev]
    | [s] => simp [generalized_mergeStack, mergeSegmentsRev]
    | r :: l :: rest =>
      have h_zero : mergeSegmentsRev (r :: l :: rest) 0 = r :: l :: rest := rfl
      have h_f := h_split 0 (by omega) r l rest h_zero
      have hr_ne : r ≠ [] := h_nonempty r (by simp)
      have hl_ne : l ≠ [] := h_nonempty l (by simp)
      have h_node : MerkleTree.node (generalized_mth f l) (generalized_mth f r) =
          generalized_mth f (l ++ r) := by
        symm
        exact generalized_mth_split f l r hl_ne hr_ne h_f

      have h_map : (r :: l :: rest).map (generalized_mth f) =
          generalized_mth f r :: generalized_mth f l :: rest.map (generalized_mth f) := rfl
      simp only [generalized_mergeStack, h_map, h_node]

      have h_nonempty_rest : ∀ s ∈ (l ++ r) :: rest, s ≠ [] := by
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs_mem
        · intro hc; rw [List.append_eq_nil_iff] at hc; exact hl_ne hc.1
        · exact h_nonempty s (List.Mem.tail _ (List.Mem.tail _ hs_mem))

      have h_split_rest : ∀ i < c, ∀ (r' l' : List (MerkleTree α)) rest',
          mergeSegmentsRev ((l ++ r) :: rest) i = r' :: l' :: rest' →
          f (l'.length + r'.length) = l'.length := by
        intro i hi r' l' rest' h_eq'
        have h_eq_orig : mergeSegmentsRev (r :: l :: rest) (i + 1) = r' :: l' :: rest' := by
          simp only [mergeSegmentsRev]
          exact h_eq'
        exact h_split (i + 1) (by omega) r' l' rest' h_eq_orig

      exact ih ((l ++ r) :: rest) h_nonempty_rest h_split_rest

/-- getD distributes over drop. -/
theorem getD_def (L : List Nat) (i : Nat) (default : Nat) :
    getD L i default = getD (L.drop i) 0 default := by
  induction i generalizing L with
  | zero => rfl
  | succ i ih =>
    match L with
    | [] => rfl
    | x :: xs =>
      simp only [getD, List.drop_succ_cons]
      exact ih xs

/-- Helper to prove intermediate splits from AppendConsistent. -/
theorem mergeSegmentsRev_split_cond {α : Type} (f : SplitPolicy) (s : MergeSchedule)
    (h_consistent : AppendConsistent f s) (n : Nat) (i : Nat) (hi : i < s n)
    (L_rev : List (List (MerkleTree α)))
    (h_sizes : L_rev.map List.length = 1 :: forestSizes f n)
    (r l : List (MerkleTree α)) (rest : List (List (MerkleTree α)))
    (h_eq : mergeSegmentsRev L_rev i = r :: l :: rest) :
    f (l.length + r.length) = l.length := by
  have h_len := length_mergeSegmentsRev i L_rev
  rw [h_eq] at h_len
  simp only [List.map_cons] at h_len
  rw [h_sizes] at h_len
  rw [mergeSizes_formula i 1 (forestSizes f n)] at h_len
  injection h_len with hr_eq hl_list
  have hl_eq : l.length = getD (forestSizes f n) i 0 := by
    rw [getD_def (forestSizes f n) i 0]
    rw [←hl_list]
    rfl

  rw [hl_eq, hr_eq]
  have h_sum_take : ((forestSizes f n).take i).sum + getD (forestSizes f n) i 0 =
      ((forestSizes f n).take (i + 1)).sum := by
    have h_split_take : ((forestSizes f n).take (i + 1)) =
        ((forestSizes f n).take i) ++ ((forestSizes f n).drop i).take 1 := by
      exact List.take_add
    rw [h_split_take, List.sum_append]
    have h_drop_take1 : ((forestSizes f n).drop i).take 1 = [l.length] := by
      rw [←hl_list]; rfl
    rw [h_drop_take1, List.sum_singleton]
    rw [getD_def (forestSizes f n) i 0, ←hl_list]
    rfl

  have h_arg : getD (forestSizes f n) i 0 + (1 + ((forestSizes f n).take i).sum) =
      1 + ((forestSizes f n).take (i + 1)).sum := by omega
  rw [h_arg]
  exact (h_consistent n).2 i hi

/-- The generalized stack loop invariant. -/
def generalized_stackInvariant {α : Type} (f : SplitPolicy) (stack : List (MerkleTree α))
    (leaves : List (MerkleTree α)) : Prop :=
  ∃ (segments : List (List (MerkleTree α))),
    segments.flatten = leaves ∧
    stack = (segments.map (generalized_mth f)).reverse ∧
    (segments.map List.length).reverse = forestSizes f leaves.length

/-- generalized_appendToStack preserves the stack invariant. -/
theorem generalized_appendToStack_invariant {α : Type} (f : SplitPolicy) (s : MergeSchedule)
    [hf : Fact (ValidSplitPolicy f)] (h_consistent : AppendConsistent f s)
    (stack : List (MerkleTree α)) (leaves : List (MerkleTree α)) (leaf : MerkleTree α)
    (h_inv : generalized_stackInvariant f stack leaves) :
    generalized_stackInvariant f (generalized_appendToStack s stack leaf leaves.length)
      (leaves ++ [leaf]) := by
  obtain ⟨segments, h_flat, h_stack, h_sizes⟩ := h_inv
  let new_segments := segments ++ [[leaf]]
  have h_flat' : new_segments.flatten = leaves ++ [leaf] := by
    simp [new_segments, h_flat]

  have h_stack_prep : leaf :: stack = (new_segments.map (generalized_mth f)).reverse := by
    simp only [new_segments, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append]
    have h_leaf : generalized_mth f [leaf] = leaf := by
      unfold generalized_mth; rfl
    rw [h_leaf, h_stack]
    rfl

  let L_rev := new_segments.reverse
  have h_nonempty : ∀ s ∈ L_rev, s ≠ [] := by
    intro s hs
    simp only [L_rev, new_segments, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append] at hs
    cases hs with
    | head =>
      intro hc; contradiction
    | tail _ hs_mem =>
      change s ∈ segments.reverse at hs_mem
      rw [List.mem_reverse] at hs_mem
      have h_len_in : s.length ∈ (segments.map List.length).reverse := by
        simp only [List.mem_reverse, List.mem_map]
        exact ⟨s, hs_mem, rfl⟩
      rw [h_sizes] at h_len_in
      have h_pos := forestSizes_pos hf.elim leaves.length s.length h_len_in
      intro hc; subst hc; simp at h_pos

  have h_split : ∀ i < s leaves.length, ∀ (r l : List (MerkleTree α)) rest,
      mergeSegmentsRev L_rev i = r :: l :: rest →
      f (l.length + r.length) = l.length := by
    intro i hi r l rest h_eq
    have h_sz : L_rev.map List.length = 1 :: forestSizes f leaves.length := by
      simp only [L_rev, new_segments, List.map_append, List.reverse_append, List.map_cons,
        List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.length_singleton]
      rw [List.map_reverse, h_sizes]
      rfl
    exact mergeSegmentsRev_split_cond f s h_consistent leaves.length i hi L_rev h_sz r l rest h_eq

  have h_merge := generalized_mergeStack_eq_mergeSegmentsRev f (s leaves.length) L_rev
      h_nonempty h_split

  let final_segments_rev := mergeSegmentsRev L_rev (s leaves.length)
  let final_segments := final_segments_rev.reverse

  use final_segments
  refine ⟨?_, ?_, ?_⟩
  · have h_flat_rev := flatten_mergeSegmentsRev (s leaves.length) L_rev
    simp only [L_rev, List.reverse_reverse] at h_flat_rev
    rw [h_flat_rev]
    exact h_flat'
  · rw [generalized_appendToStack, h_stack_prep]
    have h_stack_rev : (new_segments.map (generalized_mth f)).reverse =
        L_rev.map (generalized_mth f) := by
      simp only [L_rev, List.map_reverse]
    rw [h_stack_rev, h_merge]
    have h_final_rev : (final_segments.map (generalized_mth f)).reverse =
        final_segments_rev.map (generalized_mth f) := by
      simp only [final_segments, List.map_reverse, List.reverse_reverse]
    rw [h_final_rev]
  · have h_len_eq := length_mergeSegmentsRev (s leaves.length) L_rev
    simp only [final_segments, List.map_reverse, List.reverse_reverse]
    rw [h_len_eq]
    have h_sz : L_rev.map List.length = 1 :: forestSizes f leaves.length := by
      simp only [L_rev, new_segments, List.map_append, List.reverse_append, List.map_cons,
        List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.length_singleton]
      rw [List.map_reverse, h_sizes]
      rfl
    rw [h_sz]
    rw [mergeSizes_formula]
    have h_len_leaves : (leaves ++ [leaf]).length = leaves.length + 1 := by
      simp only [List.length_append, List.length_singleton]
    rw [h_len_leaves]
    exact (h_consistent leaves.length).1.symm

/-- generalized_buildStackAux preserves stackInvariant. -/
theorem generalized_buildStackAux_invariant {α : Type} (f : SplitPolicy) (s : MergeSchedule)
    [hf : Fact (ValidSplitPolicy f)] (h_consistent : AppendConsistent f s)
    (stack : List (MerkleTree α)) (remaining : List (MerkleTree α)) (leaves : List (MerkleTree α))
    (h_inv : generalized_stackInvariant f stack leaves) :
    generalized_stackInvariant f (generalized_buildStackAux s stack remaining leaves.length)
      (leaves ++ remaining) := by
  induction remaining generalizing stack leaves with
  | nil =>
    simp only [generalized_buildStackAux, List.append_nil]
    exact h_inv
  | cons hd tl ih =>
    simp only [generalized_buildStackAux]
    have h_inv_append := generalized_appendToStack_invariant f s h_consistent stack leaves hd h_inv
    have ih_val := ih (generalized_appendToStack s stack hd leaves.length)
        (leaves ++ [hd]) h_inv_append
    have h_len : leaves.length + 1 = (leaves ++ [hd]).length := by
      simp only [List.length_append, List.length_singleton]
    rw [h_len]
    rw [List.append_assoc] at ih_val
    exact ih_val

/-- generalized_buildStack satisfies stackInvariant. -/
theorem generalized_buildStack_invariant {α : Type} (f : SplitPolicy) (s : MergeSchedule)
    [hf : Fact (ValidSplitPolicy f)] (h_consistent : AppendConsistent f s)
    (leaves : List (MerkleTree α)) :
    generalized_stackInvariant f (generalized_buildStack s leaves) leaves := by
  have h_inv_init : generalized_stackInvariant f (α := α) [] [] := by
    refine ⟨[], rfl, rfl, ?_⟩
    unfold forestSizes
    rfl
  have h_res := generalized_buildStackAux_invariant f s h_consistent [] leaves [] h_inv_init
  simp only [List.nil_append] at h_res
  exact h_res

/-- **The Generalized Bridge Lemma.** -/
theorem generalized_bridge_lemma {α : Type} (f : SplitPolicy) (s : MergeSchedule)
    [hf : Fact (ValidSplitPolicy f)] (h_consistent : AppendConsistent f s)
    (leaves : List (MerkleTree α)) :
    generalized_ctoRoot s leaves = generalized_mth f leaves := by
  have h_inv := generalized_buildStack_invariant f s h_consistent leaves
  obtain ⟨segments, h_flat, h_stack, h_sizes⟩ := h_inv
  simp only [generalized_ctoRoot, h_stack]
  have h_sizes' : (segments.map List.length).reverse = forestSizes f segments.flatten.length := by
    rw [h_flat]
    exact h_sizes
  rw [stackRoot_segments_eq_generalized_mth f segments h_sizes']
  rw [h_flat]
