import EMLProof.Invariant

/-!
# EML Topological Reconstruction and the Bridge Lemma

This module establishes the topological equivalence between the bottom-up incremental frontier 
stack root reconstruction and the top-down Batch Merkle Tree Hash (MTH) calculation.

## Mathematical Formulation

1. **Reconstruction Equivalence**:
   For any list of segments whose lengths are strictly descending powers of 2, folding the 
   reversed segment MTHs with node combination is structurally identical to computing the MTH 
   of the concatenated segment leaves:
   $$\text{stackRoot}([\text{mth}(s_m), \dots]) = \text{mth}(s_1 \mathbin{+\!+} \dots)$$
   This equivalence is proved by induction on the segments list in `stackRoot_segments_eq_mth`. The 
   key inductive step relies on the split boundary of the Batch MTH matching the first (largest) 
   power-of-2 segment.

2. **The Bridge Lemma**:
   For any sequence of leaves, the incremental Count Trailing Ones (CTO) tree root
   equals the RFC 9162 Batch Merkle Tree Hash:
   $$\text{ctoRoot}(\text{leaves}) = \text{mth}(\text{leaves})$$
   This is proved in `bridge_lemma` using `buildStack_invariant` and `stackRoot_segments_eq_mth`.
-/

set_option linter.style.emptyLine false

/-- stackRoot over a decomposition in strictly descending size order
    yields the same result as mth over the flattened sequence.

    This is because mth splits at largestPow2Lt, which is the first
    (largest) segment, and recurses on the rest — exactly matching
    the stackRoot fold from head (smallest) to tail (largest). -/
theorem stackRoot_segments_eq_mth {α : Type} (segments : List (List (MerkleTree α)))
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
    simp only [List.flatten_cons]

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
      simp only [List.flatten_cons]
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
        simp only [List.flatten_cons, List.length_append, List.map_cons,
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
theorem bridge_lemma {α : Type} (leaves : List (MerkleTree α)) :
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
