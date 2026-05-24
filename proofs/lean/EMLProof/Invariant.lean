import EMLProof.Binary

/-!
# EML Frontier Stack Loop Invariant

This module defines the core stack loop invariant that bridges the incremental CTO state machine 
and the batch MTH representation.

## The Stack Invariant Formalism

For any list `pfx`, the frontier stack `stack` satisfies `stackInvariant pfx stack` 
if and only if there exists a partition of `pfx` into segments:
$$\text{pfx} = \text{seg}_1 \mathbin{+\!+} \dots \mathbin{+\!+} \text{seg}_m$$
such that:
1. **Lengths**: Each segment size is a power of 2:
   $$\forall j, \quad \exists k, \quad |\text{seg}_j| = 2^k$$
2. **Descending Order**: Segment sizes are strictly descending:
   $$|\text{seg}_1| > |\text{seg}_2| > \dots > |\text{seg}_m|$$
3. **MTH Elements**: The stack stores the Merkle Tree Hash (MTH) of each segment, reversed:
   $$\text{stack} = [\text{mth}(\text{seg}_m), \dots, \text{mth}(\text{seg}_1)]$$

This invariant ensures that the stack behaves like a **binomial forest** tracking the set bits 
of the number of processed leaves.
-/

set_option linter.style.emptyLine false

/-- The frontier stack loop invariant.
    Witnesses that the leaves processed so far are partitioned into strictly descending power-of-2 
    segments, and the stack contains their MTH values in reverse. -/
noncomputable def stackInvariant {α : Type} (pfx : List (MerkleTree α))
    (stack : List (MerkleTree α)) : Prop :=
  ∃ (segments : List (List (MerkleTree α))),
    segments.flatten = pfx ∧
    (∀ s ∈ segments, ∃ k, s.length = 2 ^ k) ∧
    List.Pairwise (· > ·) (segments.map List.length) ∧
    stack = (segments.map mth).reverse

/-- The merge cascade correctness theorem: merging a cascade run of power-of-2 segments 
    doubles them correctly into a single accumulated segment. -/
theorem merge_cascade {α : Type}
    (acc_content : List (MerkleTree α))
    (run : List (List (MerkleTree α)))
    (tail : List (MerkleTree α))
    (j : Nat)
    (h_acc_len : acc_content.length = 2 ^ j)
    (h_run_geo : ∀ (i : Nat) (h : i < run.length),
      (run.get ⟨i, h⟩).length = 2 ^ (j + i)) :
    mergeStack (mth acc_content :: run.map mth ++ tail) run.length =
      mth (run.reverse.flatten ++ acc_content) :: tail := by
  induction run generalizing acc_content j with
  | nil =>
    simp [mergeStack]
  | cons seg tl ih =>
    change mergeStack (MerkleTree.node (mth seg) (mth acc_content) ::
      (List.map mth tl ++ tail)) tl.length =
      mth ((seg :: tl).reverse.flatten ++ acc_content) :: tail
    have h_seg_len : seg.length = 2 ^ j := by
      have := h_run_geo 0 (Nat.zero_lt_succ _)
      simp only [List.get_eq_getElem, List.getElem_cons_zero, Nat.add_zero] at this
      exact this
    rw [mth_merge seg acc_content j h_seg_len h_acc_len]
    have h_new_len : (seg ++ acc_content).length = 2 ^ (j + 1) := by
      simp [List.length_append, h_seg_len, h_acc_len]; ring
    have h_tl_geo : ∀ (i : Nat) (h : i < tl.length),
        (tl.get ⟨i, h⟩).length = 2 ^ ((j + 1) + i) := by
      intro i hi
      have h_bound : i + 1 < (seg :: tl).length := by
        simp only [List.length_cons]
        omega
      have := h_run_geo (i + 1) h_bound
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at this
      convert this using 2
      omega
    have h_ih := ih (seg ++ acc_content) (j + 1) h_new_len h_tl_geo
    simp only [List.cons_append] at h_ih
    rw [h_ih]
    congr 1
    simp [List.reverse_cons, List.flatten_append, List.append_assoc]

/-- Single-step loop invariant preservation theorem: appending a leaf maintains stackInvariant. -/
theorem appendToStack_invariant {α : Type} (pfx₀ : List (MerkleTree α))
    (stack₀ : List (MerkleTree α))
    (leaf : MerkleTree α) (idx : Nat)
    (h_inv : stackInvariant pfx₀ stack₀)
    (h_idx : idx = pfx₀.length) :
    stackInvariant (pfx₀ ++ [leaf]) (appendToStack stack₀ leaf idx) := by
  obtain ⟨segments, h_flat, h_pow2, h_desc, h_stack⟩ := h_inv
  simp only [appendToStack]
  by_cases h_cto : cto idx = 0
  · rw [h_cto]; simp only [mergeStack]
    refine ⟨segments ++ [[leaf]], ?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_append, h_flat, List.flatten_cons, List.flatten_nil, List.append_nil]
    · intro s hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · exact h_pow2 s hs
      · exact ⟨0, rfl⟩
    · simp only [List.map_append, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil]
      have h_seg_lens := segments.map List.length
      have h_sizes_ge_2 := no_size_one_when_cto_zero
        (segments.map List.length) h_desc
        (by intro s hs
            simp only [List.mem_map] at hs
            obtain ⟨seg, h_mem, h_eq⟩ := hs
            obtain ⟨k, hk⟩ := h_pow2 seg h_mem
            exact ⟨k, by rw [← h_eq, hk]⟩)
        (by have : (segments.map List.length).sum = pfx₀.length := by
              rw [← h_flat]; simp only [List.length_flatten]
            rw [this, ← h_idx]; exact h_cto)
      rw [List.pairwise_append]
      refine ⟨h_desc, ?_, fun a ha b hb => ?_⟩
      · exact List.pairwise_singleton _ _
      · simp only [List.mem_singleton] at hb
        subst hb
        have := h_sizes_ge_2 a ha
        omega
    · simp only [List.map_append, List.reverse_append, h_stack, List.map_cons, List.map_nil,
        mth]
      rfl
  · obtain ⟨k, h_cto_eq⟩ : ∃ k, cto idx = k + 1 := by
      exact ⟨cto idx - 1, by omega⟩
    have h_odd : idx % 2 = 1 := by
      by_contra h_even
      push Not at h_even
      have : idx % 2 = 0 := by omega
      rw [cto, if_neg (by omega)] at h_cto_eq
      omega
    have h_segs_ne : segments ≠ [] := by
      intro h_empty; subst h_empty
      simp only [List.flatten_nil] at h_flat
      rw [← h_flat] at h_idx; simp only [List.length_nil] at h_idx; omega
    rw [h_cto_eq, h_stack]
    have h_leaf_mth : leaf = mth [leaf] := by simp [mth]
    let sz := segments.map List.length
    have h_sz_desc : sz.Pairwise (· > ·) := h_desc
    have h_sz_pow2 : ∀ s ∈ sz, ∃ j, s = 2 ^ j := by
      intro s hs; simp only [sz, List.mem_map] at hs
      obtain ⟨seg, hmem, rfl⟩ := hs; exact h_pow2 seg hmem
    have h_sz_sum : sz.sum = idx := by
      have : sz.sum = pfx₀.length := by
        rw [← h_flat]; simp only [sz, List.length_flatten]
      rw [this, ← h_idx]
    have h_sz_cto : cto sz.sum = k + 1 := by rw [h_sz_sum, h_cto_eq]
    have h_sz_len : k + 1 ≤ sz.length :=
      cto_trailing_geo_len sz k h_sz_desc h_sz_pow2 h_sz_cto
    have h_sz_len' : k + 1 ≤ segments.length := by
      simp only [sz, List.length_map] at h_sz_len
      exact h_sz_len
    have h_geo := cto_trailing_geo sz k h_sz_desc h_sz_pow2 h_sz_cto h_sz_len
    set n := segments.length
    set above := segments.take (n - (k + 1)) with h_above_def
    set run_segs := segments.drop (n - (k + 1)) with h_run_def
    have h_split : segments = above ++ run_segs :=
      (List.take_append_drop (n - (k + 1)) segments).symm
    have h_run_len : run_segs.length = k + 1 := by
      simp only [h_run_def, List.length_drop]
      omega
    have h_stack_rw : (segments.map mth).reverse =
        (run_segs.map mth).reverse ++ (above.map mth).reverse := by
      rw [h_split]; simp only [List.map_append, List.reverse_append]
    set mc_run := run_segs.reverse with h_mc_def
    have h_mc_len : mc_run.length = k + 1 := by
      simp only [h_mc_def, List.length_reverse, h_run_len]
    have h_mc_geo : ∀ (i : Nat) (hi : i < mc_run.length),
        (mc_run.get ⟨i, hi⟩).length = 2 ^ (0 + i) := by
      intro i hi
      rw [h_mc_len] at hi
      simp only [h_mc_def, List.get_eq_getElem, List.getElem_reverse, Nat.zero_add]
      simp only [h_run_def, List.getElem_drop]
      have h_geo_i := h_geo i (by omega)
      simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at h_geo_i
      have h_idx_eq : n - (k + 1) + (run_segs.length - 1 - i) = n - 1 - i := by
        rw [h_run_len]; omega
      have : segments[n - (k + 1) + (run_segs.length - 1 - i)] =
             segments[n - 1 - i] := by
        simp only [h_idx_eq]
      rw [this]; exact h_geo_i
    rw [h_leaf_mth, h_stack_rw]
    have h_mc := merge_cascade [leaf] mc_run ((above.map mth).reverse) 0
      rfl h_mc_geo
    rw [show (List.map mth run_segs).reverse = List.map mth mc_run from by
      simp only [h_mc_def, List.map_reverse]]
    rw [← h_mc_len]
    conv at h_mc => lhs; rw [List.cons_append]
    rw [h_mc]
    simp only [h_mc_def, List.reverse_reverse]
    set merged := run_segs.flatten ++ [leaf]
    refine ⟨above ++ [merged], ?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                  List.append_nil, merged]
      rw [← h_leaf_mth]
      rw [← List.append_assoc, ← List.flatten_append, ← h_split, h_flat]
    · intro seg h_mem
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h_mem
      rcases h_mem with h_above | h_eq
      · have : seg ∈ segments := List.mem_of_mem_take h_above
        exact h_pow2 seg this
      · subst h_eq
        refine ⟨k + 1, ?_⟩
        simp only [merged, List.length_append, List.length_flatten,
                    List.length_cons, List.length_nil]
        suffices h_sum : (run_segs.map List.length).sum = 2 ^ (k + 1) - 1 by
          have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
        suffices ∀ m, m ≤ k + 1 →
          ((segments.drop (n - m)).map List.length).sum = 2 ^ m - 1 by
          exact this (k + 1) le_rfl
        intro m hm
        induction m with
        | zero =>
          simp only [Nat.sub_zero, pow_zero, Nat.sub_self]
          have : List.drop n segments = [] := by
            change List.drop segments.length segments = []; exact List.drop_length
          rw [this]; simp
        | succ m' ih =>
          have hd : n - (m' + 1) < segments.length := by omega
          rw [List.drop_eq_getElem_cons hd]
          simp only [List.map, List.sum_cons]
          have h_eq_idx : n - (m' + 1) + 1 = n - m' := by omega
          rw [h_eq_idx]
          rw [ih (by omega)]
          have hg := h_geo m' (by omega)
          simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at hg
          have : segments[n - (m' + 1)] = segments[n - 1 - m'] := by
            simp only [show n - (m' + 1) = n - 1 - m' from by omega]
          rw [show segments[n - (m' + 1)].length = 2 ^ m' from by rw [this]; exact hg]
          have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
          have : 2 ^ m' ≥ 1 := Nat.one_le_two_pow
          omega
    · rw [List.map_append, List.map_cons, List.map_nil]
      rw [List.pairwise_append]
      have h_pw := List.pairwise_iff_getElem.mp h_desc
      simp only [List.length_map, List.getElem_map] at h_pw
      refine ⟨?_, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      · rw [show above.map List.length = (segments.map List.length).take (n - (k + 1)) from by
          simp only [above, List.map_take]]
        exact h_desc.take
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb; subst hb
        simp only [List.mem_map] at ha
        obtain ⟨seg, h_seg_mem, rfl⟩ := ha
        have h_merged_len : merged.length = 2 ^ (k + 1) := by
          simp only [merged, List.length_append, List.length_flatten,
                      List.length_cons, List.length_nil]
          suffices (run_segs.map List.length).sum = 2 ^ (k + 1) - 1 by
            have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
          suffices ∀ m, m ≤ k + 1 →
            ((segments.drop (n - m)).map List.length).sum = 2 ^ m - 1 by
            exact this (k + 1) le_rfl
          intro m hm
          induction m with
          | zero =>
            simp only [Nat.sub_zero, pow_zero, Nat.sub_self]
            have : List.drop n segments = [] := by
              change List.drop segments.length segments = []; exact List.drop_length
            rw [this]; simp
          | succ m' ih =>
            have hd : n - (m' + 1) < segments.length := by omega
            rw [List.drop_eq_getElem_cons hd]
            simp only [List.map, List.sum_cons]
            have h_eq_idx : n - (m' + 1) + 1 = n - m' := by omega
            rw [h_eq_idx]
            rw [ih (by omega)]
            have hg := h_geo m' (by omega)
            simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at hg
            have : segments[n - (m' + 1)] = segments[n - 1 - m'] := by
              simp only [show n - (m' + 1) = n - 1 - m' from by omega]
            rw [show segments[n - (m' + 1)].length = 2 ^ m' from by rw [this]; exact hg]
            have : 2 ^ (m' + 1) = 2 * 2 ^ m' := by ring
            have : 2 ^ m' ≥ 1 := Nat.one_le_two_pow
            omega
        rw [h_merged_len]
        have h_seg_in : seg ∈ segments := List.mem_of_mem_take h_seg_mem
        obtain ⟨e, h_seg_len⟩ := h_pow2 seg h_seg_in
        rw [h_seg_len]
        obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem h_seg_mem
        have h_above_len : above.length = n - (k + 1) := by
          simp only [above, List.length_take]; omega
        rw [h_above_len] at hj_lt
        have h_seg_is : seg = segments[j] := by
          rw [← hj_eq]; simp [above, List.getElem_take]
        have h_first_run : segments[n - (k + 1)].length = 2 ^ k := by
          have h_g := h_geo k (by omega)
          simp only [sz, List.get_eq_getElem, List.getElem_map, List.length_map] at h_g
          have : n - (k + 1) = segments.length - 1 - k := by omega
          simp only [this]; exact h_g
        have h_seg_gt : seg.length > 2 ^ k := by
          have := h_pw j (n - (k + 1)) (by omega) (by omega) hj_lt
          rw [h_first_run] at this; rw [h_seg_is]; exact this
        rw [h_seg_len] at h_seg_gt
        have h_e_ge : e ≥ k + 1 := by
          by_contra hc; push Not at hc
          exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
            (by omega : e ≤ k)) h_seg_gt
        by_contra h_not_gt; push Not at h_not_gt
        have h_e_eq : e = k + 1 := by
          have : e ≤ k + 1 := by
            by_contra hc; push Not at hc
            have h1 := Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              (by omega : k + 2 ≤ e)
            have : 2 ^ (k + 1) < 2 ^ (k + 2) := by
              have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
              have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
            omega
          omega
        subst h_e_eq
        have hj_eq_nk2 : j = n - (k + 2) := by
          by_contra hj_ne
          have hj_lt' : j + 1 < n - (k + 1) := by omega
          have h_lt := h_pw j (j + 1) (by omega) (by omega) (by omega)
          rw [← h_seg_is, h_seg_len] at h_lt
          have h_gt := h_pw (j + 1) (n - (k + 1)) (by omega) (by omega) hj_lt'
          rw [h_first_run] at h_gt
          obtain ⟨f, hf⟩ := h_pow2 (segments[j + 1]) (List.getElem_mem ..)
          rw [hf] at h_lt h_gt
          have : f ≥ k + 1 := by
            by_contra hc; push Not at hc
            exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              (by omega)) h_gt
          have : f ≤ k := by
            by_contra hc; push Not at hc
            exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              this) h_lt
          omega
        have h_drop_j : segments.drop j = segments[j] :: segments.drop (j + 1) :=
          List.drop_eq_getElem_cons (by omega)
        have h_drop_j1 : segments.drop (j + 1) = run_segs := by
          rw [hj_eq_nk2]; congr 1; omega
        have h_idx_split : idx =
            ((segments.take j).map List.length).sum +
            ((segments.drop j).map List.length).sum := by
          rw [← h_sz_sum]
          simp [sz, ← List.sum_append, List.take_append_drop]
        have h_tail_sum : ((segments.drop j).map List.length).sum = 2 ^ (k + 2) - 1 := by
          rw [h_drop_j]; simp only [List.map, List.sum_cons]
          rw [h_drop_j1, ← h_seg_is, h_seg_len]
          have h_rs : (run_segs.map List.length).sum = 2 ^ (k + 1) - 1 := by
            have := h_merged_len
            simp only [merged, List.length_append, List.length_flatten,
                        List.length_cons, List.length_nil] at this
            have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
          rw [h_rs]; have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
          have : 2 ^ (k + 1) ≥ 1 := Nat.one_le_two_pow; omega
        have h_head_dvd : 2 ^ (k + 2) ∣ ((segments.take j).map List.length).sum := by
          suffices ∀ x ∈ (segments.take j).map List.length, 2 ^ (k + 2) ∣ x by
            exact List.dvd_sum this
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨s, hs_mem, rfl⟩ := hx
          obtain ⟨f, hf⟩ := h_pow2 s (List.mem_of_mem_take hs_mem)
          rw [hf]
          obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hs_mem
          have hi_lt' : i < j := by
            rw [List.length_take] at hi_lt
            exact lt_of_lt_of_le hi_lt (Nat.min_le_left j n)
          have this := h_pw i j (by omega) (by omega) hi_lt'
          rw [show segments[i] = s from by
            rw [← hi_eq]; exact (List.getElem_take ..).symm] at this
          rw [← h_seg_is, h_seg_len, hf] at this
          have : f ≥ k + 2 := by
            by_contra hc; push Not at hc
            exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
              (by omega)) this
          exact Nat.pow_dvd_pow 2 this
        have h_mod : idx % 2 ^ (k + 2) = 2 ^ (k + 2) - 1 := by
          rw [h_idx_split]
          obtain ⟨q, hq⟩ := h_head_dvd
          rw [hq, h_tail_sum]
          rw [Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt (by have := Nat.one_le_two_pow (n := k + 2); omega)
        exact absurd (cto_ge_of_mod idx (k + 2) h_mod) (by omega)
    · simp [List.map_append, List.reverse_append]

/-- Preserves stackInvariant throughout the buildStack loop execution. -/
theorem buildStack_invariant {α : Type} (leaves : List (MerkleTree α)) :
    stackInvariant leaves (buildStack leaves) := by
  suffices h : ∀ (pfx₀ : List (MerkleTree α)) (stack₀ : List (MerkleTree α))
      (remaining : List (MerkleTree α)) (idx : Nat),
      stackInvariant pfx₀ stack₀ → idx = pfx₀.length →
      stackInvariant (pfx₀ ++ remaining)
        (buildStackAux stack₀ remaining idx) by
    have h_empty : stackInvariant (α := α) [] [] :=
      ⟨[], And.intro rfl (And.intro (fun _ h => nomatch h) (And.intro List.Pairwise.nil rfl))⟩
    specialize h [] [] leaves 0 h_empty rfl
    simp only [List.nil_append] at h
    exact h
  intro pfx₀ stack₀ remaining
  induction remaining generalizing pfx₀ stack₀ with
  | nil =>
    intro idx h_inv h_idx
    simp only [List.append_nil]
    exact h_inv
  | cons leaf rest ih =>
    intro idx h_inv h_idx
    simp only [buildStackAux]
    conv_lhs => rw [show pfx₀ ++ leaf :: rest = (pfx₀ ++ [leaf]) ++ rest
      from by simp]
    apply ih
    · exact appendToStack_invariant pfx₀ stack₀ leaf idx h_inv h_idx
    · simp [h_idx]
