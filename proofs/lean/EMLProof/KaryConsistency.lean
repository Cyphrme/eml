import EMLProof.Kary

set_option linter.style.longLine false

/-!
# K-ary consistency-verifier soundness (V9 follow-on d)

`Kary.lean` proved the **inclusion** verifier sound. This module does the same
for the **consistency** verifier — the property that makes the log
tamper-evident: an accepted consistency proof between two roots witnesses a
genuine append-only prefix relation between the two trees.

The Rust subject is `cml/src/consistency.rs`:

* `verify_consistency` (`consistency.rs:97`) =
  `reconstruct_consistency_roots(..).is_some_and(|(c_old, c_new)|
   c_old == old_root && c_new == new_root)` — the dual-root accept relation.
* `reconstruct_consistency_roots` (`consistency.rs:593`) recomputes **both** the
  old-size and new-size roots from a single shared `path` anchored at
  `start_hash`, using the same frontier topology as inclusion.

## What the proof shows

Anchored at the honest current tree (`newRoot = karyRoot cells`,
`newSize = cells.length`):

* **Non-vacuity** (`consistency_completeness`): the honest consistency proof
  for `(cells, oldSize)` — the honest boundary-subtree root as `start_hash`
  and the honest path — is accepted, with the reconstructed roots being the
  genuine prefix root `karyRoot (cells.take oldSize)` and the genuine current
  root `karyRoot cells`. So the accept set is provably non-empty (mirroring
  `kary_completeness`).
* **Soundness** (`consistency_soundness`): *any* accepting consistency proof
  against the honest current root forces the reconstructed `oldRoot` to equal
  `karyRoot (cells.take oldSize)` — the root of the **unique** size-`oldSize`
  prefix of the current tree — modulo `NodeHashCollision` / `CollapseAmbiguity`
  (the two explicit hash hypotheses, never axioms). An attacker cannot make
  the verifier accept a *false* history (a forged `oldRoot`) against the true
  current tree.
* **Dual soundness** (`consistency_append_only`): accepting a proof between the
  honest root of `oldCells` and the honest root of `newCells` forces
  `oldCells <+: newCells` — the append-only relation at the cell-sequence
  level. Soundness binds it at the root level; this binds it at the data level.
  (The pure existential dual — "the new root is *some* extension's root" — is
  not faithfully recoverable: a consistency proof carries perfect-subtree
  roots, not the individual appended cells.)

`cells.take oldSize` is the append-only prefix: `oldSize < newSize =
cells.length`, and `cells.take oldSize <+: cells` holds definitionally
(`List.take_prefix`). The soundness theorem **concludes** the binding of
`oldRoot` to that prefix's root; it does not assume it.

## Proof architecture (reuses `Kary.lean` heavily)

The consistency path is the **suffix of the inclusion path of the last old
leaf** (`index = oldSize - 1`), taken from the boundary subtree's height
upward: `start_hash` plays the role of that subtree's root (`perfectRoot`),
the bisection steps are the upper digit steps, and the grouping steps are
identical. Hence:

* the new-root reconstruction is `foldNary start_hash path` (each Rust step —
  bisection, target merge, final merge — applies the same null-promoting
  `naryMr (insertAt position cur siblings)` to the running boundary digest;
  skipped coordinate merges consume no step and leave it untouched);
* soundness is **completeness + uniqueness** exactly as for inclusion: the
  honest path shape-matches the consistency skeleton, both fold to
  `karyRoot cells`, and `foldNary_unique_of_shape` forces the arbitrary
  accepting path to equal the honest one — pinning `start_hash` to the genuine
  boundary root and the recorded siblings to the genuine subtree roots, hence
  `oldRoot` to `karyRoot (cells.take oldSize)`.

The old-root reconstruction is modeled faithfully via the coordinate→digest
map that `reconstruct_consistency_roots` builds (`consistencyMap`): the
boundary coordinate maps to `start_hash`, and every bisection/merge step
records its siblings at their coordinates. The old root is the
`foldFrontierRoot` over the old frontier's coordinates read back from that map
(`consistency.rs:842`).
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

namespace NEML

/-! ## Boundary topology

The "boundary" is the last (rightmost, smallest) perfect subtree of the old
frontier. Its span ends exactly at `oldSize`. These pure-arithmetic facts about
the frontier tiling anchor both the honest construction and the soundness
reduction; no hashing is involved. -/

/-- The last tile of a `Tiles` decomposition ends exactly at `stop`. -/
private theorem Tiles_last (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop bl bh : Nat),
      Tiles k start coords stop → coords.getLast? = some (bl, bh) →
        bl + k ^ bh = stop := by
  intro coords
  induction coords with
  | nil => intro start stop bl bh _ hlast; simp at hlast
  | cons p rest ih =>
    intro start stop bl bh htiles hlast
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    cases rest with
    | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at hlast
        obtain ⟨hbl, hbh⟩ := hlast
        subst hbl; subst hbh
        simp only [Tiles] at htrest
        omega
    | cons q qs =>
        rw [List.getLast?_cons_cons] at hlast
        exact ih (start + k ^ ph) stop bl bh htrest hlast

/-- The old frontier's last coordinate `(bl, bh)` spans `[bl, oldSize)`:
    `bl + k ^ bh = oldSize`. -/
private theorem frontier_getLast_eq (k n bl bh : Nat) (hk : 2 ≤ k)
    (hlast : (frontierForSizeT k n).getLast? = some (bl, bh)) :
    bl + k ^ bh = n :=
  Tiles_last k (frontierForSizeT k n) 0 n bl bh (frontier_tiles k n hk) hlast

/-- **Frontier coordinates are aligned to their height.** Every perfect subtree
    `(l, h)` in the greedy decomposition starts at a multiple of `k ^ h` — the
    decomposition strips largest-first, so each new offset stays divisible by all
    smaller heights. Stated over `frontierGo` with the matching offset hypothesis
    so the induction closes; `frontierForSizeT` is the `off = 0` case. -/
private theorem frontierGo_aligned (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off : Nat), k ^ Nat.log k n ∣ off → ∀ lh ∈ frontierGo k off n, k ^ lh.2 ∣ lh.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off hdvd lh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp only [List.not_mem_nil] at hmem
    · next h =>
        push Not at h
        obtain ⟨hn0, _⟩ := h
        rw [List.mem_cons] at hmem
        have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        rcases hmem with rfl | hmem'
        · exact hdvd
        · have hHle : Nat.log k (n - k ^ Nat.log k n) ≤ Nat.log k n :=
            Nat.log_mono_right (by omega)
          have hdvd' : k ^ Nat.log k (n - k ^ Nat.log k n) ∣ (off + k ^ Nat.log k n) :=
            Nat.dvd_add (dvd_trans (pow_dvd_pow k hHle) hdvd) (pow_dvd_pow k hHle)
          exact ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) hdvd' lh hmem'

/-- The boundary coordinate `(bl, bh)` is `k ^ bh`-aligned: `k ^ bh ∣ bl`. -/
private theorem frontier_getLast_aligned (k n bl bh : Nat) (hk : 2 ≤ k)
    (hlast : (frontierForSizeT k n).getLast? = some (bl, bh)) :
    k ^ bh ∣ bl := by
  have hmem : (bl, bh) ∈ frontierForSizeT k n := List.mem_of_getLast? hlast
  exact frontierGo_aligned k hk n 0 (by simp) (bl, bh) hmem

/-- **Greedy slot height.** A frontier slot `(sl, sh)` has `sh = log_k (n - sl)`:
    the height is the log of the leaves still remaining when the greedy
    decomposition reaches `sl` (tiling pins the remaining count to `n - sl`). -/
private theorem frontierGo_slot_height (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off sl sh : Nat), (sl, sh) ∈ frontierGo k off n →
      sh = Nat.log k (off + n - sl) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off sl sh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp only [List.not_mem_nil] at hmem
    · next h =>
        push Not at h
        obtain ⟨hn0, _⟩ := h
        rw [List.mem_cons] at hmem
        have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        rcases hmem with heq | hmem'
        · rw [Prod.ext_iff] at heq
          obtain ⟨hsl, hsh⟩ := heq
          simp only at hsl hsh
          subst hsl; subst hsh
          congr 1; omega
        · have hrec := ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) sl sh hmem'
          rw [hrec]; congr 1; omega

/-- **The boundary's new-frontier slot is at least as tall as the boundary
    subtree** (`bh ≤ sh`). The slot starts at `sl ≤ bl`, so `n - sl ≥ k ^ bh`
    leaves remain there; greedy then takes a subtree of height
    `log_k (n - sl) ≥ bh`. This is `reconstruct_consistency_roots`'s
    `new_height < boundary_height ⇒ None` guard, shown to never fire for an
    honest prefix relation. -/
private theorem newslot_height_ge (k newSize oldSize bl bh fIdx sl sh : Nat) (hk : 2 ≤ k)
    (hbspan : bl + k ^ bh = oldSize) (hold : oldSize ≤ newSize)
    (hslot : findFrontier k bl (frontierForSizeT k newSize) 0 = some (fIdx, sl, sh)) :
    bh ≤ sh := by
  obtain ⟨hget, hsle, _hblt⟩ := findFrontier_spec k bl (frontierForSizeT k newSize) 0 fIdx sl sh hslot
  have hmem : (sl, sh) ∈ frontierForSizeT k newSize :=
    List.mem_of_getElem? (by simpa using hget)
  have hheight : sh = Nat.log k (0 + newSize - sl) :=
    frontierGo_slot_height k hk newSize 0 sl sh hmem
  have hge : k ^ bh ≤ 0 + newSize - sl := by omega
  rw [hheight]
  exact Nat.le_log_of_pow_le (by omega) hge

/-- Every tile's left coordinate is at least the decomposition's start. -/
private theorem Tiles_left_ge (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat), Tiles k start coords stop →
      ∀ lh ∈ coords, start ≤ lh.1 := by
  intro coords
  induction coords with
  | nil => intro start stop _ lh hmem; simp only [List.not_mem_nil] at hmem
  | cons p rest ih =>
    intro start stop htiles lh hmem
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact le_of_eq hpl.symm
    · have := ih (start + k ^ ph) stop htrest lh hmem'; omega

/-- **`findFrontier` is tile-deterministic.** If it locates a tile `(l, h)` for
    one index, it locates the same tile for any other index that tile covers:
    the tiles are disjoint and ordered, so a second in-tile index skips exactly
    the same prefix. The fact that lets the boundary `bl` and the last old leaf
    `oldSize - 1` (both inside the boundary subtree) share a new-frontier slot. -/
private theorem findFrontier_unique (k i₁ i₂ : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop c fIdx l h : Nat),
      Tiles k start coords stop →
      findFrontier k i₁ coords c = some (fIdx, l, h) →
      l ≤ i₂ → i₂ < l + k ^ h →
      findFrontier k i₂ coords c = some (fIdx, l, h) := by
  intro coords
  induction coords with
  | nil => intro start stop c fIdx l h _ hf; simp only [findFrontier, reduceCtorEq] at hf
  | cons p rest ih =>
    intro start stop c fIdx l h htiles hf hle hlt
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    rw [findFrontier] at hf ⊢
    by_cases hc1 : pl ≤ i₁ ∧ i₁ < pl + k ^ ph
    · rw [if_pos hc1] at hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨hfi, hl, hh⟩ := hf
      subst hl; subst hh
      rw [if_pos ⟨hle, hlt⟩]
      simp [hfi]
    · rw [if_neg hc1] at hf
      obtain ⟨hget, _, _⟩ := findFrontier_spec k i₁ rest (c + 1) fIdx l h hf
      have hmem : (l, h) ∈ rest := List.mem_of_getElem? (by simpa using hget)
      have hlge : start + k ^ ph ≤ l := Tiles_left_ge k rest (start + k ^ ph) stop htrest (l, h) hmem
      have hi2 : ¬(pl ≤ i₂ ∧ i₂ < pl + k ^ ph) := by
        rintro ⟨_, hlt2⟩; omega
      rw [if_neg hi2]
      exact ih (start + k ^ ph) stop (c + 1) fIdx l h htrest hf hle hlt

/-- Dropping the low `bh` digit steps of a height-`sh` digit path leaves the
    height-`(sh - bh)` digit path of the `bh`-shifted offset. The digit-step
    counterpart of `start_hash` anchoring at the boundary height: the consistency
    skeleton's bisection steps are the inclusion skeleton's digit steps above
    `bh`. -/
private theorem digitSteps_drop (k : Nat) :
    ∀ (bh sh off : Nat), bh ≤ sh →
      (digitSteps k off sh).drop bh = digitSteps k (off / k ^ bh) (sh - bh) := by
  intro bh
  induction bh with
  | zero => intro sh off _; simp [pow_zero, Nat.div_one]
  | succ n ih =>
    intro sh off hle
    obtain ⟨s', rfl⟩ : ∃ s', sh = s' + 1 := ⟨sh - 1, by omega⟩
    rw [digitSteps, List.drop_succ_cons, ih s' (off / k) (by omega)]
    congr 1
    · rw [Nat.div_div_eq_div_mul, ← pow_succ']
    · omega

/-- `getD` into the left part of an append. -/
private theorem getD_append_lt {α} (l₁ l₂ : List α) (d : α) (i : Nat) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getD_eq_getElem?_getD]

/-- `getD` into the right part of an append. -/
private theorem getD_append_ge {α} (l₁ l₂ : List α) (d : α) (i : Nat) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getD_eq_getElem?_getD]

/-- `getD` below a `take` bound is unaffected. -/
private theorem getD_take_lt {α} (l : List α) (d : α) (n i : Nat) (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h, List.getD_eq_getElem?_getD]



/-- **Boundary/slot setup for an honest prefix.** Packages the geometric facts
    every honest-construction proof reuses: the boundary coordinate `(bl, bh)`
    (last old-frontier subtree, spanning `[bl, oldSize)`), the new-frontier slot
    `(fIdx, sl, sh)` containing both `bl` and the last old leaf `oldSize - 1`
    (`findFrontier` is tile-deterministic), with `bh ≤ sh`, `sl ≤ bl`, the
    bisection digit offsets agreeing (`(oldSize-1-sl)/k^bh = (bl-sl)/k^bh`), and
    the aligned-ancestor identity pinning the `bh`-level ancestor of `oldSize-1`
    to `bl`. -/
private theorem boundary_slot (k : Nat) (hk : 2 ≤ k) (cells : List Digest) (oldSize : Nat)
    (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    ∃ bl bh fIdx sl sh,
      (frontierForSizeT k oldSize).getLast? = some (bl, bh) ∧
      bl + k ^ bh = oldSize ∧
      findFrontier k bl (frontierForSizeT k cells.length) 0 = some (fIdx, sl, sh) ∧
      findFrontier k (oldSize - 1) (frontierForSizeT k cells.length) 0 = some (fIdx, sl, sh) ∧
      bh ≤ sh ∧ sl ≤ bl ∧
      (oldSize - 1 - sl) / k ^ bh = (bl - sl) / k ^ bh ∧
      sl + (oldSize - 1 - sl) / k ^ bh * k ^ bh = bl := by
  have hfrne : frontierForSizeT k oldSize ≠ [] := by
    intro he
    have ht := frontier_tiles k oldSize hk
    rw [he] at ht; simp only [Tiles] at ht; omega
  obtain ⟨bl, bh, hlast⟩ :
      ∃ bl bh, (frontierForSizeT k oldSize).getLast? = some (bl, bh) := by
    rcases hg : (frontierForSizeT k oldSize).getLast? with _ | ⟨bl, bh⟩
    · exact absurd (List.getLast?_eq_none_iff.mp hg) hfrne
    · exact ⟨bl, bh, rfl⟩
  have hspan : bl + k ^ bh = oldSize := frontier_getLast_eq k oldSize bl bh hk hlast
  have hbalign : k ^ bh ∣ bl := frontier_getLast_aligned k oldSize bl bh hk hlast
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  have hbllt : bl < cells.length := by omega
  obtain ⟨fIdx, sl, sh, hff⟩ := findFrontier_cover k bl (frontierForSizeT k cells.length) 0
    cells.length 0 (frontier_tiles k cells.length hk) (Nat.zero_le _) hbllt
  obtain ⟨hget, hsle, hblt⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  have hslmem : (sl, sh) ∈ frontierForSizeT k cells.length :=
    List.mem_of_getElem? (by simpa using hget)
  have hslalign : k ^ sh ∣ sl := frontierGo_aligned k hk cells.length 0 (by simp) (sl, sh) hslmem
  have hbhsh : bh ≤ sh :=
    newslot_height_ge k cells.length oldSize bl bh fIdx sl sh hk hspan (le_of_lt hnew) hff
  have hbhdvdsl : k ^ bh ∣ sl := dvd_trans (pow_dvd_pow k hbhsh) hslalign
  obtain ⟨a, ha⟩ := hbalign
  obtain ⟨b, hb⟩ := hbhdvdsl
  have hba : b ≤ a := Nat.le_of_mul_le_mul_left (by omega) hk0
  have hm : bl - sl = k ^ bh * (a - b) := by rw [ha, hb, Nat.mul_sub]
  set m := a - b with hmdef
  have hnest : bl + k ^ bh ≤ sl + k ^ sh := by
    obtain ⟨q, hq⟩ := pow_dvd_pow k hbhsh
    have h1 : k ^ bh * m < k ^ bh * q := by rw [← hq]; omega
    have hmq : m < q := lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
    have h2 : k ^ bh * (m + 1) ≤ k ^ bh * q := Nat.mul_le_mul (le_refl _) (by omega)
    have he : k ^ bh * (m + 1) = k ^ bh * m + k ^ bh := by ring
    rw [hq]; omega
  have hff2 : findFrontier k (oldSize - 1) (frontierForSizeT k cells.length) 0
      = some (fIdx, sl, sh) :=
    findFrontier_unique k bl (oldSize - 1) (frontierForSizeT k cells.length) 0 cells.length 0
      fIdx sl sh (frontier_tiles k cells.length hk) hff (by omega) (by omega)
  have hofs : (oldSize - 1 - sl) / k ^ bh = m := by
    have hrw : oldSize - 1 - sl = k ^ bh * m + (k ^ bh - 1) := by omega
    rw [hrw, Nat.mul_add_div hk0, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hdiveq : (oldSize - 1 - sl) / k ^ bh = (bl - sl) / k ^ bh := by
    rw [hofs, hm, Nat.mul_div_cancel_left m hk0]
  have halign : sl + (oldSize - 1 - sl) / k ^ bh * k ^ bh = bl := by
    have hc : m * k ^ bh = k ^ bh * m := Nat.mul_comm _ _
    rw [hofs]; omega
  exact ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, halign⟩


/-- A `Tiles` decomposition splits around any interior tile: the prefix tiles
    `[start, mid)`, the tile starts at `mid`, and the suffix tiles
    `[mid + k^height, stop)`. -/
private theorem Tiles_split (k : Nat) :
    ∀ (pre : List (Nat × Nat)) (tile : Nat × Nat) (post : List (Nat × Nat)) (start stop : Nat),
      Tiles k start (pre ++ tile :: post) stop →
      ∃ mid, Tiles k start pre mid ∧ tile.1 = mid ∧ Tiles k (mid + k ^ tile.2) post stop := by
  intro pre
  induction pre with
  | nil =>
    intro tile post start stop htiles
    obtain ⟨ht, hrest⟩ := htiles
    exact ⟨start, by simp [Tiles], ht, ht ▸ hrest⟩
  | cons p rest ih =>
    intro tile post start stop htiles
    obtain ⟨hp, hrest⟩ := htiles
    obtain ⟨mid, hpre, htile, hpost⟩ := ih tile post (start + k ^ p.2) stop hrest
    exact ⟨mid, ⟨hp, hpre⟩, htile, hpost⟩

/-- **Tiles are disjoint.** The tile located at index `fIdx` spans
    `[sl, sl + k^sh)`; every other tile's left coordinate lies outside that
    interval (prefix tiles end at or before `sl`, suffix tiles start at or after
    `sl + k^sh`). -/
private theorem Tiles_slot_avoids (k : Nat) (hk : 2 ≤ k) :
    ∀ (coords : List (Nat × Nat)) (start stop fIdx sl sh : Nat),
      Tiles k start coords stop → coords[fIdx]? = some (sl, sh) →
      ∀ i, i < coords.length → i ≠ fIdx →
        ¬ (sl ≤ (coords.getD i (0, 0)).1 ∧ (coords.getD i (0, 0)).1 < sl + k ^ sh) := by
    intro coords start stop fIdx sl sh htiles hget i hi hif
    have hflt : fIdx < coords.length := by
      rw [List.getElem?_eq_some_iff] at hget; obtain ⟨h, _⟩ := hget; exact h
    have hdecomp : coords = coords.take fIdx ++ (sl, sh) :: coords.drop (fIdx + 1) := by
      conv_lhs => rw [← List.take_append_drop fIdx coords, List.drop_eq_getElem_cons hflt]
      rw [List.getElem?_eq_getElem hflt] at hget
      rw [Option.some.injEq] at hget
      rw [hget]
    have htakelen : (coords.take fIdx).length = fIdx := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    obtain ⟨mid, hpre, htileeq, hpost⟩ :=
      Tiles_split k (coords.take fIdx) (sl, sh) (coords.drop (fIdx + 1)) start stop
        (hdecomp ▸ htiles)
    simp only at htileeq
    subst htileeq
    rintro ⟨hge, hlt⟩
    rcases Nat.lt_or_ge i fIdx with hlo | hhi
    · -- prefix tile: its span ends at or before sl
      have hmem : coords.getD i (0, 0) ∈ coords.take fIdx := by
        have hi' : i < (coords.take fIdx).length := by rw [htakelen]; exact hlo
        rw [← getD_take_lt coords (0, 0) fIdx i hlo, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi', Option.getD_some]
        exact List.getElem_mem _
      have hb := Tiles_entry_bound k (coords.take fIdx) start sl hpre _ hmem
      have hpos : 0 < k ^ (coords.getD i (0, 0)).2 := pow_pos (by omega) _
      omega
    · -- suffix tile: its left is at or beyond sl + k^sh
      have hidrop : coords.getD i (0, 0) = (coords.drop (fIdx + 1)).getD (i - (fIdx + 1)) (0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
          show (fIdx + 1) + (i - (fIdx + 1)) = i from by omega]
      have hmem : coords.getD i (0, 0) ∈ coords.drop (fIdx + 1) := by
        rw [hidrop, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (l := coords.drop (fIdx + 1))
            (by rw [List.length_drop]; omega)]
        exact List.getElem_mem _
      have hb := Tiles_left_ge k (coords.drop (fIdx + 1)) (sl + k ^ sh) stop hpost _ hmem
      omega

/-- **A frontier tile shares its parent block with the last leaf.** Every
    perfect subtree `(cl, ch)` of the greedy decomposition of `[off, off+n)` lies
    in the same `k^(ch+1)`-block as the last leaf `off+n-1`: greedy emits a
    height-`ch` tile only when the surrounding `k^(ch+1)`-block would overflow the
    range, so the block cannot have been completed to a taller tile. The
    invariants — the offset is `k^(log n)`-aligned and the remaining range fits in
    the offset's `k^(log n + 1)`-block — are preserved by the greedy step. -/
private theorem frontier_block (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off : Nat), k ^ Nat.log k n ∣ off →
      off % k ^ (Nat.log k n + 1) + n ≤ k ^ (Nat.log k n + 1) →
      ∀ cl ch, (cl, ch) ∈ frontierGo k off n →
        cl / k ^ (ch + 1) = (off + n - 1) / k ^ (ch + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off halign hfit cl ch hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp at hmem
    · next h =>
      push Not at h
      obtain ⟨hn0, _⟩ := h
      set L := Nat.log k n with hL
      have hcap : k ^ L ≤ n := Nat.pow_log_le_self k hn0
      have hcaplt : n < k ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) n
      have hcappos : 0 < k ^ L := pow_pos (by omega) L
      have hpL1 : 0 < k ^ (L + 1) := pow_pos (by omega) (L + 1)
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem'
      · -- first tile (off, L): off and off+n-1 lie in off's (L+1)-block
        rw [Prod.mk.injEq] at heq
        obtain ⟨hcl, hch⟩ := heq
        subst cl; subst ch
        have hr : off % k ^ (L + 1) + (n - 1) < k ^ (L + 1) := by omega
        have hdm : off = k ^ (L + 1) * (off / k ^ (L + 1)) + off % k ^ (L + 1) :=
          (Nat.div_add_mod off (k ^ (L + 1))).symm
        have hrw : off + n - 1 = k ^ (L + 1) * (off / k ^ (L + 1)) + (off % k ^ (L + 1) + (n - 1)) := by
          omega
        rw [hrw, Nat.mul_add_div hpL1, Nat.div_eq_of_lt hr]; omega
      · -- recursive tiles: same total `off + n`, push the invariants down
        have hL'le : Nat.log k (n - k ^ L) ≤ L :=
          Nat.log_mono_right (show n - k ^ L ≤ n by omega)
        have hdvd' : k ^ Nat.log k (n - k ^ L) ∣ off + k ^ L :=
          Nat.dvd_add (dvd_trans (pow_dvd_pow k hL'le) halign) (pow_dvd_pow k hL'le)
        have hfit' : (off + k ^ L) % k ^ (Nat.log k (n - k ^ L) + 1) + (n - k ^ L)
            ≤ k ^ (Nat.log k (n - k ^ L) + 1) := by
          set L' := Nat.log k (n - k ^ L) with hL'
          have hn'pos : 0 < n - k ^ L := by
            rcases Nat.eq_zero_or_pos (n - k ^ L) with h0 | hp
            · exfalso; rw [frontierGo, dif_pos (by left; omega)] at hmem'; simp at hmem'
            · exact hp
          have hcaplt' : n - k ^ L < k ^ (L' + 1) := Nat.lt_pow_succ_log_self (by omega) _
          rcases Nat.lt_or_ge L' L with hlt | hge
          · -- shorter: the new offset is a multiple of k^(L'+1)
            have hdvdoff : k ^ (L' + 1) ∣ off + k ^ L :=
              Nat.dvd_add (dvd_trans (pow_dvd_pow k (by omega)) halign) (pow_dvd_pow k (by omega))
            obtain ⟨c', hc'⟩ := hdvdoff
            rw [hc', Nat.mul_mod_right]; omega
          · -- equal log: the digit has not carried, so the block still fits
            have hL'eq : L' = L := by omega
            have ha : off = k ^ L * (off / k ^ L) := by
              rw [Nat.mul_comm]; exact (Nat.div_mul_cancel halign).symm
            have hmodoff : off % k ^ (L + 1) = off / k ^ L % k * k ^ L := by
              conv_lhs => rw [ha, pow_succ]
              rw [Nat.mul_mod_mul_left, Nat.mul_comm]
            have hge2 : k ^ L ≤ n - k ^ L := by
              have h := Nat.pow_log_le_self k (show n - k ^ L ≠ 0 by omega)
              rw [← hL', hL'eq] at h; exact h
            have hdigit : off / k ^ L % k + 1 < k := by
              by_contra hc
              push Not at hc
              have hmk : off / k ^ L % k = k - 1 := by
                have := Nat.mod_lt (off / k ^ L) (show 0 < k by omega); omega
              rw [hmodoff, hmk, pow_succ'] at hfit
              have e1 : (k - 1) * k ^ L + 2 * k ^ L = (k + 1) * k ^ L := by
                rw [← Nat.add_mul]; congr 1; omega
              have e2 : (k + 1) * k ^ L = k * k ^ L + k ^ L := by ring
              omega
            have hRlt : off / k ^ L % k * k ^ L + k ^ L < k ^ (L + 1) := by
              have h1 : (off / k ^ L % k + 1) * k ^ L = off / k ^ L % k * k ^ L + k ^ L := by ring
              have h2 : (off / k ^ L % k + 1) * k ^ L ≤ (k - 1) * k ^ L :=
                Nat.mul_le_mul_right (k ^ L) (by omega)
              have h3 : (k - 1) * k ^ L < k * k ^ L := (Nat.mul_lt_mul_right hcappos).mpr (by omega)
              rw [pow_succ']; omega
            have hmod2 : (off + k ^ L) % k ^ (L + 1) = off / k ^ L % k * k ^ L + k ^ L := by
              have hdecomp : off + k ^ L
                  = k ^ (L + 1) * (off / k ^ (L + 1)) + (off / k ^ L % k * k ^ L + k ^ L) := by
                have := Nat.div_add_mod off (k ^ (L + 1)); rw [hmodoff] at this; omega
              rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hRlt]
            rw [hL'eq, hmod2]
            rw [hmodoff] at hfit
            omega
        have hrec := ih (n - k ^ L) (by omega) (off + k ^ L) hdvd' hfit' cl ch hmem'
        rwa [show off + k ^ L + (n - k ^ L) - 1 = off + n - 1 from by omega] at hrec

/-- Every left coordinate in `frontierGo k off n` is at least `off`. -/
private theorem frontierGo_left_ge' (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off : Nat), ∀ lh ∈ frontierGo k off n, off ≤ lh.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off lh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp at hmem
    · next h =>
      push Not at h
      obtain ⟨hn0, _⟩ := h
      have hcap : 0 < k ^ Nat.log k n := pow_pos (by omega) _
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact le_refl _
      · have := ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) lh hmem'; omega

/-- **The old and new frontiers agree on tiles left of the slot.** While greedy
    decomposes `[off, off+sl)`, the old and current sizes emit the same tiles: a
    tile is recorded left of `sl` only when both sizes share the top power (forced
    because the slot `(sl, sh)` of the current frontier lies past it, so the top
    power fits within `sl - off`, and the old size — being at least `sl - off` and
    at most the current size — has the same log). Hence the prefix of tiles with
    left `< sl` is identical. -/
private theorem frontier_agree (k : Nat) (hk : 2 ≤ k) :
    ∀ (newN off oldN sl sh : Nat),
      k ^ Nat.log k newN ∣ off → (sl, sh) ∈ frontierGo k off newN →
      off ≤ sl → sl ≤ off + oldN → oldN ≤ newN →
      (frontierGo k off oldN).filter (fun c => decide (c.1 < sl))
        = (frontierGo k off newN).filter (fun c => decide (c.1 < sl)) := by
  intro newN
  induction newN using Nat.strong_induction_on with
  | _ newN ih =>
    intro off oldN sl sh halign hslot hoff hsl hle
    have hnew0 : newN ≠ 0 := by
      intro h; rw [h, frontierGo, dif_pos (by left; rfl)] at hslot; simp at hslot
    set L := Nat.log k newN with hL
    have hcap : k ^ L ≤ newN := Nat.pow_log_le_self k hnew0
    have hcappos : 0 < k ^ L := pow_pos (by omega) L
    rw [frontierGo, dif_neg (by push Not; exact ⟨by omega, by omega⟩)] at hslot
    rw [List.mem_cons] at hslot
    rcases hslot with heq | hmem
    · -- slot is the first tile: sl = off, no tile lies left of sl
      rw [Prod.mk.injEq] at heq
      have hsloff : sl = off := heq.1
      rw [List.filter_eq_nil_iff.mpr (fun c hc => by
            simp only [decide_eq_true_eq, not_lt]; rw [hsloff]
            exact frontierGo_left_ge' k hk oldN off c hc),
          List.filter_eq_nil_iff.mpr (fun c hc => by
            simp only [decide_eq_true_eq, not_lt]; rw [hsloff]
            exact frontierGo_left_ge' k hk newN off c hc)]
    · -- slot is deeper: the first tile is shared and lies left of sl
      have hslge : off + k ^ L ≤ sl :=
        frontierGo_left_ge' k hk (newN - k ^ L) (off + k ^ L) (sl, sh) hmem
      have hofflt : off < sl := by omega
      have hkLle : k ^ L ≤ oldN := by omega
      have hlogold : Nat.log k oldN = L := by
        have h1 : L ≤ Nat.log k oldN := Nat.le_log_of_pow_le (by omega) hkLle
        have h2 : Nat.log k oldN ≤ L := Nat.log_mono_right hle
        omega
      have hold0 : oldN ≠ 0 := by omega
      -- unfold both first tiles (both (off, L)) and strip them
      have hfO : frontierGo k off oldN
          = (off, Nat.log k oldN) :: frontierGo k (off + k ^ Nat.log k oldN) (oldN - k ^ Nat.log k oldN) := by
        rw [frontierGo, dif_neg (by push Not; exact ⟨by omega, by omega⟩)]
      have hfN : frontierGo k off newN
          = (off, L) :: frontierGo k (off + k ^ L) (newN - k ^ L) := by
        rw [frontierGo, dif_neg (by push Not; exact ⟨by omega, by omega⟩)]
      rw [hfO, hfN, hlogold, List.filter_cons_of_pos (by simp [hofflt]),
        List.filter_cons_of_pos (by simp [hofflt])]
      congr 1
      have hdvd' : k ^ Nat.log k (newN - k ^ L) ∣ off + k ^ L :=
        Nat.dvd_add (dvd_trans (pow_dvd_pow k (Nat.log_mono_right (by omega))) halign)
          (pow_dvd_pow k (Nat.log_mono_right (by omega)))
      exact ih (newN - k ^ L) (by omega) (off + k ^ L) (oldN - k ^ L) sl sh hdvd' hmem
        (by omega) (by omega) (by omega)


/-- Removing the single matching element from `range k` is `eraseIdx` at it. -/
private theorem filter_ne_range_eq_eraseIdx' (k p : Nat) (hp : p < k) :
    (List.range k).filter (fun i => i != p) = (List.range k).eraseIdx p := by
  induction k with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_ge p n with hpn | hpn
    · rw [ih hpn, List.eraseIdx_append_of_lt_length (by rw [List.length_range]; exact hpn)]
      have hb : (n != p) = true := by simp [bne_iff_ne]; omega
      simp [hb]
    · have hpeq : p = n := by omega
      subst hpeq
      have hf1 : (List.range p).filter (fun i => i != p) = List.range p := by
        apply List.filter_eq_self.mpr
        intro a ha; rw [List.mem_range] at ha; simp [bne_iff_ne]; omega
      rw [hf1, List.eraseIdx_append_of_length_le (by rw [List.length_range])]
      simp

/-- The honest digit step's `i`-th sibling (for `i` below the path digit) is the
    genuine perfect root of the `i`-th child of the level block. -/
private theorem honest_digit_sibling (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (sl offset j i : Nat) (hi : i < offset / k ^ j % k) :
    (((List.range k).filter (fun x => x != offset / k ^ j % k)).map
       (fun x => perfectRoot k cells (sl + (offset / k ^ (j + 1) * k + x) * k ^ j) j)).getD i emptyHash
      = perfectRoot k cells (sl + (offset / k ^ (j + 1) * k + i) * k ^ j) j := by
  have hd : offset / k ^ j % k < k := Nat.mod_lt _ (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, filter_ne_range_eq_eraseIdx' k _ hd,
    List.getElem?_eraseIdx, if_pos hi, List.getElem?_range (by omega)]
  rfl


/-- Tiles are strictly ordered by left coordinate. -/
private theorem Tiles_strict_mono (k : Nat) (hk : 2 ≤ k) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat), Tiles k start coords stop →
      ∀ a b, a < b → b < coords.length →
        (coords.getD a (0, 0)).1 < (coords.getD b (0, 0)).1 := by
  intro coords
  induction coords with
  | nil => intro start stop _ a b _ hb; simp at hb
  | cons p rest ih =>
    intro start stop htiles a b hab hb
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    have hcap : 0 < k ^ ph := pow_pos (by omega) ph
    cases a with
    | zero =>
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      have hmem : rest.getD b' (0, 0) ∈ rest := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp only [List.length_cons] at hb; omega)]
        exact List.getElem_mem _
      have := Tiles_left_ge k rest (start + k ^ ph) stop htrest _ hmem
      omega
    | succ a' =>
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      simp only [List.getD_cons_succ]
      exact ih (start + k ^ ph) stop htrest a' b' (by omega)
        (by simp only [List.length_cons] at hb; omega)


/-! ## The verifier model — MMR-native (inclusion of the boundary peak + peak bag)

`reconstruct_consistency_roots` (`cml/src/consistency.rs`) no longer carries a
bisection trace and coordinate map: it lifts the old tree's last peak
(`boundary_hash`) through `peak_path` to the new frontier slot it merged into
(`new_peaks[split_index]`), bags the given `new_peaks` to the new root, and bags
`new_peaks[..split_index] ++ merged-left-siblings ++ [boundary_hash]` to the old
root. The merged-left-siblings are the older peaks that fused into the boundary
mountain — the `peak_path` left-siblings, gathered highest-mountain first. -/

/-- The merged-in left-siblings gathered from the climb `path` in reverse
    (highest mountain first), each step contributing `siblings[..position]` —
    `reconstruct_consistency_roots`'s `peak_path.iter().rev()` gather (Rust caps
    the take at `siblings.len()`; `List.take` caps definitionally). -/
def mergedLeftSibs (path : List ProofStep) : List Digest :=
  path.reverse.flatMap (fun s => s.siblings.take s.position)

/-- `reconstruct_consistency_roots`, modeled functionally on the shipped
    MMR-native shape. Structural guards (split slot, height, new-frontier
    length) are decidable and gate the result here; the inclusion digest check
    (`recovered == new_peaks[split_index]`) is carried as a separate clause of
    `AcceptsConsistency` (digests have no `DecidableEq`), mirroring how the old
    model factored the dual-root match. -/
noncomputable def reconstructConsistencyRoots (k oldSize newSize : Nat)
    (boundaryHash : Digest) (newPeaks : List Digest) (splitIndex : Nat)
    (peakPath : List ProofStep) : Option (Digest × Digest) :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => none
  | some (bl, bh) =>
    match findFrontier k bl (frontierForSizeT k newSize) 0 with
    | none => none
    | some (fIdx, _sl, sh) =>
      if splitIndex = fIdx ∧ bh ≤ sh ∧
         newPeaks.length = (frontierForSizeT k newSize).length ∧
         splitIndex < newPeaks.length then
        some (foldFrontierRoot k
                (newPeaks.take splitIndex ++ mergedLeftSibs peakPath ++ [boundaryHash]),
              foldFrontierRoot k newPeaks)
      else none

/-- The consistency-proof climb skeleton pinned by `reconstruct_consistency_roots`:
    the `sh - bh` digit steps lifting the boundary subtree (height `bh`) to its
    new-frontier mountain peak (height `sh`). The bag steps above the peak are no
    longer part of the proof — the peaks are given as `new_peaks`. -/
def consistencySkeleton (k oldSize newSize : Nat) : Option (List (Nat × Nat)) :=
  if k < 2 then none
  else match (frontierForSizeT k oldSize).getLast? with
    | none => none
    | some (bl, bh) =>
      match findFrontier k bl (frontierForSizeT k newSize) 0 with
      | none => none
      | some (_fIdx, sl, sh) =>
        if bh ≤ sh then some (digitSteps k ((bl - sl) / k ^ bh) (sh - bh)) else none

/-- The peak path's per-step shape matches the climb skeleton exactly. -/
def StructureConsistencyOK (k oldSize newSize : Nat) (path : List ProofStep) : Prop :=
  ∃ skel, consistencySkeleton k oldSize newSize = some skel ∧ path.map stepShape = skel

/-- The accept relation of `verify_consistency`, minus DoS bounds: size guards,
    climb-skeleton pinning, canonical well-formedness, the inclusion check
    (`foldNary boundaryHash peakPath = new_peaks[splitIndex]`), and the dual-root
    match `reconstruct_consistency_roots(..) = some (oldRoot, newRoot)`. -/
def AcceptsConsistency (k oldSize newSize : Nat) (boundaryHash : Digest)
    (peakPath : List ProofStep) (newPeaks : List Digest) (splitIndex : Nat)
    (oldRoot newRoot : Digest) : Prop :=
  2 ≤ k ∧ 0 < oldSize ∧ oldSize < newSize ∧
  StructureConsistencyOK k oldSize newSize peakPath ∧
  WellFormedSteps peakPath ∧
  foldNary boundaryHash peakPath = newPeaks.getD splitIndex emptyHash ∧
  reconstructConsistencyRoots k oldSize newSize boundaryHash newPeaks splitIndex peakPath
    = some (oldRoot, newRoot)

/-! ## The honest prover (non-vacuity witness) -/

/-- The honest `boundary_hash`: the genuine root of the boundary subtree. -/
noncomputable def honestBoundaryHash (k : Nat) (cells : List Digest)
    (oldSize : Nat) : Digest :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => emptyHash
  | some (bl, bh) => perfectRoot k cells bl bh

/-- The honest `new_peaks`: the genuine perfect roots of the new frontier. -/
noncomputable def honestNewPeaks (k : Nat) (cells : List Digest) : List Digest :=
  (frontierForSizeT k cells.length).map (fun c => perfectRoot k cells c.1 c.2)

/-- The honest `split_index`: the new-frontier slot the boundary merged into. -/
noncomputable def honestSplitIndex (k : Nat) (cells : List Digest)
    (oldSize : Nat) : Nat :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => 0
  | some (bl, _bh) =>
    match findFrontier k bl (frontierForSizeT k cells.length) 0 with
    | none => 0
    | some (fIdx, _sl, _sh) => fIdx

/-- The honest `peak_path`: the climb of the boundary subtree to its new-frontier
    peak — the digit path of the last old leaf inside the slot, from the boundary
    height `bh` up to the slot height `sh`. -/
noncomputable def honestPeakPath (k : Nat) (cells : List Digest)
    (oldSize : Nat) : List ProofStep :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => []
  | some (bl, bh) =>
    match findFrontier k bl (frontierForSizeT k cells.length) 0 with
    | none => []
    | some (_fIdx, sl, sh) => (honestDigitPath k cells sl (oldSize - 1 - sl) sh).drop bh

/-! ## Honest climb fold and shape -/

/-- **The honest climb folds the boundary peak to the new-frontier peak.**
    `foldNary (perfectRoot bl bh) climb = perfectRoot sl sh`: the climb is the
    upper portion (heights `[bh, sh)`) of the slot's digit path, which folds the
    last old leaf to the slot peak (`digitFold`); its lower `bh` steps fold the
    leaf to the boundary peak (which `boundary_hash` is). -/
private theorem honest_climb_fold (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    foldNary (honestBoundaryHash k cells oldSize) (honestPeakPath k cells oldSize)
      = (honestNewPeaks k cells).getD (honestSplitIndex k cells oldSize) emptyHash := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨hgetN, hsleN, _hbltN⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  obtain ⟨_hget2, hsle2, hblt2⟩ :=
    findFrontier_spec k (oldSize - 1) (frontierForSizeT k cells.length) 0 fIdx sl sh hff2
  simp only [Nat.sub_zero] at hgetN
  set off := oldSize - 1 - sl with hoff
  have hoffsh : off < k ^ sh := by omega
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  -- target peak value
  have hpeakval : (honestNewPeaks k cells).getD fIdx emptyHash = perfectRoot k cells sl sh := by
    rw [honestNewPeaks, List.getD_eq_getElem?_getD, List.getElem?_map, hgetN]
    rfl
  simp only [honestBoundaryHash, honestPeakPath, honestSplitIndex, hlast, hff, hpeakval]
  set leaf := cells.getD (oldSize - 1) emptyHash with hleaf
  -- full digit path folds leaf to slot peak
  have hfullfold : foldNary leaf (honestDigitPath k cells sl off sh) = perfectRoot k cells sl sh := by
    have h := digitFold k hk cells sl sh off
    rw [show sl + off = oldSize - 1 from by omega, ← hleaf,
      Nat.div_eq_of_lt hoffsh, Nat.zero_mul, Nat.add_zero] at h
    exact h
  -- lower bh steps fold leaf to boundary peak
  have htakefold : foldNary leaf ((honestDigitPath k cells sl off sh).take bh)
      = perfectRoot k cells bl bh := by
    have htk : (honestDigitPath k cells sl off sh).take bh = honestDigitPath k cells sl off bh := by
      rw [honestDigitPath, honestDigitPath, ← List.map_take, List.take_range, Nat.min_eq_left hbhsh]
    rw [htk]
    have h := digitFold k hk cells sl bh off
    rw [show sl + off = oldSize - 1 from by omega, ← hleaf, halign] at h
    exact h
  -- split full fold at bh
  have hsplit : foldNary leaf (honestDigitPath k cells sl off sh)
      = foldNary (foldNary leaf ((honestDigitPath k cells sl off sh).take bh))
          ((honestDigitPath k cells sl off sh).drop bh) := by
    rw [foldNary, foldNary, foldNary, ← List.foldl_append, List.take_append_drop]
  rw [hsplit, htakefold] at hfullfold
  exact hfullfold

/-- **The honest climb has the pinned skeleton shape.** -/
private theorem honest_consistency_shape (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    StructureConsistencyOK k oldSize cells.length (honestPeakPath k cells oldSize) := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, _halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨⟨skel, hskel, hmap⟩, _hwf⟩ := honest_path_shape k hk cells (oldSize - 1) (by omega)
  set G := (groupingSteps k (frontierForSizeT k cells.length).length fIdx).map
    (fun pc => (pc.1, pc.2 - 1)) with hG
  have hsk : inclusionSkeleton k cells.length (oldSize - 1)
      = some (digitSteps k (oldSize - 1 - sl) sh ++ G) := by
    rw [inclusionSkeleton, if_neg (show ¬ k < 2 by omega)]
    simp only [hff2, hG]
  have hskelval : skel = digitSteps k (oldSize - 1 - sl) sh ++ G :=
    Option.some.inj (hskel.symm.trans hsk)
  -- the honest inclusion path's digit prefix maps to digitSteps
  have hincl : honestInclusionPath k cells (oldSize - 1)
      = honestDigitPath k cells sl (oldSize - 1 - sl) sh
        ++ honestGroupPath k (buildStackCells k cells) fIdx := by
    simp only [honestInclusionPath, hff2]
  have hdlen : (digitSteps k (oldSize - 1 - sl) sh).length = sh := by
    rw [digitSteps_eq_map, List.length_map, List.length_range]
  have hddlen : (honestDigitPath k cells sl (oldSize - 1 - sl) sh).length = sh := by
    rw [honestDigitPath, List.length_map, List.length_range]
  have hmapsplit : (honestDigitPath k cells sl (oldSize - 1 - sl) sh).map stepShape
      = digitSteps k (oldSize - 1 - sl) sh := by
    rw [hincl, List.map_append, hskelval] at hmap
    have hlenmatch : ((honestDigitPath k cells sl (oldSize - 1 - sl) sh).map stepShape).length
        = (digitSteps k (oldSize - 1 - sl) sh).length := by
      rw [List.length_map, hddlen, hdlen]
    exact (List.append_inj hmap hlenmatch).1
  have hcskel : consistencySkeleton k oldSize cells.length
      = some (digitSteps k ((bl - sl) / k ^ bh) (sh - bh)) := by
    rw [consistencySkeleton, if_neg (show ¬ k < 2 by omega)]
    simp only [hlast, hff, hbhsh, if_true]
  refine ⟨digitSteps k ((bl - sl) / k ^ bh) (sh - bh), hcskel, ?_⟩
  simp only [honestPeakPath, hlast, hff]
  rw [List.map_drop, hmapsplit, digitSteps_drop k bh sh (oldSize - 1 - sl) hbhsh, hdiveq]

/-- The honest climb is well-formed (a sub-portion of the honest inclusion path). -/
private theorem honest_peakpath_wf (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    WellFormedSteps (honestPeakPath k cells oldSize) := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, _hspan, hff, hff2, _hbhsh, _hsle, _hdiveq, _halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨_, hwf⟩ := honest_path_shape k hk cells (oldSize - 1) (by omega)
  have hincl : honestInclusionPath k cells (oldSize - 1)
      = honestDigitPath k cells sl (oldSize - 1 - sl) sh
        ++ honestGroupPath k (buildStackCells k cells) fIdx := by
    simp only [honestInclusionPath, hff2]
  intro s hs
  simp only [honestPeakPath, hlast, hff] at hs
  apply hwf s
  rw [hincl]
  exact List.mem_append_left _ (List.mem_of_mem_drop hs)

/-! ## The honest old-peak decomposition (the increment-proof correctness core) -/

/-- **Frontier split at a tile-start.** A greedy frontier splits at any tile
    start `sl` it contains: the tiles left of `sl` (its prefix, since the
    decomposition is left-sorted) followed by the standalone greedy frontier of
    the remaining `[sl, off+n)` region. The recursion reaches `sl` exactly
    because `sl` is a member tile start. -/
private theorem frontierGo_split (k : Nat) (hk : 2 ≤ k) (sl : Nat) :
    ∀ (n off x : Nat), (sl, x) ∈ frontierGo k off n → off ≤ sl →
      frontierGo k off n
        = (frontierGo k off n).filter (fun c => decide (c.1 < sl))
          ++ frontierGo k sl (off + n - sl) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off x hmem hoff
    have hn0 : n ≠ 0 := by rintro rfl; simp [frontierGo] at hmem
    have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
    have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
    have hunfold : frontierGo k off n
        = (off, Nat.log k n) :: frontierGo k (off + k ^ Nat.log k n) (n - k ^ Nat.log k n) := by
      conv_lhs => rw [frontierGo]
      rw [dif_neg (by push Not; exact ⟨by omega, by omega⟩)]
    by_cases hoffsl : off = sl
    · subst hoffsl
      have hfilt : (frontierGo k off n).filter (fun c => decide (c.1 < off)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        simp only [decide_eq_true_eq, not_lt]
        exact frontierGo_left_ge' k hk n off c hc
      rw [hfilt, List.nil_append]
      congr 1
      omega
    · have hofflt : off < sl := by omega
      rw [hunfold, List.mem_cons] at hmem
      have hmem' : (sl, x) ∈ frontierGo k (off + k ^ Nat.log k n) (n - k ^ Nat.log k n) := by
        rcases hmem with heq | h
        · rw [Prod.mk.injEq] at heq; omega
        · exact h
      have hge : off + k ^ Nat.log k n ≤ sl :=
        frontierGo_left_ge' k hk (n - k ^ Nat.log k n) (off + k ^ Nat.log k n) (sl, x) hmem'
      have hih := ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) x hmem' hge
      rw [show (off + k ^ Nat.log k n) + (n - k ^ Nat.log k n) - sl = off + n - sl from by omega]
        at hih
      rw [hunfold, List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hofflt),
        List.cons_append, ← hih]

/-- **Frontier offset shift.** Translating the decomposition origin by `c`
    translates every tile's left coordinate by `c`, leaving heights fixed. -/
private theorem frontierGo_shift (k : Nat) (hk : 2 ≤ k) :
    ∀ (n c off : Nat),
      frontierGo k (c + off) n = (frontierGo k off n).map (fun lh => (c + lh.1, lh.2)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c off
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp [frontierGo]
    · have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k (by omega)
      have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
      have hunfoldL : frontierGo k (c + off) n
          = (c + off, Nat.log k n)
              :: frontierGo k (c + off + k ^ Nat.log k n) (n - k ^ Nat.log k n) := by
        conv_lhs => rw [frontierGo]
        rw [dif_neg (by push Not; exact ⟨by omega, by omega⟩)]
      have hunfoldR : frontierGo k off n
          = (off, Nat.log k n)
              :: frontierGo k (off + k ^ Nat.log k n) (n - k ^ Nat.log k n) := by
        conv_lhs => rw [frontierGo]
        rw [dif_neg (by push Not; exact ⟨by omega, by omega⟩)]
      rw [hunfoldL, hunfoldR, List.map_cons]
      congr 1
      rw [show c + off + k ^ Nat.log k n = c + (off + k ^ Nat.log k n) from by omega]
      exact ih (n - k ^ Nat.log k n) (by omega) c (off + k ^ Nat.log k n)

/-- **Iterated scale.** Multiplying the leaf count by `k ^ d` raises every tile
    by `d` levels and scales its span by `k ^ d`. The `d`-fold iterate of
    `frontierForSizeT_scale`. -/
private theorem frontier_scale_pow (k : Nat) (hk : 2 ≤ k) :
    ∀ (d a : Nat),
      frontierForSizeT k (a * k ^ d)
        = (frontierForSizeT k a).map (fun lh => (lh.1 * k ^ d, lh.2 + d)) := by
  intro d
  induction d with
  | zero =>
    intro a
    simp only [pow_zero, Nat.mul_one, Nat.add_zero]
    conv_lhs => rw [← List.map_id (frontierForSizeT k a)]
    apply List.map_congr_left
    intro lh _
    rfl
  | succ d ih =>
    intro a
    have he : a * k ^ (d + 1) = (a * k ^ d) * k := by rw [pow_succ]; ring
    rw [he, frontierForSizeT_scale k hk (a * k ^ d), ih a, List.map_map]
    apply List.map_congr_left
    intro lh _
    simp only [Function.comp_apply, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [pow_succ]; ring
    · omega

/-- **Minimum tile height under divisibility.** If `k ^ d ∣ n` then every tile of
    the decomposition of `[off, off+n)` has height at least `d`: the low `d`
    digits of `n` are zero, so greedy never emits a tile shorter than `k ^ d`. -/
private theorem frontierGo_min_height (k : Nat) (hk : 2 ≤ k) (d : Nat) :
    ∀ (n off : Nat), k ^ d ∣ n → ∀ lh ∈ frontierGo k off n, d ≤ lh.2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off hdvd lh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp at hmem
    · next h =>
      push Not at h
      obtain ⟨hn0, _⟩ := h
      have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k (by omega)
      have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
      have hkd : k ^ d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hdle : d ≤ Nat.log k n := Nat.le_log_of_pow_le (by omega) hkd
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact hdle
      · have hdvd' : k ^ d ∣ (n - k ^ Nat.log k n) :=
          Nat.dvd_sub hdvd (pow_dvd_pow k hdle)
        exact ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) hdvd' lh hmem'

/-- **Climb left-siblings rebuild the in-slot frontier.** The left-child
    coordinates gathered along the digit climb of the last leaf (offset `off`
    inside its height-`sh` slot at `sl`), from level `p` upward, are exactly the
    `k^p`-scaled, `sl`-shifted frontier of `off / k ^ p`. Each climb level peels
    the low base-`k` digit of `off / k ^ p` as a suffix, mirroring
    `frontier_divstep`'s recursion (`off < k ^ sh`, so the top levels vanish). -/
private theorem climb_coords_eq (k : Nat) (hk : 2 ≤ k) (sl sh off : Nat)
    (hoff : off < k ^ sh) :
    ∀ p, p ≤ sh →
      (((List.range sh).drop p).reverse.flatMap
        (fun j => (List.range (off / k ^ j % k)).map
          (fun i => (sl + (off / k ^ (j + 1) * k + i) * k ^ j, j))))
        = (frontierForSizeT k (off / k ^ p)).map (fun lh => (sl + lh.1 * k ^ p, lh.2 + p)) := by
  suffices H : ∀ d p, p + d = sh →
      (((List.range sh).drop p).reverse.flatMap
        (fun j => (List.range (off / k ^ j % k)).map
          (fun i => (sl + (off / k ^ (j + 1) * k + i) * k ^ j, j))))
        = (frontierForSizeT k (off / k ^ p)).map (fun lh => (sl + lh.1 * k ^ p, lh.2 + p)) by
    intro p hp; exact H (sh - p) p (by omega)
  intro d
  induction d with
  | zero =>
    intro p hp
    have hpsh : p = sh := by omega
    rw [List.drop_eq_nil_of_le (by rw [List.length_range]; omega)]
    simp only [List.reverse_nil, List.flatMap_nil]
    have h0 : off / k ^ p = 0 := Nat.div_eq_of_lt (by rw [hpsh]; exact hoff)
    rw [h0]
    simp [frontierForSizeT, frontierGo]
  | succ d ih =>
    intro p hp
    have hplt : p < sh := by omega
    have hdrop : (List.range sh).drop p = p :: (List.range sh).drop (p + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [List.length_range]; exact hplt)]
      congr 1
      simp [List.getElem_range]
    rw [hdrop, List.reverse_cons, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ih (p + 1) (by omega)]
    -- digit decomposition off/k^p = (off/k^(p+1))*k + off/k^p%k
    have hb : off / k ^ p % k < k := Nat.mod_lt _ (by omega)
    have hdec : off / k ^ p = off / k ^ (p + 1) * k + off / k ^ p % k := by
      conv_lhs => rw [← Nat.div_add_mod (off / k ^ p) k]
      rw [show off / k ^ p / k = off / k ^ (p + 1) from by rw [pow_succ, Nat.div_div_eq_div_mul]]
      ring
    conv_rhs => rw [hdec, frontier_divstep k hk (off / k ^ (p + 1)) (off / k ^ p % k) hb,
        List.map_append]
    congr 1
    · rw [List.map_map]
      apply List.map_congr_left
      intro lh _
      simp only [Function.comp_apply, Prod.mk.injEq]
      exact ⟨by rw [pow_succ]; ring, by omega⟩
    · rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, Nat.zero_add]

/-- Taking the `p` lowest of `range k` with element `p` removed leaves `range p`:
    those are children `0 .. p-1`, all kept since they differ from `p`. -/
private theorem filter_ne_range_take (k p : Nat) (hp : p < k) :
    ((List.range k).filter (fun i => i != p)).take p = List.range p := by
  rw [filter_ne_range_eq_eraseIdx' k p hp,
    List.take_eraseIdx_eq_take_of_le (List.range k) p p (le_refl p),
    List.take_range, Nat.min_eq_left (le_of_lt hp)]

/-- **A sorted frontier's `< sl` tiles are exactly its `fIdx`-prefix.** With the
    slot `(sl, sh)` at index `fIdx`, every earlier tile ends at or before `sl`
    (strict monotonicity) and every later tile starts at or after `sl + k^sh`, so
    filtering on `· < sl` keeps precisely `take fIdx`. -/
private theorem Tiles_filter_lt_eq_take (k : Nat) (hk : 2 ≤ k)
    (coords : List (Nat × Nat)) (start stop fIdx sl sh : Nat)
    (htiles : Tiles k start coords stop) (hget : coords[fIdx]? = some (sl, sh)) :
    coords.filter (fun c => decide (c.1 < sl)) = coords.take fIdx := by
  have hflt : fIdx < coords.length := by
    rw [List.getElem?_eq_some_iff] at hget; obtain ⟨h, _⟩ := hget; exact h
  have hdecomp : coords = coords.take fIdx ++ (sl, sh) :: coords.drop (fIdx + 1) := by
    conv_lhs => rw [← List.take_append_drop fIdx coords, List.drop_eq_getElem_cons hflt]
    rw [List.getElem?_eq_getElem hflt] at hget
    rw [Option.some.injEq] at hget
    rw [hget]
  obtain ⟨mid, hpre, htileeq, hpost⟩ :=
    Tiles_split k (coords.take fIdx) (sl, sh) (coords.drop (fIdx + 1)) start stop
      (hdecomp ▸ htiles)
  simp only at htileeq
  subst htileeq
  conv_lhs => rw [hdecomp]
  rw [List.filter_append]
  have h1 : (coords.take fIdx).filter (fun c => decide (c.1 < sl)) = coords.take fIdx := by
    apply List.filter_eq_self.mpr
    intro c hc
    simp only [decide_eq_true_eq]
    have hb := Tiles_entry_bound k (coords.take fIdx) start sl hpre c hc
    have hpos : 0 < k ^ c.2 := pow_pos (by omega) _
    omega
  have h2 : ((sl, sh) :: coords.drop (fIdx + 1)).filter (fun c => decide (c.1 < sl)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro c hc
    simp only [decide_eq_true_eq, not_lt]
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc'
    · exact le_refl sl
    · have hge := Tiles_left_ge k (coords.drop (fIdx + 1)) (sl + k ^ sh) stop hpost c hc'
      have hpos : 0 < k ^ sh := pow_pos (by omega) _
      omega
  rw [h1, h2, List.append_nil]

/-- **Step 1 of the old-peak identity.** The climb's gathered left-siblings are
    the perfect roots of the climb's left-child coordinates: each level's
    `siblings.take position` keeps children `0 .. position-1`. -/
private theorem mergedLeftSibs_honest (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (sl off sh bh : Nat) :
    mergedLeftSibs ((honestDigitPath k cells sl off sh).drop bh)
      = (((List.range sh).drop bh).reverse.flatMap
          (fun j => (List.range (off / k ^ j % k)).map
            (fun i => (sl + (off / k ^ (j + 1) * k + i) * k ^ j, j)))).map
          (fun c => perfectRoot k cells c.1 c.2) := by
  unfold mergedLeftSibs honestDigitPath
  rw [← List.map_drop, ← List.map_reverse, List.flatMap_map]
  conv_rhs => rw [List.map_flatMap]
  congr 1
  funext j
  dsimp only
  rw [← List.map_take, filter_ne_range_take k (off / k ^ j % k) (Nat.mod_lt _ (by omega)),
    List.map_map]
  apply List.map_congr_left
  intro i _
  rfl

/-- **KEY: the honest old peaks rebuild the old frontier.** The reconstructed old
    peaks — the new peaks left of the boundary mountain, the merged-in
    left-siblings of the climb, and the boundary peak — are exactly the old
    frontier's perfect roots, in frontier order. This is the MMR increment-proof
    correctness identity.

    The proof reduces to a coordinate-list identity, then maps `perfectRoot`
    over both sides:
    `FN.take fIdx ++ climbLeftCoords ++ [(bl,bh)] = FO` (FN = new frontier,
    FO = old frontier). The new peaks left of the slot equal the old tiles `< sl`
    (`frontier_agree` + `Tiles_filter_lt_eq_take`); the climb's left-children plus
    the boundary equal the in-slot frontier `frontierGo k sl (oldSize - sl)` via a
    shift + iterated scale + single push (`(m+1)%k ≠ 0` since `bh` is the lowest
    nonzero digit), with `climb_coords_eq` aligning the climb digit recursion to
    `frontier_divstep`. `frontierGo_split` glues the prefix to the in-slot part. -/
private theorem honest_oldpeaks_eq (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length)
    (bl bh fIdx sl sh : Nat)
    (hlast : (frontierForSizeT k oldSize).getLast? = some (bl, bh))
    (hff : findFrontier k bl (frontierForSizeT k cells.length) 0 = some (fIdx, sl, sh)) :
    (honestNewPeaks k cells).take fIdx
        ++ mergedLeftSibs (honestPeakPath k cells oldSize)
        ++ [perfectRoot k cells bl bh]
      = (frontierForSizeT k oldSize).map (fun c => perfectRoot k cells c.1 c.2) := by
  obtain ⟨bl₀, bh₀, fIdx₀, sl₀, sh₀, hlast₀, hspan, hff₀, hff2, hbhsh, hsle, hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨hbl, hbh⟩ : bl = bl₀ ∧ bh = bh₀ := by
    have h := hlast.symm.trans hlast₀
    simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h
  subst hbl hbh
  obtain ⟨hfi, hsl, hsh⟩ : fIdx = fIdx₀ ∧ sl = sl₀ ∧ sh = sh₀ := by
    have h := hff.symm.trans hff₀
    simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1, h.2.1, h.2.2⟩
  subst hfi hsl hsh
  set off := oldSize - 1 - sl with hoffdef
  set m := off / k ^ bh with hmdef
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  -- slot membership and bounds
  obtain ⟨hgetN, hsleN, hbltN⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  simp only [Nat.sub_zero] at hgetN
  have hmemN : (sl, sh) ∈ frontierForSizeT k cells.length :=
    List.mem_of_getElem? (by simpa using hgetN)
  have hslalign : k ^ sh ∣ sl :=
    frontierGo_aligned k hk cells.length 0 (by simp) (sl, sh) hmemN
  obtain ⟨_hget2, hsle2, hblt2⟩ :=
    findFrontier_spec k (oldSize - 1) (frontierForSizeT k cells.length) 0 fIdx sl sh hff2
  have hoff_lt : off < k ^ sh := by rw [hoffdef]; omega
  -- climbLeftCoords abbreviation
  set CLC := (((List.range sh).drop bh).reverse.flatMap
    (fun j => (List.range (off / k ^ j % k)).map
      (fun i => (sl + (off / k ^ (j + 1) * k + i) * k ^ j, j)))) with hCLC
  -- (m+1) % k ≠ 0: bh is the lowest nonzero digit of oldSize
  have hbmemFO : (bl, bh) ∈ frontierForSizeT k oldSize := List.mem_of_getLast? hlast
  have hnotdvd : ¬ k ^ (bh + 1) ∣ oldSize := by
    intro hd
    have := frontierGo_min_height k hk (bh + 1) oldSize 0 hd (bl, bh) hbmemFO
    simp only at this; omega
  have hmk : (m + 1) % k ≠ 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]; simp [Nat.mod_eq_of_lt (show 1 < k by omega)]
    · have hshgt : bh < sh := by
        rcases Nat.lt_or_eq_of_le hbhsh with h | h
        · exact h
        · exfalso
          have hpoweq : k ^ sh = k ^ bh := by rw [h]
          have hge : k ^ bh ≤ m * k ^ bh := Nat.le_mul_of_pos_left (k ^ bh) (by omega)
          omega
      have hsldvd : k ^ (bh + 1) ∣ sl := dvd_trans (pow_dvd_pow k (by omega)) hslalign
      intro hzero
      have hkdvd : k ∣ (m + 1) := Nat.dvd_of_mod_eq_zero hzero
      apply hnotdvd
      have hos' : oldSize = sl + (m + 1) * k ^ bh := by
        have hexp : (m + 1) * k ^ bh = m * k ^ bh + k ^ bh := by ring
        omega
      rw [hos']
      apply Nat.dvd_add hsldvd
      rw [pow_succ]
      obtain ⟨c, hc⟩ := hkdvd
      exact ⟨c, by rw [hc]; ring⟩
  -- the coordinate identity D
  have hD : (frontierForSizeT k cells.length).take fIdx ++ CLC ++ [(bl, bh)]
      = frontierForSizeT k oldSize := by
    -- (2a): old tiles < sl equal the new fIdx-prefix
    have hagree : (frontierForSizeT k oldSize).filter (fun c => decide (c.1 < sl))
        = (frontierForSizeT k cells.length).filter (fun c => decide (c.1 < sl)) :=
      frontier_agree k hk cells.length 0 oldSize sl sh (by simp) hmemN (Nat.zero_le _)
        (by omega) (le_of_lt hnew)
    have hftake : (frontierForSizeT k cells.length).filter (fun c => decide (c.1 < sl))
        = (frontierForSizeT k cells.length).take fIdx :=
      Tiles_filter_lt_eq_take k hk (frontierForSizeT k cells.length) 0 cells.length fIdx sl sh
        (frontier_tiles k cells.length hk) hgetN
    have h2a : (frontierForSizeT k oldSize).filter (fun c => decide (c.1 < sl))
        = (frontierForSizeT k cells.length).take fIdx := by rw [hagree, hftake]
    -- Tiles-prefix: the new fIdx-prefix tiles [0, sl)
    have hflt : fIdx < (frontierForSizeT k cells.length).length := by
      rw [List.getElem?_eq_some_iff] at hgetN; obtain ⟨h, _⟩ := hgetN; exact h
    have hdecompN : frontierForSizeT k cells.length
        = (frontierForSizeT k cells.length).take fIdx
          ++ (sl, sh) :: (frontierForSizeT k cells.length).drop (fIdx + 1) := by
      conv_lhs =>
        rw [← List.take_append_drop fIdx (frontierForSizeT k cells.length),
          List.drop_eq_getElem_cons hflt]
      rw [List.getElem?_eq_getElem hflt, Option.some.injEq] at hgetN
      rw [hgetN]
    obtain ⟨mid, hpreN, htileeqN, _hpostN⟩ :=
      Tiles_split k ((frontierForSizeT k cells.length).take fIdx) (sl, sh)
        ((frontierForSizeT k cells.length).drop (fIdx + 1)) 0 cells.length
        (hdecompN ▸ frontier_tiles k cells.length hk)
    simp only at htileeqN
    subst htileeqN
    have hPtiles : Tiles k 0 ((frontierForSizeT k cells.length).take fIdx) sl := hpreN
    -- membership of (sl, _) in the old frontier
    have hsllt : sl < oldSize := by omega
    obtain ⟨fI', l', h', hffO⟩ :=
      findFrontier_cover k sl (frontierForSizeT k oldSize) 0 oldSize 0
        (frontier_tiles k oldSize hk) (Nat.zero_le _) hsllt
    obtain ⟨hgetO, hsleO, hbltO⟩ :=
      findFrontier_spec k sl (frontierForSizeT k oldSize) 0 fI' l' h' hffO
    simp only [Nat.sub_zero] at hgetO
    have hmemO : (l', h') ∈ frontierForSizeT k oldSize :=
      List.mem_of_getElem? (by simpa using hgetO)
    have hl'sl : l' = sl := by
      by_contra hne
      have hl'lt : l' < sl := lt_of_le_of_ne hsleO hne
      have hin : (l', h') ∈ (frontierForSizeT k oldSize).filter (fun c => decide (c.1 < sl)) := by
        rw [List.mem_filter]; exact ⟨hmemO, by simp only [decide_eq_true_eq]; exact hl'lt⟩
      rw [h2a] at hin
      have hb := Tiles_entry_bound k ((frontierForSizeT k cells.length).take fIdx) 0 sl hPtiles
        (l', h') hin
      simp only at hb
      have hpos : 0 < k ^ h' := pow_pos (by omega) _
      omega
    -- split the old frontier at sl
    have hsplit : frontierForSizeT k oldSize
        = (frontierForSizeT k oldSize).filter (fun c => decide (c.1 < sl))
          ++ frontierGo k sl (0 + oldSize - sl) :=
      frontierGo_split k hk sl oldSize 0 h' (hl'sl ▸ hmemO) (Nat.zero_le _)
    -- (i): the climb's left-children plus the boundary are the in-slot frontier
    have hclc : CLC = (frontierForSizeT k m).map (fun lh => (sl + lh.1 * k ^ bh, lh.2 + bh)) := by
      rw [hCLC, hmdef]
      exact climb_coords_eq k hk sl sh off hoff_lt bh hbhsh
    have hi : CLC ++ [(bl, bh)] = frontierGo k sl (oldSize - sl) := by
      rw [hclc]
      have hos : oldSize - sl = (m + 1) * k ^ bh := by
        have hexp : (m + 1) * k ^ bh = m * k ^ bh + k ^ bh := by ring
        omega
      rw [hos]
      have hshift : frontierGo k sl ((m + 1) * k ^ bh)
          = (frontierForSizeT k ((m + 1) * k ^ bh)).map (fun lh => (sl + lh.1, lh.2)) := by
        have h := frontierGo_shift k hk ((m + 1) * k ^ bh) sl 0
        simpa [frontierForSizeT] using h
      rw [hshift, frontier_scale_pow k hk bh (m + 1), frontierForSizeT_push k hk m hmk]
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
      congr 1
      rw [Nat.zero_add, halign]
    rw [hsplit, h2a, show 0 + oldSize - sl = oldSize - sl from by omega, ← hi,
      List.append_assoc]
  -- assemble: map perfectRoot over D
  have hHNP : (honestNewPeaks k cells).take fIdx
      = ((frontierForSizeT k cells.length).take fIdx).map (fun c => perfectRoot k cells c.1 c.2) := by
    rw [honestNewPeaks, ← List.map_take]
  have hMLS : mergedLeftSibs (honestPeakPath k cells oldSize)
      = CLC.map (fun c => perfectRoot k cells c.1 c.2) := by
    have hpp : honestPeakPath k cells oldSize = (honestDigitPath k cells sl off sh).drop bh := by
      simp only [honestPeakPath, hlast, hff, hoffdef]
    rw [hpp, hCLC]
    exact mergedLeftSibs_honest k hk cells sl off sh bh
  rw [hHNP, hMLS,
    show [perfectRoot k cells bl bh]
      = [(bl, bh)].map (fun c => perfectRoot k cells c.1 c.2) from rfl,
    ← List.map_append, ← List.map_append, hD]

/-- **The honest old-root read-back yields the genuine prefix root.** -/
private theorem honest_oldpeaks_bag (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length)
    (bl bh fIdx sl sh : Nat)
    (hlast : (frontierForSizeT k oldSize).getLast? = some (bl, bh))
    (hff : findFrontier k bl (frontierForSizeT k cells.length) 0 = some (fIdx, sl, sh)) :
    foldFrontierRoot k ((honestNewPeaks k cells).take fIdx
        ++ mergedLeftSibs (honestPeakPath k cells oldSize)
        ++ [perfectRoot k cells bl bh])
      = karyRoot k (cells.take oldSize) := by
  rw [honest_oldpeaks_eq k hk cells oldSize hold hnew bl bh fIdx sl sh hlast hff]
  rw [karyRoot, kary_bridge k hk (cells.take oldSize)]
  have hlen : (cells.take oldSize).length = oldSize := by rw [List.length_take]; omega
  rw [hlen]
  apply congrArg
  apply List.map_congr_left
  intro c hc
  have hbound : c.1 + k ^ c.2 ≤ oldSize :=
    Tiles_entry_bound k (frontierForSizeT k oldSize) 0 oldSize (frontier_tiles k oldSize hk) c hc
  have hstab := perfectRoot_stable k (cells.take oldSize) (cells.drop oldSize) c.2 c.1
    (by rw [hlen]; exact hbound)
  rw [List.take_append_drop] at hstab
  exact hstab.symm

/-! ## The theorems -/

/-- **Non-vacuity: honest consistency proofs verify.** -/
theorem consistency_completeness (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    AcceptsConsistency k oldSize cells.length
      (honestBoundaryHash k cells oldSize) (honestPeakPath k cells oldSize)
      (honestNewPeaks k cells) (honestSplitIndex k cells oldSize)
      (karyRoot k (cells.take oldSize)) (karyRoot k cells) := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨hgetN, _, _⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  simp only [Nat.sub_zero] at hgetN
  have hfIlt : fIdx < (frontierForSizeT k cells.length).length := by
    rw [List.getElem?_eq_some_iff] at hgetN; obtain ⟨h, _⟩ := hgetN; exact h
  have hsplit : honestSplitIndex k cells oldSize = fIdx := by
    simp only [honestSplitIndex, hlast, hff]
  have hbhash : honestBoundaryHash k cells oldSize = perfectRoot k cells bl bh := by
    simp only [honestBoundaryHash, hlast]
  have hnplen : (honestNewPeaks k cells).length = (frontierForSizeT k cells.length).length := by
    rw [honestNewPeaks, List.length_map]
  have hnewbag : foldFrontierRoot k (honestNewPeaks k cells) = karyRoot k cells := by
    rw [honestNewPeaks, ← kary_bridge k hk cells, karyRoot]
  refine ⟨hk, hold, hnew, honest_consistency_shape k hk cells oldSize hold hnew,
    honest_peakpath_wf k hk cells oldSize hold hnew,
    honest_climb_fold k hk cells oldSize hold hnew, ?_⟩
  -- reconstruct = some (karyRoot take, karyRoot cells)
  simp only [reconstructConsistencyRoots, hlast, hff]
  rw [if_pos ⟨hsplit, hbhsh, hnplen, by rw [hsplit, hnplen]; exact hfIlt⟩]
  rw [hsplit, hbhash, hnewbag,
    honest_oldpeaks_bag k hk cells oldSize hold hnew bl bh fIdx sl sh hlast hff]

/-- **Consistency-verifier soundness: accept ⇒ genuine append-only prefix.** -/
theorem consistency_soundness (k : Nat) (cells : List Digest)
    (oldSize : Nat) (boundaryHash oldRoot : Digest) (peakPath : List ProofStep)
    (newPeaks : List Digest) (splitIndex : Nat)
    (hacc : AcceptsConsistency k oldSize cells.length boundaryHash peakPath newPeaks splitIndex
      oldRoot (karyRoot k cells))
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    oldRoot = karyRoot k (cells.take oldSize) := by
  obtain ⟨hk, hold, holdnew, hstruct, hwf, hincl, hrec⟩ := hacc
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold holdnew
  obtain ⟨hgetN, _, _⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  simp only [Nat.sub_zero] at hgetN
  have hfIlt : fIdx < (frontierForSizeT k cells.length).length := by
    rw [List.getElem?_eq_some_iff] at hgetN; obtain ⟨h, _⟩ := hgetN; exact h
  -- unfold reconstruct: extract guards and root values
  simp only [reconstructConsistencyRoots, hlast, hff] at hrec
  split at hrec
  · next hcond =>
    obtain ⟨hsplitEq, _, hnplen, _⟩ := hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hrec
    obtain ⟨hoR, hnR⟩ := hrec
    -- pin newPeaks to the honest peaks via foldFrontierRoot injectivity
    have hnplen' : newPeaks.length = (honestNewPeaks k cells).length := by
      rw [honestNewPeaks, List.length_map, hnplen]
    have hnewbag : foldFrontierRoot k (honestNewPeaks k cells) = karyRoot k cells := by
      rw [honestNewPeaks, ← kary_bridge k hk cells, karyRoot]
    have hpeaks : newPeaks = honestNewPeaks k cells :=
      foldFrontierRoot_inj k hk hH hN newPeaks.length newPeaks (honestNewPeaks k cells)
        rfl hnplen'.symm (by rw [hnR, hnewbag])
    -- the slot peak value
    have hslotpeak : newPeaks.getD splitIndex emptyHash = perfectRoot k cells sl sh := by
      rw [hpeaks, hsplitEq, honestNewPeaks, List.getD_eq_getElem?_getD, List.getElem?_map, hgetN]
      rfl
    -- inclusion equation drives the climb uniqueness
    have hclimbfold := honest_climb_fold k hk cells oldSize hold holdnew
    have hsplitH : honestSplitIndex k cells oldSize = fIdx := by
      simp only [honestSplitIndex, hlast, hff]
    have hbhash : honestBoundaryHash k cells oldSize = perfectRoot k cells bl bh := by
      simp only [honestBoundaryHash, hlast]
    have hhpeak : (honestNewPeaks k cells).getD fIdx emptyHash = perfectRoot k cells sl sh := by
      rw [honestNewPeaks, List.getD_eq_getElem?_getD, List.getElem?_map, hgetN]; rfl
    rw [hsplitH, hbhash, hhpeak] at hclimbfold
    have hfeq : foldNary boundaryHash peakPath
        = foldNary (perfectRoot k cells bl bh) (honestPeakPath k cells oldSize) := by
      rw [hincl, hslotpeak]; exact hclimbfold.symm
    -- shapes agree (both equal the climb skeleton)
    obtain ⟨skel, hcsk, hpsh⟩ := hstruct
    obtain ⟨skel', hcsk', hpsh'⟩ := honest_consistency_shape k hk cells oldSize hold holdnew
    have hshapes : peakPath.map stepShape
        = (honestPeakPath k cells oldSize).map stepShape := by
      have hskeq : skel = skel' := Option.some.inj (hcsk.symm.trans hcsk')
      rw [hpsh, hskeq, ← hpsh']
    obtain ⟨hb_eq, hp_eq⟩ := foldNary_unique_of_shape boundaryHash (perfectRoot k cells bl bh)
      peakPath (honestPeakPath k cells oldSize) hshapes hwf
      (honest_peakpath_wf k hk cells oldSize hold holdnew) hfeq hH hN
    -- old peaks are now fully pinned to the honest ones
    rw [← hoR, hpeaks, hsplitEq, hp_eq, hb_eq,
      honest_oldpeaks_bag k hk cells oldSize hold holdnew bl bh fIdx sl sh hlast hff]
  · exact absurd hrec (by simp)

/-- **Dual soundness: accept between two honest roots ⇒ data-level append-only.** -/
theorem consistency_append_only (k : Nat) (oldCells newCells : List Digest)
    (boundaryHash : Digest) (peakPath : List ProofStep)
    (newPeaks : List Digest) (splitIndex : Nat)
    (hacc : AcceptsConsistency k oldCells.length newCells.length boundaryHash peakPath
      newPeaks splitIndex (karyRoot k oldCells) (karyRoot k newCells))
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    oldCells <+: newCells := by
  have hk : 2 ≤ k := hacc.1
  have hsize : oldCells.length < newCells.length := hacc.2.2.1
  have hsound := consistency_soundness k newCells oldCells.length boundaryHash
    (karyRoot k oldCells) peakPath newPeaks splitIndex hacc hH hN
  have hlen : oldCells.length = (newCells.take oldCells.length).length := by
    rw [List.length_take]; omega
  have heqcells := karyRoot_inj_of_length k hk oldCells (newCells.take oldCells.length)
    hlen hsound hH hN
  rw [heqcells]
  exact List.take_prefix oldCells.length newCells

/-- The append-only prefix the soundness conclusion is about. -/
theorem consistency_prefix_relation (cells : List Digest) (oldSize : Nat)
    (h : oldSize < cells.length) :
    (cells.take oldSize) <+: cells ∧ oldSize < cells.length :=
  ⟨List.take_prefix oldSize cells, h⟩

end NEML
