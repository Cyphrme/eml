import EMLProof.Kary

/-!
# K-ary consistency-verifier soundness (V9 follow-on d)

`Kary.lean` proved the **inclusion** verifier sound. This module does the same
for the **consistency** verifier — the property that makes the log
tamper-evident: an accepted consistency proof between two roots witnesses a
genuine append-only prefix relation between the two trees.

The Rust subject is `neml/src/proof.rs`:

* `verify_consistency` (`proof.rs:97`) =
  `reconstruct_consistency_roots(..).is_some_and(|(c_old, c_new)|
   c_old == old_root && c_new == new_root)` — the dual-root accept relation.
* `reconstruct_consistency_roots` (`proof.rs:593`) recomputes **both** the
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
(`proof.rs:842`).
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
        push_neg at h
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
        push_neg at h
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

/-! ## The coordinate→digest map of `reconstruct_consistency_roots` -/

/-- A coordinate `(left, height)` → digest map, as `reconstruct_consistency_roots`
    builds it (`proof.rs:652`, a `HashMap<(u64, u32), Vec<u8>>`). -/
abbrev CMap := (Nat × Nat) → Option Digest

/-- The empty map. -/
def cmEmpty : CMap := fun _ => none

/-- Functional `map.insert(coord, digest)` (last write wins). -/
def cmInsert (m : CMap) (c : Nat × Nat) (d : Digest) : CMap :=
  fun c' => if c' = c then some d else m c'

/-- Record one bisection step's siblings (`proof.rs:683-698`). The path node
    sits at `(curLeft, ch)`; its parent at `(curLeft - position·k^ch, ch+1)`.
    Sibling `j` (`0 ≤ j < k-1`) is the child at horizontal offset
    `j·k^ch` (left of the path node) or `(j+1)·k^ch` (right of it), recorded at
    its own coordinate, height `ch`. -/
noncomputable def recordBisectSibs (k : Nat) (m : CMap) (curLeft ch : Nat) (s : ProofStep) : CMap :=
  let cap := k ^ ch
  let parentLeft := curLeft - s.position * cap
  (List.range s.siblings.length).foldl
    (fun mm j =>
      let cLeft := if j < s.position then parentLeft + j * cap else parentLeft + j * cap + cap
      cmInsert mm (cLeft, ch) (s.siblings.getD j emptyHash)) m

/-- The bisection phase (`proof.rs:661-708`): trace `start_hash`'s coordinate up
    `bisection_steps` levels, recording each step's siblings. Tracks only the
    coordinate (`curLeft, ch`) — the running digest is recovered separately by
    `foldNary`; sibling *coordinates* need no digest state. -/
noncomputable def cmBisect (k : Nat) : List ProofStep → Nat → Nat → CMap → CMap
  | [], _, _, m => m
  | s :: rest, curLeft, ch, m =>
      cmBisect k rest (curLeft - s.position * k ^ ch) (ch + 1) (recordBisectSibs k m curLeft ch s)

/-- Record one merge step's siblings (`proof.rs:754-772` and `815-826`): a
    window `nodes` of frontier coordinates with the target at local index `pos`;
    the other `nodes.length - 1` entries are recorded from `s.siblings`
    (sibling index shifted past the target, mirroring
    `if j < step.position { j } else { j - 1 }`). -/
noncomputable def recordMergeSibs (m : CMap) (nodes : List (Nat × Nat)) (pos : Nat) (s : ProofStep) : CMap :=
  (List.range nodes.length).foldl
    (fun mm j =>
      if j = pos then mm
      else
        let sibIdx := if j < s.position then j else j - 1
        cmInsert mm (nodes.getD j (0, 0)) (s.siblings.getD sibIdx emptyHash)) m

/-- One coordinate-merge length step: `mergeTopCoords` strictly shrinks a list
    longer than `k` (for `k ≥ 2`). -/
theorem mergeTopCoords_length_lt (k : Nat) (coords : List (Nat × Nat))
    (hk : 2 ≤ k) (hlen : k < coords.length) :
    (mergeTopCoords k coords).length < coords.length := by
  unfold mergeTopCoords
  rw [if_neg (by omega)]
  cases hd : (coords.drop (coords.length - k)).head? with
  | none =>
      exfalso
      have : (coords.drop (coords.length - k)).length = k := by
        rw [List.length_drop]; omega
      rw [List.head?_eq_none_iff] at hd
      rw [hd] at this; simp at this; omega
  | some lh =>
      obtain ⟨l, h⟩ := lh
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
      omega

/-- The dynamic-merge phase (`proof.rs:710-836`): fold the new frontier by
    repeatedly merging the rightmost `k`, recording the siblings of every merge
    the target participates in (window merges consume a path step; coordinate
    merges that skip the target do not), then the final root merge. Records
    sibling coordinates into the map. -/
noncomputable def cmMergeGo (k : Nat) (frontier : List (Nat × Nat)) (targetIdx : Nat)
    (path : List ProofStep) (m : CMap) : CMap :=
    if h : k < 2 ∨ frontier.length ≤ k then
      if 1 < frontier.length then
        match path with
        | [] => m
        | s :: _ => recordMergeSibs m frontier targetIdx s
      else m
    else
      let split := frontier.length - k
      if targetIdx ≥ split then
        match path with
        | [] => m
        | s :: rest =>
            cmMergeGo k (mergeTopCoords k frontier) split rest
              (recordMergeSibs m (frontier.drop split) (targetIdx - split) s)
      else
        cmMergeGo k (mergeTopCoords k frontier) targetIdx path m
termination_by frontier.length
decreasing_by
  all_goals (push_neg at h; exact mergeTopCoords_length_lt k frontier (by omega) h.2)

/-- One-step unfolding of `cmMergeGo` (the generated equation, with `let`
    inlined), used to rewrite a single merge step. -/
private theorem cmMergeGo_unfold (k : Nat) (frontier : List (Nat × Nat)) (targetIdx : Nat)
    (path : List ProofStep) (m : CMap) :
    cmMergeGo k frontier targetIdx path m =
      if h : k < 2 ∨ frontier.length ≤ k then
        (if 1 < frontier.length then
          match path with
          | [] => m
          | s :: _ => recordMergeSibs m frontier targetIdx s
        else m)
      else
        (if targetIdx ≥ frontier.length - k then
          match path with
          | [] => m
          | s :: rest =>
              cmMergeGo k (mergeTopCoords k frontier) (frontier.length - k) rest
                (recordMergeSibs m (frontier.drop (frontier.length - k))
                  (targetIdx - (frontier.length - k)) s)
        else cmMergeGo k (mergeTopCoords k frontier) targetIdx path m) := by
  rw [cmMergeGo.eq_def]

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

/-- The full coordinate→digest map after a consistency reconstruction: the
    boundary coordinate seeded with `start_hash` (`proof.rs:654`), then the
    bisection and merge phases. -/
noncomputable def consistencyMap (k oldSize newSize : Nat) (startHash : Digest)
    (path : List ProofStep) : CMap :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => cmEmpty
  | some (bl, bh) =>
    match findFrontier k bl (frontierForSizeT k newSize) 0 with
    | none => cmEmpty
    | some (fIdx, _sl, sh) =>
        let bisSteps := sh - bh
        let m0 := cmInsert cmEmpty (bl, bh) startHash
        let m1 := cmBisect k (path.take bisSteps) bl bh m0
        cmMergeGo k (frontierForSizeT k newSize) fIdx (path.drop bisSteps) m1

/-! ## The verifier model -/

/-- The list of old-frontier digests read back from the map (`proof.rs:842-847`):
    `None` if any old-frontier coordinate is absent (the algorithm aborts). -/
noncomputable def consistencyOldHashes (k oldSize newSize : Nat) (startHash : Digest)
    (path : List ProofStep) : Option (List Digest) :=
  (frontierForSizeT k oldSize).mapM (consistencyMap k oldSize newSize startHash path)

/-- `reconstruct_consistency_roots` (`proof.rs:593`), modeled functionally:
    the old root is the `foldFrontierRoot` over the old frontier's digests read
    from the map (`proof.rs:849-867`); the new root is the running boundary
    digest folded through the whole path (`foldNary start_hash path`), which is
    exactly the merge phase's `computed_new_root` (`proof.rs:870`). Returns
    `none` exactly when the map read-back fails. -/
noncomputable def reconstructConsistencyRoots (L k oldSize newSize : Nat)
    (startHash : Digest) (path : List ProofStep) : Option (Digest × Digest) :=
  match consistencyOldHashes k oldSize newSize startHash path with
  | none => none
  | some hs => some (foldFrontierRoot L k hs, foldNary L startHash path)

/-- The consistency-proof skeleton pinned by `reconstruct_consistency_roots`'s
    structural guards: `sh - bh` bisection steps (each `k - 1` siblings, position
    the base-`k` digit of the boundary subtree's offset in its new slot,
    `proof.rs:667-675`) then the grouping steps from that slot to the spine root
    (`proof.rs:739-836`). The boundary subtree root is a pure log-topology node,
    so — unlike inclusion — there is **no** unconstrained within-subtree prefix:
    the whole path is shape-pinned. -/
def consistencySkeleton (k oldSize newSize : Nat) : Option (List (Nat × Nat)) :=
  if k < 2 then none
  else match (frontierForSizeT k oldSize).getLast? with
    | none => none
    | some (bl, bh) =>
      match findFrontier k bl (frontierForSizeT k newSize) 0 with
      | none => none
      | some (fIdx, sl, sh) =>
        if bh ≤ sh then
          some (digitSteps k ((bl - sl) / k ^ bh) (sh - bh) ++
            (groupingSteps k (frontierForSizeT k newSize).length fIdx).map
              (fun pc => (pc.1, pc.2 - 1)))
        else none

/-- `verify_consistency`'s structural acceptance (`proof.rs:647-840`): the path's
    per-step shape matches the consistency skeleton exactly (full match — no free
    prefix). The k-ary analog of `StructureOK`, minus the existential depth. -/
def StructureConsistencyOK (k oldSize newSize : Nat) (path : List ProofStep) : Prop :=
  ∃ skel, consistencySkeleton k oldSize newSize = some skel ∧ path.map stepShape = skel

/-- The accept relation of `verify_consistency`, minus DoS bounds: size guards,
    skeleton pinning, canonical well-formedness (zero-sibling steps rejected,
    insert position in range — `proof.rs:617-625,667-670`), and the dual-root
    match `reconstruct_consistency_roots(..) == some (oldRoot, newRoot)`
    (`proof.rs:107`). -/
def AcceptsConsistency (L k oldSize newSize : Nat) (startHash : Digest)
    (path : List ProofStep) (oldRoot newRoot : Digest) : Prop :=
  2 ≤ k ∧ 0 < oldSize ∧ oldSize < newSize ∧
  StructureConsistencyOK k oldSize newSize path ∧
  WellFormedSteps path ∧
  reconstructConsistencyRoots L k oldSize newSize startHash path = some (oldRoot, newRoot)

/-! ## The honest prover (non-vacuity witness) -/

/-- The honest `start_hash`: the genuine root of the boundary subtree — the
    rightmost (last) perfect subtree of the old frontier. -/
noncomputable def honestStartHash (L k : Nat) (cells : List Digest)
    (oldSize : Nat) : Digest :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => emptyHash
  | some (bl, bh) => perfectRoot L k cells bl bh

/-- The honest consistency path: the inclusion path of the last old leaf
    (`index = oldSize - 1`) in the current tree, taken from the boundary
    subtree's height upward (dropping the `bh` lower digit steps that fold the
    leaf up to the boundary subtree root — which `start_hash` already is). -/
noncomputable def honestConsistencyPath (L k : Nat) (cells : List Digest)
    (oldSize : Nat) : List ProofStep :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => []
  | some (_bl, bh) => (honestInclusionPath L k cells (oldSize - 1)).drop bh

/-! ## Honest new-root reconstruction -/

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

/-- **The honest consistency path reconstructs the genuine new root.**
    Folding the honest boundary-subtree root (`start_hash`) through the honest
    consistency path yields `karyRoot cells`. The path is the suffix, from the
    boundary height up, of the inclusion path of the last old leaf
    (`oldSize - 1`): `honest_path_folds` folds that leaf to the root, and the
    dropped lower `bh` digit steps fold the leaf up to the boundary subtree root
    (`digitFold`), which `start_hash` is. The boundary lands in a new-frontier
    slot of height `≥ bh` (`newslot_height_ge`), shared with `oldSize - 1`
    (`findFrontier_unique`), and the boundary's aligned position pins the
    `bh`-level ancestor of `oldSize - 1` to `bl`. -/
private theorem honest_consistency_newroot (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    foldNary L (honestStartHash L k cells oldSize) (honestConsistencyPath L k cells oldSize)
      = karyRoot L k cells := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, _hff, hff2, hbhsh, hsle, _hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  -- unfold the honest start hash and path
  simp only [honestStartHash, honestConsistencyPath, hlast]
  -- honest inclusion path through the shared slot
  have hincl : honestInclusionPath L k cells (oldSize - 1)
      = honestDigitPath L k cells sl (oldSize - 1 - sl) sh
        ++ honestGroupPath L k (buildStackCells L k cells) fIdx := by
    simp only [honestInclusionPath, hff2]
  set leaf := cells.getD (oldSize - 1) emptyHash with hleaf
  have hfull := honest_path_folds L k hk cells (oldSize - 1) (by omega)
  -- the dropped lower bh steps fold the leaf to the boundary subtree root
  have htakefold : foldNary L leaf
      ((honestInclusionPath L k cells (oldSize - 1)).take bh) = perfectRoot L k cells bl bh := by
    rw [hincl]
    have hdlen : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).length = sh := by
      rw [honestDigitPath, List.length_map, List.length_range]
    rw [List.take_append_of_le_length (by rw [hdlen]; exact hbhsh)]
    have htk : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).take bh
        = honestDigitPath L k cells sl (oldSize - 1 - sl) bh := by
      rw [honestDigitPath, honestDigitPath, ← List.map_take, List.take_range, Nat.min_eq_left hbhsh]
    rw [htk]
    have hdf := digitFold L k hk cells sl bh (oldSize - 1 - sl)
    rw [show sl + (oldSize - 1 - sl) = oldSize - 1 from by omega, halign] at hdf
    rw [hleaf]; exact hdf
  -- assemble via the take/drop split of the honest fold
  have hsplit : foldNary L leaf (honestInclusionPath L k cells (oldSize - 1))
      = foldNary L (foldNary L leaf ((honestInclusionPath L k cells (oldSize - 1)).take bh))
          ((honestInclusionPath L k cells (oldSize - 1)).drop bh) := by
    rw [foldNary, foldNary, foldNary, ← List.foldl_append, List.take_append_drop]
  rw [← hfull, hsplit, htakefold]

/-- **The honest consistency path has the pinned skeleton shape.** Its per-step
    shape equals `consistencySkeleton`. The honest path is the inclusion path of
    the last old leaf dropped to the boundary height; its shape is therefore the
    inclusion skeleton dropped by `bh`, whose bisection digit steps coincide with
    the consistency skeleton's (`digitSteps_drop` plus the agreeing digit offset)
    and whose grouping steps are identical. -/
private theorem honest_consistency_shape (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    StructureConsistencyOK k oldSize cells.length (honestConsistencyPath L k cells oldSize) := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, _halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨⟨skel, hskel, hmap⟩, _hwf⟩ := honest_path_shape L k hk cells (oldSize - 1) (by omega)
  set G := (groupingSteps k (frontierForSizeT k cells.length).length fIdx).map
    (fun pc => (pc.1, pc.2 - 1)) with hG
  have hsk : inclusionSkeleton k cells.length (oldSize - 1)
      = some (digitSteps k (oldSize - 1 - sl) sh ++ G) := by
    rw [inclusionSkeleton, if_neg (show ¬ k < 2 by omega)]
    simp only [hff2, hG]
  have hskelval : skel = digitSteps k (oldSize - 1 - sl) sh ++ G :=
    Option.some.inj (hskel.symm.trans hsk)
  have hcskel : consistencySkeleton k oldSize cells.length
      = some (digitSteps k ((bl - sl) / k ^ bh) (sh - bh) ++ G) := by
    rw [consistencySkeleton, if_neg (show ¬ k < 2 by omega)]
    simp only [hlast, hff, hbhsh, if_true, hG]
  have hdslen : (digitSteps k (oldSize - 1 - sl) sh).length = sh := by
    rw [digitSteps_eq_map, List.length_map, List.length_range]
  refine ⟨digitSteps k ((bl - sl) / k ^ bh) (sh - bh) ++ G, hcskel, ?_⟩
  simp only [honestConsistencyPath, hlast]
  rw [List.map_drop, hmap, hskelval,
    List.drop_append_of_le_length (by rw [hdslen]; exact hbhsh),
    digitSteps_drop k bh sh (oldSize - 1 - sl) hbhsh, hdiveq]

/-- `mapM` over the `Option` monad succeeds with the elementwise-mapped list when
    every element maps to `some (g c)`. The lift that turns the pointwise
    coordinate read-back into the whole-frontier read-back. -/
private theorem mapM_option_some {α β} (g : α → β) :
    ∀ (l : List α) (f : α → Option β), (∀ c ∈ l, f c = some (g c)) →
      l.mapM f = some (l.map g) := by
  intro l
  induction l with
  | nil => intro f _; rfl
  | cons x xs ih =>
    intro f h
    rw [List.mapM_cons, h x (List.mem_cons_self ..),
      ih f (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    rfl

/-- A `foldl` of map-updating steps that each leave coordinate `c` untouched
    leaves `c` untouched overall. The pointwise core under both
    `recordBisectSibs` and `recordMergeSibs` (folds of conditional `cmInsert`). -/
private theorem cmInsert_foldl_pointwise {β} (c : Nat × Nat) :
    ∀ (js : List β) (step : CMap → β → CMap) (m : CMap),
      (∀ j ∈ js, ∀ mm : CMap, step mm j c = mm c) →
      (js.foldl step m) c = m c := by
  intro js
  induction js with
  | nil => intro step m _; rfl
  | cons x xs ih =>
    intro step m h
    rw [List.foldl_cons, ih step (step m x) (fun j hj mm => h j (List.mem_cons_of_mem _ hj) mm),
      h x (List.mem_cons_self ..) m]

/-- Reading a `cmInsert` at a coordinate other than the inserted one is the old
    value. -/
private theorem cmInsert_ne (m : CMap) (key c : Nat × Nat) (d : Digest) (h : c ≠ key) :
    cmInsert m key d c = m c := by
  simp only [cmInsert, if_neg h]

/-- **Reading a uniquely-written key.** In a `foldl` of conditional `cmInsert`,
    if `x` is the only un-skipped element whose key equals `key x`, then reading
    `key x` afterward yields `val x` (no later step overwrites it). The dual of
    `cmInsert_foldl_pointwise`, used to extract a recorded sibling's value. -/
private theorem foldl_cmInsert_hits {β} (P : β → Prop) [DecidablePred P]
    (key : β → Nat × Nat) (val : β → Digest) (x : β) :
    ∀ (js : List β) (m : CMap),
      js.Nodup → x ∈ js → ¬ P x →
      (∀ y ∈ js, ¬ P y → key y = key x → y = x) →
      (js.foldl (fun mm z => if P z then mm else cmInsert mm (key z) (val z)) m) (key x)
        = some (val x) := by
  intro js
  induction js with
  | nil => intro m _ hx _ _; simp at hx
  | cons z zs ih =>
    intro m hnd hx hPx huniq
    rw [List.nodup_cons] at hnd
    obtain ⟨hznotin, hndzs⟩ := hnd
    rw [List.foldl_cons]
    by_cases hzx : z = x
    · subst hzx
      simp only [if_neg hPx]
      rw [cmInsert_foldl_pointwise (key z)]
      · simp [cmInsert]
      · intro y hy mm
        by_cases hPy : P y
        · simp only [if_pos hPy]
        · simp only [if_neg hPy]
          apply cmInsert_ne
          intro hkey
          exact hznotin (huniq y (List.mem_cons_of_mem _ hy) hPy hkey.symm ▸ hy)
    · have hxzs : x ∈ zs := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hzx
        · exact h
      refine ih (if P z then m else cmInsert m (key z) (val z)) hndzs hxzs hPx ?_
      intro y hy hPy hkey
      exact huniq y (List.mem_cons_of_mem _ hy) hPy hkey

/-- `recordMergeSibs` leaves `c` untouched when `c` differs from every recorded
    (non-target) window coordinate. -/
private theorem recordMergeSibs_avoids (m : CMap) (nodes : List (Nat × Nat))
    (pos : Nat) (s : ProofStep) (c : Nat × Nat)
    (h : ∀ j, j < nodes.length → j ≠ pos → c ≠ nodes.getD j (0, 0)) :
    recordMergeSibs m nodes pos s c = m c := by
  rw [recordMergeSibs]
  apply cmInsert_foldl_pointwise
  intro j hj mm
  rw [List.mem_range] at hj
  by_cases hjp : j = pos
  · simp only [if_pos hjp]
  · simp only [if_neg hjp]
    exact cmInsert_ne mm _ c _ (h j hj hjp)

/-- Skip-free variant of `foldl_cmInsert_hits` (every step inserts). -/
private theorem foldl_cmInsert_hits' {β} (key : β → Nat × Nat) (val : β → Digest) (x : β) :
    ∀ (js : List β) (m : CMap),
      js.Nodup → x ∈ js → (∀ y ∈ js, key y = key x → y = x) →
      (js.foldl (fun mm z => cmInsert mm (key z) (val z)) m) (key x) = some (val x) := by
  intro js m hnd hx huniq
  have := foldl_cmInsert_hits (fun _ : β => False) key val x js m hnd hx (by simp)
    (fun y hy _ hkey => huniq y hy hkey)
  simpa using this

/-- `recordBisectSibs` records each sibling at its child coordinate (height `ch`):
    reading the `j0`-th child's coordinate returns the `j0`-th recorded sibling. -/
private theorem recordBisectSibs_hits (k : Nat) (hk : 2 ≤ k) (m : CMap) (curLeft ch : Nat)
    (s : ProofStep) (j0 : Nat) (hj0 : j0 < s.siblings.length) :
    recordBisectSibs k m curLeft ch s
        ((if j0 < s.position then curLeft - s.position * k ^ ch + j0 * k ^ ch
          else curLeft - s.position * k ^ ch + j0 * k ^ ch + k ^ ch), ch)
      = some (s.siblings.getD j0 emptyHash) := by
  rw [recordBisectSibs]
  have hcap : 0 < k ^ ch := pow_pos (by omega) ch
  exact foldl_cmInsert_hits'
    (fun j => ((if j < s.position then curLeft - s.position * k ^ ch + j * k ^ ch
                else curLeft - s.position * k ^ ch + j * k ^ ch + k ^ ch), ch))
    (fun j => s.siblings.getD j emptyHash) j0 (List.range s.siblings.length) m
    List.nodup_range (List.mem_range.mpr hj0)
    (fun y _ hkey => by
      simp only [Prod.mk.injEq] at hkey
      have h1 := hkey.1
      have key1 : ∀ a : Nat,
          (if a < s.position then curLeft - s.position * k ^ ch + a * k ^ ch
            else curLeft - s.position * k ^ ch + a * k ^ ch + k ^ ch)
          = curLeft - s.position * k ^ ch + (if a < s.position then a else a + 1) * k ^ ch := by
        intro a
        by_cases ha : a < s.position
        · rw [if_pos ha, if_pos ha]
        · rw [if_neg ha, if_neg ha, add_mul, one_mul]; omega
      rw [key1, key1] at h1
      have h2 : (if y < s.position then y else y + 1) * k ^ ch
          = (if j0 < s.position then j0 else j0 + 1) * k ^ ch := by omega
      have h3 := Nat.eq_of_mul_eq_mul_right hcap h2
      rcases Nat.lt_or_ge y s.position with hy | hy <;>
        rcases Nat.lt_or_ge j0 s.position with hj | hj
      · rw [if_pos hy, if_pos hj] at h3; omega
      · rw [if_pos hy, if_neg (by omega)] at h3; omega
      · rw [if_neg (by omega), if_pos hj] at h3; omega
      · rw [if_neg (by omega), if_neg (by omega)] at h3; omega)

/-- `recordBisectSibs` only writes height-`ch` coordinates. -/
private theorem recordBisectSibs_preserves (k : Nat) (m : CMap) (curLeft ch : Nat)
    (s : ProofStep) (c : Nat × Nat) (h : c.2 ≠ ch) :
    recordBisectSibs k m curLeft ch s c = m c := by
  rw [recordBisectSibs]
  apply cmInsert_foldl_pointwise
  intro j _ mm
  apply cmInsert_ne
  intro hcq
  exact h (by rw [hcq])

/-- `recordBisectSibs` never overwrites the path node `(curLeft, ch)` itself:
    every recorded sibling sits at a different left coordinate. -/
private theorem recordBisectSibs_preserves_node (k : Nat) (hk : 2 ≤ k) (m : CMap)
    (curLeft ch : Nat) (s : ProofStep) (hpos : s.position * k ^ ch ≤ curLeft) :
    recordBisectSibs k m curLeft ch s (curLeft, ch) = m (curLeft, ch) := by
  rw [recordBisectSibs]
  apply cmInsert_foldl_pointwise
  intro j _ mm
  apply cmInsert_ne
  intro hcq
  rw [Prod.mk.injEq] at hcq
  obtain ⟨h1, _⟩ := hcq
  have hcap : 0 < k ^ ch := pow_pos (by omega) ch
  by_cases hjp : j < s.position
  · simp only [if_pos hjp] at h1
    have hlt : j * k ^ ch < s.position * k ^ ch := (Nat.mul_lt_mul_right hcap).mpr hjp
    omega
  · simp only [if_neg hjp] at h1
    have hge : s.position * k ^ ch ≤ j * k ^ ch := Nat.mul_le_mul_right (k ^ ch) (by omega)
    omega

/-- The bisection phase leaves coordinates below the current level untouched:
    each step records at its own (rising) level. -/
private theorem cmBisect_preserves_below (k : Nat) :
    ∀ (path : List ProofStep) (curLeft ch : Nat) (m : CMap) (c : Nat × Nat),
      c.2 < ch → cmBisect k path curLeft ch m c = m c := by
  intro path
  induction path with
  | nil => intro curLeft ch m c _; rfl
  | cons s rest ih =>
    intro curLeft ch m c h
    rw [cmBisect, ih _ (ch + 1) _ c (by omega),
      recordBisectSibs_preserves k m curLeft ch s c (by omega)]

/-- `recordMergeSibs` records the sibling digest at a window coordinate whose
    position is distinct from every other window coordinate. -/
private theorem recordMergeSibs_hits (m : CMap) (nodes : List (Nat × Nat)) (pos : Nat)
    (s : ProofStep) (j0 : Nat) (hj0 : j0 < nodes.length) (hjp : j0 ≠ pos)
    (hdist : ∀ j, j < nodes.length → nodes.getD j (0, 0) = nodes.getD j0 (0, 0) → j = j0) :
    recordMergeSibs m nodes pos s (nodes.getD j0 (0, 0))
      = some (s.siblings.getD (if j0 < s.position then j0 else j0 - 1) emptyHash) := by
  rw [recordMergeSibs]
  exact foldl_cmInsert_hits (fun j => j = pos) (fun j => nodes.getD j (0, 0))
    (fun j => s.siblings.getD (if j < s.position then j else j - 1) emptyHash) j0
    (List.range nodes.length) m List.nodup_range (List.mem_range.mpr hj0) hjp
    (fun y hy _ hkey => hdist y (List.mem_range.mp hy) hkey)

/-- **The merge phase never writes inside the target slot.** Every coordinate
    `cmMergeGo` records is a non-target window coordinate, whose left lies outside
    the half-open interval `[a, b)` as long as that holds for every non-target
    coordinate of the input list (an invariant preserved by the coordinate
    merge, since a merged node inherits its leftmost child's left). So any
    coordinate whose left is in `[a, b)` keeps its incoming value. -/
private theorem cmMergeGo_avoids (k a b : Nat) (hk : 2 ≤ k) :
    ∀ (n : Nat) (coords : List (Nat × Nat)) (tgt : Nat) (path : List ProofStep) (m : CMap),
      coords.length = n → tgt < coords.length →
      (∀ i, i < coords.length → i ≠ tgt →
        ¬ (a ≤ (coords.getD i (0, 0)).1 ∧ (coords.getD i (0, 0)).1 < b)) →
      ∀ c, a ≤ c.1 → c.1 < b → cmMergeGo k coords tgt path m c = m c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro coords tgt path m hn htgt hP2 c hca hcb
    have hcin : a ≤ c.1 ∧ c.1 < b := ⟨hca, hcb⟩
    -- c differs from every non-target coordinate of `coords`
    have hcne : ∀ i, i < coords.length → i ≠ tgt → c ≠ coords.getD i (0, 0) := by
      intro i hi hit heq
      exact hP2 i hi hit (by rw [← heq]; exact hcin)
    rw [cmMergeGo_unfold]
    by_cases hbase : k < 2 ∨ coords.length ≤ k
    · rw [dif_pos hbase]
      by_cases h1 : 1 < coords.length
      · rw [if_pos h1]
        cases path with
        | nil => rfl
        | cons s rest =>
            apply recordMergeSibs_avoids
            intro j hj hjt
            exact hcne j hj hjt
      · rw [if_neg h1]
    · rw [dif_neg hbase]
      push_neg at hbase
      obtain ⟨_, hgt⟩ := hbase
      -- the coordinate merge: drop the last `k`, append their parent
      have hmergedhead : mergeTopCoords k coords
          = coords.take (coords.length - k)
            ++ [((coords.getD (coords.length - k) (0, 0)).1,
                 (coords.getD (coords.length - k) (0, 0)).2 + 1)] := by
        rw [mergeTopCoords, if_neg (by omega)]
        have hhd : (coords.drop (coords.length - k)).head?
            = some (coords.getD (coords.length - k) (0, 0)) := by
          rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hhd]
      have hmlen : (mergeTopCoords k coords).length = coords.length - k + 1 := by
        rw [hmergedhead, List.length_append, List.length_take, List.length_cons,
          List.length_nil, Nat.min_eq_left (by omega)]
      have htakelen : (coords.take (coords.length - k)).length = coords.length - k := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      -- prefix coordinates unchanged
      have hmleft : ∀ i, i < coords.length - k →
          (mergeTopCoords k coords).getD i (0, 0) = coords.getD i (0, 0) := by
        intro i hi
        rw [hmergedhead, getD_append_lt _ _ _ _ (by rw [htakelen]; exact hi), getD_take_lt _ _ _ _ hi]
      -- merged coordinate inherits its leftmost child's left
      have hmlast : ((mergeTopCoords k coords).getD (coords.length - k) (0, 0)).1
          = (coords.getD (coords.length - k) (0, 0)).1 := by
        rw [hmergedhead, getD_append_ge _ _ _ _ (by rw [htakelen]),
          htakelen, Nat.sub_self, List.getD_cons_zero]
      by_cases hge : tgt ≥ coords.length - k
      · rw [if_pos hge]
        cases path with
        | nil => rfl
        | cons s rest =>
            have hrec : recordMergeSibs m (coords.drop (coords.length - k))
                (tgt - (coords.length - k)) s c = m c := by
              apply recordMergeSibs_avoids
              intro j hj hjt
              rw [List.length_drop] at hj
              have hidx : (coords.drop (coords.length - k)).getD j (0, 0)
                  = coords.getD ((coords.length - k) + j) (0, 0) := by
                rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
              rw [hidx]
              apply hcne ((coords.length - k) + j) (by omega)
              omega
            have hP2' : ∀ i, i < (mergeTopCoords k coords).length → i ≠ coords.length - k →
                ¬ (a ≤ ((mergeTopCoords k coords).getD i (0, 0)).1 ∧
                   ((mergeTopCoords k coords).getD i (0, 0)).1 < b) := by
              intro i hi hik
              rw [hmleft i (by rw [hmlen] at hi; omega)]
              exact hP2 i (by rw [hmlen] at hi; omega) (by omega)
            exact (ih (mergeTopCoords k coords).length (by omega) (mergeTopCoords k coords)
              (coords.length - k) rest (recordMergeSibs m (coords.drop (coords.length - k))
                (tgt - (coords.length - k)) s) rfl (by rw [hmlen]; omega) hP2' c hca hcb).trans hrec
      · rw [if_neg hge]
        have hP2' : ∀ i, i < (mergeTopCoords k coords).length → i ≠ tgt →
            ¬ (a ≤ ((mergeTopCoords k coords).getD i (0, 0)).1 ∧
               ((mergeTopCoords k coords).getD i (0, 0)).1 < b) := by
          intro i hi hit
          rw [hmlen] at hi
          by_cases hlt : i < coords.length - k
          · rw [hmleft i hlt]; exact hP2 i (by omega) hit
          · have hieq : i = coords.length - k := by omega
            rw [hieq, hmlast]; exact hP2 (coords.length - k) (by omega) (by omega)
        exact ih (mergeTopCoords k coords).length (by omega) (mergeTopCoords k coords)
          tgt path m rfl (by rw [hmlen]; omega) hP2' c hca hcb

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
      push_neg at h
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
              push_neg at hc
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
      push_neg at h
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
    rw [frontierGo, dif_neg (by push_neg; exact ⟨by omega, by omega⟩)] at hslot
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
        rw [frontierGo, dif_neg (by push_neg; exact ⟨by omega, by omega⟩)]
      have hfN : frontierGo k off newN
          = (off, L) :: frontierGo k (off + k ^ L) (newN - k ^ L) := by
        rw [frontierGo, dif_neg (by push_neg; exact ⟨by omega, by omega⟩)]
      rw [hfO, hfN, hlogold, List.filter_cons_of_pos (by simp [hofflt]),
        List.filter_cons_of_pos (by simp [hofflt])]
      congr 1
      have hdvd' : k ^ Nat.log k (newN - k ^ L) ∣ off + k ^ L :=
        Nat.dvd_add (dvd_trans (pow_dvd_pow k (Nat.log_mono_right (by omega))) halign)
          (pow_dvd_pow k (Nat.log_mono_right (by omega)))
      exact ih (newN - k ^ L) (by omega) (off + k ^ L) (oldN - k ^ L) sl sh hdvd' hmem
        (by omega) (by omega) (by omega)

/-- Reading a list below an erased index is unaffected. -/
private theorem getD_eraseIdx_lt {α} [Inhabited α] (l : List α) (d : α) (n i : Nat) (h : i < n) :
    (l.eraseIdx n).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx,
    if_pos h]

/-- **The merge phase records every slot left of the target.** Folding the honest
    grouping path of the digest stack `digests = coords.map perfectRoot` (on the
    target prefix) records, at every coordinate strictly left of the target slot,
    that slot's genuine perfect root. The target's lineage absorbs the left slots
    one window at a time, each pristine (never previously merged), so its recorded
    digest is still its original perfect root; later windows never overwrite it
    (coordinates are strictly left-ordered). -/
private theorem cmMergeGo_left_cover (L k : Nat) (hk : 2 ≤ k) (cells : List Digest) :
    ∀ (n : Nat) (coords : List (Nat × Nat)) (digests : List Digest) (tgt : Nat) (m : CMap),
      coords.length = n → digests.length = coords.length → tgt < coords.length →
      (∀ a b, a < coords.length → b < coords.length → a < b →
        (coords.getD a (0, 0)).1 < (coords.getD b (0, 0)).1) →
      (∀ i, i < tgt → digests.getD i emptyHash
        = perfectRoot L k cells (coords.getD i (0, 0)).1 (coords.getD i (0, 0)).2) →
      ∀ i, i < tgt →
        (cmMergeGo k coords tgt (honestGroupPath L k digests tgt) m) (coords.getD i (0, 0))
          = some (perfectRoot L k cells (coords.getD i (0, 0)).1 (coords.getD i (0, 0)).2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro coords digests tgt m hn hdl htgt hsorted hJ i hi
    have hlen2 : 1 < coords.length := by omega
    have hdistinct : ∀ a b, a < coords.length → b < coords.length →
        coords.getD a (0, 0) = coords.getD b (0, 0) → a = b := by
      intro a b ha hb heq
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact absurd (heq ▸ hsorted a b ha hb h) (lt_irrefl _)
      · exact h
      · exact absurd (heq ▸ hsorted b a hb ha h) (lt_irrefl _)
    rw [cmMergeGo_unfold]
    by_cases hbase : k < 2 ∨ coords.length ≤ k
    · rw [dif_pos hbase, if_pos hlen2]
      set step : ProofStep := { position := tgt, siblings := digests.eraseIdx tgt } with hstep_def
      have hgp : honestGroupPath L k digests tgt = [step] := by
        rw [honestGroupPath, dif_pos (by rw [hdl]; exact hbase), if_pos (by rw [hdl]; exact hlen2),
          hstep_def]
      rw [hgp]
      show recordMergeSibs m coords tgt step (coords.getD i (0, 0))
        = some (perfectRoot L k cells (coords.getD i (0, 0)).1 (coords.getD i (0, 0)).2)
      rw [recordMergeSibs_hits m coords tgt step i (by omega) (by omega)
        (fun j hj hjk => hdistinct j i hj (by omega) hjk), hstep_def]
      simp only [if_pos hi]
      rw [getD_eraseIdx_lt digests emptyHash tgt i hi, hJ i hi]
    · rw [dif_neg hbase]
      push_neg at hbase
      obtain ⟨_, hgt⟩ := hbase
      have hgtd : k < digests.length := by rw [hdl]; exact hgt
      -- coordinate-merge shape facts
      have htakelen : (coords.take (coords.length - k)).length = coords.length - k := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      have hmergedhead : mergeTopCoords k coords
          = coords.take (coords.length - k)
            ++ [((coords.getD (coords.length - k) (0, 0)).1,
                 (coords.getD (coords.length - k) (0, 0)).2 + 1)] := by
        rw [mergeTopCoords, if_neg (by omega)]
        have hhd : (coords.drop (coords.length - k)).head?
            = some (coords.getD (coords.length - k) (0, 0)) := by
          rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hhd]
      have hmlen : (mergeTopCoords k coords).length = coords.length - k + 1 := by
        rw [hmergedhead, List.length_append, List.length_take, List.length_cons,
          List.length_nil, Nat.min_eq_left (by omega)]
      have hcleft : ∀ j, j < coords.length - k →
          (mergeTopCoords k coords).getD j (0, 0) = coords.getD j (0, 0) := by
        intro j hj
        rw [hmergedhead, getD_append_lt _ _ _ _ (by rw [htakelen]; exact hj), getD_take_lt _ _ _ _ hj]
      have hclast : ((mergeTopCoords k coords).getD (coords.length - k) (0, 0)).1
          = (coords.getD (coords.length - k) (0, 0)).1 := by
        rw [hmergedhead, getD_append_ge _ _ _ _ (by rw [htakelen]),
          htakelen, Nat.sub_self, List.getD_cons_zero]
      have hdleft : ∀ j, j < coords.length - k →
          (mergeTopD L k digests).getD j emptyHash = digests.getD j emptyHash := by
        intro j hj
        rw [mergeTopD, if_neg (by omega), getD_append_lt _ _ _ _
          (by rw [List.length_take, Nat.min_eq_left (by omega)]; rw [hdl]; exact hj),
          getD_take_lt _ _ _ _ (by rw [hdl]; exact hj)]
      have hdll : (mergeTopD L k digests).length = (mergeTopCoords k coords).length := by
        rw [hmlen, mergeTopD, if_neg (by omega), List.length_append, List.length_take,
          List.length_cons, List.length_nil, Nat.min_eq_left (by omega), hdl]
      -- sorted is preserved
      have hsorted' : ∀ a b, a < (mergeTopCoords k coords).length →
          b < (mergeTopCoords k coords).length → a < b →
          ((mergeTopCoords k coords).getD a (0, 0)).1 < ((mergeTopCoords k coords).getD b (0, 0)).1 := by
        intro a b ha hb hab
        rw [hmlen] at ha hb
        by_cases hbs : b < coords.length - k
        · rw [hcleft a (by omega), hcleft b hbs]; exact hsorted a b (by omega) (by omega) hab
        · have hbe : b = coords.length - k := by omega
          rw [hcleft a (by omega), hbe, hclast]
          exact hsorted a (coords.length - k) (by omega) (by omega) (by omega)
      by_cases hge : tgt ≥ coords.length - k
      · rw [if_pos hge]
        set headStep : ProofStep :=
          { position := tgt - (coords.length - k),
            siblings := (digests.drop (coords.length - k)).eraseIdx (tgt - (coords.length - k)) }
          with hhead
        have hgp : honestGroupPath L k digests tgt
            = headStep :: honestGroupPath L k (mergeTopD L k digests) (coords.length - k) := by
          rw [honestGroupPath, dif_neg (by push_neg; exact ⟨by omega, by omega⟩),
            if_pos (by rw [hdl]; exact hge)]
          rw [hhead, hdl]
        rw [hgp]
        set m' := recordMergeSibs m (coords.drop (coords.length - k))
          (tgt - (coords.length - k)) headStep with hm'
        -- the recursion's invariants
        have hJ' : ∀ j, j < coords.length - k →
            (mergeTopD L k digests).getD j emptyHash
              = perfectRoot L k cells ((mergeTopCoords k coords).getD j (0, 0)).1
                  ((mergeTopCoords k coords).getD j (0, 0)).2 := by
          intro j hj
          rw [hdleft j hj, hcleft j hj]; exact hJ j (by omega)
        by_cases hisplit : i < coords.length - k
        · rw [← hcleft i hisplit]
          exact ih (mergeTopCoords k coords).length (by rw [hmlen]; omega) (mergeTopCoords k coords)
            (mergeTopD L k digests) (coords.length - k) m' rfl hdll (by rw [hmlen]; omega)
            hsorted' hJ' i hisplit
        · -- split ≤ i < tgt: coords[i] is recorded in m' and survives the recursion
          have hidx : coords.getD i (0, 0)
              = (coords.drop (coords.length - k)).getD (i - (coords.length - k)) (0, 0) := by
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
              show (coords.length - k) + (i - (coords.length - k)) = i from by omega]
          have hsurv : (cmMergeGo k (mergeTopCoords k coords) (coords.length - k)
              (honestGroupPath L k (mergeTopD L k digests) (coords.length - k)) m')
              (coords.getD i (0, 0))
              = m' (coords.getD i (0, 0)) := by
            apply cmMergeGo_avoids k (coords.getD i (0, 0)).1 ((coords.getD i (0, 0)).1 + 1) hk
              (mergeTopCoords k coords).length (mergeTopCoords k coords) (coords.length - k)
              _ m' rfl (by rw [hmlen]; omega) _ _ (by omega) (by omega)
            intro j hj hjk
            rw [hmlen] at hj
            rw [hcleft j (by omega)]
            rintro ⟨hle, _⟩
            have := hsorted j i (by omega) (by omega) (by omega)
            omega
          show cmMergeGo k (mergeTopCoords k coords) (coords.length - k)
              (honestGroupPath L k (mergeTopD L k digests) (coords.length - k)) m'
              (coords.getD i (0, 0))
            = some (perfectRoot L k cells (coords.getD i (0, 0)).1 (coords.getD i (0, 0)).2)
          have hdist : ∀ j, j < (coords.drop (coords.length - k)).length →
              (coords.drop (coords.length - k)).getD j (0, 0)
                = (coords.drop (coords.length - k)).getD (i - (coords.length - k)) (0, 0) →
              j = i - (coords.length - k) := by
            intro j hj hjk
            rw [List.length_drop] at hj
            have hg1 : (coords.drop (coords.length - k)).getD j (0, 0)
                = coords.getD ((coords.length - k) + j) (0, 0) := by
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
            have hg2 : (coords.drop (coords.length - k)).getD (i - (coords.length - k)) (0, 0)
                = coords.getD i (0, 0) := by
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
                show (coords.length - k) + (i - (coords.length - k)) = i from by omega]
            rw [hg1, hg2] at hjk
            have := hdistinct ((coords.length - k) + j) i (by omega) (by omega) hjk
            omega
          have hm'val : m' (coords.getD i (0, 0)) = some (digests.getD i emptyHash) := by
            rw [hm', hidx, recordMergeSibs_hits m (coords.drop (coords.length - k))
              (tgt - (coords.length - k)) headStep (i - (coords.length - k))
              (by rw [List.length_drop]; omega) (by omega) hdist, hhead]
            simp only [if_pos (show i - (coords.length - k) < tgt - (coords.length - k) from by omega)]
            rw [getD_eraseIdx_lt _ emptyHash _ _ (by omega)]
            congr 1
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
              show (coords.length - k) + (i - (coords.length - k)) = i from by omega]
          rw [hsurv, hm'val, hJ i hi]
      · rw [if_neg hge]
        have hgp : honestGroupPath L k digests tgt
            = honestGroupPath L k (mergeTopD L k digests) tgt := by
          rw [honestGroupPath, dif_neg (by push_neg; exact ⟨by omega, by omega⟩),
            if_neg (by rw [hdl]; exact hge)]
        rw [hgp, ← hcleft i (by omega)]
        have hJ' : ∀ j, j < tgt →
            (mergeTopD L k digests).getD j emptyHash
              = perfectRoot L k cells ((mergeTopCoords k coords).getD j (0, 0)).1
                  ((mergeTopCoords k coords).getD j (0, 0)).2 := by
          intro j hj
          rw [hdleft j (by omega), hcleft j (by omega)]; exact hJ j hj
        exact ih (mergeTopCoords k coords).length (by rw [hmlen]; omega) (mergeTopCoords k coords)
          (mergeTopD L k digests) tgt m rfl hdll (by rw [hmlen]; omega)
          hsorted' hJ' i hi

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
      simp [List.filter_cons, hb]
    · have hpeq : p = n := by omega
      subst hpeq
      have hf1 : (List.range p).filter (fun i => i != p) = List.range p := by
        apply List.filter_eq_self.mpr
        intro a ha; rw [List.mem_range] at ha; simp [bne_iff_ne]; omega
      rw [hf1, List.eraseIdx_append_of_length_le (by rw [List.length_range])]
      simp [List.filter_cons]

/-- The honest digit step's `i`-th sibling (for `i` below the path digit) is the
    genuine perfect root of the `i`-th child of the level block. -/
private theorem honest_digit_sibling (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (sl offset j i : Nat) (hi : i < offset / k ^ j % k) :
    (((List.range k).filter (fun x => x != offset / k ^ j % k)).map
       (fun x => perfectRoot L k cells (sl + (offset / k ^ (j + 1) * k + x) * k ^ j) j)).getD i emptyHash
      = perfectRoot L k cells (sl + (offset / k ^ (j + 1) * k + i) * k ^ j) j := by
  have hd : offset / k ^ j % k < k := Nat.mod_lt _ (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, filter_ne_range_eq_eraseIdx' k _ hd,
    List.getElem?_eraseIdx, if_pos hi, List.getElem?_range (by omega)]
  rfl

/-- **The bisection phase records every left sibling with its perfect root.**
    Starting from the boundary coordinate's ancestor at level `ch`, folding the
    honest digit steps records, at every coordinate that is a child to the left of
    the path node at some level `level ∈ [ch, sh)`, that child subtree's genuine
    perfect root. The recording happens at `level`; lower steps never reach it and
    higher steps record at higher levels, so it survives. -/
private theorem cmBisect_covers (L k : Nat) (hk : 2 ≤ k) (cells : List Digest) (sl offset sh : Nat) :
    ∀ (d ch curLeft : Nat) (m : CMap),
      ch + d = sh → curLeft = sl + offset / k ^ ch * k ^ ch →
      ∀ (level i : Nat), ch ≤ level → level < sh → i < offset / k ^ level % k →
        (cmBisect k ((honestDigitPath L k cells sl offset sh).drop ch) curLeft ch m)
            (sl + offset / k ^ (level + 1) * k ^ (level + 1) + i * k ^ level, level)
          = some (perfectRoot L k cells
              (sl + offset / k ^ (level + 1) * k ^ (level + 1) + i * k ^ level) level) := by
  intro d
  induction d with
  | zero => intro ch curLeft m hd _ level i hcl hlt _; omega
  | succ d ih =>
    intro ch curLeft m hd hcurLeft level i hcl hlt hi
    have hchlt : ch < sh := by omega
    have hcap : 0 < k ^ ch := pow_pos (by omega) ch
    have hdig : offset / k ^ ch % k < k := Nat.mod_lt _ (by omega)
    -- name the head step at level ch
    set s : ProofStep :=
      { position := offset / k ^ ch % k,
        siblings := ((List.range k).filter (fun x => x != offset / k ^ ch % k)).map
          fun x => perfectRoot L k cells (sl + (offset / k ^ (ch + 1) * k + x) * k ^ ch) ch }
      with hs
    have hstep : (honestDigitPath L k cells sl offset sh).drop ch
        = s :: (honestDigitPath L k cells sl offset sh).drop (ch + 1) := by
      rw [hs]
      unfold honestDigitPath
      rw [← List.map_drop, ← List.map_drop,
        List.drop_eq_getElem_cons (by rw [List.length_range]; exact hchlt), List.map_cons,
        List.getElem_range]
    have hspos : s.position = offset / k ^ ch % k := by rw [hs]
    rw [hstep, cmBisect]
    -- the recursion's new anchor is the level-(ch+1) ancestor
    have hnext : curLeft - s.position * k ^ ch = sl + offset / k ^ (ch + 1) * k ^ (ch + 1) := by
      rw [hspos, hcurLeft]
      have hpow : k ^ (ch + 1) = k ^ ch * k := pow_succ k ch
      have hdm : offset / k ^ ch = offset / k ^ (ch + 1) * k + offset / k ^ ch % k := by
        rw [show offset / k ^ (ch + 1) = offset / k ^ ch / k from by rw [hpow, Nat.div_div_eq_div_mul]]
        exact (Nat.div_add_mod' (offset / k ^ ch) k).symm
      have hACB : offset / k ^ ch * k ^ ch
          = offset / k ^ (ch + 1) * k ^ (ch + 1) + offset / k ^ ch % k * k ^ ch := by
        conv_lhs => rw [hdm]
        rw [add_mul, hpow]; ring
      omega
    rcases Nat.lt_or_ge ch level with hlvl | hlvl
    · -- target is at a higher level: this step misses it, recurse
      exact ih (ch + 1) _ _ (by omega) hnext level i (by omega) hlt hi
    · -- target is at this level: record it now, it survives the recursion
      have hleq : level = ch := by omega
      subst hleq
      rw [cmBisect_preserves_below k _ _ (level + 1) _ _ (by simp only []; omega)]
      have hslen : s.siblings.length = k - 1 := by
        rw [hs, List.length_map, filter_ne_range_eq_eraseIdx' k _ hdig,
          List.length_eraseIdx_of_lt (by rw [List.length_range]; exact hdig), List.length_range]
      have hhit := recordBisectSibs_hits k hk m curLeft level s i (by rw [hslen]; omega)
      rw [hspos, if_pos hi, hnext] at hhit
      rw [hhit]
      congr 1
      rw [hs, honest_digit_sibling L k hk cells sl offset level i hi]
      congr 1
      rw [pow_succ]; ring

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

/-- **Coordinate-coverage core.** For an honest consistency proof the verifier's
    coordinate map reads back, at every old-frontier coordinate, that subtree's
    genuine `perfectRoot`: the boundary is `start_hash = perfectRoot (bl, bh)`,
    the bisection siblings are the perfect roots flanking the boundary path
    inside its slot, and the merge siblings are the perfect roots of the
    new-frontier slots left of it — together exactly the old frontier. This is
    the remaining inductive obligation over `cmBisect` / `cmMergeGo`. -/
private theorem honest_oldroot_coverage (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    consistencyOldHashes k oldSize cells.length (honestStartHash L k cells oldSize)
        (honestConsistencyPath L k cells oldSize)
      = some ((frontierForSizeT k oldSize).map (fun c => perfectRoot L k cells c.1 c.2)) := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  -- the honest consistency path splits into the upper digit steps and the group path
  have hincl : honestInclusionPath L k cells (oldSize - 1)
      = honestDigitPath L k cells sl (oldSize - 1 - sl) sh
        ++ honestGroupPath L k (buildStackCells L k cells) fIdx := by
    simp only [honestInclusionPath, hff2]
  have hdlen : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).length = sh := by
    rw [honestDigitPath, List.length_map, List.length_range]
  set D := honestDigitPath L k cells sl (oldSize - 1 - sl) sh with hD
  set G := honestGroupPath L k (buildStackCells L k cells) fIdx with hG
  have hcpath : honestConsistencyPath L k cells oldSize = D.drop bh ++ G := by
    simp only [honestConsistencyPath, hlast]
    rw [hincl, List.drop_append_of_le_length (by rw [hdlen]; exact hbhsh)]
  have hD'len : (D.drop bh).length = sh - bh := by rw [List.length_drop, hdlen]
  rw [consistencyOldHashes]
  apply mapM_option_some
  intro c hc
  -- unfold the honest consistency map to its bisection/merge composition
  simp only [consistencyMap, honestStartHash, hlast, hff, hcpath]
  rw [List.take_left' hD'len, List.drop_left' hD'len]
  set m0 := cmInsert cmEmpty (bl, bh) (perfectRoot L k cells bl bh) with hm0
  set m1 := cmBisect k (D.drop bh) bl bh m0 with hm1
  set M := cmMergeGo k (frontierForSizeT k cells.length) fIdx G m1 with hM
  show M c = some (perfectRoot L k cells c.1 c.2)
  -- new-frontier slot data: membership, ordering, slot-interval avoidance
  obtain ⟨hgetN, hsleN, hbltN⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  simp only [Nat.sub_zero] at hgetN
  have htilesN := frontier_tiles k cells.length hk
  have hfIlt : fIdx < (frontierForSizeT k cells.length).length := by
    simpa using findFrontier_slot_lt k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  have hP2 : ∀ i, i < (frontierForSizeT k cells.length).length → i ≠ fIdx →
      ¬ (sl ≤ ((frontierForSizeT k cells.length).getD i (0, 0)).1 ∧
         ((frontierForSizeT k cells.length).getD i (0, 0)).1 < sl + k ^ sh) :=
    Tiles_slot_avoids k hk (frontierForSizeT k cells.length) 0 cells.length fIdx sl sh htilesN hgetN
  -- boundary is the last old tile: split it off
  obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  obtain ⟨mid, hTpre, hmideq, _⟩ :=
    Tiles_split k pre (bl, bh) [] 0 oldSize (hpre ▸ frontier_tiles k oldSize hk)
  simp only at hmideq; subst hmideq
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  rcases List.mem_append.mp (hpre ▸ hc) with hcpre | hcbnd
  · -- c is an interior old tile: c.1 + k^c.2 ≤ bl
    have hcb : c.1 + k ^ c.2 ≤ bl := Tiles_entry_bound k pre 0 bl hTpre c hcpre
    have hcpos : 0 < k ^ c.2 := pow_pos (by omega) c.2
    by_cases hcsl : c.1 < sl
    · -- left of the slot: supplied by the merge phase
      have hagree := frontier_agree k hk cells.length 0 oldSize sl sh (by simp)
        (List.mem_of_getElem? hgetN) (Nat.zero_le _) (by omega) (le_of_lt hnew)
      have hcfilt : c ∈ (frontierGo k 0 cells.length).filter (fun x => decide (x.1 < sl)) := by
        rw [← hagree, List.mem_filter]; exact ⟨hc, by simp [hcsl]⟩
      have hcmemN : c ∈ frontierForSizeT k cells.length := List.mem_of_mem_filter hcfilt
      obtain ⟨i, hilt, hieq⟩ := List.mem_iff_getElem.mp hcmemN
      have hidx : (frontierForSizeT k cells.length).getD i (0, 0) = c := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some, hieq]
      have hslval : ((frontierForSizeT k cells.length).getD fIdx (0, 0)).1 = sl := by
        rw [List.getD_eq_getElem?_getD, hgetN, Option.getD_some]
      have hilt' : i < fIdx := by
        by_contra hge
        push_neg at hge
        rcases Nat.lt_or_eq_of_le hge with hlt | heq
        · have hmono := Tiles_strict_mono k hk _ 0 cells.length htilesN fIdx i hlt hilt
          rw [hslval, hidx] at hmono
          omega
        · rw [heq, hidx] at hslval
          omega
      have hbridge := kary_bridge L k hk cells
      have hJ : ∀ i, i < fIdx → (buildStackCells L k cells).getD i emptyHash
          = perfectRoot L k cells ((frontierForSizeT k cells.length).getD i (0, 0)).1
              ((frontierForSizeT k cells.length).getD i (0, 0)).2 := by
        intro j hj
        have hjlt : j < (frontierForSizeT k cells.length).length := by omega
        rw [hbridge, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjlt,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt]
        rfl
      have hsortedN : ∀ a b, a < (frontierForSizeT k cells.length).length →
          b < (frontierForSizeT k cells.length).length → a < b →
          ((frontierForSizeT k cells.length).getD a (0, 0)).1
            < ((frontierForSizeT k cells.length).getD b (0, 0)).1 :=
        fun a b _ hb hab => Tiles_strict_mono k hk _ 0 cells.length htilesN a b hab hb
      have hcov := cmMergeGo_left_cover L k hk cells (frontierForSizeT k cells.length).length
        (frontierForSizeT k cells.length) (buildStackCells L k cells) fIdx m1 rfl
        (by rw [hbridge, List.length_map]) hfIlt hsortedN hJ i hilt'
      rw [hidx] at hcov
      have hlen' : (frontierForSizeT k cells.length).length = (buildStackCells L k cells).length := by
        rw [hbridge, List.length_map]
      rw [hM]
      rw [show G = honestGroupPath L k (buildStackCells L k cells) fIdx from hG] at *
      exact hcov
    · -- inside the slot, left of the boundary: supplied by the bisection phase
      push_neg at hcsl
      have hcbl : c.1 < bl := by omega
      have hchsh : c.2 < sh := by
        have : k ^ c.2 < k ^ sh := by
          calc k ^ c.2 ≤ bl - c.1 := by omega
            _ ≤ bl - sl := by omega
            _ < k ^ sh := by omega
        exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
      have hbhch : bh ≤ c.2 := by
        have hge : k ^ bh ≤ oldSize - c.1 := by omega
        have hsh := frontierGo_slot_height k hk oldSize 0 c.1 c.2 hc
        simp only [Nat.zero_add] at hsh
        rw [hsh]; exact Nat.le_log_of_pow_le (by omega) hge
      -- the merge phase preserves the slot interval, reducing to the bisection map
      have hMm1 : M c = m1 c := by
        rw [hM]
        exact cmMergeGo_avoids k sl (sl + k ^ sh) hk (frontierForSizeT k cells.length).length
          (frontierForSizeT k cells.length) fIdx G m1 rfl hfIlt hP2 c (by omega) (by omega)
      -- geometry: c is a left sibling of the path at level c.2
      have haligncl : k ^ c.2 ∣ c.1 := frontierGo_aligned k hk oldSize 0 (by simp) c hc
      have halignsl : k ^ (c.2 + 1) ∣ sl := by
        have : k ^ sh ∣ sl := frontierGo_aligned k hk cells.length 0 (by simp)
          (sl, sh) (List.mem_of_getElem? hgetN)
        exact dvd_trans (pow_dvd_pow k (by omega)) this
      have hblock := frontier_block k hk oldSize 0 (by simp)
        (by simp only [Nat.zero_mod, Nat.zero_add];
            exact le_of_lt (Nat.lt_pow_succ_log_self (by omega) oldSize))
        c.1 c.2 hc
      simp only [Nat.zero_add] at hblock
      -- normalise to (c.1 - sl) and offset = oldSize - 1 - sl
      set offset := oldSize - 1 - sl with hoff
      have hcsldvd : k ^ c.2 ∣ c.1 - sl :=
        Nat.dvd_sub haligncl (dvd_trans (pow_dvd_pow k (by omega))
          (frontierGo_aligned k hk cells.length 0 (by simp) (sl, sh) (List.mem_of_getElem? hgetN)))
      obtain ⟨q, hq⟩ := hcsldvd
      rw [Nat.mul_comm] at hq
      have hsldvd1 : k ^ (c.2 + 1) ∣ sl := halignsl
      obtain ⟨t, ht⟩ := hsldvd1
      -- block condition descended to (c.1 - sl)/k^(c.2+1) = offset/k^(c.2+1)
      have hp2 : k ^ (c.2 + 1) = k ^ c.2 * k := by rw [pow_succ]
      have hQ : (c.1 - sl) / k ^ (c.2 + 1) = offset / k ^ (c.2 + 1) := by
        have e1 : c.1 = k ^ (c.2 + 1) * t + (c.1 - sl) := by rw [← ht]; omega
        have e2 : oldSize - 1 = k ^ (c.2 + 1) * t + offset := by rw [← ht]; omega
        rw [e1, e2, Nat.mul_add_div (pow_pos (by omega) _), Nat.mul_add_div (pow_pos (by omega) _)]
          at hblock
        omega
      -- i := the child index; q = (offset/k^(c.2+1))*k + i
      have hqk : q / k = offset / k ^ (c.2 + 1) := by
        have hqd : (c.1 - sl) / k ^ (c.2 + 1) = q / k := by
          rw [hq, hp2, Nat.mul_comm q (k ^ c.2),
            Nat.mul_div_mul_left q k (pow_pos (by omega) c.2)]
        rw [← hqd]; exact hQ
      set i := q % k with hi
      have hqdecomp : q = offset / k ^ (c.2 + 1) * k + i := by
        rw [hi, ← hqk]; exact (Nat.div_add_mod' q k).symm
      have hc1form : c.1 = sl + offset / k ^ (c.2 + 1) * k ^ (c.2 + 1) + i * k ^ c.2 := by
        have : c.1 - sl = q * k ^ c.2 := hq
        rw [hqdecomp] at this
        have hexp : (offset / k ^ (c.2 + 1) * k + i) * k ^ c.2
            = offset / k ^ (c.2 + 1) * k ^ (c.2 + 1) + i * k ^ c.2 := by
          rw [hp2]; ring
        omega
      -- i is below the path digit at level c.2
      have hilt : i < offset / k ^ c.2 % k := by
        have hqlt : q < offset / k ^ c.2 := by
          have hq1 : (q + 1) * k ^ c.2 ≤ offset := by
            have hqq : c.1 - sl = q * k ^ c.2 := hq
            have hexp : (q + 1) * k ^ c.2 = q * k ^ c.2 + k ^ c.2 := by ring
            omega
          have := (Nat.le_div_iff_mul_le hcpos).mpr hq1
          omega
        have hoff_decomp : offset / k ^ c.2 = offset / k ^ (c.2 + 1) * k + offset / k ^ c.2 % k := by
          conv_lhs => rw [← Nat.div_add_mod' (offset / k ^ c.2) k]
          rw [show offset / k ^ c.2 / k = offset / k ^ (c.2 + 1) from by
            rw [hp2, Nat.div_div_eq_div_mul]]
        omega
      -- the bisection map records c with its perfect root
      rw [hMm1, hm1]
      have key := cmBisect_covers L k hk cells sl offset sh (sh - bh) bh bl m0
        (by omega) halign.symm c.2 i hbhch hchsh hilt
      rw [show c = (c.1, c.2) from rfl, hc1form]
      exact key
  · -- c is the boundary tile: read straight from the seed
    rw [List.mem_singleton] at hcbnd; subst hcbnd
    have hMm1 : M (bl, bh) = m1 (bl, bh) := by
      rw [hM]
      exact cmMergeGo_avoids k sl (sl + k ^ sh) hk (frontierForSizeT k cells.length).length
        (frontierForSizeT k cells.length) fIdx G m1 rfl hfIlt hP2 (bl, bh) (by exact hsle)
        (by exact hbltN)
    have hm1m0 : m1 (bl, bh) = m0 (bl, bh) := by
      rw [hm1, hD]
      cases hdb : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).drop bh with
      | nil => rfl
      | cons s rest =>
        rw [cmBisect, cmBisect_preserves_below k rest _ (bh + 1) _ (bl, bh) (by simp)]
        apply recordBisectSibs_preserves_node k hk m0 bl bh s
        -- s.position * k^bh ≤ bl
        have hshgt : bh < sh := by
          rcases Nat.lt_or_ge bh sh with h | h
          · exact h
          · exfalso; have hnil : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).drop bh = [] := by
              rw [List.drop_eq_nil_iff, hdlen]; omega
            rw [hnil] at hdb; simp at hdb
        have hd : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).drop bh
            = { position := (oldSize - 1 - sl) / k ^ bh % k,
                siblings := ((List.range k).filter (fun x => x != (oldSize - 1 - sl) / k ^ bh % k)).map
                  fun x => perfectRoot L k cells
                    (sl + ((oldSize - 1 - sl) / k ^ (bh + 1) * k + x) * k ^ bh) bh }
              :: (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).drop (bh + 1) := by
          unfold honestDigitPath
          rw [← List.map_drop, ← List.map_drop,
            List.drop_eq_getElem_cons (by rw [List.length_range]; exact hshgt),
            List.map_cons, List.getElem_range]
        rw [hd] at hdb
        injection hdb with hs_eq _
        have hspos : s.position = (oldSize - 1 - sl) / k ^ bh % k := by rw [← hs_eq]
        rw [hspos]
        calc (oldSize - 1 - sl) / k ^ bh % k * k ^ bh
            ≤ (oldSize - 1 - sl) / k ^ bh * k ^ bh := by
              exact Nat.mul_le_mul_right (k ^ bh) (Nat.mod_le _ _)
          _ = bl - sl := by omega
          _ ≤ bl := by omega
    rw [hMm1, hm1m0, hm0]
    simp [cmInsert]

/-- **The honest old-root read-back yields the genuine prefix root.** Folding
    the perfect roots the coordinate map records (`honest_oldroot_coverage`) with
    the frontier grouping gives `karyRoot` of the size-`oldSize` prefix: by
    `kary_bridge` on `cells.take oldSize`, that prefix's root is the same fold of
    the same perfect roots (`perfectRoot` only reads in-range cells, so taking
    the prefix does not change them). -/
private theorem honest_oldroot_readback (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    ∃ hs, consistencyOldHashes k oldSize cells.length (honestStartHash L k cells oldSize)
        (honestConsistencyPath L k cells oldSize) = some hs ∧
      foldFrontierRoot L k hs = karyRoot L k (cells.take oldSize) := by
  refine ⟨(frontierForSizeT k oldSize).map (fun c => perfectRoot L k cells c.1 c.2),
    honest_oldroot_coverage L k hk cells oldSize hold hnew, ?_⟩
  rw [karyRoot, kary_bridge L k hk (cells.take oldSize)]
  have hlen : (cells.take oldSize).length = oldSize := by rw [List.length_take]; omega
  rw [hlen]
  apply congrArg
  apply List.map_congr_left
  intro c hc
  have hbound : c.1 + k ^ c.2 ≤ oldSize :=
    Tiles_entry_bound k (frontierForSizeT k oldSize) 0 oldSize (frontier_tiles k oldSize hk) c hc
  have hstab := perfectRoot_stable L k (cells.take oldSize) (cells.drop oldSize) c.2 c.1
    (by rw [hlen]; exact hbound)
  rw [List.take_append_drop] at hstab
  exact hstab.symm

/-! ## The theorems -/

/-- **Non-vacuity: honest consistency proofs verify.** The honest boundary-root
    `start_hash` and honest path are accepted against the genuine current root
    `karyRoot cells`, reconstructing the genuine prefix root
    `karyRoot (cells.take oldSize)`. So `AcceptsConsistency` is satisfiable for
    every valid `(cells, oldSize)`, and the soundness theorem below quantifies
    over a provably non-empty accept set — mirroring how `kary_completeness`
    guards `kary_inclusion_soundness`.

    *Strategy:* `start_hash = perfectRoot (bl, bh)` is the digest the last old
    leaf reaches after `bh` digit steps (`digitFold`); the dropped honest path
    therefore folds it to `karyRoot cells` by `honest_path_folds` +
    `List.foldl` append decomposition. The shape matches `consistencySkeleton`
    (the dropped portion of `honest_path_shape`). The old-root read-back equals
    `karyRoot (cells.take oldSize)` because every old-frontier coordinate is
    recorded with its genuine `perfectRoot` and `foldFrontierRoot` over them is
    `karyRoot` of the prefix (`kary_bridge` on `cells.take oldSize`). -/
theorem consistency_completeness (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    AcceptsConsistency L k oldSize cells.length
      (honestStartHash L k cells oldSize) (honestConsistencyPath L k cells oldSize)
      (karyRoot L k (cells.take oldSize)) (karyRoot L k cells) := by
  refine ⟨hk, hold, hnew, honest_consistency_shape L k hk cells oldSize hold hnew, ?_, ?_⟩
  · -- WellFormedSteps: the honest consistency path is a suffix of the honest
    -- inclusion path, which is well-formed
    obtain ⟨_, hwf⟩ := honest_path_shape L k hk cells (oldSize - 1) (by omega)
    obtain ⟨bl, bh, _, _, _, hlast, _⟩ := boundary_slot k hk cells oldSize hold hnew
    intro s hs
    simp only [honestConsistencyPath, hlast] at hs
    exact hwf s (List.mem_of_mem_drop hs)
  · -- dual-root reconstruction
    obtain ⟨hs, hhs, hfold⟩ := honest_oldroot_readback L k hk cells oldSize hold hnew
    simp only [reconstructConsistencyRoots, hhs]
    rw [hfold, honest_consistency_newroot L k hk cells oldSize hold hnew]

/-- **Consistency-verifier soundness: accept ⇒ genuine append-only prefix.**
    If `verify_consistency` accepts `(start_hash, path, oldRoot)` against the
    honest current root `karyRoot cells` (`newSize = cells.length`), then the
    reconstructed `oldRoot` is forced to be the genuine root of the size-`oldSize`
    prefix `cells.take oldSize` — modulo `NodeHashCollision` / `CollapseAmbiguity`.

    This is the V9 tamper-evidence statement for the consistency verifier: there
    is no `(start_hash, path)` making the verifier accept a `oldRoot` that
    disagrees with the true history of the genuine current tree. Combined with
    `consistency_completeness` (the accept set is non-empty), the verifier
    accepts an `oldRoot` **iff** it is the true prefix root.

    *Strategy (completeness + uniqueness — no new induction):* the path
    shape-matches `consistencySkeleton`; so does the honest path
    (`consistency_completeness`'s shape obligation). Both fold `start_hash` /
    the honest boundary root to `karyRoot cells`. `foldNary_unique_of_shape`
    forces `start_hash` to the genuine boundary root and `path` to the honest
    path; the old-root read-back is then `karyRoot (cells.take oldSize)` by the
    completeness computation. -/
theorem consistency_soundness (L k : Nat) (cells : List Digest)
    (oldSize : Nat) (startHash oldRoot : Digest) (path : List ProofStep)
    (hacc : AcceptsConsistency L k oldSize cells.length startHash path oldRoot
      (karyRoot L k cells))
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) :
    oldRoot = karyRoot L k (cells.take oldSize) := by
  obtain ⟨hk, hold, holdnew, hstruct, hwf, hrec⟩ := hacc
  obtain ⟨skel, hcsk, hpsh⟩ := hstruct
  obtain ⟨skel', hcsk', hpsh'⟩ := honest_consistency_shape L k hk cells oldSize hold holdnew
  have hskeq : skel = skel' := Option.some.inj (hcsk.symm.trans hcsk')
  have hshapes : path.map stepShape
      = (honestConsistencyPath L k cells oldSize).map stepShape := by
    rw [hpsh, hskeq, ← hpsh']
  have hwf_honest : WellFormedSteps (honestConsistencyPath L k cells oldSize) := by
    obtain ⟨_, hwfI⟩ := honest_path_shape L k hk cells (oldSize - 1) (by omega)
    obtain ⟨bl, bh, _, _, _, hlast, _⟩ := boundary_slot k hk cells oldSize hold holdnew
    intro s hs
    simp only [honestConsistencyPath, hlast] at hs
    exact hwfI s (List.mem_of_mem_drop hs)
  have hnewfold := honest_consistency_newroot L k hk cells oldSize hold holdnew
  obtain ⟨hsh, hoph, hfoldh⟩ := honest_oldroot_readback L k hk cells oldSize hold holdnew
  unfold reconstructConsistencyRoots at hrec
  split at hrec
  · simp at hrec
  · next hsp hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hrec
    obtain ⟨hoR, hnR⟩ := hrec
    have hfeq : foldNary L startHash path
        = foldNary L (honestStartHash L k cells oldSize)
            (honestConsistencyPath L k cells oldSize) := by rw [hnR, hnewfold]
    obtain ⟨hstart, hpatheq⟩ := foldNary_unique_of_shape L startHash
      (honestStartHash L k cells oldSize) path (honestConsistencyPath L k cells oldSize)
      hshapes hwf hwf_honest hfeq hH hN
    rw [hstart, hpatheq, hoph] at hop
    have hsphs : hsp = hsh := (Option.some.inj hop).symm
    rw [← hoR, hsphs]
    exact hfoldh

/-! ### `karyRoot` injectivity (supports the dual append-only theorem) -/

/-- Every index in `[start, stop)` lands in some tile of a `Tiles`
    decomposition. -/
private theorem Tiles_covers (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat), Tiles k start coords stop →
      ∀ i, start ≤ i → i < stop → ∃ c ∈ coords, c.1 ≤ i ∧ i < c.1 + k ^ c.2 := by
  intro coords
  induction coords with
  | nil => intro start stop htiles i hs hi; simp only [Tiles] at htiles; omega
  | cons p rest ih =>
    intro start stop htiles i hs hi
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    by_cases hlt : i < start + k ^ ph
    · refine ⟨(pl, ph), ?_, ?_, ?_⟩
      · simp
      · show pl ≤ i; omega
      · show i < pl + k ^ ph; omega
    · obtain ⟨c, hc, h1, h2⟩ := ih (start + k ^ ph) stop htrest i (by omega) hi
      exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩

/-- **`perfectRoot` injectivity over a span.** Equal perfect-subtree roots over
    `xs` and `ys` force the two cell lists to agree at every index the subtree
    covers — or a hash assumption broke. Induction on height, `naryMr_inj_of_length`
    at each level. -/
private theorem perfectRoot_inj (L k : Nat) (hk : 2 ≤ k)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) (xs ys : List Digest) :
    ∀ (h left : Nat), perfectRoot L k xs left h = perfectRoot L k ys left h →
      ∀ i, i < k ^ h → xs.getD (left + i) emptyHash = ys.getD (left + i) emptyHash := by
  intro h
  induction h with
  | zero =>
    intro left heq i hi
    simp only [pow_zero, Nat.lt_one_iff] at hi
    subst hi
    simpa only [perfectRoot, Nat.add_zero] using heq
  | succ n ih =>
    intro left heq i hi
    have eL : perfectRoot L k xs left (n + 1)
        = naryMr L ((List.range k).map (fun j => perfectRoot L k xs (left + j * k ^ n) n)) := by
      rw [perfectRoot]
    have eR : perfectRoot L k ys left (n + 1)
        = naryMr L ((List.range k).map (fun j => perfectRoot L k ys (left + j * k ^ n) n)) := by
      rw [perfectRoot]
    rw [eL, eR] at heq
    have h2 : 2 ≤ ((List.range k).map
        (fun j => perfectRoot L k xs (left + j * k ^ n) n)).length := by simp; omega
    have hlen : ((List.range k).map (fun j => perfectRoot L k xs (left + j * k ^ n) n)).length
        = ((List.range k).map (fun j => perfectRoot L k ys (left + j * k ^ n) n)).length := by simp
    have hmapeq := naryMr_inj_of_length L _ _ hlen h2 heq hH hN
    -- per-child equality
    have hchild : ∀ j, j < k →
        perfectRoot L k xs (left + j * k ^ n) n = perfectRoot L k ys (left + j * k ^ n) n :=
      fun j hj => List.map_inj_left.mp hmapeq j (List.mem_range.mpr hj)
    -- decompose i = j*k^n + r
    have hkn : 0 < k ^ n := pow_pos (by omega) n
    have hj : i / k ^ n < k := by
      have hpow : k ^ (n + 1) = k ^ n * k := pow_succ k n
      rw [hpow] at hi
      exact Nat.div_lt_of_lt_mul hi
    have hr : i % k ^ n < k ^ n := Nat.mod_lt _ hkn
    have hdecomp : left + i = (left + (i / k ^ n) * k ^ n) + i % k ^ n := by
      have hdm := Nat.div_add_mod i (k ^ n)
      have hc : (i / k ^ n) * k ^ n = k ^ n * (i / k ^ n) := Nat.mul_comm _ _
      omega
    rw [hdecomp]
    exact ih (left + (i / k ^ n) * k ^ n) (hchild _ hj) (i % k ^ n) hr

/-- `naryMr` injectivity extended to **all** equal lengths (including the
    empty and singleton cases the length-≥2 version excludes): the empty/empty
    and singleton/singleton arms are promotion (no hashing). -/
private theorem naryMr_inj_eqlen (L : Nat) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : naryMr L xs = naryMr L ys)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) : xs = ys := by
  rcases xs with _ | ⟨a, xs'⟩
  · rcases ys with _ | ⟨c, ys'⟩
    · rfl
    · simp only [List.length_nil, List.length_cons] at hlen; omega
  · rcases ys with _ | ⟨c, ys'⟩
    · simp only [List.length_nil, List.length_cons] at hlen; omega
    · rcases xs' with _ | ⟨b, s⟩
      · rcases ys' with _ | ⟨d, t⟩
        · have e1 : naryMr L [a] = a := rfl
          have e2 : naryMr L [c] = c := rfl
          rw [e1, e2] at heq; rw [heq]
        · simp only [List.length_cons, List.length_nil] at hlen; omega
      · rcases ys' with _ | ⟨d, t⟩
        · simp only [List.length_cons, List.length_nil] at hlen; omega
        · exact naryMr_inj_of_length L _ _ hlen (by simp) heq hH hN

/-- **`foldFrontierRoot` injectivity over equal-length stacks.** Two stacks of
    equal length folding to the same spine root coincide — or a hash assumption
    broke. Strong induction on the (shared) length: the merge schedule is
    length-determined, so each `mergeTopD` step stays aligned and inverts via
    `naryMr_inj_of_length`. -/
private theorem foldFrontierRoot_inj (L k : Nat) (hk : 2 ≤ k)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) :
    ∀ (n : Nat) (xs ys : List Digest), xs.length = n → ys.length = n →
      foldFrontierRoot L k xs = foldFrontierRoot L k ys → xs = ys := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs ys hx hy heq
    by_cases hbase : xs.length ≤ k
    · have hbx : k < 2 ∨ xs.length ≤ k := Or.inr hbase
      have hby : k < 2 ∨ ys.length ≤ k := Or.inr (by omega)
      rw [foldFrontierRoot, dif_pos hbx] at heq
      conv_rhs at heq => rw [foldFrontierRoot, dif_pos hby]
      -- heq : naryMr L xs = naryMr L ys
      exact naryMr_inj_eqlen L xs ys (by omega) heq hH hN
    · push_neg at hbase
      have hbx : ¬(k < 2 ∨ xs.length ≤ k) := by push_neg; exact ⟨by omega, by omega⟩
      have hby : ¬(k < 2 ∨ ys.length ≤ k) := by push_neg; exact ⟨by omega, by omega⟩
      rw [foldFrontierRoot, dif_neg hbx] at heq
      conv_rhs at heq => rw [foldFrontierRoot, dif_neg hby]
      have hmx : (mergeTopD L k xs).length = n - k + 1 := by
        rw [mergeTopD, if_neg (by omega)]; simp only [List.length_append, List.length_take,
          List.length_cons, List.length_nil]; omega
      have hmy : (mergeTopD L k ys).length = n - k + 1 := by
        rw [mergeTopD, if_neg (by omega)]; simp only [List.length_append, List.length_take,
          List.length_cons, List.length_nil]; omega
      have hmerge := ih (n - k + 1) (by omega) (mergeTopD L k xs) (mergeTopD L k ys) hmx hmy heq
      -- mergeTopD xs = mergeTopD ys  ⇒  xs = ys
      rw [mergeTopD, if_neg (by omega), mergeTopD, if_neg (by omega)] at hmerge
      have hlenx : (xs.take (xs.length - k)).length = (ys.take (ys.length - k)).length := by
        simp only [List.length_take]; omega
      obtain ⟨htake, hsnoc⟩ := List.append_inj hmerge hlenx
      have hdrop2 : 2 ≤ (xs.drop (xs.length - k)).length := by
        simp only [List.length_drop]; omega
      have hdroplen : (xs.drop (xs.length - k)).length = (ys.drop (ys.length - k)).length := by
        simp only [List.length_drop]; omega
      have hnary : naryMr L (xs.drop (xs.length - k)) = naryMr L (ys.drop (ys.length - k)) := by
        have := List.cons.inj hsnoc; exact this.1
      have hdrop := naryMr_inj_of_length L _ _ hdroplen hdrop2 hnary hH hN
      calc xs = xs.take (xs.length - k) ++ xs.drop (xs.length - k) := (List.take_append_drop _ _).symm
        _ = ys.take (ys.length - k) ++ ys.drop (ys.length - k) := by rw [htake, hdrop]
        _ = ys := List.take_append_drop _ _

/-- **`karyRoot` injectivity over equal-length cell lists.** Two cell lists of
    the same length with equal k-ary root coincide — or a hash assumption broke.
    Equal length is essential: by the flat-null-promotion design, all-null lists
    of *different* lengths share a root (`naryRoot = nullDigest`), so injectivity
    can only hold once length is pinned (which the consistency proof's size
    fields do). The k-ary analog of `naryMr_inj_of_length` lifted from one node
    to the whole frontier fold.

    *Strategy:* induct on the frontier structure / `foldFrontierRoot`, applying
    `naryMr_inj_of_length` at each merge; the equal-length hypothesis keeps the
    two folds shape-aligned. -/
theorem karyRoot_inj_of_length (L k : Nat) (hk : 2 ≤ k) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : karyRoot L k xs = karyRoot L k ys)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) :
    xs = ys := by
  rw [karyRoot, karyRoot, kary_bridge L k hk xs, kary_bridge L k hk ys, ← hlen] at heq
  set F := frontierForSizeT k xs.length with hF
  have hstacklen : (F.map (fun lh => perfectRoot L k xs lh.1 lh.2)).length
      = (F.map (fun lh => perfectRoot L k ys lh.1 lh.2)).length := by simp
  have hmaps := foldFrontierRoot_inj L k hk hH hN _ _ _ rfl hstacklen.symm heq
  -- per-coordinate root equality
  have hcoord : ∀ c ∈ F, perfectRoot L k xs c.1 c.2 = perfectRoot L k ys c.1 c.2 :=
    fun c hc => List.map_inj_left.mp hmaps c hc
  -- index-wise equality via tiling
  have hcover := Tiles_covers k F 0 xs.length (frontier_tiles k xs.length hk)
  have hpt : ∀ i, i < xs.length → xs.getD i emptyHash = ys.getD i emptyHash := by
    intro i hi
    obtain ⟨c, hc, h1, h2⟩ := hcover i (by omega) hi
    have hpr := perfectRoot_inj L k hk hH hN xs ys c.2 c.1 (hcoord c hc) (i - c.1) (by omega)
    rwa [show c.1 + (i - c.1) = i from by omega] at hpr
  apply List.ext_getElem hlen
  intro i h1 h2
  have hp := hpt i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at hp
  exact hp

/-- **Dual soundness: accept between two honest roots ⇒ data-level append-only.**
    If `verify_consistency` accepts a proof between the honest root of `oldCells`
    and the honest root of `newCells`, then `oldCells` is a genuine prefix of
    `newCells` — the append-only relation at the cell-sequence level, modulo
    `NodeHashCollision` / `CollapseAmbiguity`.

    This is the dual of `consistency_soundness`: that theorem fixes the honest
    *new* tree and binds the reconstructed `oldRoot` to the prefix root; this one
    fixes the honest *old* tree as well and concludes that the accepted new tree
    genuinely *extends* it (`oldCells <+: newCells`). The two together are the
    complete tamper-evidence story — an accepted consistency proof between honest
    roots witnesses, at the data level, that the new log was formed by appending
    to the old one.

    The pure existential dual ("∃ extension whose root is `newRoot`") is *not*
    stated, because it is not faithfully recoverable: a consistency proof carries
    perfect-subtree *roots* for the appended range, never the individual new
    cells, so no leaf-level extension can be reconstructed from an arbitrary
    accepting proof. The two-honest-tree prefix relation is the faithful dual.

    *Strategy:* `consistency_soundness` (with `cells := newCells`) gives
    `karyRoot oldCells = karyRoot (newCells.take oldCells.length)`; both lists
    have length `oldCells.length`, so `karyRoot_inj_of_length` yields
    `oldCells = newCells.take oldCells.length`, i.e. `oldCells <+: newCells`. -/
theorem consistency_append_only (L k : Nat) (oldCells newCells : List Digest)
    (startHash : Digest) (path : List ProofStep)
    (hacc : AcceptsConsistency L k oldCells.length newCells.length startHash path
      (karyRoot L k oldCells) (karyRoot L k newCells))
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity L) :
    oldCells <+: newCells := by
  have hk : 2 ≤ k := hacc.1
  have hsize : oldCells.length < newCells.length := hacc.2.2.1
  have hsound := consistency_soundness L k newCells oldCells.length startHash
    (karyRoot L k oldCells) path hacc hH hN
  have hlen : oldCells.length = (newCells.take oldCells.length).length := by
    rw [List.length_take]; omega
  have heqcells := karyRoot_inj_of_length L k hk oldCells (newCells.take oldCells.length)
    hlen hsound hH hN
  rw [heqcells]
  exact List.take_prefix oldCells.length newCells

/-- The append-only prefix the soundness conclusion is about: `cells.take
    oldSize` is a genuine prefix of the current `cells`, with
    `oldSize < cells.length`. Definitional, recorded to make the prefix
    relation explicit at the statement surface. -/
theorem consistency_prefix_relation (cells : List Digest) (oldSize : Nat)
    (h : oldSize < cells.length) :
    (cells.take oldSize) <+: cells ∧ oldSize < cells.length :=
  ⟨List.take_prefix oldSize cells, h⟩

end NEML
