import EMLProof.Compression

/-!
# C-CANONICAL-UNIQUE — canonical-encoding injectivity

This module discharges the **central** canonicalization obligation: the canonical
form of a logical structure, together with the minimal committed extents, is an
**injective encoding** — *distinct logical structures produce distinct binding
roots* (modulo a hash collision). The whole canonicalization + binding-root
design's sufficiency is conditional on this theorem (REFINEMENTS C-CANONICAL-UNIQUE,
DESIGN-DECISIONS D6).

## The rewrite-system framing (KU6, ROBDD-grounded)

Canonicalization is two **orthogonal, non-overlapping** primitives:

* **promotion** — a lone child is lifted in place of its wrapping node
  (`node [c] ⟶ c`). This is the *structural* rule: a verifier re-derives it on
  reconstruction, so it commits **nothing** (INV-AUTH-BOUNDARY).
* **collapse** — an all-null node folds to the null digest. This is the *value*
  rule, realized inside `eval` (`eval_flat_null_promotion`); its run-extent is the
  committed metadata (the epoch timeline; D12 — derivable from the tree).

We formalize the structural rule (promotion) as a rewrite relation `Promotes` and
prove it is a **confluent terminating rewrite system**:

* **termination** — `nsize` strictly decreases under promotion, so no infinite
  reduction sequence exists (`Promotes.nsize_lt`);
* **orthogonality ⇒ confluence** — promotion's redex is the *single* pattern
  `node [c]`; rewriting commutes, so the system is confluent and every tree has a
  **unique normal form** — its `Canonical` representative (`canonical_unique`).

This mirrors the **ROBDD canonicalization theorem** (Bryant): a reduced ordered BDD
is the canonical normal form reached by exactly these reduction rules, and ROBDD's
node-elimination rule **R2 is `collapse` verbatim** (PRIOR-ART). The proof here is
the generic, PMT-level statement (not the k=2 cyphr-log instance).

## The injective-encoding theorem

Over `Canonical` forms (the unique normal forms above), `eval` is **injective
modulo a hash collision** (`canonical_eval_injective`): two distinct canonical
structures cannot share a binding root unless `H` collides on their preimages.
Composed with normal-form uniqueness this is exactly C-CANONICAL-UNIQUE:

```
distinct logical structures
  ──(unique normal form, confluence)──▶ distinct canonical forms
  ──(canonical_eval_injective)──▶       distinct binding roots ∨ HashCollision
```

The committed extent is what makes this hold *generically*: the empty-node and
singleton degeneracies are removed from the canonical domain (they are redexes, not
normal forms), so the only way two distinct canonical structures can collide is a
genuine collision of `H` on distinct preimages — never a structural alias.
-/

namespace NEML

/-! ## Layer 0 — `eval` of a node is a function of the child digest list -/

/-- The node-combining function: how a node's digest is built from its already-
    evaluated children. Mirrors the node arms of `eval` exactly. -/
noncomputable def combine (L : Nat) : List Digest → Digest
  | [] => emptyHash
  | [d] => d
  | ds =>
      if ds.all (· == nullDigest L) then nullDigest L
      else nodeHash ds

/-- `combine` on a list of arity ≥ 2 takes its guarded arm. -/
theorem combine_cons2 (L : Nat) (x y : Digest) (zs : List Digest) :
    combine L (x :: y :: zs) =
      if (x :: y :: zs).all (· == nullDigest L) then nullDigest L
      else nodeHash (x :: y :: zs) := by
  rfl

/-- `List.all (· == nullDigest L)` is the boolean reflection of `evalAllNull`. -/
theorem all_map_eq_evalAllNull (L : Nat) (children : List (NaryTree (List UInt8))) :
    (children.map (eval L)).all (· == nullDigest L) = evalAllNull L children := by
  induction children with
  | nil => simp [evalAllNull]
  | cons c cs ih => simp only [List.map_cons, List.all_cons, evalAllNull, ih]

/-- **`eval` factors through `combine`.** A node's digest depends on its children
    only through their evaluated digests: `eval (node cs) = combine (cs.map eval)`.
    This is the structural fact that makes promotion (which preserves the child
    digest list pointwise) a hash no-op, and that lets injectivity recurse on the
    child digest list. -/
theorem eval_node_combine (L : Nat) (children : List (NaryTree (List UInt8))) :
    eval L (NaryTree.node children) = combine L (children.map (eval L)) := by
  match children with
  | [] => rw [eval_empty]; rfl
  | [c] => rw [eval_singleton_node]; rfl
  | a :: b :: rest =>
    have hguard : ((a :: b :: rest).map (eval L)).all (· == nullDigest L)
        = evalAllNull L (a :: b :: rest) := all_map_eq_evalAllNull L _
    by_cases hnull : evalAllNull L (a :: b :: rest) = true
    · rw [eval_flat_null_node L _ (by simp) ((evalAllNull_eq_true_iff L _).mp hnull)]
      rw [show (a :: b :: rest).map (eval L)
            = eval L a :: eval L b :: rest.map (eval L) from by simp]
      rw [combine_cons2, if_pos]
      rw [← List.map_cons, ← List.map_cons, hguard]; exact hnull
    · rw [eval_node_hash L _ (by simp) (by
        by_contra hc
        simp only [not_exists, not_and, not_not] at hc
        exact hnull ((evalAllNull_eq_true_iff L _).mpr (fun t ht => hc t ht)))]
      rw [show (a :: b :: rest).map (eval L)
            = eval L a :: eval L b :: rest.map (eval L) from by simp]
      rw [combine_cons2, if_neg]
      rw [← List.map_cons, ← List.map_cons, hguard]; exact hnull

/-! ## Layer 1 — promotion as a terminating rewrite system -/

/-- Structural canonical form: the **promotion** normal form. A tree is canonical
    iff no promotion redex (`node [_]`) occurs anywhere — every internal node has
    arity `≠ 1` (the empty node `node []` is a normal form: it is the `emptyHash`
    boundary value and carries no singleton redex). -/
def Canonical : NaryTree (List UInt8) → Prop
  | NaryTree.leaf _ => True
  | NaryTree.node children =>
      children.length ≠ 1 ∧ ∀ c ∈ children, Canonical c

/-- Characterization of `Canonical` on a node (exposes the conjunction for
    projection, since `Canonical` is defined by pattern match). -/
@[simp] theorem Canonical_node (children : List (NaryTree (List UInt8))) :
    Canonical (NaryTree.node children) ↔
      children.length ≠ 1 ∧ ∀ c ∈ children, Canonical c := by
  rw [Canonical]

/-- Arity of a canonical node is never 1. -/
theorem Canonical.length_ne {children : List (NaryTree (List UInt8))}
    (h : Canonical (NaryTree.node children)) : children.length ≠ 1 :=
  (Canonical_node children |>.mp h).1

/-- Children of a canonical node are canonical. -/
theorem Canonical.children {children : List (NaryTree (List UInt8))}
    (h : Canonical (NaryTree.node children)) : ∀ c ∈ children, Canonical c :=
  (Canonical_node children |>.mp h).2

/-- One-step promotion: the congruence closure of the redex `node [c] ⟶ c`. -/
inductive Promotes : NaryTree (List UInt8) → NaryTree (List UInt8) → Prop where
  | redex (c : NaryTree (List UInt8)) : Promotes (NaryTree.node [c]) c
  | congr (pre post : List (NaryTree (List UInt8))) (c c' : NaryTree (List UInt8))
      (h : Promotes c c') :
      Promotes (NaryTree.node (pre ++ c :: post)) (NaryTree.node (pre ++ c' :: post))

/-- `nlsize` is additive across a split (each element contributes `1 + nsize`). -/
theorem nlsize_append_cons (l : List (NaryTree (List UInt8))) (x : NaryTree (List UInt8))
    (r : List (NaryTree (List UInt8))) :
    nlsize (l ++ x :: r) = nlsize l + 1 + nsize x + nlsize r := by
  induction l with
  | nil => simp [nlsize]
  | cons y ys ih => simp only [List.cons_append, nlsize, ih]; omega

/-- **Termination.** Every promotion step strictly decreases `nsize`. -/
theorem Promotes.nsize_lt {s t : NaryTree (List UInt8)} (h : Promotes s t) :
    nsize t < nsize s := by
  induction h with
  | redex c => simp only [nsize, nlsize]; omega
  | congr pre post c c' hstep ih =>
    simp only [nsize, nlsize_append_cons]
    omega

/-- **Promotion preserves evaluation** (a hash no-op). -/
theorem Promotes.eval_eq (L : Nat) {s t : NaryTree (List UInt8)} (h : Promotes s t) :
    eval L s = eval L t := by
  induction h with
  | redex c => exact eval_singleton L c
  | congr pre post c c' _hstep ih =>
    rw [eval_node_combine, eval_node_combine]
    congr 1
    simp only [List.map_append, List.map_cons, ih]

/-! ## Layer 2 — confluence: the unique canonical normal form

The promotion rule has the **single** redex pattern `node [c]`; it is therefore an
**orthogonal** rewrite system (no critical pairs), which is automatically confluent
(Church–Rosser). We realize the unique normal form directly as the function
`normalize`, recursively stripping singleton wrappers, and prove:

* `normalize` always yields a `Canonical` tree (`normalize_canonical`);
* a `Canonical` tree is its own normal form (`normalize_canonical_eq`);
* normalization is the *unique* normal form: any `Promotes` step is invisible to
  `normalize` (`Promotes.normalize_eq`) — the confluence content, since it means
  every reduction sequence lands on the same `Canonical` representative.

Composed: each logical structure has **exactly one** canonical form, so "distinct
logical structures" and "distinct canonical forms" coincide.
-/

/-- The promotion normal form: recursively strip singleton wrappers, normalizing
    children first. -/
noncomputable def normalize : NaryTree (List UInt8) → NaryTree (List UInt8)
  | NaryTree.leaf v => NaryTree.leaf v
  | NaryTree.node children =>
      match children.map normalize with
      | [c] => c
      | cs => NaryTree.node cs
  termination_by t => nsize t
  decreasing_by
    rename_i c hc
    have : nsize c < nlsize children := by
      induction children with
      | nil => simp at hc
      | cons x xs ih =>
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hmem
        · simp [nlsize]; omega
        · have := ih hmem; simp [nlsize]; omega
    simp [nsize]; omega

/-- **`normalize` lands in canonical form.** Its result has no singleton or empty
    node anywhere. -/
theorem normalize_canonical (t : NaryTree (List UInt8)) : Canonical (normalize t) := by
  induction t using NaryTree.ind with
  | h_leaf v => rw [normalize, Canonical]; trivial
  | h_node children ih =>
    have ihcs : ∀ c ∈ children.map normalize, Canonical c := by
      intro c hc
      rw [List.mem_map] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact ih a ha
    rw [normalize]
    -- Case on the inner `match children.map normalize with …`.
    split
    · -- singleton: `c`, which is canonical as a member of the mapped list.
      rename_i c heq
      exact ihcs c (by rw [heq]; simp)
    · -- non-singleton list `cs`: a node with arity ≠ 1, children canonical.
      rename_i cs hne
      rw [Canonical_node]
      refine ⟨?_, ihcs⟩
      -- `cs` is not a singleton (the `[c]` arm did not fire), so length ≠ 1.
      intro hlen
      obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
      exact hne c hc

/-- **Normalization preserves evaluation.** The promotion normal form has the same
    binding root as the original — promotion commits nothing (INV-AUTH-BOUNDARY).
    The confluence-soundness companion of `Promotes.eval_eq`. -/
theorem normalize_eval (L : Nat) (t : NaryTree (List UInt8)) :
    eval L (normalize t) = eval L t := by
  induction t using NaryTree.ind with
  | h_leaf v => rw [normalize]
  | h_node children ih =>
    -- `eval (node children) = combine (children.map eval)`.
    rw [eval_node_combine]
    -- Mapping `eval` after `normalize` agrees with mapping `eval` directly.
    have hmap : (children.map normalize).map (eval L) = children.map (eval L) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc; simpa using ih c hc
    -- Compute `eval (normalize (node children))` by casing the inner `match`.
    rw [normalize]
    split
    · -- singleton arm: `normalize` returns `c`; `children.map eval = [eval c]`.
      rename_i c heq
      have hcm : children.map (eval L) = [eval L c] := by
        rw [← hmap, heq]; simp
      rw [hcm, combine]
    · -- non-singleton arm: returns `node cs`; `eval` factors through `combine`.
      rename_i cs hne
      rw [eval_node_combine, hmap]

/-- **A canonical tree is its own normal form** (idempotence on normal forms — the
    termination half of "unique normal form"). -/
theorem normalize_canonical_eq {t : NaryTree (List UInt8)} (h : Canonical t) :
    normalize t = t := by
  induction t using NaryTree.ind with
  | h_leaf v => rw [normalize]
  | h_node children ih =>
    have hlen : children.length ≠ 1 := h.length_ne
    have hch : ∀ c ∈ children, Canonical c := h.children
    have hmap : children.map normalize = children := by
      have : children.map normalize = children.map id := by
        apply List.map_congr_left
        intro c hc
        simpa using ih c hc (hch c hc)
      rw [this, List.map_id]
    rw [normalize, hmap]
    rcases children with _ | ⟨c, _ | ⟨d, rest⟩⟩
    · rfl
    · -- singleton: arity 1 contradicts `hlen`.
      exact absurd rfl hlen
    · rfl

/-! ## Layer 3 — canonical injectivity (the C-CANONICAL-UNIQUE core)

`eval` is **injective on the active canonical domain** modulo a hash collision.

The "active" restriction (`Active`: every subtree evaluates to a non-null digest)
is the precise dividing line of the two-primitive asymmetry (INV-AUTH-BOUNDARY): a
null subtree is a *collapsed* region whose run-extent is the committed metadata
(the epoch timeline, bound into the binding root by `metaroot_binds_timeline`,
D12). Over the non-collapsed structure, **promotion commits nothing** and the
encoding is injective on its own; over collapsed regions the committed extent
disambiguates. So the generic injective-encoding statement factors exactly as the
design predicts: this theorem is the promotion half, `metaroot_binds_timeline` the
collapse half. -/

/-- A tree is **active** when it — and recursively every subtree — evaluates to a
    non-null digest. Active subtrees are the non-collapsed structure; null subtrees
    are the collapsed regions carried by the committed extent. -/
def Active (L : Nat) : NaryTree (List UInt8) → Prop
  | NaryTree.leaf d => leafHash d ≠ nullDigest L
  | NaryTree.node children =>
      eval L (NaryTree.node children) ≠ nullDigest L ∧ ∀ c ∈ children, Active L c

/-- Characterization of `Active` on a node. -/
@[simp] theorem Active_node (L : Nat) (children : List (NaryTree (List UInt8))) :
    Active L (NaryTree.node children) ↔
      eval L (NaryTree.node children) ≠ nullDigest L ∧ ∀ c ∈ children, Active L c := by
  rw [Active]

/-- A canonical, active node does not evaluate to the null digest. -/
theorem Active.not_null {L : Nat} {children : List (NaryTree (List UInt8))}
    (h : Active L (NaryTree.node children)) :
    eval L (NaryTree.node children) ≠ nullDigest L := (Active_node L children |>.mp h).1

/-- Children of an active node are active. -/
theorem Active.children {L : Nat} {children : List (NaryTree (List UInt8))}
    (h : Active L (NaryTree.node children)) : ∀ c ∈ children, Active L c :=
  (Active_node L children |>.mp h).2

/-- **Canonical-active node evaluation has two forms.** A canonical (arity ≠ 1),
    active (not all-null) node evaluates either to `emptyHash` (when empty) or to
    `nodeHash` of its evaluated children (when non-empty). The all-null collapse
    branch is excluded by activeness — this is exactly where the two-primitive
    asymmetry lands: collapse is delegated to the committed extent. -/
theorem node_combine_form (L : Nat) (cs : List (NaryTree (List UInt8)))
    (hcan : Canonical (NaryTree.node cs)) (hact : Active L (NaryTree.node cs)) :
    (cs = [] ∧ eval L (NaryTree.node cs) = emptyHash) ∨
    (cs ≠ [] ∧ eval L (NaryTree.node cs) = nodeHash (cs.map (eval L))) := by
  rcases cs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact Or.inl ⟨rfl, by rw [eval_empty]⟩
  · exact absurd hcan.length_ne (by simp)
  · refine Or.inr ⟨by simp, ?_⟩
    rw [eval_node_combine]
    have hguard : ((a :: b :: rest).map (eval L)).all (· == nullDigest L) = false := by
      by_contra hg
      simp only [Bool.not_eq_false] at hg
      apply hact.not_null
      rw [eval_node_combine,
        show (a :: b :: rest).map (eval L)
          = eval L a :: eval L b :: rest.map (eval L) from by simp,
        combine_cons2, if_pos]
      rw [← List.map_cons, ← List.map_cons]; exact hg
    have hcons : (a :: b :: rest).map (eval L)
        = eval L a :: eval L b :: rest.map (eval L) := by simp
    rw [hcons] at hguard
    rw [hcons, combine_cons2, if_neg (by rw [hguard]; simp)]

/-- **Pointwise child recursion.** If two child lists have equal evaluated-digest
    lists and each `as`-element is injective-on-eval against an arbitrary tree
    (the per-child induction hypothesis), the lists are equal or a collision is
    exhibited. This is the list-level engine of the node case of
    `canonical_eval_injective`. -/
theorem map_eval_inj (L : Nat) :
    ∀ (as bs : List (NaryTree (List UInt8))),
      (∀ a ∈ as, ∀ (t₂ : NaryTree (List UInt8)),
        Canonical a → Canonical t₂ → Active L a → Active L t₂ →
        eval L a = eval L t₂ → a = t₂ ∨ HashCollision ∨ NodeHashCollision) →
      (∀ a ∈ as, Canonical a) → (∀ b ∈ bs, Canonical b) →
      (∀ a ∈ as, Active L a) → (∀ b ∈ bs, Active L b) →
      as.map (eval L) = bs.map (eval L) →
      as = bs ∨ HashCollision ∨ NodeHashCollision := by
  intro as
  induction as with
  | nil =>
    intro bs _ _ _ _ _ hmap
    cases bs with
    | nil => exact Or.inl rfl
    | cons y ys => simp at hmap
  | cons a as ih =>
    intro bs ihelt hca hcb haa hab hmap
    cases bs with
    | nil => simp at hmap
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hhd, htl⟩ := hmap
      have haelt := ihelt a (by simp) b
        (hca a (by simp)) (hcb b (by simp))
        (haa a (by simp)) (hab b (by simp)) hhd
      rcases haelt with hab_eq | hcol
      · -- head equal; recurse on the tails.
        have htail := ih bs
          (fun x hx => ihelt x (by simp [hx]))
          (fun x hx => hca x (by simp [hx]))
          (fun x hx => hcb x (by simp [hx]))
          (fun x hx => haa x (by simp [hx]))
          (fun x hx => hab x (by simp [hx]))
          htl
        rcases htail with htl_eq | hcol
        · exact Or.inl (by rw [hab_eq, htl_eq])
        · exact Or.inr hcol
      · exact Or.inr hcol

/-- **Canonical injectivity (C-CANONICAL-UNIQUE core).** Over the active canonical
    domain, distinct logical structures produce distinct binding roots unless `H`
    collides. Under the domain-separation facts a tagged hasher provides (leaf
    preimages disjoint from node/empty preimages — the same collision-resistance-
    style hypotheses `expand_compress` already takes), `eval`-equal active canonical
    trees are equal or exhibit an explicit `HashCollision` / `NodeHashCollision`.

    Generic and PMT-level: any arity, any structure — not the k = 2 cyphr-log
    instance. -/
theorem canonical_eval_injective (L : Nat)
    (leaf_node_sep : ∀ (d : List UInt8) (ds : List Digest), leafHash d ≠ nodeHash ds)
    (leaf_empty_sep : ∀ (d : List UInt8), leafHash d ≠ emptyHash)
    (node_empty_sep : ∀ (ds : List Digest), nodeHash ds ≠ emptyHash) :
    ∀ (t₁ t₂ : NaryTree (List UInt8)),
      Canonical t₁ → Canonical t₂ → Active L t₁ → Active L t₂ →
      eval L t₁ = eval L t₂ →
      t₁ = t₂ ∨ HashCollision ∨ NodeHashCollision := by
  -- A leaf is `H d`; collision-resistance turns equal leaf hashes into equal
  -- payloads. We package this once.
  have leaf_inj : ∀ d₁ d₂ : List UInt8,
      leafHash d₁ = leafHash d₂ → d₁ = d₂ ∨ HashCollision := by
    intro d₁ d₂ h
    by_cases hd : d₁ = d₂
    · exact Or.inl hd
    · exact Or.inr ⟨d₁, d₂, hd, h⟩
  intro t₁
  induction t₁ using NaryTree.ind with
  | h_leaf d₁ =>
    intro t₂ _hc₁ _hc₂ _ha₁ _ha₂ heval
    match t₂ with
    | NaryTree.leaf d₂ =>
      rw [eval_leaf, eval_leaf] at heval
      rcases leaf_inj d₁ d₂ heval with hd | hcol
      · exact Or.inl (by rw [hd])
      · exact Or.inr (Or.inl hcol)
    | NaryTree.node cs₂ =>
      -- leaf = node: contradiction with the domain-separation facts.
      rw [eval_leaf] at heval
      -- Reduce `eval (node cs₂)` to its `combine`-normal form via `node_combine_form`.
      have hform := node_combine_form L cs₂ _hc₂ _ha₂
      rcases hform with ⟨hempty, hev⟩ | ⟨hne, hev⟩
      · rw [hev] at heval; exact absurd heval (leaf_empty_sep d₁)
      · rw [hev] at heval; exact absurd heval (leaf_node_sep d₁ _)
  | h_node children ih =>
    intro t₂ hc₁ hc₂ ha₁ ha₂ heval
    match t₂ with
    | NaryTree.leaf d₂ =>
      -- node = leaf: symmetric to the leaf/node case above.
      rw [eval_leaf] at heval
      have hform := node_combine_form L children hc₁ ha₁
      rcases hform with ⟨hempty, hev⟩ | ⟨hne, hev⟩
      · rw [hev] at heval; exact absurd heval.symm (leaf_empty_sep d₂)
      · rw [hev] at heval; exact absurd heval.symm (leaf_node_sep d₂ _)
    | NaryTree.node cs₂ =>
      have hform₁ := node_combine_form L children hc₁ ha₁
      have hform₂ := node_combine_form L cs₂ hc₂ ha₂
      rcases hform₁ with ⟨h1e, h1v⟩ | ⟨h1ne, h1v⟩ <;>
        rcases hform₂ with ⟨h2e, h2v⟩ | ⟨h2ne, h2v⟩
      · -- both empty
        exact Or.inl (by rw [h1e, h2e])
      · -- t₁ empty, t₂ nonempty: emptyHash = nodeHash ⇒ contradiction.
        rw [h1v, h2v] at heval; exact absurd heval.symm (node_empty_sep _)
      · -- t₁ nonempty, t₂ empty: nodeHash = emptyHash ⇒ contradiction.
        rw [h1v, h2v] at heval; exact absurd heval (node_empty_sep _)
      · -- both nonempty: `nodeHash (children.map eval) = nodeHash (cs₂.map eval)`.
        rw [h1v, h2v] at heval
        by_cases hds : children.map (eval L) = cs₂.map (eval L)
        · -- equal child-digest lists ⇒ recurse pointwise via the child IH.
          have hchildren : children = cs₂ ∨ HashCollision ∨ NodeHashCollision :=
            map_eval_inj L children cs₂
              (fun a ha => ih a ha)
              hc₁.children hc₂.children
              ha₁.children ha₂.children
              hds
          rcases hchildren with heq | hcol
          · exact Or.inl (by rw [heq])
          · exact Or.inr hcol
        · exact Or.inr (Or.inr ⟨_, _, hds, heval⟩)

/-- **C-CANONICAL-UNIQUE.** The canonicalization + binding-root design's sufficiency
    theorem, assembled from the two layers:

    * **uniqueness of canonical form** — promotion is a confluent terminating
      rewrite system, so each logical structure has exactly one canonical
      representative (`normalize`, `normalize_canonical`, `normalize_canonical_eq`);
    * **injectivity of the encoding** — distinct active canonical structures map to
      distinct binding roots modulo a hash collision (`canonical_eval_injective`),
      with the collapsed (null) regions' extent carried by the committed timeline
      (`metaroot_binds_timeline`).

    Stated for two arbitrary trees via their canonical forms: if the binding roots
    agree and the active canonical normal forms are reached, the structures are the
    same canonical form or `H` collides. -/
theorem canonical_unique (L : Nat)
    (leaf_node_sep : ∀ (d : List UInt8) (ds : List Digest), leafHash d ≠ nodeHash ds)
    (leaf_empty_sep : ∀ (d : List UInt8), leafHash d ≠ emptyHash)
    (node_empty_sep : ∀ (ds : List Digest), nodeHash ds ≠ emptyHash)
    (t₁ t₂ : NaryTree (List UInt8))
    (ha₁ : Active L (normalize t₁)) (ha₂ : Active L (normalize t₂))
    (hroot : eval L t₁ = eval L t₂) :
    normalize t₁ = normalize t₂ ∨ HashCollision ∨ NodeHashCollision := by
  have heval : eval L (normalize t₁) = eval L (normalize t₂) := by
    rw [normalize_eval, normalize_eval]; exact hroot
  exact canonical_eval_injective L leaf_node_sep leaf_empty_sep node_empty_sep
    (normalize t₁) (normalize t₂)
    (normalize_canonical t₁) (normalize_canonical t₂) ha₁ ha₂ heval

end NEML
