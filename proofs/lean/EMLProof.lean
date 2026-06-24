-- Trust base.
import EMLProof.Foundations

-- Merkle Spine (structural core).
import EMLProof.NEML
import EMLProof.Canonical
import EMLProof.Compression
import EMLProof.Kary
import EMLProof.LeafProof

-- Epoch combinator (over the spine).
import EMLProof.Epoch
import EMLProof.BindingProof

-- CML / consistency layer.
import EMLProof.KaryConsistency
import EMLProof.SnapshotProof

-- CT-lineage (relegated CT-build reference; not authoritative).
import EMLProof.Projection
import EMLProof.General.Instantiation

/-!
# EMLProof — proof corpus root

The corpus mirrors the layered code cut: a structural **Merkle Spine**, the
**epoch combinator** over it, and the canonical-log consistency layer. The
**authoritative** chain depends only on the four trust-base axioms in
`Foundations`; the CT-lineage binary-bridge material is **relegated** to CT-build
reference and is no longer authoritative.

## Trust base
* `EMLProof.Foundations` — the four structural axioms (`Digest`, `Digest.nonempty`,
  `H`, `digestToBytes`) and the shared hash constants. The entire TCB.

## Merkle Spine (structural core)
Epoch-free; no activation timeline, binding root, or null-run-extent. Operates over
the positional topology and the canonical evaluator alone.
* `EMLProof.NEML` — the n-ary tree, the canonicalizing evaluator (collapse +
  promotion), and the canonical inclusion proofs: `not_canonical_of_promoted`,
  `inclusion_soundness`, `inclusion_proof_unique`.
* `EMLProof.Canonical` — **C-CANONICAL-UNIQUE (structural half)**: canonicalization
  as a confluent terminating rewrite system → unique canonical normal form, and
  canonical-encoding injectivity (`canonical_eval_injective`, `canonical_unique`).
  Distinct canonical structures ⇒ distinct roots; stands alone for a
  single-algorithm consumer with no epoch.
* `EMLProof.Compression` — canonicalization soundness over the `Option`-payload
  view (`eval_compress`, `expand_compress`).
* `EMLProof.Kary` — k-ary inclusion soundness/completeness over the shared topology
  (`kary_inclusion_soundness`, `kary_completeness`).
* `EMLProof.LeafProof` — the live leaf-proof API over the spine topology.

## Epoch combinator (over the spine)
Consumes the spine's roots as **opaque digest bytes**; never touches `eval` or
`canonical_unique`. The dependency arrow runs epoch → spine only.
* `EMLProof.Epoch` — the committed activation timeline (Design A+), the combined
  root as the raw-concat canonicalization fold, the per-algorithm binding root, and
  **C-CANONICAL-UNIQUE (timeline-binding half)**: `combinedRoot_binds_timeline`
  (distinct committed activations ⇒ distinct binding roots), plus
  `coupling_extract_sound`.
* `EMLProof.BindingProof` — the cross-algorithm binding-proof soundness theorems
  (`binding_root_sound`, `binding_proof_consistent`, `binding_proof_forgery_rejected`).

## Consistency layer (canonical log over the spine)
* `EMLProof.KaryConsistency` — consistency soundness/completeness and append-only
  (`consistency_soundness`, `consistency_completeness`, `consistency_append_only`).
  This is the theorem that discharges the permanent/ephemeral immutability model:
  permanent (complete-subtree) hashes are the only hashes proofs bind against, and
  the append-only-prefix guarantee is exactly "an append never mutates a permanent
  (bound) hash"; the ephemeral frontier fold is the sole churn and is never proven
  against (SAD §4.2 / D17).
* `EMLProof.SnapshotProof` — the multi-algorithm snapshot proof bridging the
  structural and binding tiers.

## CT-lineage (relegated — CT-build reference, NOT authoritative)
The `Tree → Binary → Invariant → Bridge → Projection`/`General/*` chain is the
binary CT-construction proof material. The authoritative spine/epoch chain above
does not depend on it (NEML sources its axioms from `Foundations`, not
`Projection`); it is retained only as CT-build reference. See `EMLProof.Projection`'s
header.
-/
