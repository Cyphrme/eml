-- Trust base.
import EMLProof.Foundations

-- PMT layer.
import EMLProof.NEML
import EMLProof.Canonical
import EMLProof.Compression
import EMLProof.Kary
import EMLProof.BindingProof

-- EML layer.
import EMLProof.KaryConsistency

-- CT-lineage (relegated CT-build reference; not authoritative).
import EMLProof.Projection
import EMLProof.General.Instantiation

/-!
# EMLProof — proof corpus root

The corpus mirrors the three-layer code cut. The **authoritative** chain depends
only on the four trust-base axioms in `Foundations`; the CT-lineage binary-bridge
material is **relegated** to CT-build reference and is no longer authoritative.

## Trust base
* `EMLProof.Foundations` — the four structural axioms (`Digest`, `Digest.nonempty`,
  `H`, `digestToBytes`) and the shared hash constants. The entire TCB.

## PMT layer (polymorphic Merkle tree kernel)
* `EMLProof.NEML` — the n-ary tree, evaluator (canonicalizing reduction), epoch
  construction, the binding-root metaroot, canonical inclusion proofs:
  `metaroot_binds_timeline`, `not_canonical_of_promoted`, `inclusion_proof_unique`.
* `EMLProof.Canonical` — **C-CANONICAL-UNIQUE**: canonicalization as a confluent
  terminating rewrite system → unique canonical normal form, and canonical-encoding
  injectivity (`canonical_eval_injective`, `canonical_unique`).
* `EMLProof.Compression` — canonicalization soundness over the `Option`-payload
  view (`eval_compress`, `expand_compress`).
* `EMLProof.Kary` — k-ary inclusion soundness/completeness over the shared topology
  (`kary_inclusion_soundness`, `kary_completeness`).

## EML layer (epoch Merkle log over the PMT)
* `EMLProof.KaryConsistency` — consistency soundness/completeness and append-only
  (`consistency_soundness`, `consistency_completeness`, `consistency_append_only`).

## CT-lineage (relegated — CT-build reference, NOT authoritative)
The `Tree → Binary → Invariant → Bridge → Projection`/`General/*` chain is the
binary CT-construction proof material. The authoritative PMT/EML chain above does
not depend on it (NEML sources its axioms from `Foundations`, not `Projection`);
it is retained only as CT-build reference. See `EMLProof.Projection`'s header.
-/
