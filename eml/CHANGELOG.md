# Changelog

All notable changes to the `eml` crate are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed

- `polydigest`: a log resumed from a seal now carries every algorithm that
  was closed before the seal. Previously `Sealed` froze frontiers only for
  algorithms active at the sealed size, so the resumed log forgot a closed
  algorithm: `resume_algorithm` on it failed, and re-adding it registered it
  fresh over nulls. The roots of a resumed log with a closed algorithm change
  from wrong to right (they now equal the unsealed log's).
- `canonical-ml`: reconstructing a frontier on a subtree-kind log trusts the
  stored node over a partially active range instead of recursing into
  children a resumed log never stored.

### Added

- `polydigest::Sealed::dormant_frontiers` and `with_dormant_frontiers`: each
  closed algorithm's frontier peaks at its close size, O(log n) per
  algorithm. Member roots, binding roots and run-extents are unchanged.

### Migration

- Pass a hasher to `NaryMerkleLog::resume` for every id in
  `sealed.dormant_frontiers()`, not only `sealed.frontiers()`. A closed
  algorithm resumed without its hasher stays registered (so `add_algorithm`
  of that id fails `DuplicateAlgorithm` instead of silently re-registering
  it) but cannot be resumed and is still frozen by a later `seal`. A closed
  algorithm's hasher is optional everywhere: `from_storage` likewise loads a
  stored closed algorithm without one (an open algorithm still needs its
  hasher, `OrphanedMetadata` otherwise). The combined roots of such a log
  include the closed algorithm's timeline, as the original log's do. The
  one exception is a seal of a log reopened from storage whose close-size
  frontier has a peak over a range that never held a leaf: that peak's null
  constant belongs to the missing hasher, so `seal` fails `UnknownAlgorithm`.

## [0.12.0]

### Changed

- **Breaking:** `eml` no longer re-exports `polydigest`'s mutable-tree
  surface. `EpochTree`, `CmtConfig`, `CmtError`, `CmtResult`, and the
  cmt-specific rebalanced-tree topology (`rebalanced_bag`,
  `rebalanced_skeleton`) were previously reachable through `eml::*` as
  incidental leakage from a blanket `pub use polydigest::*;`; `eml` is
  the append-only log facade and never used these symbols itself.
  Consumers that need the mutable-tree API should depend on
  `polydigest` directly, or use the `emt` crate, which is the
  dedicated mutable-tree facade.
- The `eml::storage` and `eml::proof` module paths are now re-exported
  explicitly and remain available, unchanged.

## [0.11.0] and earlier

Not tracked in this changelog.
