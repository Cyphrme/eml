# Changelog

All notable changes to the `eml` crate are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
