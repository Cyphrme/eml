#!/usr/bin/env bash
#
# check_acceptance.sh — The one command that must exit 0 before a branch is
# considered green.
#
# `cargo test --workspace` alone is not sufficient: `fuzz/` opens its own
# `[workspace]` table (so it is invisible to that command entirely) and
# `eml/tests/complexity.rs` is `#![cfg(not(debug_assertions))]` (so it
# compiles to nothing under a plain debug `cargo test`). Both holes let a
# breaking change to the `Storage` trait or a public API pass a fully green
# `cargo test --workspace` while the fuzz crate fails to compile or the
# complexity bounds go unchecked. This script closes both by running every
# piece the repository's tests actually depend on, in one place, so no
# future acceptance run can silently drop one of them again.
#
# Usage:
#   ./check_acceptance.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
cd "$SCRIPT_DIR"

echo "==> cargo test --workspace --no-fail-fast"
cargo test --workspace --no-fail-fast

echo "==> cargo test --release --test complexity -p eml"
cargo test --release --test complexity -p eml

echo "==> cargo clippy --workspace --all-targets -- -D warnings"
cargo clippy --workspace --all-targets -- -D warnings

echo "==> cargo fmt --check"
cargo fmt --check

echo "==> (cd fuzz && cargo check --all-targets)"
(cd fuzz && cargo check --all-targets)

echo "All acceptance checks passed."
