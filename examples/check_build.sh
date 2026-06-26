#!/usr/bin/env bash
#
# check_build.sh — Verify that all examples binaries compile.
#
# `cargo test --workspace` does not build examples (only dev-deps and tests),
# so a stale example binary can silently rot between benchmark runs. This
# script compiles the eml-examples binaries in debug mode as a build gate.
#
# Usage:
#   ./examples/check_build.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
WORKSPACE_ROOT="$(cd "${SCRIPT_DIR}/.." &>/dev/null && pwd)"

echo "Building eml-examples binaries..."
cargo build -p eml-examples --bins --manifest-path "${WORKSPACE_ROOT}/Cargo.toml"
echo "Build check passed: all examples binaries compile."
