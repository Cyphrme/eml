#!/usr/bin/env bash
#
# check_build.sh — Compile every fuzz target and fail loudly if any breaks.
#
# The fuzz/ directory is a separate workspace, invisible to `cargo test
# --workspace`, so a stale or broken target can compile-fail silently for
# months.  Run this script at the gate (e.g. in CI or a pre-commit hook) to
# catch breakage early:
#
#   cd fuzz && ./check_build.sh
#
# Exit 0 when all targets build; non-zero (and loud) on any failure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
cd "$SCRIPT_DIR"

if ! command -v cargo-fuzz &> /dev/null; then
    echo "error: 'cargo-fuzz' is not installed or not in PATH." >&2
    echo "Install: cargo install cargo-fuzz" >&2
    exit 1
fi

echo "Building all fuzz targets..."
cargo fuzz build
echo "All fuzz targets built successfully."
