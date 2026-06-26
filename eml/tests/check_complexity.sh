#!/usr/bin/env bash
#
# check_complexity.sh — Run the complexity-scaling regression suite correctly.
#
# The tests in complexity.rs (this directory) infer asymptotic complexity from
# measured runtimes, so they must run one at a time: under `cargo test`'s
# default parallelism a sibling test's setup contends for CPU during another
# test's timing loop, inflating the larger inputs enough to flip an O(log n) fit
# to O(n log n) and fail spuriously. They are also gated on not(debug_assertions),
# so they only compile under --release. Run this script at the gate (CI or a
# pre-commit hook) to invoke them with the required flags:
#
#   ./eml/tests/check_complexity.sh
#
# Exit 0 when every complexity test passes; non-zero (and loud) on any failure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
cd "$SCRIPT_DIR"

echo "Running complexity suite (release, single-threaded)..."
cargo test --release -p eml --test complexity -- --test-threads=1
echo "All complexity tests passed."
