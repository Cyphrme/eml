#!/usr/bin/env bash
# One-time setup: materialize the frozen neml baseline outside the workspace.
#
# `difftest` depends on the pre-campaign neml source (git ref 4827561) as a
# Cargo path dependency.  Because Cargo absorbs any path dep that lives INSIDE
# the workspace root as a workspace member, the baseline must sit OUTSIDE the
# workspace directory tree.  A git worktree at the sibling path
# `.scratch/worktrees/baseline-N1` (relative to the repo root) satisfies both
# constraints: it is outside the workspace root, it is tracked by git (no
# manual copy needed), and `cargo test --workspace` resolves it from the same
# position as the committed Cargo.toml path dependency.
#
# Run once from the repo root after a fresh clone:
#
#   bash difftest/setup-baseline.sh
#
# Idempotent: exits 0 if the worktree already exists at the expected path.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
BASELINE_REF="4827561"
BASELINE_PATH="$REPO_ROOT/.scratch/worktrees/baseline-N1"

if [ -d "$BASELINE_PATH" ]; then
    echo "baseline worktree already present at $BASELINE_PATH — nothing to do."
    exit 0
fi

mkdir -p "$REPO_ROOT/.scratch/worktrees"
git worktree add --detach "$BASELINE_PATH" "$BASELINE_REF"

echo "baseline worktree created at $BASELINE_PATH (ref $BASELINE_REF)."
echo "cargo test --workspace will now resolve the neml_baseline dependency."
