#!/usr/bin/env bash
# Install the Thiele Machine git hooks.
#
# Mechanism: `git config --local core.hooksPath .githooks` points git at the
# in-repo `.githooks/` directory directly. No copy into `.git/hooks/` is
# required — edits to `.githooks/pre-commit` are picked up immediately,
# and a fresh clone only needs this one command (auto-run by the
# Makefile's `install-hooks` target on which `test` and every gate
# depends, so it happens without user intervention).
#
# Idempotent: re-running just verifies the config is current.
#
# Usage:
#   bash scripts/install-git-hooks.sh
#   make install-hooks         (equivalent; also runs automatically as a
#                               prerequisite of test/gate targets)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [ ! -d ".git" ]; then
    echo "ERROR: .git/ directory not found. This is not a git checkout." >&2
    exit 1
fi

if [ ! -f ".githooks/pre-commit" ]; then
    echo "ERROR: .githooks/pre-commit not found in repo. Re-clone or check out the hook source first." >&2
    exit 1
fi

current="$(git config --local --get core.hooksPath || true)"

if [ "$current" = ".githooks" ]; then
    # Already configured; nothing to do. Stay quiet so this is cheap to
    # call as a Makefile prerequisite on every gate invocation.
    exit 0
fi

if [ -n "$current" ] && [ "$current" != ".githooks" ]; then
    echo "WARNING: core.hooksPath is set to '$current' (expected '.githooks')."
    echo "         Overwriting to '.githooks' so the Thiele Machine hooks run."
fi

git config --local core.hooksPath .githooks
chmod +x .githooks/pre-commit

echo "✓ core.hooksPath -> .githooks"
echo ""
echo "Every commit (any branch) now auto-refreshes and stages:"
echo "  - artifacts/rtl_pipeline_manifest.json"
echo "  - artifacts/rtl_text_transform_audit.json"
echo "  - artifacts/proof_dependency_{dag,connectivity}.json"
echo "  - artifacts/proof_dependency_file_graph.mmd"
echo "  - artifacts/PROOF_FOUNDATION_AUDIT.md"
echo "  - artifacts/final_claim_audit/*.json"
echo "Coq proof-scope drift is also gated when .v / _CoqProject changes are staged."
