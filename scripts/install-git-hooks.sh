#!/usr/bin/env bash
# Install the Thiele Machine git hooks.
# Idempotent: re-running just verifies the install is current.
#
# Usage:
#   bash scripts/install-git-hooks.sh
#   make install-hooks         (equivalent)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

SRC=".githooks/pre-commit"
DST=".git/hooks/pre-commit"
MARKER="thiele-machine-pre-commit"

if [ ! -f "$SRC" ]; then
    echo "ERROR: $SRC not found in repo. Are you running from the wrong directory?" >&2
    exit 1
fi

if [ ! -d ".git" ]; then
    echo "ERROR: .git/ directory not found. This is not a git checkout." >&2
    exit 1
fi

if [ -f "$DST" ] && ! grep -q "$MARKER" "$DST"; then
    echo "WARNING: $DST already exists and is NOT the Thiele Machine hook."
    echo "         Refusing to overwrite. To proceed, inspect the existing hook,"
    echo "         then either delete it or merge its logic with $SRC manually."
    exit 1
fi

cp "$SRC" "$DST"
chmod +x "$DST"
echo "✓ Installed $DST"
echo "  (sources: $SRC)"
echo ""
echo "Next commit that touches a tracked Coq source will auto-refresh"
echo "artifacts/rtl_pipeline_manifest.json and stage it."
