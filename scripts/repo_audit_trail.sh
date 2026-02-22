#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ART_DIR="$ROOT/artifacts/final_claim_audit"
mkdir -p "$ART_DIR"
cd "$ROOT"

NOW="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
HEAD_SHA="$(git rev-parse HEAD 2>/dev/null || echo unknown)"

STATUS_FILE="$ART_DIR/git_status_porcelain.txt"
git status --porcelain=v1 > "$STATUS_FILE" || true

{
  echo "# Final Claim Audit Trail"
  echo
  echo "- generated_at_utc: $NOW"
  echo "- branch: $BRANCH"
  echo "- head: $HEAD_SHA"
  echo "- workspace: $ROOT"
  echo
  echo "## Verification Artifacts"
  for p in \
    artifacts/proof_gate/metadata.txt \
    artifacts/proof_gate/admitted_count.txt \
    artifacts/proof_gate/checksums.sha256 \
    artifacts/synthesis_gate/stats_run1.txt \
    artifacts/synthesis_gate/stats_run2.txt \
    artifacts/synthesis_gate/simulation_payload.json \
    artifacts/synthesis_gate/checksums.sha256; do
    if [[ -f "$p" ]]; then
      echo "- $p"
    else
      echo "- MISSING: $p"
    fi
  done
  echo
  echo "## Git Status Snapshot"
  echo
  echo '```text'
  cat "$STATUS_FILE"
  echo '```'
} > "$ART_DIR/final_claim_audit.md"

sha256sum "$ART_DIR/final_claim_audit.md" "$STATUS_FILE" > "$ART_DIR/checksums.sha256"

echo "[audit] wrote $ART_DIR/final_claim_audit.md"
