#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
# The maintained claim evidence is generated from MasterSummary, not from
# a working-session branch, machine path, or dirty-tree snapshot.
python3 scripts/generate_master_summary_artifacts.py --out-dir artifacts/final_claim_audit
