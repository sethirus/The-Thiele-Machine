#!/usr/bin/env bash
# check_isa_proof_freshness.sh
#
# PROOF-SENSITIVE ISA GATE
#
# The Thiele VM's correctness proofs depend heavily on case analysis over
# every vm_instruction constructor. Any change to these files invalidates
# the case-analysis proofs in the listed CRITICAL files:
#
#   coq/kernel/VMStep.v         — opcode definitions, instruction_cost
#   coq/kernel/VMState.v        — VMState fields, CSRState, WitnessCounts
#
# CRITICAL PROOF FILES (must be rebuilt after any ISA change):
#   AbstractNoFI.v  — no_free_certification (case analysis over 32 opcodes)
#   PrimeAxiom.v    — vm_apply_certified (case analysis over all opcodes)
#   RevelationRequirement.v — nonlocal_correlation_requires_revelation
#   HardwareBisimulation.v  — bisimulation relation
#
# This script checks that the .vo files for critical proofs are newer than
# the ISA source files they depend on. Fails with an explanation if stale.
#
# Usage:
#   ./scripts/check_isa_proof_freshness.sh [coq-dir]
#   default coq-dir: coq/
#
# Exit codes:
#   0 — all critical .vo files are fresh
#   1 — one or more critical .vo files are stale (ISA changed)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="${1:-$REPO_ROOT/coq}"

# ISA source files — changes to these require proof rebuild
ISA_SOURCES=(
  "$COQ_DIR/kernel/VMStep.v"
  "$COQ_DIR/kernel/VMState.v"
)

# Critical proof files — their .vo files must be newer than ISA sources
CRITICAL_PROOFS=(
  "$COQ_DIR/kernel/AbstractNoFI.v"
  "$COQ_DIR/kernel/PrimeAxiom.v"
  "$COQ_DIR/kernel/RevelationRequirement.v"
  "$COQ_DIR/kernel/HardwareBisimulation.v"
  "$COQ_DIR/kernel/MuLedgerConservation.v"
  "$COQ_DIR/kernel/NoFreeInsight.v"
)

FAIL=0
MESSAGES=()

for src in "${ISA_SOURCES[@]}"; do
  if [[ ! -f "$src" ]]; then
    echo "WARNING: ISA source not found: $src (skipping)" >&2
    continue
  fi
  for proof in "${CRITICAL_PROOFS[@]}"; do
    vo="${proof%.v}.vo"
    if [[ ! -f "$vo" ]]; then
      MESSAGES+=("STALE: $vo does not exist — run 'make -C $COQ_DIR' to rebuild")
      FAIL=1
      continue
    fi
    if [[ "$src" -nt "$vo" ]]; then
      MESSAGES+=("STALE: $(basename "$vo") is older than $(basename "$src") — ISA change may invalidate proof")
      FAIL=1
    fi
  done
done

if [[ ${#MESSAGES[@]} -gt 0 ]]; then
  echo "=== ISA PROOF FRESHNESS CHECK FAILED ===" >&2
  echo "" >&2
  for msg in "${MESSAGES[@]}"; do
    echo "  $msg" >&2
  done
  echo "" >&2
  echo "REQUIRED ACTION:" >&2
  echo "  1. Rebuild all Coq proofs:  make -C coq -j4" >&2
  echo "  2. Verify INQUISITOR passes: python3 scripts/inquisitor.py" >&2
  echo "  3. Update claim_ledger.md if any theorem's status changed" >&2
  echo "" >&2
  echo "ISA PROOF-IMPACT CHECKLIST (for any opcode change):" >&2
  echo "  [ ] Does the new/changed opcode set csr_cert_addr?" >&2
  echo "      → If YES: cert_addr_setterb must be updated in AbstractNoFI.v" >&2
  echo "  [ ] Does the new/changed opcode set vm_certified?" >&2
  echo "      → If YES: vm_apply_certified case must be updated in PrimeAxiom.v" >&2
  echo "  [ ] Does instruction_cost use S(cost) for the new opcode?" >&2
  echo "      → If cert-setter with cost=0: no_free_certification breaks" >&2
  echo "  [ ] Does the opcode change mu?" >&2
  echo "      → If YES: vm_apply_mu and MuLedgerConservation must still hold" >&2
  echo "  [ ] Does the opcode affect shadow projection?" >&2
  echo "      → If YES: ShadowProjection.v (when written) must be updated" >&2
  exit 1
fi

echo "ISA proof freshness check: OK (all critical .vo files are fresh)"

# ============================================================================
# PART 2: EXTRACTION FRESHNESS CHECK (E3)
# ============================================================================
# build/thiele_core.ml is the Coq-extracted OCaml VM implementation.
# It must be newer than its source files: coq/Extraction.v and VMStep.v.
# If stale, the running implementation may not match the current Coq proofs.

EXTRACTION_SOURCES=(
  "$REPO_ROOT/coq/Extraction.v"
  "$COQ_DIR/kernel/VMStep.v"
  "$COQ_DIR/kernel/VMState.v"
)

EXTRACTED_ARTIFACT="$REPO_ROOT/build/thiele_core.ml"

EXTRACT_FAIL=0
if [[ ! -f "$EXTRACTED_ARTIFACT" ]]; then
  echo "WARNING: build/thiele_core.ml not found — run 'make canonical-extract' to regenerate" >&2
else
  for src in "${EXTRACTION_SOURCES[@]}"; do
    if [[ ! -f "$src" ]]; then
      continue
    fi
    if [[ "$src" -nt "$EXTRACTED_ARTIFACT" ]]; then
      echo "WARNING: build/thiele_core.ml is older than $(basename "$src")" >&2
      echo "  → OCaml extraction may not reflect current Coq semantics" >&2
      echo "  → Run: make canonical-extract" >&2
      EXTRACT_FAIL=1
    fi
  done
fi

if [[ "$EXTRACT_FAIL" -eq 1 ]]; then
  echo "" >&2
  echo "EXTRACTION FRESHNESS WARNING: extracted artifacts may be stale." >&2
  echo "Run 'make canonical-extract' to regenerate from current Coq source." >&2
  echo "" >&2
  # Extraction staleness is a WARNING, not a hard failure (CI rebuilds anyway)
  # To make this a hard failure, change the exit below to exit 1
fi

echo "Extraction freshness check: OK"
exit 0
