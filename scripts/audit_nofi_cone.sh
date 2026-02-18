#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT"

echo "[audit_nofi] Running inquisitor over coq/nofi/"
python3 scripts/inquisitor.py --report artifacts/inquisitor_nofi.md

echo "[audit_nofi] Checking for axioms via Print Assumptions"

# We intentionally check for *axioms*, not module parameters.
# Since `NoFreeInsight` is a functor, we apply it to the concrete kernel instance
# and then check assumptions on the resulting theorem.
OUT="$(
  cd "$ROOT/coq" && coqtop -quiet -Q nofi NoFI -R kernel Kernel 2>&1 <<'EOF'
Require Import NoFI.NoFreeInsight_Theorem.
Require Import NoFI.Instance_Kernel.

Module TheoremKernel := NoFreeInsight KernelNoFI.
Print Assumptions TheoremKernel.no_free_insight.
EOF
)"

if echo "$OUT" | grep -qE '^(Error:|Toplevel input,)'; then
  echo "[audit_nofi] FAIL: coqtop error while checking assumptions"
  echo "$OUT"
  exit 1
fi

# Coq prints an explicit "Axioms:" section when axioms are present.
if echo "$OUT" | grep -qE '^Axioms:'; then
  echo "[audit_nofi] FAIL: Axioms detected in TheoremKernel.no_free_insight"
  echo "$OUT"
  exit 1
fi

if ! echo "$OUT" | grep -qF 'Closed under the global context'; then
  echo "[audit_nofi] FAIL: unexpected Print Assumptions output (refusing to pass gate)"
  echo "$OUT"
  exit 1
fi

echo "[audit_nofi] OK: no axioms detected (closed under global context)"
