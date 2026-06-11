#!/usr/bin/env bash
# verify_core.sh — the button. I don't expect you to take the claim on faith;
# I didn't either, so here are the two checks I lean on, and you can run them
# yourself in about ten seconds.
#
#   1. minimal/MuCore.v: the whole claim in one Coq file. It compiles from a
#      clean checkout in seconds with nothing but the standard library, and
#      every theorem ends in `Print Assumptions` reporting "Closed under the
#      global context", so there are no axioms, mine or anyone's, hiding the
#      work.
#
#   2. minimal/nofi_demo.py: the same floor measured from scratch in plain
#      Python, no Thiele code anywhere near it, every step checking itself.
#
# Same inputs, same numbers, whoever runs it. Exit 0 means both held; anything
# else means one didn't, and the output tells you which.

set -euo pipefail
cd "$(dirname "$0")/.."

EXPECTED_CLOSED=10
fail() { echo "VERIFY: FAIL — $1" >&2; exit 1; }

echo "== [1/2] minimal Coq core (minimal/MuCore.v) =="
if command -v coqc >/dev/null 2>&1; then
    rm -f minimal/MuCore.vo minimal/MuCore.vok minimal/MuCore.vos minimal/MuCore.glob minimal/.MuCore.aux
    out="$(coqc minimal/MuCore.v 2>&1)" || { echo "$out"; fail "MuCore.v did not compile"; }
    closed="$(printf '%s\n' "$out" | grep -c 'Closed under the global context' || true)"
    if printf '%s\n' "$out" | grep -q 'Axioms:'; then
        printf '%s\n' "$out"
        fail "an assumption audit reported axioms"
    fi
    [ "$closed" -eq "$EXPECTED_CLOSED" ] || { printf '%s\n' "$out"; fail "expected $EXPECTED_CLOSED 'Closed under the global context' receipts, saw $closed"; }
    echo "  compiled clean; $closed/$EXPECTED_CLOSED theorems closed under the global context (zero axioms)"
else
    fail "coqc not found — install Coq 8.18+ (e.g. 'apt-get install coq' or via opam) and re-run"
fi

echo "== [2/2] clean-room measurement (minimal/nofi_demo.py) =="
python3 minimal/nofi_demo.py

echo
echo "VERIFY: PASS — core claim machine-checked (zero axioms) and independently measured."
