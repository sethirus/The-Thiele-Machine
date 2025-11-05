#!/usr/bin/env bash
set -euo pipefail

echo "Running local Coq preflight checks..."
ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

echo "Searching for 'Admitted' in coq/..."
admit_count=$(grep -R "\bAdmitted\b" coq --include="*.v" | wc -l || true)
if [ "$admit_count" -ne 0 ]; then
  echo "ERROR: Found $admit_count 'Admitted' occurrences:" >&2
  grep -n "\bAdmitted\b" coq --include="*.v" || true
  exit 2
fi

echo "Checking Axiom inventory consistency..."
grep -R "^Axiom " coq --include="*.v" | sed 's/:.*$//' | sort | uniq > /tmp/axioms_found.txt || true
awk '/^- `/{gsub(/`/,"",$2); print $2}' coq/AXIOM_INVENTORY.md | sort | uniq > /tmp/axioms_expected.txt || true
if ! diff -u /tmp/axioms_expected.txt /tmp/axioms_found.txt >/dev/null 2>&1; then
  echo "ERROR: Axiom inventory mismatch. Run coq/scripts/find_admits_and_axioms.sh for details." >&2
  echo "Expected (AXIOM_INVENTORY.md):"; cat /tmp/axioms_expected.txt || true
  echo "Found (coq sources):"; cat /tmp/axioms_found.txt || true
  exit 3
fi

echo "Preflight checks passed."