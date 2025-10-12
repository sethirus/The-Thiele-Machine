#!/usr/bin/env bash
set -euo pipefail

# This script searches the coq/ tree for Admitted occurrences and Axiom declarations
# and writes a small report to stdout and to coq/ADMIT_REPORT.txt.

REPORT=coq/ADMIT_REPORT.txt
: > "$REPORT"

echo "Admitted occurrences (file:line):" | tee -a "$REPORT"
grep -R -n "\bAdmitted\b" coq --include="*.v" || true | tee -a "$REPORT"

echo "" | tee -a "$REPORT"
echo "Axiom declarations (file:line):" | tee -a "$REPORT"
grep -R -n "^Axiom " coq --include="*.v" || true | tee -a "$REPORT"

echo "" | tee -a "$REPORT"
echo "Summary:" | tee -a "$REPORT"
num_admits=$(grep -R -n "\bAdmitted\b" coq --include="*.v" | wc -l || true)
num_axioms=$(grep -R -n "^Axiom " coq --include="*.v" | wc -l || true)
echo "  Admitted count: ${num_admits}" | tee -a "$REPORT"
echo "  Axiom declarations: ${num_axioms}" | tee -a "$REPORT"

echo "Report written to ${REPORT}"
