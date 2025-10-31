#!/usr/bin/env bash
set -euo pipefail

# This wrapper preserves the historical entry point while delegating to the
# repository-wide admit/axiom scanner.

python -m tools.generate_admit_report

echo "Report written to ADMIT_REPORT.txt"
