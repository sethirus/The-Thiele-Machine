#!/usr/bin/env bash
set -euo pipefail

echo "Scanning for Admitted statements and Axioms..."
# Search Coq files for Admitted or Axiom declarations.
rg -n --glob "*.v" -e "Admitted\\." -e "admit\\." -e "^\\s*Axiom" || true
