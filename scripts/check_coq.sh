#!/usr/bin/env bash
set -euo pipefail
# Compile all Coq proof files under the coq/ directory.
# This ensures every proof stays in sync with the codebase.
find coq -name '*.v' | sort | while read -r file; do
  echo "Checking $file"
  coqc "$file"
done
