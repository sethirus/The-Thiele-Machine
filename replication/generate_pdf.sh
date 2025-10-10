#!/usr/bin/env bash
set -euo pipefail

TARGETS=(EVIDENCE_AT_A_GLANCE.md DECLARATION_OF_INDEPENDENCE.md)
OUT=experiments/Declaration_Evidence.pdf

if ! command -v pandoc >/dev/null 2>&1 ; then
  echo "pandoc is required to generate PDF. Install pandoc or set GEN_PDF=false."
  exit 1
fi

pandoc "${TARGETS[@]}" -o "$OUT" && echo "PDF generated at $OUT"
