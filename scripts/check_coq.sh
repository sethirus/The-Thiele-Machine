#!/usr/bin/env bash
set -euo pipefail
echo "Checking all Coq proofs via make..."
(cd coq/ && /usr/bin/coq_makefile -f _CoqProject -o Makefile && make)
