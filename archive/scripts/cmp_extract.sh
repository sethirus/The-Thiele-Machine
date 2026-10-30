#!/usr/bin/env bash
# Extract the verified compiler and its runner from Coq to OCaml and build
# the driver.
#
#   scripts/cmp_extract.sh [OUT_DIR]
#
# Needs the project compiled (coq/kernel/foundation/Cmp*.vo, as after
# `make -C coq`), coqc 8.18, and OCaml with zarith (apt install ocaml
# libzarith-ocaml-dev). Writes cmp_extracted.ml and .mli (from
# ocaml/CmpExtract.v) and the executable cmp_driver (from ocaml/cmp_driver.ml)
# into OUT_DIR (default build/cmp). The repository is not written to: the
# extraction file is compiled in OUT_DIR.
#
# The driver reads commands from standard input; see the header of
# ocaml/cmp_driver.ml, and tests/test_cmp_compiler.py for how the python
# tests use it.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:-$ROOT/build/cmp}"
COQC="${COQC:-coqc}"
# The compiled tree (minimal/*.vo, coq/kernel/foundation/*.vo): the repository itself
# unless THIELE_COQ_BUILD names another tree laid out the same way (the same variable
# the python tests read).
BUILD="${THIELE_COQ_BUILD:-$ROOT}"
UNDEC="${THIELE_UNDEC:-$BUILD/vendor/coq-undecidability/theories}"

mkdir -p "$OUT"
cp "$ROOT/ocaml/CmpExtract.v" "$OUT/CmpExtract.v"
cp "$ROOT/ocaml/cmp_driver.ml" "$OUT/cmp_driver.ml"
cd "$OUT"

"$COQC" -Q "$UNDEC" Undecidability -Q "$BUILD/minimal" Minimal \
        -R "$BUILD/coq/kernel/foundation" Kernel CmpExtract.v

ocamlfind ocamlopt -package zarith -linkpkg \
  cmp_extracted.mli cmp_extracted.ml cmp_driver.ml -o cmp_driver

echo "built $OUT/cmp_driver"
