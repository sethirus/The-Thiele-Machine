#!/usr/bin/env bash
# Extract the machines from Coq to OCaml and build the driver.
#
#   scripts/realize_extract.sh [OUT_DIR]
#
# Needs the project compiled (coq/kernel/foundation/Realize*.vo, as after
# `make -C coq`), coqc 8.18, and OCaml with zarith (apt install ocaml
# libzarith-ocaml-dev). Writes realize_extracted.ml and .mli (from
# ocaml/RealizeExtract.v) and the executable realize_driver
# (from ocaml/realize_driver.ml) into OUT_DIR (default build/realize). The
# repository is not written to: the extraction file is compiled in OUT_DIR.
#
# The driver reads commands from standard input; see the header of
# ocaml/realize_driver.ml, and tests/test_realize_ocaml.py for how the
# python tests use it.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:-$ROOT/build/realize}"
COQC="${COQC:-coqc}"
# The compiled tree (minimal/*.vo, coq/kernel/foundation/*.vo): the repository itself
# unless THIELE_COQ_BUILD names another tree laid out the same way (the same variable
# the python tests read).
BUILD="${THIELE_COQ_BUILD:-$ROOT}"
UNDEC="${THIELE_UNDEC:-$BUILD/vendor/coq-undecidability/theories}"

mkdir -p "$OUT"
cp "$ROOT/ocaml/RealizeExtract.v" "$OUT/RealizeExtract.v"
cp "$ROOT/ocaml/realize_driver.ml" "$OUT/realize_driver.ml"
cd "$OUT"

"$COQC" -Q "$UNDEC" Undecidability -Q "$BUILD/minimal" Minimal \
        -R "$BUILD/coq/kernel/foundation" Kernel RealizeExtract.v

ocamlfind ocamlopt -package zarith -linkpkg \
  realize_extracted.mli realize_extracted.ml realize_driver.ml -o realize_driver

echo "built $OUT/realize_driver"
