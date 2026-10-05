#!/bin/bash
# usage: build.sh file.v ...
C="C:/Users/tbagt/AppData/Local/Temp/claude/C--GitHub-The-Thiele-Machine/8c62bf23-1cf2-40aa-9dc7-dc81f99092b8/scratchpad/compiler"
cd "$C"
COQC=C:/Users/tbagt/Coq-8.18/bin/coqc
FLAGS="-w -notation-overridden,-opaque-let,-overriding-logical-loadpath -Q . Minimal -Q C:/thiele-build/vendor/coq-undecidability/theories Undecidability -Q vend Undecidability"
for f in "$@"; do
  echo "== $f"
  timeout 600 $COQC $FLAGS "$f" || exit 1
done
