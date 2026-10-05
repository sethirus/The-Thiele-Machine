#!/bin/bash
# usage: build.sh file.v ...
C="C:/Users/tbagt/AppData/Local/Temp/claude/C--GitHub-The-Thiele-Machine/8c62bf23-1cf2-40aa-9dc7-dc81f99092b8/scratchpad/final"
cd "$C"
COQC=C:/Users/tbagt/Coq-8.18/bin/coqc
FLAGS="-w -notation-overridden,-opaque-let,-overriding-logical-loadpath -Q . Minimal -Q C:/thiele-build/vendor/coq-undecidability/theories Undecidability -Q vend Undecidability"
for f in "$@"; do
  echo "== $f"
  timeout 1200 $COQC $FLAGS "$f" > "logs/$(basename $f .v).log" 2>&1
  rc=$?
  grep -v -E "was previously bound|^Warning:$|remapped to|overriding-logical-loadpath|^C:.*scratchpad.final.vend|^Undecidability\.[A-Za-z.]*$|Closed under the global context" "logs/$(basename $f .v).log"
  echo "closed: $(grep -c 'Closed under the global context' logs/$(basename $f .v).log)"
  test $rc -eq 0 || { echo "FAILED rc=$rc"; exit 1; }
done
