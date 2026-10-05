#!/bin/bash
# usage: build.sh File.v ...   (compiles in order)
S=/c/Users/tbagt/AppData/Local/Temp/claude/C--GitHub-The-Thiele-Machine/8c62bf23-1cf2-40aa-9dc7-dc81f99092b8/scratchpad/recursion-small
COQC=/c/Users/tbagt/Coq-8.18/bin/coqc
cd $S
for f in "$@"; do
  echo "== $f"
  timeout 3000 $COQC -Q $S/minimal Minimal -Q C:/thiele-build/vendor/coq-undecidability/theories Undecidability -R $S/sm Sm sm/$f || exit 1
done
