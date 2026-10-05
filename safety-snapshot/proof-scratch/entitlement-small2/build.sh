#!/bin/bash
# Build every file of this directory in dependency order with Coq 8.18.0.
# Usage (Git Bash), from this directory:  bash build.sh
C=/c/Users/tbagt/Coq-8.18/bin/coqc
for f in EarnedCore EarnedGeneric EarnedMulti ThieleComplete ThieleCompleteWindow \
         EntitlementSmall FragmentSmall MultiThiele2 BitSearch2 EntitlementMore2 \
         BitSearchMember2 BitSearchObserved2 CompressionSmall2 TimeTax2 CoveringNeeded2; do
  timeout 900 $C -Q . Minimal $f.v > $f.log 2>&1 || { echo "FAIL $f"; tail -20 $f.log; exit 1; }
done
for f in MultiThiele2 BitSearch2 BitSearchMember2 BitSearchObserved2 EntitlementMore2 CompressionSmall2 TimeTax2 CoveringNeeded2; do
  n=$(grep -c "Closed under the global context" $f.log); p=$(grep -c "^Print Assumptions" $f.v)
  echo "$f: Print Assumptions=$p closed=$n"
done
