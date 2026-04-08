#!/bin/bash
cd /workspaces/The-Thiele-Machine/coq
/usr/bin/coqc -Q kernel Kernel -Q . Top kernel/LandauerDerivation.v 2>&1
RC=$?
echo "===EXIT_CODE=== $RC"
if [ -f kernel/LandauerDerivation.vo ]; then
  echo "===VO_CREATED=== YES"
else
  echo "===VO_CREATED=== NO"
fi
