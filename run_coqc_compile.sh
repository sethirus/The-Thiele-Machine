#!/bin/bash
cd /workspaces/The-Thiele-Machine/coq
/usr/bin/coqc -Q . Kernel -Q kami_hw KamiHW -Q ../vendor/kami/Kami Kami ThieleMachineComplete.v 2>&1 | tail -50
echo "EXIT_STATUS=${PIPESTATUS[0]}"
