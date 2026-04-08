#!/bin/bash
cd /workspaces/The-Thiele-Machine/coq
/usr/bin/coqc -Q . Kernel -Q kami_hw KamiHW -Q ../vendor/kami/Kami Kami ThieleMachineComplete.v > /workspaces/The-Thiele-Machine/coqc_result.log 2>&1
echo "RC=$?" >> /workspaces/The-Thiele-Machine/coqc_result.log
date >> /workspaces/The-Thiele-Machine/coqc_result.log
touch /workspaces/The-Thiele-Machine/coqc_done.flag
