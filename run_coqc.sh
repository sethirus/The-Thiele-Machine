#!/bin/bash
cd /workspaces/The-Thiele-Machine/coq
timeout 120 coqc -Q . Kernel -Q kami_hw KamiHW -Q ../vendor/kami/Kami Kami ThieleMachineComplete.v > /workspaces/The-Thiele-Machine/coq_compile_result.txt 2>&1
echo "EXIT_CODE=$?" >> /workspaces/The-Thiele-Machine/coq_compile_result.txt
