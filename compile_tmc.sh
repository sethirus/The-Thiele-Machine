#!/bin/bash
set -e
cd /workspaces/The-Thiele-Machine/coq

echo "=== Starting coqc compilation at $(date) ==="
echo "=== File: ThieleMachineComplete.v ==="

/usr/bin/coqc -Q . Kernel -Q kami_hw KamiHW -Q ../vendor/kami/Kami Kami ThieleMachineComplete.v 2>&1

EC=$?
echo "=== Finished at $(date) ==="
echo "=== Exit code: $EC ==="
