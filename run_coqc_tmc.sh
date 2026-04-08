#!/bin/bash
cd /workspaces/The-Thiele-Machine/coq
timeout 600 /usr/bin/coqc \
  -Q . Kernel \
  -Q kernel Kernel \
  -Q kami_hw KamiHW \
  -Q nofi NoFI \
  -Q spacetime Spacetime \
  -Q thielemachine ThieleMachine \
  -Q physics Physics \
  -Q self_reference SelfReference \
  -Q thiele_manifold ThieleManifold \
  -Q thermodynamic Thermodynamic \
  -Q tests Tests \
  -Q ../vendor/kami/Kami Kami \
  ThieleMachineComplete.v 2>&1 | tail -40
echo "EXIT: $?"
