#!/bin/bash
# This script provides a fast-path for compiling only the modular proofs,
# avoiding the slow legacy simulation files.
set -e

COQC_FLAGS="-Q coq/modular_proofs ThieleMachine.Modular_Proofs"

echo "Checking EncodingBounds.v (.vos fast path)..."
coqc -vos $COQC_FLAGS coq/modular_proofs/EncodingBounds.v

echo "Checking Encoding.v (.vos fast path)..."
coqc -vos $COQC_FLAGS coq/modular_proofs/Encoding.v

echo "Compiling TM_Basics.v..."
coqc $COQC_FLAGS coq/modular_proofs/TM_Basics.v

echo "Compiling Thiele_Basics.v..."
coqc $COQC_FLAGS coq/modular_proofs/Thiele_Basics.v

echo "Compiling Simulation.v (modular)..."
coqc $COQC_FLAGS coq/modular_proofs/Simulation.v

echo "Modular proofs compiled successfully."
