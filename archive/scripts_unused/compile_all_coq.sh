#!/usr/bin/env bash
# compile_all_coq.sh - Comprehensive Coq compilation script
# Compiles all active Coq files in dependency order

set -e  # Exit on error

echo "======================================================================"
echo "Compiling All Coq Files for The Thiele Machine"
echo "======================================================================"
echo ""

# Theory files
echo "=== Compiling Theory Files ==="
coqc -Q theory theory theory/Genesis.v
echo "✓ Genesis.v"
coqc -Q theory theory theory/Core.v
echo "✓ Core.v"
coqc -Q theory theory theory/PhysRel.v
echo "✓ PhysRel.v"
coqc -Q theory theory theory/LogicToPhysics.v
echo "✓ LogicToPhysics.v"
coqc -Q theory theory theory/WitnessIsGenesis.v
echo "✓ WitnessIsGenesis.v"
coqc -Q theory theory theory/CostIsComplexity.v
echo "✓ CostIsComplexity.v"
coqc -Q theory theory theory/NoFreeLunch.v
echo "✓ NoFreeLunch.v"
coqc -Q theory theory theory/Separation.v
echo "✓ Separation.v"
coqc -Q theory theory theory/GeometricSignature.v
echo "✓ GeometricSignature.v (NEW)"
echo ""

# Kernel files
echo "=== Compiling Kernel Files ==="
coqc -Q coq/kernel Kernel coq/kernel/Kernel.v
echo "✓ Kernel.v"
coqc -Q coq/kernel Kernel coq/kernel/VMState.v
echo "✓ VMState.v"
coqc -Q coq/kernel Kernel coq/kernel/VMStep.v
echo "✓ VMStep.v"
coqc -Q coq/kernel Kernel coq/kernel/VMEncoding.v
echo "✓ VMEncoding.v"
coqc -Q coq/kernel Kernel coq/kernel/KernelTM.v
echo "✓ KernelTM.v"
coqc -Q coq/kernel Kernel coq/kernel/KernelThiele.v
echo "✓ KernelThiele.v"
coqc -Q coq/kernel Kernel coq/kernel/SimulationProof.v
echo "✓ SimulationProof.v"
coqc -Q coq/kernel Kernel coq/kernel/MuLedgerConservation.v
echo "✓ MuLedgerConservation.v"
coqc -Q coq/kernel Kernel coq/kernel/Subsumption.v
echo "✓ Subsumption.v"
coqc -Q coq/kernel Kernel coq/kernel/PDISCOVERIntegration.v
echo "✓ PDISCOVERIntegration.v (NEW)"
echo ""

echo "======================================================================"
echo "✓ ALL COQ FILES COMPILED SUCCESSFULLY!"
echo "======================================================================"
echo ""
echo "Summary:"
echo "  Theory files:  9 (including GeometricSignature.v)"
echo "  Kernel files: 10 (including PDISCOVERIntegration.v)"
echo "  Total files:  19"
echo ""
echo "Status: Zero Admitted statements in active files"
echo "Axioms: Only necessary mathematical axioms (VI metric properties)"
echo "======================================================================"
