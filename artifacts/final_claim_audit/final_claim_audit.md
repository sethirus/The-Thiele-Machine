# Final Claim Audit Trail

- generated_at_utc: 2026-02-22T08:30:26Z
- branch: main
- head: 1959b4633d627b0b37df87366c8e8091a79b59a4
- workspace: /workspaces/The-Thiele-Machine

## Verification Artifacts
- artifacts/proof_gate/metadata.txt
- artifacts/proof_gate/admitted_count.txt
- artifacts/proof_gate/checksums.sha256
- artifacts/synthesis_gate/stats_run1.txt
- artifacts/synthesis_gate/stats_run2.txt
- artifacts/synthesis_gate/simulation_payload.json
- artifacts/synthesis_gate/checksums.sha256

## Git Status Snapshot

```text
M  .atlas_state/atlas_history.json
M  .github/workflows/ci.yml
A  .gitmodules
A  HANDOFF.md
M  INQUISITOR_REPORT.md
M  Makefile
M  a.out
M  artifacts/ATLAS.md
M  artifacts/atlas/atlas_definition_of_done.json
M  artifacts/atlas/atlas_inquisitor_summary.json
M  artifacts/atlas/atlas_latex_coverage.json
M  artifacts/atlas/atlas_priority_plan.json
M  artifacts/atlas/atlas_summary.json
M  artifacts/atlas/file_action_breakdown.mmd
M  artifacts/atlas/layer_flow.mmd
M  artifacts/atlas/python_rtl_focus.mmd
M  artifacts/atlas/symbol_class_breakdown.mmd
M  artifacts/atlas/top_file_links.mmd
M  artifacts/atlas/triad_topology.mmd
A  artifacts/final_claim_audit/checksums.sha256
A  artifacts/final_claim_audit/final_claim_audit.md
AM artifacts/final_claim_audit/git_status_porcelain.txt
A  artifacts/proof_gate/admitted_count.txt
A  artifacts/proof_gate/checksums.sha256
A  artifacts/proof_gate/metadata.txt
AM artifacts/synthesis_gate/checksums.sha256
A  artifacts/synthesis_gate/simulation_payload.json
A  artifacts/synthesis_gate/stats_diff.txt
A  artifacts/synthesis_gate/stats_run1.txt
A  artifacts/synthesis_gate/stats_run2.txt
M  build/extracted_vm_runner
A  build/kami_hw/Main.cmi
A  build/kami_hw/Main.cmx
A  build/kami_hw/Main.ml
A  build/kami_hw/Main.o
A  build/kami_hw/PP.cmi
A  build/kami_hw/PP.cmx
A  build/kami_hw/PP.ml
A  build/kami_hw/PP.o
A  build/kami_hw/Target.cmi
A  build/kami_hw/Target.cmx
A  build/kami_hw/Target.ml
A  build/kami_hw/Target.mli
A  build/kami_hw/Target.o
A  build/kami_hw/blink.bsv
A  build/kami_hw/blink_clean.bo
A  build/kami_hw/blink_clean.bsv
A  build/kami_hw/kami_to_bsv
A  build/kami_hw/mkModule1.v
A  build/kami_hw/thiele_cpu.bsv
A  build/kami_hw/thiele_cpu_clean.bo
A  build/kami_hw/thiele_cpu_clean.bsv
A  build/kami_hw/thiele_cpu_final.bo
A  build/kami_hw/thiele_cpu_final.bsv
A  build/kami_hw/thiele_cpu_kami_minimal.v
A  build/kami_hw/thiele_hw.bsv
A  build/kami_hw/thiele_hw_clean.bo
A  build/kami_hw/thiele_hw_clean.bsv
A  build/kami_hw/thiele_hw_fixed.bo
A  build/kami_hw/thiele_hw_fixed.bsv
M  build/partition_core_tb
M  build/thiele_core.cmi
M  build/thiele_core.cmo
D  build/thiele_core.cmx
M  build/thiele_core.ml
M  build/thiele_core.mli
D  build/thiele_core.o
M  build/thiele_core_minimal.ml
M  build/thiele_core_minimal.mli
AM build/thiele_cpu_kami_tb.out
D  check_test_timeouts.py
D  coq/.Makefile.conf.d
D  coq/.Makefile.coq.d
D  coq/.Makefile.temp.d
D  coq/.Makefile.test.d
M  coq/Extraction.vo
M  coq/Makefile.conf
M  coq/Makefile.coq.conf
M  coq/MinimalExtraction.vo
M  coq/_CoqProject
M  coq/bridge/BoxWorld_to_Kernel.vo
M  coq/bridge/FiniteQuantum_to_Kernel.vo
M  coq/bridge/PythonMuLedgerBisimulation.vo
D  coq/isomorphism/coqproofs/.lia.cache
A  coq/kami_hw/Abstraction.glob
A  coq/kami_hw/Abstraction.v
A  coq/kami_hw/Abstraction.vo
A  coq/kami_hw/Blink.glob
A  coq/kami_hw/Blink.v
A  coq/kami_hw/Blink.vo
A  coq/kami_hw/KamiExtraction.glob
A  coq/kami_hw/KamiExtraction.v
A  coq/kami_hw/KamiExtraction.vo
A  coq/kami_hw/ThieleCPUCore.glob
A  coq/kami_hw/ThieleCPUCore.v
A  coq/kami_hw/ThieleCPUCore.vo
A  coq/kami_hw/ThieleTypes.glob
A  coq/kami_hw/ThieleTypes.v
A  coq/kami_hw/ThieleTypes.vo
D  coq/kernel/.Makefile.coq.d
M  coq/kernel/ArrowOfTimeSynthesis.vo
M  coq/kernel/CHSH.vo
M  coq/kernel/CHSHExtraction.vo
A  coq/kernel/CPURefinement.glob
A  coq/kernel/CPURefinement.v
A  coq/kernel/CPURefinement.vo
M  coq/kernel/CausalSetAxioms.glob
M  coq/kernel/CausalSetAxioms.v
M  coq/kernel/CausalSetAxioms.vo
M  coq/kernel/Certification.glob
M  coq/kernel/Certification.v
M  coq/kernel/Certification.vo
M  coq/kernel/ClassicalBound.vo
M  coq/kernel/Closure.glob
M  coq/kernel/Closure.v
M  coq/kernel/Closure.vo
M  coq/kernel/ConeAlgebra.vo
M  coq/kernel/ConeDerivation.vo
M  coq/kernel/CrossLayerManifest.glob
M  coq/kernel/CrossLayerManifest.v
M  coq/kernel/CrossLayerManifest.vo
M  coq/kernel/Definitions.vo
M  coq/kernel/DerivedTime.vo
A  coq/kernel/DiscreteCalculus.glob
A  coq/kernel/DiscreteCalculus.v
R  coq/kernel/Test.vo -> coq/kernel/DiscreteCalculus.vo
M  coq/kernel/DiscreteGaussBonnet.vo
M  coq/kernel/DiscreteTopology.vo
M  coq/kernel/EinsteinEmergence.vo
M  coq/kernel/EinsteinEquations4D.glob
M  coq/kernel/EinsteinEquations4D.v
M  coq/kernel/EinsteinEquations4D.vo
M  coq/kernel/EntropyImpossibility.vo
M  coq/kernel/FalsifiablePrediction.glob
M  coq/kernel/FalsifiablePrediction.v
M  coq/kernel/FalsifiablePrediction.vo
M  coq/kernel/FiniteInformation.vo
M  coq/kernel/FourDSimplicialComplex.vo
M  coq/kernel/GeodesicCompleteness.vo
M  coq/kernel/HardwareBisimulation.vo
M  coq/kernel/InformationCausality.vo
M  coq/kernel/InverseSquareLaw.vo
M  coq/kernel/KernelBenchmarks.vo
M  coq/kernel/KernelNoether.glob
M  coq/kernel/KernelNoether.v
M  coq/kernel/KernelNoether.vo
M  coq/kernel/KernelPhysics.vo
M  coq/kernel/LocalInfoLoss.glob
M  coq/kernel/LocalInfoLoss.v
M  coq/kernel/LocalInfoLoss.vo
M  coq/kernel/Locality.glob
M  coq/kernel/Locality.v
M  coq/kernel/Locality.vo
M  coq/kernel/LorentzNotForced.vo
M  coq/kernel/LorentzSignature.glob
M  coq/kernel/LorentzSignature.v
M  coq/kernel/LorentzSignature.vo
M  coq/kernel/MasterSummary.glob
M  coq/kernel/MasterSummary.v
M  coq/kernel/MasterSummary.vo
M  coq/kernel/MetricFromMuCosts.vo
M  coq/kernel/ModularObservation.glob
M  coq/kernel/ModularObservation.v
M  coq/kernel/ModularObservation.vo
M  coq/kernel/MuChaitin.vo
M  coq/kernel/MuCostDerivation.glob
M  coq/kernel/MuCostDerivation.v
M  coq/kernel/MuCostDerivation.vo
M  coq/kernel/MuCostModel.vo
M  coq/kernel/MuGeometry.vo
M  coq/kernel/MuGravity.glob
M  coq/kernel/MuGravity.v
M  coq/kernel/MuGravity.vo
M  coq/kernel/MuGravity_BridgeTheorems.vo
M  coq/kernel/MuGravity_ConstructiveBridges.vo
M  coq/kernel/MuGravity_Definitions.glob
M  coq/kernel/MuGravity_Definitions.v
M  coq/kernel/MuGravity_Definitions.vo
M  coq/kernel/MuGravity_Emergence.vo
M  coq/kernel/MuInformation.vo
M  coq/kernel/MuInitiality.vo
M  coq/kernel/MuLedgerConservation.glob
M  coq/kernel/MuLedgerConservation.v
M  coq/kernel/MuLedgerConservation.vo
M  coq/kernel/MuNecessity.vo
M  coq/kernel/MuNoFreeInsightQuantitative.vo
M  coq/kernel/NPMuCostBound.vo
M  coq/kernel/NoArbitrage.vo
M  coq/kernel/NoFreeInsight.glob
M  coq/kernel/NoFreeInsight.v
M  coq/kernel/NoFreeInsight.vo
M  coq/kernel/NoGo.vo
M  coq/kernel/NoGoSensitivity.vo
M  coq/kernel/NonCircularityAudit.vo
M  coq/kernel/ObserverDerivation.vo
M  coq/kernel/PDISCOVERIntegration.vo
M  coq/kernel/PNEWTopologyChange.vo
M  coq/kernel/POVMBridge.vo
M  coq/kernel/PartitionSeparation.vo
M  coq/kernel/Persistence.glob
M  coq/kernel/Persistence.vo
M  coq/kernel/PhysicsClosure.vo
M  coq/kernel/PoissonEquation.vo
M  coq/kernel/ProbabilityImpossibility.vo
M  coq/kernel/PythonBisimulation.glob
M  coq/kernel/PythonBisimulation.v
M  coq/kernel/PythonBisimulation.vo
M  coq/kernel/QuantumBound.vo
M  coq/kernel/QuantumEquivalence.vo
M  coq/kernel/ReceiptIntegrity.vo
M  coq/kernel/RevelationRequirement.glob
M  coq/kernel/RevelationRequirement.v
M  coq/kernel/RevelationRequirement.vo
M  coq/kernel/RiemannTensor4D.glob
M  coq/kernel/RiemannTensor4D.v
M  coq/kernel/RiemannTensor4D.vo
M  coq/kernel/SemanticComplexityIsomorphism.vo
M  coq/kernel/SemanticMuCost.vo
M  coq/kernel/SimulationProof.glob
M  coq/kernel/SimulationProof.v
M  coq/kernel/SimulationProof.vo
M  coq/kernel/SpacetimeEmergence.vo
M  coq/kernel/StateSpaceCounting.vo
M  coq/kernel/StressEnergyDynamics.vo
M  coq/kernel/TOE.vo
M  coq/kernel/TOEDecision.glob
M  coq/kernel/TOEDecision.v
M  coq/kernel/TOEDecision.vo
D  coq/kernel/Test.glob
M  coq/kernel/ThreeLayerIsomorphism.glob
M  coq/kernel/ThreeLayerIsomorphism.v
M  coq/kernel/ThreeLayerIsomorphism.vo
M  coq/kernel/TopologyCurvatureBridge.vo
M  coq/kernel/TsirelsonDerivation.vo
M  coq/kernel/TsirelsonLowerBound.vo
M  coq/kernel/TsirelsonUniqueness.vo
M  coq/kernel/TsirelsonUpperBound.glob
M  coq/kernel/TsirelsonUpperBound.v
M  coq/kernel/TsirelsonUpperBound.vo
M  coq/kernel/VMEncoding.glob
M  coq/kernel/VMEncoding.v
M  coq/kernel/VMEncoding.vo
M  coq/kernel/VMState.glob
M  coq/kernel/VMState.v
M  coq/kernel/VMState.vo
M  coq/kernel/VMStep.glob
M  coq/kernel/VMStep.v
M  coq/kernel/VMStep.vo
A  "coq/kernel/What Remains Admitted (3 lemmas, inquisi"
M  coq/kernel_toe/Closure.glob
M  coq/kernel_toe/Closure.v
M  coq/kernel_toe/Closure.vo
M  coq/kernel_toe/Definitions.vo
M  coq/kernel_toe/NoGo.vo
M  coq/kernel_toe/NoGoSensitivity.vo
M  coq/kernel_toe/Persistence.glob
M  coq/kernel_toe/Persistence.vo
M  coq/kernel_toe/TOE.vo
M  coq/nofi/Instance_Kernel.glob
M  coq/nofi/Instance_Kernel.v
M  coq/nofi/Instance_Kernel.vo
M  coq/nofi/MuChaitinTheory_Interface.vo
M  coq/nofi/MuChaitinTheory_Theorem.vo
M  coq/physics/TriangularLattice.vo
R  coq/thielemachine/coqproofs/DissipativeEmbedding.glob -> coq/physics_exploration/DissipativeEmbedding.glob
R  coq/thielemachine/coqproofs/DissipativeEmbedding.v -> coq/physics_exploration/DissipativeEmbedding.v
R  coq/thielemachine/coqproofs/DissipativeEmbedding.vo -> coq/physics_exploration/DissipativeEmbedding.vo
M  coq/physics_exploration/EmergentSpacetime.vo
R  coq/thielemachine/coqproofs/HardwareVMHarness.glob -> coq/physics_exploration/HardwareVMHarness.glob
R  coq/thielemachine/coqproofs/HardwareVMHarness.v -> coq/physics_exploration/HardwareVMHarness.v
R  coq/thielemachine/coqproofs/HardwareVMHarness.vo -> coq/physics_exploration/HardwareVMHarness.vo
M  coq/physics_exploration/HolographicGravity.vo
M  coq/physics_exploration/ParticleMasses.vo
R  coq/thielemachine/coqproofs/PhysicsEmbedding.glob -> coq/physics_exploration/PhysicsEmbedding.glob
R  coq/thielemachine/coqproofs/PhysicsEmbedding.v -> coq/physics_exploration/PhysicsEmbedding.v
R  coq/thielemachine/coqproofs/PhysicsEmbedding.vo -> coq/physics_exploration/PhysicsEmbedding.vo
M  coq/physics_exploration/PlanckDerivation.vo
R  coq/thielemachine/coqproofs/WaveEmbedding.glob -> coq/physics_exploration/WaveEmbedding.glob
R  coq/thielemachine/coqproofs/WaveEmbedding.v -> coq/physics_exploration/WaveEmbedding.v
R  coq/thielemachine/coqproofs/WaveEmbedding.vo -> coq/physics_exploration/WaveEmbedding.vo
D  coq/project_cerberus/coqproofs/.lia.cache
M  coq/quantum_derivation/BornRuleUnique.vo
M  coq/quantum_derivation/CollapseDetermination.vo
M  coq/quantum_derivation/CompositePartitions.vo
M  coq/quantum_derivation/ObservationIrreversibility.vo
M  coq/quantum_derivation/ProjectionFromPartitions.vo
M  coq/quantum_derivation/SchrodingerFromPartitions.vo
M  coq/quantum_derivation/TensorNecessity.vo
M  coq/quantum_derivation/TwoDimensionalNecessity.vo
M  coq/shor_primitives/PolylogConjecture.glob
M  coq/shor_primitives/PolylogConjecture.vo
D  coq/shor_primitives/StructureRevelationFramework.glob
M  coq/tests/TestNecessity.vo
M  coq/tests/verify_zero_admits.vo
M  coq/theory/ArchTheorem.vo
M  coq/thiele_manifold/PhysicalConstants.vo
M  coq/thiele_manifold/PhysicsIsomorphism.vo
M  coq/thiele_manifold/ThieleManifoldBridge.vo
M  coq/thielemachine/coqproofs/AlgebraicLaws.vo
D  coq/thielemachine/coqproofs/Axioms.glob
M  coq/thielemachine/coqproofs/BellArtifacts.vo
M  coq/thielemachine/coqproofs/BellCheck.vo
M  coq/thielemachine/coqproofs/BellInequality.glob
M  coq/thielemachine/coqproofs/BellInequality.v
M  coq/thielemachine/coqproofs/BellInequality.vo
M  coq/thielemachine/coqproofs/BellReceiptLocalBound.vo
M  coq/thielemachine/coqproofs/BellReceiptLocalGeneral.vo
M  coq/thielemachine/coqproofs/BellReceiptSemantics.vo
M  coq/thielemachine/coqproofs/BellReceiptSoundness.glob
M  coq/thielemachine/coqproofs/BellReceiptSoundness.v
M  coq/thielemachine/coqproofs/BellReceiptSoundness.vo
M  coq/thielemachine/coqproofs/CompositionPrimitive.vo
M  coq/thielemachine/coqproofs/ComputationIsomorphism.vo
M  coq/thielemachine/coqproofs/CoreSemantics.glob
M  coq/thielemachine/coqproofs/CoreSemantics.v
M  coq/thielemachine/coqproofs/CoreSemantics.vo
M  coq/thielemachine/coqproofs/Embedding_TM.vo
M  coq/thielemachine/coqproofs/GoldenVectors.vo
M  coq/thielemachine/coqproofs/HardwareBridge.glob
M  coq/thielemachine/coqproofs/HardwareBridge.v
M  coq/thielemachine/coqproofs/HardwareBridge.vo
M  coq/thielemachine/coqproofs/HyperThiele_Halting.vo
M  coq/thielemachine/coqproofs/LogicIsomorphism.vo
M  coq/thielemachine/coqproofs/Oracle.vo
M  coq/thielemachine/coqproofs/QuantumAdmissibilityDeliverableB.vo
M  coq/thielemachine/coqproofs/QuantumAdmissibilityTsirelson.vo
M  coq/thielemachine/coqproofs/QuantumTheorems.vo
M  coq/thielemachine/coqproofs/RepresentationTheorem.vo
M  coq/thielemachine/coqproofs/SemanticBridge.vo
D  coq/thielemachine/coqproofs/Simulation.glob
M  coq/thielemachine/coqproofs/ThieleFoundations.vo
M  coq/thielemachine/coqproofs/ThieleKernelCausality.glob
M  coq/thielemachine/coqproofs/ThieleKernelCausality.v
M  coq/thielemachine/coqproofs/ThieleKernelCausality.vo
M  coq/thielemachine/coqproofs/ThieleMachineConcrete.glob
M  coq/thielemachine/coqproofs/ThieleMachineConcrete.v
M  coq/thielemachine/coqproofs/ThieleMachineConcrete.vo
M  coq/thielemachine/coqproofs/ThieleProofCarryingReality.vo
M  coq/thielemachine/coqproofs/ThieleSpaceland.glob
M  coq/thielemachine/coqproofs/ThieleSpaceland.v
M  coq/thielemachine/coqproofs/ThieleSpaceland.vo
M  coq/thielemachine/coqproofs/ThieleUnificationDemo.vo
M  coq/thielemachine/coqproofs/ThieleUnificationProtocol.vo
M  coq/thielemachine/coqproofs/ThieleUnificationTensor.vo
M  coq/thielemachine/coqproofs/ThieleVMOpcodes.glob
M  coq/thielemachine/coqproofs/ThieleVMOpcodes.v
M  coq/thielemachine/coqproofs/ThieleVMOpcodes.vo
M  coq/thielemachine/coqproofs/TsirelsonBoundBridge.vo
M  coq/thielemachine/verification/Admissibility.vo
D  coq/thielemachine/verification/BridgeDefinitions.glob
D  coq/thielemachine/verification/BridgeDefinitions.vo
D  coq/thielemachine/verification/BridgeProof.glob
M  coq/thielemachine/verification/Deliverable_CHSHSeparation.glob
M  coq/thielemachine/verification/Deliverable_CHSHSeparation.v
M  coq/thielemachine/verification/Deliverable_CHSHSeparation.vo
M  coq/thielemachine/verification/Deliverable_NoSignaling.vo
M  coq/thielemachine/verification/Deliverable_SignalingLowerBound.vo
M  coq/thielemachine/verification/ObservationInterface.vo
M  coq/thielemachine/verification/PhysicsPillars.vo
M  coq/thielemachine/verification/Prediction.vo
M  coq/thielemachine/verification/PredictionNoFI.vo
M  coq/thielemachine/verification/RandomnessNoFI.vo
M  coq/thielemachine/verification/Symmetry.vo
D  coq/thielemachine/verification/ThieleUniversalBridge.glob
D  coq/thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.glob
D  coq/thielemachine/verification/modular/Bridge_BridgeCore.glob
A  coq/thieleuniversal/coqproofs/Axioms.glob
R  coq/thielemachine/coqproofs/Axioms.v -> coq/thieleuniversal/coqproofs/Axioms.v
R  coq/thielemachine/coqproofs/Axioms.vo -> coq/thieleuniversal/coqproofs/Axioms.vo
R  coq/thielemachine/coqproofs/Impossibility.glob -> coq/thieleuniversal/coqproofs/Impossibility.glob
R  coq/thielemachine/coqproofs/Impossibility.v -> coq/thieleuniversal/coqproofs/Impossibility.v
R  coq/thielemachine/coqproofs/Impossibility.vo -> coq/thieleuniversal/coqproofs/Impossibility.vo
A  coq/thieleuniversal/coqproofs/Simulation.glob
R  coq/thielemachine/coqproofs/Simulation.v -> coq/thieleuniversal/coqproofs/Simulation.v
R  coq/thielemachine/coqproofs/Simulation.vo -> coq/thieleuniversal/coqproofs/Simulation.vo
M  coq/thieleuniversal/coqproofs/ThieleUniversal.glob
M  coq/thieleuniversal/coqproofs/ThieleUniversal.v
M  coq/thieleuniversal/coqproofs/ThieleUniversal.vo
R  coq/thielemachine/coqproofs/UTMStaticCheck.glob -> coq/thieleuniversal/coqproofs/UTMStaticCheck.glob
R  coq/thielemachine/coqproofs/UTMStaticCheck.v -> coq/thieleuniversal/coqproofs/UTMStaticCheck.v
R  coq/thielemachine/coqproofs/UTMStaticCheck.vo -> coq/thieleuniversal/coqproofs/UTMStaticCheck.vo
R  coq/thielemachine/verification/BridgeCheckpoints.glob -> coq/thieleuniversal/verification/BridgeCheckpoints.glob
R  coq/thielemachine/verification/BridgeCheckpoints.v -> coq/thieleuniversal/verification/BridgeCheckpoints.v
R  coq/thielemachine/verification/BridgeCheckpoints.vo -> coq/thieleuniversal/verification/BridgeCheckpoints.vo
A  coq/thieleuniversal/verification/BridgeDefinitions.glob
R  coq/thielemachine/verification/BridgeDefinitions.v -> coq/thieleuniversal/verification/BridgeDefinitions.v
A  coq/thieleuniversal/verification/BridgeDefinitions.vo
A  coq/thieleuniversal/verification/BridgeProof.glob
R  coq/thielemachine/verification/BridgeProof.v -> coq/thieleuniversal/verification/BridgeProof.v
R  coq/thielemachine/verification/BridgeProof.vo -> coq/thieleuniversal/verification/BridgeProof.vo
A  coq/thieleuniversal/verification/ThieleUniversalBridge.glob
R  coq/thielemachine/verification/ThieleUniversalBridge.v -> coq/thieleuniversal/verification/ThieleUniversalBridge.v
R  coq/thielemachine/verification/ThieleUniversalBridge.vo -> coq/thieleuniversal/verification/ThieleUniversalBridge.vo
A  coq/thieleuniversal/verification/ThieleUniversalBridge_Axiom_Tests.glob
R  coq/thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v -> coq/thieleuniversal/verification/ThieleUniversalBridge_Axiom_Tests.v
R  coq/thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.vo -> coq/thieleuniversal/verification/ThieleUniversalBridge_Axiom_Tests.vo
A  coq/thieleuniversal/verification/modular/Bridge_BridgeCore.glob
R  coq/thielemachine/verification/modular/Bridge_BridgeCore.v -> coq/thieleuniversal/verification/modular/Bridge_BridgeCore.v
R  coq/thielemachine/verification/modular/Bridge_BridgeCore.vo -> coq/thieleuniversal/verification/modular/Bridge_BridgeCore.vo
M  debug_synth.ys
D  find_empty_tests.py
A  inquisitor_final.txt
M  inquisitor_output.txt
A  probe_thiele.py
M  scripts/automated_verification.sh
M  scripts/equivalence_bundle.py
M  scripts/forge_artifact.sh
M  scripts/generate_full_mesh_audit.py
M  scripts/inquisitor.py
A  scripts/kami_extract.sh
A  scripts/parity_extracted_only.sh
A  scripts/proof_gate_reproducible.sh
A  scripts/repo_audit_trail.sh
M  scripts/run_the_synthesis.sh
A  scripts/synthesis_repro_gate.sh
M  scripts/validate_mu_alignment.sh
M  scripts/verify_3layer.py
M  scripts/verify_isomorphism.py
M  tests/alignment/test_comprehensive_alignment.py
M  tests/test_bisimulation_complete.py
M  tests/test_isomorphism_vm_vs_coq.py
M  tests/test_opcode_isomorphism.py
M  tests/test_property_bisimulation.py
M  tests/test_rigorous_isomorphism.py
M  tests/test_rtl_compute_isomorphism.py
M  tests/test_rtl_synthesis_gate.py
M  tests/test_unified_cpu_semantic_contracts.py
M  tests/test_unified_cpu_semantic_invariants.py
M  tests/test_verilog_cosim.py
M  thielecpu/generated/generated_core.py
M  thielecpu/hardware/cosim.py
M  thielecpu/hardware/rtl/generated_opcodes.vh
M  thielecpu/hardware/rtl/synth_lite_out.v
A  thielecpu/hardware/rtl/thiele_cpu_kami.v
A  thielecpu/hardware/rtl/thiele_cpu_pipelined.v
M  thielecpu/hardware/rtl/thiele_cpu_unified.v
A  thielecpu/hardware/testbench/thiele_cpu_isomorphism_tb
A  thielecpu/hardware/testbench/thiele_cpu_isomorphism_tb.v
A  thielecpu/hardware/testbench/thiele_cpu_kami_tb.v
M  thielecpu/hardware/testbench/thiele_cpu_tb.v
M  thielecpu/isa.py
M  thielecpu/state.py
M  thielecpu/vm.py
M  tools/extracted_vm_runner.cmi
M  tools/extracted_vm_runner.cmo
M  tools/extracted_vm_runner.cmx
M  tools/extracted_vm_runner.ml
M  tools/extracted_vm_runner.o
A  vendor/bbv
A  vendor/kami
```
