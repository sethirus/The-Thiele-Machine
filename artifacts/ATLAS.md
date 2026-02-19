# Thiele Integration Atlas

Generated: 2026-02-19T20:21:50.823431+00:00

Single canonical atlas for cross-layer integration planning (Coq + VM/Python + RTL/Verilog + tests).

## Executive Summary

- Total symbols: **14953**
- Total edges: **108989**
- 3-layer triads: **164**
- Partial triads (2/3 layers): **90**
- Integrate candidates: **0**
- Safe removals (strict): **0**
- Inquisitor gate: **PASS**
- Proof accuracy: **100.00%**
- Test verification gate: **FAIL**
- Definition of Done: **NOT_COMPLETED**

Conservative policy: no Coq proof declarations are ever recommended for removal.
Important: Proof accuracy is Inquisitor proof-hygiene quality, not project completion percentage.

## Inquisitor Proof Gate

| Metric | Value |
|---|---:|
| Gate rating | PASS |
| Strict pass | True |
| Proof accuracy | 100.00% |
| Proof grade | A+ |
| Scanned Coq files | 308 |
| HIGH findings | 0 |
| MEDIUM findings | 0 |
| LOW findings | 0 |
| Inquisitor return code | 0 |

Top failing rule families from Inquisitor:

| Rule | Count |
|---|---:|
| *(none parsed)* | 0 |

## Kernel Organization Guidance

- Kernel Coq files: **123**, average connectivity **73%**
- Non-kernel Coq files: **182**, average connectivity **74%**
- Guidance: Kernel connectivity is weaker than non-kernel Coq files; prioritize proving bridge lemmas from physics/domain theorems into kernel VM semantics before moving declarations into kernel.

## Isomorphism Guidance Scorecard

| Metric | Value |
|---|---:|
| Isomorphism score (0-100) | 87.55 |
| Core+Bridge production ratio | 100% |
| Triad completion ratio | 65% |
| Directional coverage | 6/6 |
| Integrate-file pressure | 0% |
| Completion readiness (heuristic) | 63.52 |

## Test Verification Gate

| Metric | Value |
|---|---:|
| Gate rating | FAIL |
| Production symbol coverage | 7% |
| Production file coverage | 47% |
| Isolated test files | 0 |
| Covered prod symbols | 899/12076 |
| Covered prod files | 235/505 |

## Definition of Done (Unambiguous Completion Gate)

Overall status: **NOT_COMPLETED**

| Check | Actual | Target | Pass |
|---|---:|---:|---|
| isomorphism_score | 87.55 | >= 100.0 | False |
| triad_completion_ratio | 0.6457 | >= 1.0 | False |
| core_bridge_ratio | 0.9986 | >= 1.0 | False |
| test_prod_symbol_coverage_ratio | 0.0744 | >= 1.0 | False |
| test_prod_file_coverage_ratio | 0.4653 | >= 1.0 | False |
| isolated_test_files | 0.0 | <= 0.0 | True |
| per_proof_doc_ratio | 0.9988 | >= 1.0 | False |
| proof_files_with_readme_ratio | 1.0 | >= 1.0 | True |
| kernel_proof_latex_coverage_ratio | 0.9962 | >= 1.0 | False |
| coq_compile_pass | 1.0 | >= 1.0 | True |
| extraction_freshness_pass | 1.0 | >= 1.0 | True |
| rtl_synthesis_pass | 1.0 | >= 1.0 | True |
| inquisitor_strict_pass | 1.0 | == 1.0 | True |

Unmet checks:

- isomorphism_score: actual=87.55 target >= 100.0
- triad_completion_ratio: actual=0.6457 target >= 1.0
- core_bridge_ratio: actual=0.9986 target >= 1.0
- test_prod_symbol_coverage_ratio: actual=0.0744 target >= 1.0
- test_prod_file_coverage_ratio: actual=0.4653 target >= 1.0
- per_proof_doc_ratio: actual=0.9988 target >= 1.0
- kernel_proof_latex_coverage_ratio: actual=0.9962 target >= 1.0

## Toolchain Reality Gates

These gates verify **actual compilation, extraction, and synthesis** — not just
static graph analysis. All four must PASS for the isomorphism to be mechanically
checkable end-to-end.

| Gate | Ran | Pass | Detail |
|---|---|---|---|
| Coq compile (make -C coq, zero Admitted) | ✓ | **PASS** | 311/311 .vo, admits=0 |
| Extraction freshness (thiele_core.ml ≥ Extraction.v) | ✓ | **PASS** | — |
| RTL synthesis (Yosys lite, top=thiele_cpu, cells>0) | ✓ | **PASS** | cells=2 top=True |
| Co-simulation (iverilog/vvp testbench) | ✓ | **PASS** | rc=0 fatal=False |

## Thesis/Math LaTeX Coverage

| Metric | Value |
|---|---:|
| TeX files scanned | 20 |
| Kernel proof symbols mentioned in TeX | 1042/1046 |
| Kernel proof LaTeX coverage ratio | 100% |
| Triad norms mentioned in TeX | 93/164 |
| Triad norm LaTeX coverage ratio | 57% |

Top missing kernel proof symbols in TeX (first 20):

| Symbol |
|---|
| alpha_fundamental |
| p_13_equals_101 |
| p_14_equals_135 |
| p_15_equals_176 |

## Coq Proof Documentation Coverage (Low Priority)

| Metric | Value |
|---|---:|
| Proof files | 275 |
| Proof files with local README | 275/275 |
| Proof files with comment blocks | 275/275 |
| Proof files documented (README + comments) | 274/275 |

| Proof file | Proof count | Has comments | Has README | Status |
|---|---:|---|---|---|
| coq/kernel/AlphaDerivation.v | 4 | True | True | needs_docs |
| coq/bridge/BoxWorld_to_Kernel.v | 7 | True | True | documented |
| coq/bridge/Causal_to_Kernel.v | 1 | True | True | documented |
| coq/bridge/Entropy_to_Kernel.v | 1 | True | True | documented |
| coq/bridge/FiniteQuantum_to_Kernel.v | 9 | True | True | documented |
| coq/bridge/PythonMuLedgerBisimulation.v | 8 | True | True | documented |
| coq/bridge/Randomness_to_Kernel.v | 1 | True | True | documented |
| coq/bridge/Tomography_to_Kernel.v | 1 | True | True | documented |
| coq/catnet/coqproofs/CatNet.v | 3 | True | True | documented |
| coq/isomorphism/coqproofs/Universe.v | 3 | True | True | documented |
| coq/kernel/AlgebraicCoherence.v | 17 | True | True | documented |
| coq/kernel/ArrowOfTimeSynthesis.v | 15 | True | True | documented |
| coq/kernel/BornRule.v | 10 | True | True | documented |
| coq/kernel/BornRuleFromSymmetry.v | 4 | True | True | documented |
| coq/kernel/BoxCHSH.v | 7 | True | True | documented |
| coq/kernel/CHSH.v | 5 | True | True | documented |
| coq/kernel/CHSHExtraction.v | 6 | True | True | documented |
| coq/kernel/CausalSetAxioms.v | 11 | True | True | documented |
| coq/kernel/Certification.v | 11 | True | True | documented |
| coq/kernel/ClassicalBound.v | 2 | True | True | documented |
| coq/kernel/Closure.v | 1 | True | True | documented |
| coq/kernel/Composition.v | 5 | True | True | documented |
| coq/kernel/ConeAlgebra.v | 14 | True | True | documented |
| coq/kernel/ConeDerivation.v | 2 | True | True | documented |
| coq/kernel/ConstantDerivationStrength.v | 14 | True | True | documented |
| coq/kernel/ConstantUnification.v | 6 | True | True | documented |
| coq/kernel/ConstructivePSD.v | 23 | True | True | documented |
| coq/kernel/DerivedTime.v | 3 | True | True | documented |
| coq/kernel/DiscreteGaussBonnet.v | 11 | True | True | documented |
| coq/kernel/DiscreteTopology.v | 18 | True | True | documented |
| coq/kernel/EinsteinEmergence.v | 7 | True | True | documented |
| coq/kernel/EinsteinEquations4D.v | 38 | True | True | documented |
| coq/kernel/EntropyImpossibility.v | 4 | True | True | documented |
| coq/kernel/FalsifiablePrediction.v | 2 | True | True | documented |
| coq/kernel/FiniteInformation.v | 17 | True | True | documented |
| coq/kernel/FourDSimplicialComplex.v | 11 | True | True | documented |
| coq/kernel/GeodesicCompleteness.v | 8 | True | True | documented |
| coq/kernel/HardAssumptions.v | 2 | True | True | documented |
| coq/kernel/HardMathFactsProven.v | 7 | True | True | documented |
| coq/kernel/HardwareBisimulation.v | 11 | True | True | documented |
| coq/kernel/InformationCausality.v | 13 | True | True | documented |
| coq/kernel/InverseSquareLaw.v | 13 | True | True | documented |
| coq/kernel/KernelBenchmarks.v | 5 | True | True | documented |
| coq/kernel/KernelNoether.v | 12 | True | True | documented |
| coq/kernel/KernelPhysics.v | 23 | True | True | documented |
| coq/kernel/KernelTM.v | 1 | True | True | documented |
| coq/kernel/L2Derivation.v | 10 | True | True | documented |
| coq/kernel/LocalInfoLoss.v | 8 | True | True | documented |
| coq/kernel/Locality.v | 14 | True | True | documented |
| coq/kernel/LorentzNotForced.v | 3 | True | True | documented |
| coq/kernel/LorentzSignature.v | 17 | True | True | documented |
| coq/kernel/MasterSummary.v | 5 | True | True | documented |
| coq/kernel/MetricFromMuCosts.v | 13 | True | True | documented |
| coq/kernel/MinimalE.v | 2 | True | True | documented |
| coq/kernel/MinorConstraints.v | 13 | True | True | documented |
| coq/kernel/ModularObservation.v | 4 | True | True | documented |
| coq/kernel/MuChaitin.v | 3 | True | True | documented |
| coq/kernel/MuComplexity.v | 5 | True | True | documented |
| coq/kernel/MuCostDerivation.v | 10 | True | True | documented |
| coq/kernel/MuCostModel.v | 7 | True | True | documented |
| coq/kernel/MuGeometry.v | 5 | True | True | documented |
| coq/kernel/MuGravity.v | 108 | True | True | documented |
| coq/kernel/MuGravity_BridgeTheorems.v | 1 | True | True | documented |
| coq/kernel/MuGravity_Definitions.v | 1 | True | True | documented |
| coq/kernel/MuGravity_Emergence.v | 1 | True | True | documented |
| coq/kernel/MuInformation.v | 5 | True | True | documented |
| coq/kernel/MuInitiality.v | 18 | True | True | documented |
| coq/kernel/MuLedgerConservation.v | 24 | True | True | documented |
| coq/kernel/MuNecessity.v | 4 | True | True | documented |
| coq/kernel/MuNoFreeInsightQuantitative.v | 7 | True | True | documented |
| coq/kernel/NPAMomentMatrix.v | 7 | True | True | documented |
| coq/kernel/NPMuCostBound.v | 9 | True | True | documented |
| coq/kernel/NoArbitrage.v | 5 | True | True | documented |
| coq/kernel/NoCloning.v | 7 | True | True | documented |
| coq/kernel/NoCloningFromMuMonotonicity.v | 4 | True | True | documented |
| coq/kernel/NoFreeInsight.v | 3 | True | True | documented |
| coq/kernel/NoGo.v | 11 | True | True | documented |
| coq/kernel/NoGoSensitivity.v | 4 | True | True | documented |
| coq/kernel/NonCircularityAudit.v | 15 | True | True | documented |
| coq/kernel/ObserverDerivation.v | 7 | True | True | documented |
| coq/kernel/OracleImpossibility.v | 7 | True | True | documented |
| coq/kernel/PDISCOVERIntegration.v | 6 | True | True | documented |
| coq/kernel/PNEWTopologyChange.v | 7 | True | True | documented |
| coq/kernel/POVMBridge.v | 8 | True | True | documented |
| coq/kernel/PartitionSeparation.v | 5 | True | True | documented |
| coq/kernel/Persistence.v | 3 | True | True | documented |
| coq/kernel/PhysicsClosure.v | 1 | True | True | documented |
| coq/kernel/PoissonEquation.v | 9 | True | True | documented |
| coq/kernel/ProbabilityImpossibility.v | 3 | True | True | documented |
| coq/kernel/ProperSubsumption.v | 6 | True | True | documented |
| coq/kernel/Purification.v | 7 | True | True | documented |
| coq/kernel/PythonBisimulation.v | 5 | True | True | documented |
| coq/kernel/QuantumBound.v | 8 | True | True | documented |
| coq/kernel/QuantumEquivalence.v | 10 | True | True | documented |
| coq/kernel/ReceiptCore.v | 1 | True | True | documented |
| coq/kernel/ReceiptIntegrity.v | 17 | True | True | documented |
| coq/kernel/RevelationRequirement.v | 5 | True | True | documented |
| coq/kernel/SemanticComplexityIsomorphism.v | 12 | True | True | documented |
| coq/kernel/SemanticMuCost.v | 2 | True | True | documented |
| coq/kernel/SemidefiniteProgramming.v | 5 | True | True | documented |
| coq/kernel/SimulationProof.v | 29 | True | True | documented |
| coq/kernel/SpacetimeEmergence.v | 23 | True | True | documented |
| coq/kernel/StateSpaceCounting.v | 7 | True | True | documented |
| coq/kernel/StressEnergyDynamics.v | 5 | True | True | documented |
| coq/kernel/Subsumption.v | 3 | True | True | documented |
| coq/kernel/TOE.v | 1 | True | True | documented |
| coq/kernel/TOEDecision.v | 4 | True | True | documented |
| coq/kernel/ThreeLayerIsomorphism.v | 21 | True | True | documented |
| coq/kernel/Tier1Proofs.v | 6 | True | True | documented |
| coq/kernel/TopologyCurvatureBridge.v | 5 | True | True | documented |
| coq/kernel/TsirelsonComputation.v | 1 | True | True | documented |
| coq/kernel/TsirelsonDerivation.v | 5 | True | True | documented |
| coq/kernel/TsirelsonFromAlgebra.v | 11 | True | True | documented |
| coq/kernel/TsirelsonGeneral.v | 15 | True | True | documented |
| coq/kernel/TsirelsonLowerBound.v | 2 | True | True | documented |
| coq/kernel/TsirelsonUniqueness.v | 1 | True | True | documented |
| coq/kernel/TsirelsonUpperBound.v | 19 | True | True | documented |
| coq/kernel/Unitarity.v | 7 | True | True | documented |
| coq/kernel/VMEncoding.v | 15 | True | True | documented |
| coq/kernel/VMState.v | 32 | True | True | documented |
| coq/kernel/ValidCorrelation.v | 1 | True | True | documented |
| coq/kernel_toe/Closure.v | 1 | True | True | documented |
| coq/kernel_toe/NoGo.v | 11 | True | True | documented |
| coq/kernel_toe/NoGoSensitivity.v | 4 | True | True | documented |
| coq/kernel_toe/Persistence.v | 3 | True | True | documented |
| coq/kernel_toe/TOE.v | 1 | True | True | documented |
| coq/modular_proofs/CornerstoneThiele.v | 5 | True | True | documented |
| coq/modular_proofs/Encoding.v | 16 | True | True | documented |
| coq/modular_proofs/EncodingBounds.v | 18 | True | True | documented |
| coq/modular_proofs/Minsky.v | 2 | True | True | documented |
| coq/modular_proofs/Simulation.v | 2 | True | True | documented |
| coq/modular_proofs/TM_Basics.v | 10 | True | True | documented |
| coq/modular_proofs/TM_to_Minsky.v | 12 | True | True | documented |
| coq/modular_proofs/ThieleInstance.v | 12 | True | True | documented |
| coq/modular_proofs/Thiele_Basics.v | 2 | True | True | documented |
| coq/nofi/Instance_Kernel.v | 5 | True | True | documented |
| coq/nofi/MuChaitinTheory_Theorem.v | 3 | True | True | documented |
| coq/nofi/NoFreeInsight_Theorem.v | 1 | True | True | documented |
| coq/physics/DiscreteModel.v | 15 | True | True | documented |
| coq/physics/DissipativeModel.v | 5 | True | True | documented |
| coq/physics/LandauerBridge.v | 10 | True | True | documented |
| coq/physics/PreregSplit.v | 4 | True | True | documented |
| coq/physics/TriangularLattice.v | 27 | True | True | documented |
| coq/physics/WaveModel.v | 23 | True | True | documented |
| coq/physics_exploration/EmergentSchrodinger.v | 4 | True | True | documented |
| coq/physics_exploration/EmergentSpacetime.v | 3 | True | True | documented |
| coq/physics_exploration/HolographicGravity.v | 2 | True | True | documented |
| coq/physics_exploration/ParticleMasses.v | 2 | True | True | documented |
| coq/physics_exploration/PlanckDerivation.v | 7 | True | True | documented |
| coq/physics_exploration/PlanckEmergenceClean.v | 14 | True | True | documented |
| coq/project_cerberus/coqproofs/Cerberus.v | 6 | True | True | documented |
| coq/quantum_derivation/BornRuleUnique.v | 2 | True | True | documented |
| coq/quantum_derivation/CollapseDetermination.v | 3 | True | True | documented |
| coq/quantum_derivation/ComplexNecessity.v | 13 | True | True | documented |
| coq/quantum_derivation/CompositePartitions.v | 5 | True | True | documented |
| coq/quantum_derivation/ObservationIrreversibility.v | 4 | True | True | documented |
| coq/quantum_derivation/ProjectionFromPartitions.v | 4 | True | True | documented |
| coq/quantum_derivation/SchrodingerFromPartitions.v | 3 | True | True | documented |
| coq/quantum_derivation/TensorNecessity.v | 5 | True | True | documented |
| coq/quantum_derivation/TwoDimensionalNecessity.v | 8 | True | True | documented |
| coq/self_reference/SelfReference.v | 4 | True | True | documented |
| coq/shor_primitives/Euclidean.v | 3 | True | True | documented |
| coq/shor_primitives/Modular.v | 8 | True | True | documented |
| coq/shor_primitives/PeriodFinding.v | 1 | True | True | documented |
| coq/shor_primitives/PolylogConjecture.v | 1 | True | True | documented |
| coq/spacetime/Spacetime.v | 7 | True | True | documented |
| coq/spacetime_projection/SpacetimeProjection.v | 10 | True | True | documented |
| coq/test_vscoq/coqproofs/test_vscoq.v | 3 | True | True | documented |
| coq/theory/ArchTheorem.v | 11 | True | True | documented |
| coq/theory/Core.v | 2 | True | True | documented |
| coq/theory/CostIsComplexity.v | 6 | True | True | documented |
| coq/theory/EvolutionaryForge.v | 14 | True | True | documented |
| coq/theory/Genesis.v | 3 | True | True | documented |
| coq/theory/GeometricSignature.v | 11 | True | True | documented |
| coq/theory/LogicToPhysics.v | 1 | True | True | documented |
| coq/theory/NoFreeLunch.v | 2 | True | True | documented |
| coq/theory/PhysRel.v | 4 | True | True | documented |
| coq/theory/Representations.v | 7 | True | True | documented |
| coq/theory/Separation.v | 6 | True | True | documented |
| coq/theory/Universality.v | 13 | True | True | documented |
| coq/theory/WitnessIsGenesis.v | 4 | True | True | documented |
| coq/thermodynamic/LandauerDerived.v | 18 | True | True | documented |
| coq/thermodynamic/ThermodynamicBridge.v | 16 | True | True | documented |
| coq/thiele_manifold/PhysicsIsomorphism.v | 7 | True | True | documented |
| coq/thiele_manifold/ThieleManifold.v | 12 | True | True | documented |
| coq/thiele_manifold/ThieleManifoldBridge.v | 20 | True | True | documented |
| coq/thielemachine/coqproofs/AbstractLTS.v | 22 | True | True | documented |
| coq/thielemachine/coqproofs/AlgebraicLaws.v | 6 | True | True | documented |
| coq/thielemachine/coqproofs/AmortizedAnalysis.v | 5 | True | True | documented |
| coq/thielemachine/coqproofs/Axioms.v | 8 | True | True | documented |
| coq/thielemachine/coqproofs/BellArtifacts.v | 8 | True | True | documented |
| coq/thielemachine/coqproofs/BellCheck.v | 8 | True | True | documented |
| coq/thielemachine/coqproofs/BellInequality.v | 210 | True | True | documented |
| coq/thielemachine/coqproofs/BellReceiptLocalBound.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/BellReceiptLocalGeneral.v | 14 | True | True | documented |
| coq/thielemachine/coqproofs/BellReceiptSoundness.v | 6 | True | True | documented |
| coq/thielemachine/coqproofs/BlindSighted.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/CompositionPrimitive.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/ComputationIsomorphism.v | 3 | True | True | documented |
| coq/thielemachine/coqproofs/Confluence.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/CoreSemantics.v | 25 | True | True | documented |
| coq/thielemachine/coqproofs/DiscoveryProof.v | 26 | True | True | documented |
| coq/thielemachine/coqproofs/DissipativeEmbedding.v | 9 | True | True | documented |
| coq/thielemachine/coqproofs/EfficientDiscovery.v | 9 | True | True | documented |
| coq/thielemachine/coqproofs/Embedding_TM.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/EncodingBridge.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/HardwareBridge.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/HardwareVMHarness.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/HyperThiele_Oracle.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/Impossibility.v | 3 | True | True | documented |
| coq/thielemachine/coqproofs/InfoTheory.v | 9 | True | True | documented |
| coq/thielemachine/coqproofs/LogicIsomorphism.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/MuAlignmentExample.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/MuAlu.v | 3 | True | True | documented |
| coq/thielemachine/coqproofs/NUSD.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/Oracle.v | 40 | True | True | documented |
| coq/thielemachine/coqproofs/OracleImpossibility.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/PartitionDiscoveryIsomorphism.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/PartitionLogic.v | 10 | True | True | documented |
| coq/thielemachine/coqproofs/PhaseThree.v | 3 | True | True | documented |
| coq/thielemachine/coqproofs/PhysicsEmbedding.v | 12 | True | True | documented |
| coq/thielemachine/coqproofs/QHelpers.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/QuantumAdmissibilityDeliverableB.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/QuantumAdmissibilityTsirelson.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/QuantumTheorems.v | 5 | True | True | documented |
| coq/thielemachine/coqproofs/RepresentationTheorem.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/SemanticBridge.v | 6 | True | True | documented |
| coq/thielemachine/coqproofs/Separation.v | 5 | True | True | documented |
| coq/thielemachine/coqproofs/Simulation.v | 5 | True | True | documented |
| coq/thielemachine/coqproofs/SpacelandComplete.v | 19 | True | True | documented |
| coq/thielemachine/coqproofs/SpacelandCore.v | 8 | True | True | documented |
| coq/thielemachine/coqproofs/SpacelandProved.v | 8 | True | True | documented |
| coq/thielemachine/coqproofs/SpecSound.v | 5 | True | True | documented |
| coq/thielemachine/coqproofs/SpectralApproximation.v | 22 | True | True | documented |
| coq/thielemachine/coqproofs/StructuredInstances.v | 5 | True | True | documented |
| coq/thielemachine/coqproofs/Subsumption.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleFoundations.v | 3 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleKernelCausality.v | 9 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleMachine.v | 15 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleMachineConcrete.v | 20 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleMachineSig.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleProc.v | 19 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleProofCarryingReality.v | 2 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleSpaceland.v | 37 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleUnificationProtocol.v | 9 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleUnificationTensor.v | 8 | True | True | documented |
| coq/thielemachine/coqproofs/ThieleVMOpcodes.v | 18 | True | True | documented |
| coq/thielemachine/coqproofs/TsirelsonBoundBridge.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/UTMStaticCheck.v | 1 | True | True | documented |
| coq/thielemachine/coqproofs/WaveCheck.v | 4 | True | True | documented |
| coq/thielemachine/coqproofs/WaveEmbedding.v | 10 | True | True | documented |
| coq/thielemachine/verification/Admissibility.v | 5 | True | True | documented |
| coq/thielemachine/verification/BridgeDefinitions.v | 68 | True | True | documented |
| coq/thielemachine/verification/BridgeProof.v | 5 | True | True | documented |
| coq/thielemachine/verification/Deliverable_CHSHSeparation.v | 5 | True | True | documented |
| coq/thielemachine/verification/Deliverable_MuEntropyNBits.v | 20 | True | True | documented |
| coq/thielemachine/verification/Deliverable_MuEntropyOneBit.v | 4 | True | True | documented |
| coq/thielemachine/verification/Deliverable_SignalingLowerBound.v | 1 | True | True | documented |
| coq/thielemachine/verification/FullIsomorphism.v | 10 | True | True | documented |
| coq/thielemachine/verification/ObservationInterface.v | 8 | True | True | documented |
| ... 15 more proof-doc rows omitted | | | | |

Top uncovered production files (first 20):

| Production file |
|---|
| coq/Extraction.v |
| coq/MinimalExtraction.v |
| coq/bridge/Randomness_to_Kernel.v |
| coq/kernel/AlgebraicCoherence.v |
| coq/kernel/ArrowOfTimeSynthesis.v |
| coq/kernel/AssumptionBundle.v |
| coq/kernel/BornRule.v |
| coq/kernel/BornRuleFromSymmetry.v |
| coq/kernel/CHSH.v |
| coq/kernel/CHSHExtraction.v |
| coq/kernel/CausalSetAxioms.v |
| coq/kernel/Certification.v |
| coq/kernel/ClassicalBound.v |
| coq/kernel/Closure.v |
| coq/kernel/Composition.v |
| coq/kernel/ConeAlgebra.v |
| coq/kernel/ConeDerivation.v |
| coq/kernel/ConstantDerivationStrength.v |
| coq/kernel/CrossLayerManifest.v |
| coq/kernel/DerivedTime.v |

## Fragmented Correctness Diagnostics

- Proof gate PASS but test gate FAIL: verified statements are not yet sufficiently exercised against runtime surfaces.
- Production symbol coverage by tests is below strict target; dynamic paths are under-verified.

## Top 10 Highest-Impact Closure Tasks

| Rank | Task | Type | Estimated score gain | Details |
|---:|---|---|---:|---|
| 1 | Complete triad 'alpha_em' | close_partial_triad | 0.14 | missing=rtl present=coq,python |
| 2 | Complete triad 'base' | close_partial_triad | 0.14 | missing=rtl present=coq,python |
| 3 | Complete triad 'csr_cert_addr' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 4 | Complete triad 'csr_error' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 5 | Complete triad 'csr_status' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 6 | Complete triad 'err_chain' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 7 | Complete triad 'err_mu_mismatch' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 8 | Complete triad 'err_none' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 9 | Complete triad 'err_overflow' | close_partial_triad | 0.14 | missing=coq present=python,rtl |
| 10 | Complete triad 'err_unknown_op' | close_partial_triad | 0.14 | missing=coq present=python,rtl |

## Test File Verification Detail

| Test file | Layer | Symbols | Coverage edges | Covered prod files | Covered prod symbols | Status |
|---|---|---:|---:|---:|---:|---|
| thielecpu/hardware/testbench/partition_core_tb.v | rtl_tb | 25 | 1 | 1 | 1 | covered |
| thielecpu/hardware/testbench/thiele_cpu_engines_tb.v | rtl_tb | 51 | 1 | 1 | 1 | covered |
| thielecpu/hardware/testbench/thiele_cpu_genesis_compression_strict_tb.v | rtl_tb | 29 | 1 | 1 | 1 | covered |
| thielecpu/hardware/testbench/thiele_cpu_genesis_compression_tb.v | rtl_tb | 27 | 1 | 1 | 1 | covered |
| thielecpu/hardware/testbench/thiele_cpu_inverse_genesis_tb.v | rtl_tb | 27 | 1 | 1 | 1 | covered |
| thielecpu/hardware/testbench/thiele_cpu_tb.v | rtl_tb | 30 | 1 | 1 | 1 | covered |
| tests/test_even_factor.py | test | 3 | 2 | 1 | 1 | covered |
| thielecpu/hardware/testbench/mu_alu_tb.v | rtl_tb | 11 | 2 | 2 | 2 | covered |
| thielecpu/hardware/testbench/fuzz_harness_simple.v | rtl_tb | 26 | 3 | 3 | 3 | covered |
| coq/tests/verify_zero_admits.v | test | 5 | 6 | 4 | 6 | covered |
| tests/test_shor_demo.py | test | 8 | 9 | 3 | 4 | covered |
| coq/tests/TestNecessity.v | test | 20 | 10 | 2 | 8 | covered |
| tests/test_christoffel_flat_spacetime.py | test | 4 | 10 | 1 | 2 | covered |
| tests/test_emergent_geometry_proxies.py | test | 10 | 11 | 7 | 7 | covered |
| tests/test_coq_available.py | test | 4 | 12 | 9 | 9 | covered |
| tests/test_metric_diagnosis.py | test | 2 | 13 | 11 | 12 | covered |
| tests/test_metric_position_dependent.py | test | 1 | 13 | 11 | 12 | covered |
| tests/test_einstein_equation_empirical.py | test | 5 | 14 | 1 | 3 | covered |
| tests/test_einstein_nonvacuum_empirical.py | test | 2 | 14 | 11 | 13 | covered |
| tests/test_rsa_scaling.py | test | 5 | 14 | 3 | 3 | covered |
| tests/test_transition_logic.py | test | 8 | 16 | 4 | 7 | covered |
| tests/test_mu_gravity_physics_analysis.py | test | 7 | 18 | 5 | 6 | covered |
| tests/test_foundry_generated_surface.py | test | 6 | 20 | 10 | 13 | covered |
| tests/test_vm_cli_input_prompt.py | test | 5 | 22 | 13 | 15 | covered |
| tests/test_structure_period_finding.py | test | 10 | 25 | 9 | 10 | covered |
| tests/trs_conformance/test_vectors.py | test | 19 | 25 | 8 | 8 | covered |
| tests/test_axiom_geometric_calibration.py | test | 8 | 26 | 16 | 21 | covered |
| tests/test_certcheck.py | test | 6 | 27 | 4 | 7 | covered |
| tests/test_christoffel_corrected_metric.py | test | 4 | 27 | 18 | 21 | covered |
| tests/test_christoffel_v3_metric.py | test | 3 | 27 | 18 | 21 | covered |
| tests/test_mu_gravity_calibration_validator.py | test | 8 | 30 | 7 | 9 | covered |
| tests/test_mu_entropy_n_bits_certificate.py | test | 4 | 31 | 7 | 9 | covered |
| tests/test_gauss_bonnet_2d.py | test | 8 | 32 | 14 | 18 | covered |
| tests/test_mu_entropy_one_bit_certificate.py | test | 6 | 34 | 6 | 9 | covered |
| tests/test_rtl_mu_charging.py | test | 10 | 37 | 17 | 17 | covered |
| tests/test_actual_truth_simplified.py | test | 13 | 38 | 15 | 21 | covered |
| tests/test_period_oracle.py | test | 10 | 38 | 15 | 16 | covered |
| tests/test_utm_program_validation.py | test | 12 | 39 | 8 | 9 | covered |
| tests/test_partition_rsa_factorization.py | test | 8 | 40 | 17 | 18 | covered |
| tests/test_real_angles_from_metric.py | test | 10 | 40 | 18 | 25 | covered |
| tests/test_chsh_manifold.py | test | 22 | 41 | 13 | 17 | covered |
| tests/test_phase3_bad_graph.py | test | 22 | 41 | 8 | 8 | covered |
| tests/test_vm_cli_c_and_stdin.py | test | 6 | 41 | 17 | 19 | covered |
| tests/test_einstein_vacuum_empirical.py | test | 9 | 47 | 19 | 23 | covered |
| tests/test_opcode_isomorphism.py | test | 11 | 47 | 15 | 16 | covered |
| tests/test_2d_mesh_creation.py | test | 6 | 50 | 14 | 22 | covered |
| tests/test_openfpga_flow.py | test | 14 | 50 | 21 | 25 | covered |
| tests/test_phase4_null_hypothesis.py | test | 17 | 52 | 8 | 16 | covered |
| tests/test_discrete_topology.py | test | 12 | 53 | 14 | 20 | covered |
| tests/test_fine_structure.py | test | 12 | 53 | 15 | 20 | covered |
| tests/test_opcode_alignment.py | test | 11 | 56 | 19 | 20 | covered |
| tests/alignment/test_mu_alignment.py | test | 16 | 59 | 21 | 27 | covered |
| tests/test_c_rand_randomness_verifier.py | test | 13 | 59 | 5 | 10 | covered |
| tests/test_c_causal_causal_verifier.py | test | 13 | 61 | 7 | 11 | covered |
| tests/test_c_entropy_entropy2_verifier.py | test | 13 | 61 | 7 | 11 | covered |
| tests/test_c1_physics_divergence_verifier.py | test | 20 | 62 | 14 | 19 | covered |
| scripts/test_16_instructions_tdd.py | test | 4 | 63 | 25 | 32 | covered |
| tests/test_phase1_long_run.py | test | 20 | 64 | 13 | 20 | covered |
| tests/test_advantage_benchmarks.py | test | 39 | 65 | 5 | 5 | covered |
| tests/test_nofi_pyexec_nonforgeability.py | test | 6 | 65 | 30 | 37 | covered |
| tests/test_c_tomo_tomography_verifier.py | test | 13 | 67 | 8 | 12 | covered |
| tests/test_coq_bridge_coverage_links.py | test | 17 | 71 | 37 | 42 | covered |
| tests/test_three_layer_isomorphism_fuzz.py | test | 15 | 74 | 18 | 28 | covered |
| tests/test_nofi_semantic_structure_event.py | test | 8 | 76 | 33 | 43 | covered |
| tests/test_geometric_factorization_claim.py | test | 13 | 83 | 22 | 31 | covered |
| tests/test_mu_signaling_lower_bound.py | test | 7 | 85 | 20 | 29 | covered |
| tests/test_mu.py | test | 5 | 86 | 28 | 39 | covered |
| tests/test_axiom_source_normalization.py | test | 13 | 90 | 22 | 33 | covered |
| tests/test_equivalence_bundle.py | test | 18 | 91 | 40 | 41 | covered |
| tests/test_christoffel_empirical.py | test | 9 | 93 | 19 | 22 | covered |
| tests/test_find_actual_truth.py | test | 15 | 100 | 24 | 34 | covered |
| tests/test_topology_curvature_bridge.py | test | 15 | 103 | 22 | 30 | covered |
| tests/test_full_stack_geometric_factorization.py | test | 16 | 104 | 27 | 34 | covered |
| tests/test_dialogue_of_the_one.py | test | 20 | 105 | 21 | 29 | covered |
| tests/test_pnew_topology_change.py | test | 16 | 110 | 17 | 22 | covered |
| tests/test_axiom_horizon_cycle.py | test | 14 | 112 | 21 | 30 | covered |
| tests/test_stress_energy_pnew.py | test | 21 | 118 | 35 | 46 | covered |
| tests/test_properties.py | test | 25 | 122 | 22 | 29 | covered |
| tests/test_observational_no_signaling.py | test | 8 | 124 | 19 | 29 | covered |
| tests/test_security_monitor.py | test | 13 | 129 | 29 | 37 | covered |
| tests/test_quantitative_nofreeinsight.py | test | 25 | 135 | 6 | 12 | covered |
| tests/test_mu_gravity_axioms.py | test | 16 | 138 | 27 | 39 | covered |
| tests/test_connectivity_enforcement.py | test | 23 | 151 | 35 | 40 | covered |
| tests/test_refinement.py | test | 23 | 168 | 27 | 39 | covered |
| scripts/test_three_layer_isomorphism.py | test | 17 | 170 | 38 | 54 | covered |
| tests/trs_conformance/test_trs10.py | test | 36 | 170 | 22 | 31 | covered |
| tests/test_crypto_isomorphism.py | test | 21 | 171 | 31 | 51 | covered |
| tests/test_mu_profiler_universality.py | test | 39 | 174 | 16 | 24 | covered |
| tests/test_canonical_hash_golden.py | test | 30 | 190 | 11 | 24 | covered |
| tests/test_cross_platform_isomorphism.py | test | 28 | 197 | 29 | 53 | covered |
| tests/test_predicate_parser.py | test | 31 | 213 | 13 | 17 | covered |
| tests/test_rtl_synthesis_gate.py | test | 30 | 240 | 44 | 51 | covered |
| tests/test_rtl_compute_isomorphism.py | test | 19 | 250 | 61 | 89 | covered |
| tests/test_alpha_refinement.py | test | 16 | 255 | 39 | 73 | covered |
| tests/test_verification_fuzz.py | test | 60 | 273 | 6 | 13 | covered |
| tests/test_random_program_fuzz.py | test | 50 | 277 | 66 | 87 | covered |
| tests/test_falsifiable_predictions.py | test | 39 | 284 | 27 | 40 | covered |
| tests/test_property_bisimulation.py | test | 39 | 296 | 61 | 90 | covered |
| tests/test_receipt_chain.py | test | 30 | 302 | 21 | 42 | covered |
| tests/test_cross_layer_comprehensive.py | test | 55 | 303 | 38 | 70 | covered |
| tests/test_three_layer_isomorphism_semantic.py | test | 43 | 306 | 10 | 31 | covered |
| tests/test_extraction_freshness.py | test | 25 | 310 | 49 | 60 | covered |
| tests/test_thesis_verify.py | test | 39 | 333 | 13 | 37 | covered |
| tests/test_mu_fixed.py | test | 42 | 353 | 11 | 44 | covered |
| tests/test_partition_boundary.py | test | 18 | 353 | 23 | 37 | covered |
| tests/test_discovery_enhancements.py | test | 39 | 355 | 24 | 40 | covered |
| tests/test_bisimulation.py | test | 47 | 366 | 67 | 110 | covered |
| tests/test_coq_compile_gate.py | test | 27 | 382 | 47 | 54 | covered |
| tests/test_isomorphism_violation_detection.py | test | 49 | 382 | 41 | 73 | covered |
| tests/test_efficient_discovery.py | test | 39 | 396 | 39 | 72 | covered |
| tests/test_partition_isomorphism_minimal.py | test | 32 | 468 | 67 | 108 | covered |
| tests/test_extracted_vm_runner.py | test | 22 | 469 | 60 | 75 | covered |
| tests/test_accelerator_cosim.py | test | 56 | 476 | 38 | 65 | covered |
| tests/test_verilog_cosim.py | test | 72 | 498 | 51 | 68 | covered |
| tests/test_structural_verifier.py | test | 56 | 520 | 33 | 59 | covered |
| tests/test_vm_encoding_validation.py | test | 16 | 520 | 25 | 41 | covered |
| tests/test_isomorphism_vm_vs_coq.py | test | 36 | 546 | 55 | 75 | covered |
| tests/test_benchmark_suite.py | test | 56 | 627 | 40 | 70 | covered |
| tests/alignment/test_comprehensive_alignment.py | test | 53 | 667 | 51 | 61 | covered |
| tests/test_bianchi_enforcement.py | test | 47 | 692 | 50 | 80 | covered |
| tests/test_three_layer_isomorphism.py | test | 48 | 706 | 75 | 142 | covered |
| tests/test_isomorphism_vm_vs_verilog.py | test | 43 | 736 | 68 | 106 | covered |
| tests/test_fuzz_isomorphism.py | test | 35 | 737 | 65 | 110 | covered |
| tests/test_mu_costs.py | test | 53 | 815 | 32 | 68 | covered |
| tests/test_qm_divergent.py | test | 78 | 864 | 31 | 72 | covered |
| tests/test_bisimulation_complete.py | test | 80 | 1372 | 75 | 124 | covered |
| tests/test_rigorous_isomorphism.py | test | 72 | 1491 | 72 | 119 | covered |

## Run-to-Run Progress Delta

- History snapshots tracked: **86**
- Score delta vs previous run: **+0.00**
- Triad delta vs previous run: **+0**
- Partial-triad delta vs previous run: **+0**
- Integrate-file delta vs previous run: **+0**

## Guided Next Actions (Priority Queue)

- Close partial triad 'partition' by adding missing layer(s): rtl [present: coq,python]
- Close partial triad 'opc_halt' by adding missing layer(s): coq [present: python,rtl]
- Close partial triad 'opc_mdlacc' by adding missing layer(s): coq [present: python,rtl]
- Close partial triad 'opc_pmerge' by adding missing layer(s): coq [present: python,rtl]
- Close partial triad 'opc_pnew' by adding missing layer(s): coq [present: python,rtl]
- Close partial triad 'opc_psplit' by adding missing layer(s): coq [present: python,rtl]
- Close partial triad 'alpha_em' by adding missing layer(s): rtl [present: coq,python]
- Close partial triad 'base' by adding missing layer(s): rtl [present: coq,python]

## Coverage by Layer

| Layer | Files | Symbols |
|---|---:|---:|
| coq | 305 | 6661 |
| python | 192 | 4816 |
| rtl | 8 | 599 |
| rtl_tb | 8 | 226 |
| test | 119 | 2651 |
| stale | 0 | 0 |

## Connectivity Legend

- **core**: connected to all three production layers
- **bridge**: connected to exactly two production layers
- **island**: connected only inside one layer
- **orphan**: no edges
- **duplicate**: same normalized symbol appears in multiple files of same layer
- **stale**: located under archive/disabled/exploratory/legacy markers
- **test_only**: symbol declared in test or testbench layer

## Symbol Classification

| Class | Count |
|---|---:|
| core | 4139 |
| bridge | 5199 |
| island | 18 |
| orphan | 216 |
| duplicate | 2504 |
| stale | 0 |
| test_only | 2877 |

## Edge Kinds

| Edge kind | Count |
|---|---:|
| cross_ref | 35810 |
| py_ref | 23241 |
| test_covers | 16944 |
| coq_ref | 16786 |
| cross_stem | 10300 |
| cross_transitive | 3267 |
| cross_name | 1578 |
| cross_norm | 832 |
| cross_opcode | 208 |
| rtl_ref | 23 |

## Layer Interaction Diagram

```mermaid
flowchart LR
  C["Coq\n6661 symbols"]
  P["Python/VM\n4816 symbols"]
  R["RTL/Verilog\n599 symbols"]
  T["Tests/TB\n2877 symbols"]
  C -->|17704| P
  P -->|16631| C
  C -->|4853| R
  R -->|4158| C
  P -->|4526| R
  R -->|4123| P
  T -. coverage .-> C
  T -. coverage .-> P
  T -. coverage .-> R
```

## File-Level Connection Diagram (Top Links)

```mermaid
flowchart LR
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N2["thielecpu/cross_layer_manifest.py"]
  N1 -->|197| N2
  N2["thielecpu/cross_layer_manifest.py"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N2 -->|194| N1
  N3["coq/kernel/MuGravity.v"]
  N4["thielecpu/hardware/rtl/cross_layer_defs.vh"]
  N3 -->|181| N4
  N5["thielecpu/vm.py"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N5 -->|170| N1
  N4["thielecpu/hardware/rtl/cross_layer_defs.vh"]
  N3["coq/kernel/MuGravity.v"]
  N4 -->|163| N3
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N5["thielecpu/vm.py"]
  N1 -->|151| N5
  N6["coq/thielemachine/coqproofs/BellInequality.v"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N6 -->|148| N1
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N7["thielecpu/receipts.py"]
  N1 -->|145| N7
  N7["thielecpu/receipts.py"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N7 -->|145| N1
  N6["coq/thielemachine/coqproofs/BellInequality.v"]
  N2["thielecpu/cross_layer_manifest.py"]
  N6 -->|140| N2
  N6["coq/thielemachine/coqproofs/BellInequality.v"]
  N8["experiments/qd3_literature_comparison.py"]
  N6 -->|117| N8
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N6["coq/thielemachine/coqproofs/BellInequality.v"]
  N1 -->|117| N6
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N9["coq/kernel/CrossLayerManifest.v"]
  N1 -->|116| N9
  N9["coq/kernel/CrossLayerManifest.v"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N9 -->|113| N1
  N8["experiments/qd3_literature_comparison.py"]
  N6["coq/thielemachine/coqproofs/BellInequality.v"]
  N8 -->|107| N6
  N10["thielecpu/dsl/executor.py"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N10 -->|103| N1
  N2["thielecpu/cross_layer_manifest.py"]
  N6["coq/thielemachine/coqproofs/BellInequality.v"]
  N2 -->|101| N6
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N10["thielecpu/dsl/executor.py"]
  N1 -->|97| N10
  N3["coq/kernel/MuGravity.v"]
  N11["scripts/validate_mu_gravity_calibration.py"]
  N3 -->|86| N11
  N12["coq/thielemachine/coqproofs/CoreSemantics.v"]
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N12 -->|86| N1
  N13["coq/kernel/VMState.v"]
  N4["thielecpu/hardware/rtl/cross_layer_defs.vh"]
  N13 -->|82| N4
  N1["thielecpu/hardware/rtl/thiele_cpu_unified.v"]
  N12["coq/thielemachine/coqproofs/CoreSemantics.v"]
  N1 -->|82| N12
```

## Triad Topology Diagram

```mermaid
flowchart TB
  C["Coq"]
  P["Python"]
  R["RTL"]
  T1["step"]
  C --> T1
  T1 --> P
  T1 --> R
  T2["state"]
  C --> T2
  T2 --> P
  T2 --> R
  T3["receipt"]
  C --> T3
  T3 --> P
  T3 --> R
  T4["hash"]
  C --> T4
  T4 --> P
  T4 --> R
  T5["mu_cost"]
  C --> T5
  T5 --> P
  T5 --> R
  T6["instr"]
  C --> T6
  T6 --> P
  T6 --> R
  T7["tsirelson_bound"]
  C --> T7
  T7 --> P
  T7 --> R
  T8["hash_state"]
  C --> T8
  T8 --> P
  T8 --> R
  T9["instruction"]
  C --> T9
  T9 --> P
  T9 --> R
  T10["muledger"]
  C --> T10
  T10 --> P
  T10 --> R
  T11["num_modules"]
  C --> T11
  T11 --> P
  T11 --> R
  T12["tau_mu"]
  C --> T12
  T12 --> P
  T12 --> R
  T13["compile"]
  C --> T13
  T13 --> P
  T13 --> R
  T14["decode"]
  C --> T14
  T14 --> P
  T14 --> R
  T15["energy"]
  C --> T15
  T15 --> P
  T15 --> R
  T16["mu_total"]
  C --> T16
  T16 --> P
  T16 --> R
  T17["q16_max"]
  C --> T17
  T17 --> P
  T17 --> R
  T18["q16_min"]
  C --> T18
  T18 --> P
  T18 --> R
```

## Cross-Layer Matrix

| From \ To | coq | python | rtl |
|---|---:|---:|---:|
| coq | 0 | 17704 | 4853 |
| python | 16631 | 0 | 4526 |
| rtl | 4158 | 4123 | 0 |

## Confirmed 3-Layer Triads (Isomorphic Name Clusters)

| Normalized | Coq | Python/VM | RTL/Verilog | Multiplicity (C/P/R) |
|---|---|---|---|---|
| step | step | step | step | 16/3/1 |
| state | State | State | state | 15/1/2 |
| receipt | Receipt | Receipt | receipt | 11/1/1 |
| hash | Hash | __hash__ | hash | 6/5/1 |
| mu_cost | mu_cost | mu_cost | mu_cost | 8/1/2 |
| instr | instr | Instr | instr | 6/1/2 |
| tsirelson_bound | tsirelson_bound | TSIRELSON_BOUND | TSIRELSON_BOUND | 5/3/1 |
| hash_state | hash_state | hash_state | hash_state | 3/3/1 |
| instruction | instruction | instruction | instruction | 4/1/2 |
| muledger | MuLedger | MuLedger | muledger | 3/3/1 |
| num_modules | NUM_MODULES | num_modules | num_modules | 1/3/3 |
| tau_mu | tau_mu | tau_mu | TAU_MU | 3/3/1 |
| compile | compile | compile | compile | 3/2/1 |
| decode | decode | decode | decode | 4/1/1 |
| energy | energy | _energy | energy | 2/3/1 |
| mu_total | mu_total | mu_total | mu_total | 4/1/1 |
| q16_max | Q16_MAX | Q16_MAX | Q16_MAX | 2/2/2 |
| q16_min | Q16_MIN | Q16_MIN | q16_min | 1/2/3 |
| region_size | region_size | REGION_SIZE | REGION_SIZE | 3/2/1 |
| chsh_value | chsh_value | chsh_value | chsh_value | 2/1/2 |
| compute_geometric_signature | compute_geometric_signature | compute_geometric_signature | compute_geometric_signature | 3/1/1 |
| encode | encode | encode | encode | 3/1/1 |
| entropy | Entropy | entropy | entropy | 3/1/1 |
| is_valid_partition | is_valid_partition | is_valid_partition | is_valid_partition | 3/1/1 |
| isomorphism | Isomorphism | ISOMORPHISM | isomorphism | 1/3/1 |
| log2_nat | log2_nat | log2_nat | log2_nat | 2/2/1 |
| neighbors | neighbors | neighbors | neighbors | 1/3/1 |
| op_lassert | op_lassert | _op_lassert | OP_LASSERT | 1/2/2 |
| op_pmerge | op_pmerge | _op_pmerge | OP_PMERGE | 1/2/2 |
| op_pnew | OP_PNEW | _op_pnew | OP_PNEW | 1/2/2 |
| op_psplit | op_psplit | _op_psplit | OP_PSPLIT | 1/2/2 |
| opcode | OPCODE | Opcode | opcode | 2/1/2 |
| problem | Problem | Problem | PROBLEM | 2/2/1 |
| q16_one | Q16_ONE | Q16_ONE | Q16_ONE | 2/1/2 |
| q16_shift | Q16_SHIFT | Q16_SHIFT | Q16_SHIFT | 2/1/2 |
| trivial_partition | trivial_partition | trivial_partition | trivial_partition | 3/1/1 |
| verify_receipt | verify_receipt | verify_receipt | verify_receipt | 2/2/1 |
| vmstate | VMState | VMState | VMState | 1/3/1 |
| charge_discovery | charge_discovery | charge_discovery | charge_discovery | 1/2/1 |
| check_lrat | check_lrat | check_lrat | CHECK_LRAT | 2/1/1 |
| check_model | check_model | check_model | check_model | 2/1/1 |
| chsh | chsh | chsh | CHSH | 2/1/1 |
| classical_bound | classical_bound | CLASSICAL_BOUND | classical_bound | 2/1/1 |
| clause_satisfied | clause_satisfied | _clause_satisfied | clause_satisfied | 2/1/1 |
| config | config | CONFIG | CONFIG | 2/1/1 |
| count_operators | count_operators | count_operators | count_operators | 1/2/1 |
| d_mu | d_mu | d_mu | D_MU | 2/1/1 |
| degree_partition | degree_partition | degree_partition | degree_partition | 2/1/1 |
| encode_instruction | encode_instruction | encode_instruction | encode_instruction | 1/2/1 |
| information_gain | information_gain | information_gain | INFORMATION_GAIN | 2/1/1 |
| mu_information | mu_information | mu_information | mu_information | 1/2/1 |
| op_chsh_trial | op_chsh_trial | OP_CHSH_TRIAL | OP_CHSH_TRIAL | 1/1/2 |
| op_emit | op_emit | OP_EMIT | OP_EMIT | 1/1/2 |
| op_halt | op_halt | OP_HALT | OP_HALT | 1/1/2 |
| op_ljoin | op_ljoin | OP_LJOIN | OP_LJOIN | 1/1/2 |
| op_mdlacc | op_mdlacc | OP_MDLACC | OP_MDLACC | 1/1/2 |
| op_oracle | op_oracle | OP_ORACLE | OP_ORACLE | 1/1/2 |
| op_pdiscover | op_pdiscover | OP_PDISCOVER | OP_PDISCOVER | 1/1/2 |
| op_pyexec | op_pyexec | OP_PYEXEC | OP_PYEXEC | 1/1/2 |
| op_reveal | op_reveal | OP_REVEAL | OP_REVEAL | 1/1/2 |
| op_xfer | op_xfer | OP_XFER | OP_XFER | 1/1/2 |
| op_xor_add | op_xor_add | OP_XOR_ADD | OP_XOR_ADD | 1/1/2 |
| op_xor_load | op_xor_load | OP_XOR_LOAD | OP_XOR_LOAD | 1/1/2 |
| op_xor_rank | op_xor_rank | OP_XOR_RANK | OP_XOR_RANK | 1/1/2 |
| op_xor_swap | op_xor_swap | OP_XOR_SWAP | OP_XOR_SWAP | 1/1/2 |
| opcode_chsh_trial | opcode_CHSH_TRIAL | OPCODE_CHSH_TRIAL | OPCODE_CHSH_TRIAL | 1/1/2 |
| opcode_emit | opcode_EMIT | OPCODE_EMIT | OPCODE_EMIT | 1/1/2 |
| opcode_halt | opcode_HALT | OPCODE_HALT | OPCODE_HALT | 1/1/2 |
| opcode_lassert | opcode_LASSERT | OPCODE_LASSERT | OPCODE_LASSERT | 1/1/2 |
| opcode_ljoin | opcode_LJOIN | OPCODE_LJOIN | OPCODE_LJOIN | 1/1/2 |
| opcode_mdlacc | opcode_MDLACC | OPCODE_MDLACC | OPCODE_MDLACC | 1/1/2 |
| opcode_oracle_halts | opcode_ORACLE_HALTS | OPCODE_ORACLE_HALTS | OPCODE_ORACLE_HALTS | 1/1/2 |
| opcode_pdiscover | opcode_PDISCOVER | OPCODE_PDISCOVER | OPCODE_PDISCOVER | 1/1/2 |
| opcode_pmerge | opcode_PMERGE | OPCODE_PMERGE | OPCODE_PMERGE | 1/1/2 |
| opcode_pnew | opcode_PNEW | OPCODE_PNEW | OPCODE_PNEW | 1/1/2 |
| opcode_psplit | opcode_PSPLIT | OPCODE_PSPLIT | OPCODE_PSPLIT | 1/1/2 |
| opcode_pyexec | opcode_PYEXEC | OPCODE_PYEXEC | OPCODE_PYEXEC | 1/1/2 |
| opcode_reveal | opcode_REVEAL | OPCODE_REVEAL | OPCODE_REVEAL | 1/1/2 |
| opcode_xfer | opcode_XFER | OPCODE_XFER | OPCODE_XFER | 1/1/2 |
| opcode_xor_add | opcode_XOR_ADD | OPCODE_XOR_ADD | OPCODE_XOR_ADD | 1/1/2 |
| opcode_xor_load | opcode_XOR_LOAD | OPCODE_XOR_LOAD | OPCODE_XOR_LOAD | 1/1/2 |
| opcode_xor_rank | opcode_XOR_RANK | OPCODE_XOR_RANK | OPCODE_XOR_RANK | 1/1/2 |
| opcode_xor_swap | opcode_XOR_SWAP | OPCODE_XOR_SWAP | OPCODE_XOR_SWAP | 1/1/2 |
| partitioncandidate | PartitionCandidate | PartitionCandidate | PartitionCandidate | 2/1/1 |
| total_mu_cost | total_mu_cost | total_mu_cost | TOTAL_MU_COST | 2/1/1 |
| trial | Trial | Trial | TRIAL | 2/1/1 |
| add_entry | add_entry | _add_entry | add_entry | 1/1/1 |
| angle_defect_curvature | angle_defect_curvature | angle_defect_curvature | ANGLE_DEFECT_CURVATURE | 1/1/1 |
| arithexpr | ArithExpr | ArithExpr | ArithExpr | 1/1/1 |
| axiom_bitlength | axiom_bitlength | axiom_bitlength | axiom_bitlength | 1/1/1 |
| bounded_run | bounded_run | bounded_run | bounded_run | 1/1/1 |
| cert_addr | cert_addr | CERT_ADDR | cert_addr | 1/1/1 |
| classify | classify | _classify | classify | 1/1/1 |
| compute_chsh | compute_chsh | compute_chsh | COMPUTE_CHSH | 1/1/1 |
| constraint | Constraint | Constraint | Constraint | 1/1/1 |
| count_atoms | count_atoms | count_atoms | count_atoms | 1/1/1 |
| count_vars | count_vars | count_vars | count_vars | 1/1/1 |
| count_vars_arith | count_vars_arith | count_vars_arith | count_vars_arith | 1/1/1 |
| cryptoreceipt | CryptoReceipt | CryptoReceipt | CryptoReceipt | 1/1/1 |
| cryptostepwitness | CryptoStepWitness | CryptoStepWitness | CryptoStepWitness | 1/1/1 |
| degree | degree | degree | degree | 1/1/1 |
| discover_partition | discover_partition | discover_partition | discover_partition | 1/1/1 |
| edge | Edge | Edge | Edge | 1/1/1 |
| encode_modules | encode_modules | encode_modules | encode_modules | 1/1/1 |
| encode_partition | encode_partition | encode_partition | encode_partition | 1/1/1 |
| encode_program | encode_program | encode_program | encode_program | 1/1/1 |
| encode_region | encode_region | encode_region | encode_region | 1/1/1 |
| encode_state | encode_state | encode_state | encode_state | 1/1/1 |
| execute_instruction | execute_instruction | _execute_instruction | EXECUTE_INSTRUCTION | 1/1/1 |
| expectation | expectation | expectation | expectation | 1/1/1 |
| graph | Graph | Graph | Graph | 1/1/1 |
| graph_lookup | graph_lookup | graph_lookup | graph_lookup | 1/1/1 |
| hash256 | hash256 | hash256 | hash256 | 1/1/1 |
| horizon_area | horizon_area | horizon_area | horizon_area | 1/1/1 |
| info | info | info | info | 1/1/1 |
| instruction_cost | instruction_cost | instruction_cost | instruction_cost | 1/1/1 |
| is_structured | is_structured | is_structured | is_structured | 1/1/1 |
| l_planck | l_planck | l_planck | l_planck | 1/1/1 |
| ledger_entries | ledger_entries | ledger_entries | LEDGER_ENTRIES | 1/1/1 |
| mask | mask | MASK | mask | 1/1/1 |
| module_exists | module_exists | module_exists | module_exists | 1/1/1 |
| module_neighbors | module_neighbors | _module_neighbors | module_neighbors | 1/1/1 |
| module_neighbors_adjacent | module_neighbors_adjacent | _module_neighbors_adjacent | module_neighbors_adjacent | 1/1/1 |
| module_neighbors_complete | module_neighbors_complete | _module_neighbors_complete | MODULE_NEIGHBORS_COMPLETE | 1/1/1 |
| module_structural_mass | module_structural_mass | _module_structural_mass | MODULE_STRUCTURAL_MASS | 1/1/1 |
| modulus | modulus | MODULUS | MODULUS | 1/1/1 |
| mu_bits | mu_bits | mu_bits | mu_bits | 1/1/1 |
| mu_cost_density | mu_cost_density | _mu_cost_density | mu_cost_density | 1/1/1 |
| mu_laplacian | mu_laplacian | mu_laplacian | mu_laplacian | 1/1/1 |
| mu_module_distance | mu_module_distance | _mu_module_distance | mu_module_distance | 1/1/1 |
| mucost | MuCost | MuCost | MUCOST | 1/1/1 |
| next_id | next_id | next_id | next_id | 1/1/1 |
| normalize_region | normalize_region | normalize_region | normalize_region | 1/1/1 |
| parse_assignment | parse_assignment | _parse_assignment | parse_assignment | 1/1/1 |
| partitiongraph | PartitionGraph | PartitionGraph | PartitionGraph | 1/1/1 |
| partitions | partitions | PARTITIONS | partitions | 1/1/1 |
| pr_box | pr_box | PR_BOX | PR_BOX | 1/1/1 |
| primitive | Primitive | Primitive | PRIMITIVE | 1/1/1 |
| problemclass | ProblemClass | ProblemClass | PROBLEMCLASS | 1/1/1 |
| problemtype | ProblemType | ProblemType | ProblemType | 1/1/1 |
| refine_partition | refine_partition | _refine_partition | REFINE_PARTITION | 1/1/1 |
| reversible | reversible | reversible | REVERSIBLE | 1/1/1 |
| run_program | run_program | _run_program | run_program | 1/1/1 |
| run_vm | run_vm | run_vm | run_vm | 1/1/1 |
| semantic_complexity_bits | semantic_complexity_bits | semantic_complexity_bits | semantic_complexity_bits | 1/1/1 |
| status | status | STATUS | status | 1/1/1 |
| stepresult | StepResult | StepResult | StepResult | 1/1/1 |
| stress_energy | stress_energy | stress_energy | stress_energy | 1/1/1 |
| sum_angles | sum_angles | _sum_angles | sum_angles | 1/1/1 |
| symbol | Symbol | Symbol | SYMBOL | 1/1/1 |
| triangle_angle | triangle_angle | _triangle_angle | triangle_angle | 1/1/1 |
| tsirelson | tsirelson | TSIRELSON | tsirelson | 1/1/1 |
| tsirelson_alice_outcome | tsirelson_alice_outcome | TSIRELSON_ALICE_OUTCOME | tsirelson_alice_outcome | 1/1/1 |
| tsirelson_alice_setting | tsirelson_alice_setting | TSIRELSON_ALICE_SETTING | tsirelson_alice_setting | 1/1/1 |
| tsirelson_bob_outcome | tsirelson_bob_outcome | TSIRELSON_BOB_OUTCOME | tsirelson_bob_outcome | 1/1/1 |
| tsirelson_bob_setting | tsirelson_bob_setting | TSIRELSON_BOB_SETTING | tsirelson_bob_setting | 1/1/1 |
| unit_conflict | unit_conflict | _unit_conflict | unit_conflict | 1/1/1 |
| variation_of_information | variation_of_information | _variation_of_information | variation_of_information | 1/1/1 |
| verify_crypto_receipt | verify_crypto_receipt | verify_crypto_receipt | verify_crypto_receipt | 1/1/1 |
| verify_hash_chain | verify_hash_chain | verify_hash_chain | verify_hash_chain | 1/1/1 |
| verify_rup_clause | verify_rup_clause | _verify_rup_clause | verify_rup_clause | 1/1/1 |
| vm_apply | vm_apply | vm_apply | VM_APPLY | 1/1/1 |
| vmaxiom | VMAxiom | VMAxiom | VMAxiom | 1/1/1 |
| witnessstate | WitnessState | WitnessState | WitnessState | 1/1/1 |

## Partial Triads (Missing One Layer)

| Normalized | Present layers | Missing layer(s) | Weight |
|---|---|---|---:|
| partition | coq,python | rtl | 17 |
| opc_halt | python,rtl | coq | 4 |
| opc_mdlacc | python,rtl | coq | 4 |
| opc_pmerge | python,rtl | coq | 4 |
| opc_pnew | python,rtl | coq | 4 |
| opc_psplit | python,rtl | coq | 4 |
| alpha_em | coq,python | rtl | 3 |
| base | coq,python | rtl | 3 |
| csr_cert_addr | python,rtl | coq | 3 |
| csr_error | python,rtl | coq | 3 |
| csr_status | python,rtl | coq | 3 |
| err_chain | python,rtl | coq | 3 |
| err_mu_mismatch | python,rtl | coq | 3 |
| err_none | python,rtl | coq | 3 |
| err_overflow | python,rtl | coq | 3 |
| err_unknown_op | python,rtl | coq | 3 |
| idle | python,rtl | coq | 3 |
| op_add | python,rtl | coq | 3 |
| op_claim_factor | python,rtl | coq | 3 |
| op_div | python,rtl | coq | 3 |
| op_info_gain | python,rtl | coq | 3 |
| op_log2 | python,rtl | coq | 3 |
| op_mul | python,rtl | coq | 3 |
| op_sub | python,rtl | coq | 3 |
| opc_pdiscover | python,rtl | coq | 3 |
| reg_q | coq,python | rtl | 3 |
| shift_big | coq,python | rtl | 3 |
| shift_small | coq,python | rtl | 3 |
| st_allowed | python,rtl | coq | 3 |
| st_checking | python,rtl | coq | 3 |
| st_denied_cost | python,rtl | coq | 3 |
| st_denied_iso | python,rtl | coq | 3 |
| st_receipt_ok | python,rtl | coq | 3 |
| add_const | python,rtl | coq | 2 |
| alu_ctx_mdlacc | python,rtl | coq | 2 |
| alu_ctx_oracle | python,rtl | coq | 2 |
| alu_ctx_pdiscover1 | python,rtl | coq | 2 |
| alu_ctx_pdiscover2 | python,rtl | coq | 2 |
| avg_threshold | python,rtl | coq | 2 |
| causal_query_op | coq,python | rtl | 2 |
| coarse_grain_op | coq,python | rtl | 2 |
| csr_info_gain | python,rtl | coq | 2 |
| csr_mdl_ops | python,rtl | coq | 2 |
| csr_partition_ops | python,rtl | coq | 2 |
| done | python,rtl | coq | 2 |
| enc_base | coq,python | rtl | 2 |
| kb_ln2_q16 | python,rtl | coq | 2 |
| max_mu | python,rtl | coq | 2 |
| meas_trial_op | coq,python | rtl | 2 |
| mem_size | coq,python | rtl | 2 |
| minus_one_fifth | python,rtl | coq | 2 |
| mixing | python,rtl | coq | 2 |
| mul_const | python,rtl | coq | 2 |
| one_half | python,rtl | coq | 2 |
| opc_emit | python,rtl | coq | 2 |
| opc_lassert | python,rtl | coq | 2 |
| opc_ljoin | python,rtl | coq | 2 |
| opc_pyexec | python,rtl | coq | 2 |
| opc_xfer | python,rtl | coq | 2 |
| opc_xor_add | python,rtl | coq | 2 |
| opc_xor_load | python,rtl | coq | 2 |
| opc_xor_rank | python,rtl | coq | 2 |
| opc_xor_swap | python,rtl | coq | 2 |
| pr_e_b0_b0 | coq,python | rtl | 2 |
| pr_e_b0_b1 | coq,python | rtl | 2 |
| pr_e_b1_b0 | coq,python | rtl | 2 |
| pr_e_b1_b1 | coq,python | rtl | 2 |
| pr_s | coq,python | rtl | 2 |
| psd5 | coq,python | rtl | 2 |
| psd_1 | coq,python | rtl | 2 |
| psd_2 | coq,python | rtl | 2 |
| psd_4 | coq,python | rtl | 2 |
| rand_trial_op | coq,python | rtl | 2 |
| reg_addr | coq,python | rtl | 2 |
| reg_count | coq,python | rtl | 2 |
| reg_head | coq,python | rtl | 2 |
| reg_move | coq,python | rtl | 2 |
| reg_pc | coq,python | rtl | 2 |
| reg_sym | coq,python | rtl | 2 |
| reg_temp1 | coq,python | rtl | 2 |
| reg_temp2 | coq,python | rtl | 2 |
| reg_write | coq,python | rtl | 2 |
| rules_start_addr | coq,python | rtl | 2 |
| shift_len | coq,python | rtl | 2 |
| st_done | python,rtl | coq | 2 |
| st_exec | python,rtl | coq | 2 |
| std_threshold | python,rtl | coq | 2 |
| tape_start_addr | coq,python | rtl | 2 |
| three_tenths | python,rtl | coq | 2 |
| two_tenths | python,rtl | coq | 2 |

## Integration Backlog (Action = integrate)

| File | Layer | Symbols | Core | Bridge | Island | Orphan | Connectivity |
|---|---|---:|---:|---:|---:|---:|---:|

## Duplicate Collisions

| File | Layer | Duplicate symbols |
|---|---|---:|
| coq/Extraction.v | coq | 5 |
| coq/MinimalExtraction.v | coq | 5 |
| coq/kernel/MuGravity_ConstructiveBridges.v | coq | 2 |
| coq/kernel/Test.v | coq | 1 |
| coq/thielemachine/coqproofs/HyperThiele_Halting.v | coq | 1 |
| coq/thielemachine/coqproofs/ListHelpers.v | coq | 4 |
| coq/thielemachine/verification/Deliverable_MuEntropy.v | coq | 2 |
| thielecpu/generated/__init__.py | python | 1 |
| coq/kernel/MuGravity_Emergence.v | coq | 6 |
| coq/thielemachine/verification/ThieleUniversalBridge.v | coq | 4 |
| coq/kernel/MuGravity_BridgeTheorems.v | coq | 4 |
| coq/thielemachine/verification/Deliverable_SignalingLowerBound.v | coq | 4 |
| coq/kernel/Closure.v | coq | 6 |
| coq/kernel/PhysicsClosure.v | coq | 3 |
| coq/kernel/TOEDecision.v | coq | 9 |
| coq/kernel_toe/Closure.v | coq | 6 |
| experiments/data_sources/__init__.py | python | 3 |
| experiments/run_isomorphism_suite.py | python | 7 |
| experiments/turbulence/__init__.py | python | 3 |
| thielecpu/_types.py | python | 2 |
| coq/kernel/AssumptionBundle.v | coq | 4 |
| coq/thielemachine/coqproofs/Confluence.v | coq | 3 |
| coq/nofi/MuChaitinTheory_Theorem.v | coq | 6 |
| experiments/phase_tunneling/gen_structured_3sat.py | python | 7 |
| coq/kernel/TOE.v | coq | 2 |
| coq/kernel_toe/TOE.v | coq | 2 |
| coq/nofi/NoFreeInsight_Theorem.v | coq | 2 |
| coq/thielemachine/coqproofs/Subsumption.v | coq | 2 |
| scripts/run_experiment.py | python | 4 |
| thielecpu/assemble.py | python | 4 |
| thielecpu/shor_cf.py | python | 8 |
| scripts/run_tests_with_timeout.py | python | 4 |
| thielecpu/program_sweep.py | python | 13 |
| experiments/phase_tunneling/run_experiments.py | python | 8 |
| coq/kernel/KernelThiele.v | coq | 3 |
| coq/thielemachine/coqproofs/ThieleProofCarryingReality.v | coq | 3 |
| experiments/phase_tunneling/gen_random_3sat.py | python | 3 |
| scripts/analyze_waveforms.py | python | 3 |
| experiments/measure_problem_classes.py | python | 15 |
| experiments/run_metadata.py | python | 9 |
| scripts/calculate_mu_cost.py | python | 7 |
| thielecpu/hardware/pyexec_bridge.py | python | 7 |
| coq/kernel/MinimalE.v | coq | 4 |
| coq/kernel/TsirelsonUniqueness.v | coq | 4 |
| coq/quantum_derivation/CollapseDetermination.v | coq | 6 |
| coq/thielemachine/coqproofs/ThieleUnificationDemo.v | coq | 4 |
| coq/thielemachine/verification/Deliverable_NoSignaling.v | coq | 4 |
| coq/thielemachine/verification/PredictionNoFI.v | coq | 1 |
| experiments/vm_integration_adapter.py | python | 7 |
| scripts/validate_isomorphism.py | python | 4 |
| coq/shor_primitives/Euclidean.v | coq | 4 |
| coq/kernel/MuChaitin.v | coq | 6 |
| coq/thielemachine/coqproofs/BellReceiptLocalBound.v | coq | 4 |
| coq/thielemachine/coqproofs/QuantumAdmissibilityDeliverableB.v | coq | 6 |
| scripts/resign_receipts.py | python | 6 |
| experiments/data_sources/zenodo.py | python | 14 |
| experiments/empirical_validation.py | python | 6 |
| tools/vm_wrapper.py | python | 8 |
| coq/kernel/Tier1Proofs.v | coq | 10 |
| experiments/ledger_io.py | python | 11 |
| experiments/thermodynamic_factoring.py | python | 12 |
| build/thiele_vm.py | python | 10 |
| coq/kernel/AlphaDerivation.v | coq | 4 |
| coq/kernel/HardAssumptions.v | coq | 7 |
| coq/kernel/TestTripartite.v | coq | 2 |
| coq/modular_proofs/Simulation.v | coq | 2 |
| coq/thielemachine/coqproofs/Embedding_TM.v | coq | 3 |
| coq/thielemachine/coqproofs/QuantumAdmissibilityTsirelson.v | coq | 3 |
| coq/thielemachine/coqproofs/TsirelsonBoundBridge.v | coq | 2 |
| coq/thielemachine/verification/Deliverable_CHSHSeparation.v | coq | 5 |
| demos/scripts/demo_isomorphism_cli.py | python | 6 |
| demos/scripts/solve_sudoku.py | python | 2 |
| demos/scripts/solve_tsp.py | python | 2 |
| experiments/data_sources/download.py | python | 14 |
| experiments/data_sources/dryad.py | python | 14 |
| experiments/data_sources/figshare.py | python | 14 |
| experiments/data_sources/osf.py | python | 15 |
| scripts/analyze_admits.py | python | 3 |
| scripts/check_pip_audit.py | python | 3 |
| scripts/final_validation.py | python | 3 |
| scripts/make_synthesizable.py | python | 2 |
| thielecpu/benchmarks/problem_families.py | python | 13 |
| thielecpu/cnf.py | python | 5 |
| thielecpu/logger.py | python | 5 |
| thielecpu/security_monitor.py | python | 11 |
| thielecpu/semantic_mu.py | python | 12 |
| verifier/c_tomography.py | python | 4 |
| verifier/physics_divergence.py | python | 5 |
| verifier/receipt_protocol.py | python | 5 |
| coq/kernel/BoxCHSH.v | coq | 13 |
| scripts/generate_heuristic_heatmaps.py | python | 13 |
| thielecpu/semantic_canonical.py | python | 13 |
| scripts/generate_proof_dependency_dag.py | python | 12 |
| scripts/verify_thiele_machine.py | python | 11 |
| thielecpu/period_finder.py | python | 9 |
| thielecpu/shor_oracle.py | python | 8 |
| coq/kernel/HardMathFactsProven.v | coq | 7 |
| experiments/turbulence/protocol.py | python | 12 |
| coq/thielemachine/coqproofs/Impossibility.v | coq | 6 |
| experiments/numbertheory_factoring.py | python | 7 |
| thielecpu/partition_factorization.py | python | 7 |
| coq/kernel/MasterSummary.v | coq | 3 |
| experiments/plot_utils.py | python | 5 |
| experiments/visualize_predictions.py | python | 2 |
| thielecpu/factoring.py | python | 2 |
| experiments/pdiscover_factoring.py | python | 11 |
| coq/kernel/TopologyCurvatureBridge.v | coq | 5 |
| coq/quantum_derivation/BornRuleUnique.v | coq | 5 |
| coq/thielemachine/coqproofs/ComputationIsomorphism.v | coq | 5 |
| experiments/run_einstein.py | python | 15 |
| scripts/generate_full_dashboard.py | python | 9 |
| thielecpu/certcheck.py | python | 9 |
| coq/thielemachine/coqproofs/RepresentationTheorem.v | coq | 2 |
| coq/thielemachine/verification/BridgeProof.v | coq | 4 |
| experiments/run_all_predictions.py | python | 4 |
| scripts/keys.py | python | 4 |
| scripts/run_logging_smoke.py | python | 5 |
| thielecpu/coq_bridge.py | python | 8 |
| verifier/c_causal.py | python | 4 |
| thielecpu/hardware/accel_cosim.py | python | 11 |
| thielecpu/hardware/cosim.py | python | 11 |
| coq/kernel/MuNecessity.v | coq | 6 |
| coq/nofi/MuChaitinTheory_Interface.v | coq | 7 |
| experiments/comprehensive_stress_test.py | python | 14 |
| coq/kernel/ConeDerivation.v | coq | 2 |
| coq/thielemachine/coqproofs/QHelpers.v | coq | 1 |
| coq/thielemachine/coqproofs/UTMStaticCheck.v | coq | 3 |
| experiments/observer_effect.py | python | 6 |
| experiments/summarize_partition_scaling.py | python | 15 |
| scripts/fetch_artifacts.py | python | 2 |
| thielecpu/geometric_oracle.py | python | 3 |
| thielecpu/memory.py | python | 6 |
| verifier/c_entropy2.py | python | 3 |
| verifier/c_randomness.py | python | 3 |
| demos/scripts/tsp_optimizer.py | python | 17 |
| experiments/complexity_gap.py | python | 11 |
| coq/kernel/StateSpaceCounting.v | coq | 8 |
| experiments/run_einstein_refined.py | python | 7 |
| thielecpu/pdiscover_factorization.py | python | 8 |
| demos/scripts/shor_on_thiele_demo.py | python | 10 |
| experiments/receipt_forgery.py | python | 10 |
| scripts/canonicalize_receipts.py | python | 9 |
| scripts/structural_heat_experiment.py | python | 10 |
| scripts/verify_receipt.py | python | 5 |
| thielecpu/audit_demo.py | python | 7 |
| coq/kernel/EinsteinEmergence.v | coq | 6 |
| demos/scripts/tsp_solver.py | python | 9 |
| experiments/data_sources/jhtdb.py | python | 8 |
| experiments/run_landauer.py | python | 15 |
| scripts/thermo_experiment.py | python | 13 |
| coq/bridge/Causal_to_Kernel.v | coq | 2 |
| coq/bridge/Entropy_to_Kernel.v | coq | 2 |
| coq/bridge/Randomness_to_Kernel.v | coq | 2 |
| coq/bridge/Tomography_to_Kernel.v | coq | 2 |
| coq/kernel/MinorConstraints.v | coq | 12 |
| coq/kernel/MuNoFreeInsightQuantitative.v | coq | 6 |
| coq/modular_proofs/Thiele_Basics.v | coq | 2 |
| coq/shor_primitives/PeriodFinding.v | coq | 3 |
| experiments/derive_c_numerical.py | python | 6 |
| experiments/run_entropy.py | python | 16 |
| experiments/vm_instrumentation.py | python | 2 |
| thielecpu/bell_semantics.py | python | 6 |
| thielecpu/genesis_wave.py | python | 14 |
| coq/thielemachine/verification/RandomnessNoFI.v | coq | 10 |
| coq/thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v | coq | 4 |
| experiments/run_cwd.py | python | 14 |
| coq/thielemachine/coqproofs/AlgebraicLaws.v | coq | 5 |
| experiments/logic_only_factoring.py | python | 5 |
| experiments/revelation_factoring.py | python | 5 |
| scripts/halting_trap.py | python | 5 |
| thielecpu/geometric_factorization.py | python | 5 |
| demos/scripts/graph_coloring_demo.py | python | 18 |
| coq/kernel/NoFreeInsight.v | coq | 8 |
| thielecpu/dsl/verify.py | python | 14 |
| coq/kernel/BornRuleFromSymmetry.v | coq | 3 |
| coq/kernel/Composition.v | coq | 5 |
| coq/kernel/DerivedTime.v | coq | 3 |
| coq/kernel/TsirelsonComputation.v | coq | 3 |
| coq/physics_exploration/EmergentSpacetime.v | coq | 1 |
| coq/quantum_derivation/ProjectionFromPartitions.v | coq | 3 |
| scripts/generate_impact_deliverable.py | python | 3 |
| scripts/thiele_energy.py | python | 6 |
| thielecpu/benchmarks/solvers.py | python | 12 |
| coq/kernel/Certification.v | coq | 13 |
| experiments/partition_collapse_test.py | python | 10 |
| coq/kernel/StressEnergyDynamics.v | coq | 7 |
| thielecpu/genesis.py | python | 14 |
| tools/dialogue_engine.py | python | 4 |
| experiments/phi_vs_mu_correlation.py | python | 11 |
| coq/kernel/MuGeometry.v | coq | 4 |
| coq/kernel/RiemannTensor4D.v | coq | 4 |
| coq/thielemachine/coqproofs/HardwareVMHarness.v | coq | 3 |
| experiments/energy_meter.py | python | 4 |
| experiments/red_team.py | python | 8 |
| experiments/use_ledger_landauer.py | python | 4 |
| scripts/check_print_assumptions.py | python | 3 |
| scripts/genesis.py | python | 3 |
| experiments/proofpack.py | python | 12 |
| coq/kernel/MuInformation.v | coq | 5 |
| experiments/graph_isomorphism_partitions.py | python | 14 |
| ... 291 more duplicate rows omitted | | |

## Strict Safe-Removal Candidates

A file appears here only if ALL conditions hold:
1) path contains remove-safe markers (unused/deprecated/legacy/dead/tmp/disabled)
2) every symbol has zero incident edges
3) no Coq proof declarations involved

| File | Layer | Symbols | Reason |
|---|---|---:|---|
| *(none)* | | | strict filter found no safe removals |

## Archive/Legacy Files

| File | Symbols |
|---|---:|

## Highest Isolation Files

| File | Layer | Symbols | Orphan | Island | Connectivity |
|---|---|---:|---:|---:|---:|
| thielecpu/vm.py | python | 224 | 12 | 3 | 77% |
| demos/scripts/tsp_optimizer.py | python | 66 | 11 | 0 | 58% |
| coq/kernel/ConstructivePSD.v | coq | 45 | 4 | 2 | 82% |
| experiments/run_isomorphism_suite.py | python | 16 | 5 | 0 | 25% |
| thielecpu/primitives.py | python | 44 | 2 | 3 | 70% |
| coq/kernel/AlphaDerivation.v | coq | 16 | 3 | 1 | 50% |
| experiments/visualize_predictions.py | python | 13 | 4 | 0 | 54% |
| thielecpu/factoring.py | python | 13 | 4 | 0 | 54% |
| coq/kernel/TOEDecision.v | coq | 16 | 3 | 0 | 25% |
| coq/thielemachine/verification/PredictionNoFI.v | coq | 7 | 3 | 0 | 43% |
| experiments/turbulence/protocol.py | python | 32 | 3 | 0 | 53% |
| coq/kernel/MasterSummary.v | coq | 13 | 3 | 0 | 54% |
| scripts/run_logging_smoke.py | python | 18 | 3 | 0 | 56% |
| coq/kernel/EinsteinEmergence.v | coq | 22 | 3 | 0 | 59% |
| coq/thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v | coq | 18 | 3 | 0 | 61% |
| tools/dialogue_engine.py | python | 19 | 3 | 0 | 63% |
| thielecpu/discovery.py | python | 64 | 3 | 0 | 67% |
| scripts/thiele_catnet_integration.py | python | 63 | 3 | 0 | 71% |
| coq/theory/ArchTheorem.v | coq | 29 | 3 | 0 | 79% |
| coq/theory/Universality.v | coq | 36 | 3 | 0 | 81% |
| coq/thielemachine/verification/BridgeDefinitions.v | coq | 89 | 3 | 0 | 94% |
| coq/thielemachine/coqproofs/Confluence.v | coq | 7 | 2 | 0 | 29% |
| scripts/run_experiment.py | python | 9 | 2 | 0 | 33% |
| coq/quantum_derivation/CollapseDetermination.v | coq | 14 | 2 | 0 | 43% |
| coq/thielemachine/coqproofs/BellReceiptLocalBound.v | coq | 11 | 2 | 0 | 46% |
| thielecpu/security_monitor.py | python | 26 | 2 | 0 | 50% |
| coq/thielemachine/coqproofs/RepresentationTheorem.v | coq | 9 | 2 | 0 | 56% |
| coq/thielemachine/coqproofs/QHelpers.v | coq | 7 | 2 | 0 | 57% |
| scripts/verify_receipt.py | python | 17 | 2 | 0 | 59% |
| scripts/thermo_experiment.py | python | 37 | 1 | 1 | 60% |
| coq/kernel/MinorConstraints.v | coq | 35 | 2 | 0 | 60% |
| coq/physics_exploration/EmergentSpacetime.v | coq | 8 | 2 | 0 | 62% |
| coq/thielemachine/verification/Prediction.v | coq | 18 | 2 | 0 | 67% |
| scripts/stress_test_verifier.py | python | 30 | 1 | 1 | 67% |
| tools/mu_profiler.py | python | 41 | 2 | 0 | 71% |

## Embedded Machine Snapshot

```json
{
  "generated_at": "2026-02-19T20:21:50.823431+00:00",
  "summary": {
    "symbols": 14953,
    "edges": 108989,
    "triads": 164,
    "partial_triads": 90,
    "classifications": {
      "duplicate": 2504,
      "bridge": 5199,
      "core": 4139,
      "orphan": 216,
      "island": 18,
      "test_only": 2877
    },
    "integrate_files": 0,
    "remove_safe_files": 0
  },
  "isomorphism_metrics": {
    "isomorphism_score": 87.55,
    "core_bridge_ratio": 0.9986,
    "triad_completion_ratio": 0.6457,
    "directional_coverage_ratio": 1.0,
    "integrate_file_ratio": 0.0,
    "prod_symbol_count": 8861,
    "core_bridge_count": 8849,
    "triad_count": 164,
    "partial_triad_count": 90,
    "active_direction_count": 6,
    "direction_count": 6,
    "integrate_file_count": 0,
    "prod_file_count": 505
  },
  "trend_delta": {
    "has_previous": true,
    "score_delta": 0.0,
    "triad_delta": 0,
    "partial_triad_delta": 0,
    "integrate_file_delta": 0,
    "core_bridge_ratio_delta": 0.0
  },
  "proof_quality_metrics": {
    "proof_accuracy": 100.0,
    "proof_quality_grade": "A+",
    "gate_rating": "PASS",
    "high": 0,
    "medium": 0,
    "low": 0,
    "scanned_files": 308,
    "weighted_penalty": 0.0,
    "strict_pass": true
  },
  "test_verification_metrics": {
    "test_gate": "FAIL",
    "strict_pass": false,
    "test_file_count": 127,
    "isolated_test_file_count": 0,
    "prod_symbol_coverage_ratio": 0.0744,
    "prod_file_coverage_ratio": 0.4653,
    "covered_prod_symbol_count": 899,
    "prod_symbol_count": 12076,
    "covered_prod_file_count": 235,
    "prod_file_count": 505,
    "uncovered_prod_files_top": [
      "coq/Extraction.v",
      "coq/MinimalExtraction.v",
      "coq/bridge/Randomness_to_Kernel.v",
      "coq/kernel/AlgebraicCoherence.v",
      "coq/kernel/ArrowOfTimeSynthesis.v",
      "coq/kernel/AssumptionBundle.v",
      "coq/kernel/BornRule.v",
      "coq/kernel/BornRuleFromSymmetry.v",
      "coq/kernel/CHSH.v",
      "coq/kernel/CHSHExtraction.v",
      "coq/kernel/CausalSetAxioms.v",
      "coq/kernel/Certification.v",
      "coq/kernel/ClassicalBound.v",
      "coq/kernel/Closure.v",
      "coq/kernel/Composition.v",
      "coq/kernel/ConeAlgebra.v",
      "coq/kernel/ConeDerivation.v",
      "coq/kernel/ConstantDerivationStrength.v",
      "coq/kernel/CrossLayerManifest.v",
      "coq/kernel/DerivedTime.v",
      "coq/kernel/EinsteinEmergence.v",
      "coq/kernel/EntropyImpossibility.v",
      "coq/kernel/FourDSimplicialComplex.v",
      "coq/kernel/GeodesicCompleteness.v",
      "coq/kernel/HardAssumptions.v",
      "coq/kernel/HardMathFactsProven.v",
      "coq/kernel/HardwareBisimulation.v",
      "coq/kernel/InformationCausality.v",
      "coq/kernel/InverseSquareLaw.v",
      "coq/kernel/KernelBenchmarks.v"
    ]
  },
  "priority_plan": [
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'alpha_em'",
      "details": "missing=rtl present=coq,python",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'base'",
      "details": "missing=rtl present=coq,python",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'csr_cert_addr'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'csr_error'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'csr_status'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'err_chain'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'err_mu_mismatch'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'err_none'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'err_overflow'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    },
    {
      "type": "close_partial_triad",
      "priority": 1,
      "task": "Complete triad 'err_unknown_op'",
      "details": "missing=coq present=python,rtl",
      "estimated_score_gain": 0.14
    }
  ],
  "fragmented_correctness_flags": [
    "Proof gate PASS but test gate FAIL: verified statements are not yet sufficiently exercised against runtime surfaces.",
    "Production symbol coverage by tests is below strict target; dynamic paths are under-verified."
  ],
  "latex_coverage_metrics": {
    "tex_file_count": 20,
    "kernel_proof_symbol_count": 1046,
    "kernel_proof_symbol_mentioned_count": 1042,
    "kernel_proof_latex_coverage_ratio": 0.9962,
    "kernel_proof_missing_top": [
      "alpha_fundamental",
      "p_13_equals_101",
      "p_14_equals_135",
      "p_15_equals_176"
    ],
    "triad_norm_count": 164,
    "triad_norm_mentioned_count": 93,
    "triad_norm_latex_coverage_ratio": 0.5671
  },
  "proof_documentation_metrics": {
    "proof_file_count": 275,
    "total_proof_count": 2582,
    "documented_proof_count": 2579,
    "per_proof_doc_ratio": 0.9988,
    "fully_documented_file_count": 274,
    "fully_documented_file_ratio": 0.9964,
    "proof_files_with_readme_count": 275,
    "proof_files_with_comment_blocks_count": 275,
    "proof_files_documented_count": 274,
    "proof_files_with_readme_ratio": 1.0,
    "proof_files_with_comment_ratio": 1.0,
    "proof_files_documented_ratio": 0.9964,
    "missing_readme_proof_files_top": [],
    "underdocumented_proof_files_top": [
      "coq/kernel/AlphaDerivation.v"
    ]
  },
  "definition_of_done": {
    "status": "NOT_COMPLETED",
    "completed": false,
    "checks": [
      {
        "name": "isomorphism_score",
        "actual": 87.55,
        "comparator": ">=",
        "threshold": 100.0,
        "passed": false
      },
      {
        "name": "triad_completion_ratio",
        "actual": 0.6457,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "core_bridge_ratio",
        "actual": 0.9986,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "test_prod_symbol_coverage_ratio",
        "actual": 0.0744,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "test_prod_file_coverage_ratio",
        "actual": 0.4653,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "isolated_test_files",
        "actual": 0.0,
        "comparator": "<=",
        "threshold": 0.0,
        "passed": true
      },
      {
        "name": "per_proof_doc_ratio",
        "actual": 0.9988,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "proof_files_with_readme_ratio",
        "actual": 1.0,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": true
      },
      {
        "name": "kernel_proof_latex_coverage_ratio",
        "actual": 0.9962,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "coq_compile_pass",
        "actual": 1.0,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": true
      },
      {
        "name": "extraction_freshness_pass",
        "actual": 1.0,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": true
      },
      {
        "name": "rtl_synthesis_pass",
        "actual": 1.0,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": true
      },
      {
        "name": "inquisitor_strict_pass",
        "actual": 1.0,
        "comparator": "==",
        "threshold": 1.0,
        "passed": true
      }
    ],
    "unmet_check_count": 7,
    "unmet_checks": [
      {
        "name": "isomorphism_score",
        "actual": 87.55,
        "comparator": ">=",
        "threshold": 100.0,
        "passed": false
      },
      {
        "name": "triad_completion_ratio",
        "actual": 0.6457,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "core_bridge_ratio",
        "actual": 0.9986,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "test_prod_symbol_coverage_ratio",
        "actual": 0.0744,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "test_prod_file_coverage_ratio",
        "actual": 0.4653,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "per_proof_doc_ratio",
        "actual": 0.9988,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      },
      {
        "name": "kernel_proof_latex_coverage_ratio",
        "actual": 0.9962,
        "comparator": ">=",
        "threshold": 1.0,
        "passed": false
      }
    ]
  },
  "toolchain_gates": {
    "coq_compile": {
      "ran": true,
      "pass": true,
      "returncode": 0,
      "stderr_tail": "",
      "total_v_files": 311,
      "total_vo_files": 311,
      "compile_ratio": 1.0,
      "admitted_count": 0
    },
    "extraction_freshness": {
      "ran": true,
      "pass": true,
      "files": {
        "Extraction.v": {
          "exists": true,
          "nonempty": true,
          "symbols_ok": true,
          "missing_symbols": [],
          "fresh": true,
          "pass": true
        },
        "MinimalExtraction.v": {
          "exists": true,
          "nonempty": true,
          "symbols_ok": true,
          "missing_symbols": [],
          "fresh": true,
          "pass": true
        }
      }
    },
    "rtl_synthesis": {
      "ran": true,
      "pass": true,
      "mode": "full_synthesis",
      "returncode": 0,
      "cell_count": 2,
      "top_module_present": true,
      "modules_found": [
        "energy_calc",
        "tsirelson_checker",
        "hash256",
        "clz8",
        "mu_core",
        "receipt_integrity_checker",
        "mu_alu",
        "thiele_cpu"
      ],
      "stderr_tail": ""
    },
    "cosim": {
      "ran": true,
      "pass": true,
      "returncode": 0,
      "has_fail_marker": false,
      "stdout_tail": "0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0,\n    0\n  ],\n  \"modules\": [\n    {\"id\": -1, \"region\": []}\n  ]\n}\n/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_tb.v:297: $finish called at 345000 (1ps)\n"
    }
  },
  "inquisitor": {
    "status": "PASS",
    "returncode": 0,
    "report_path": "INQUISITOR_REPORT.md"
  },
  "cross_layer_matrix": {
    "coq->python": 17704,
    "coq->rtl": 4853,
    "python->coq": 16631,
    "python->rtl": 4526,
    "rtl->coq": 4158,
    "rtl->python": 4123
  },
  "top_cross_file_links": [
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "thielecpu/cross_layer_manifest.py",
      "weight": 197
    },
    {
      "src": "thielecpu/cross_layer_manifest.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 194
    },
    {
      "src": "coq/kernel/MuGravity.v",
      "dst": "thielecpu/hardware/rtl/cross_layer_defs.vh",
      "weight": 181
    },
    {
      "src": "thielecpu/vm.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 170
    },
    {
      "src": "thielecpu/hardware/rtl/cross_layer_defs.vh",
      "dst": "coq/kernel/MuGravity.v",
      "weight": 163
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "thielecpu/vm.py",
      "weight": 151
    },
    {
      "src": "coq/thielemachine/coqproofs/BellInequality.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 148
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "thielecpu/receipts.py",
      "weight": 145
    },
    {
      "src": "thielecpu/receipts.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 145
    },
    {
      "src": "coq/thielemachine/coqproofs/BellInequality.v",
      "dst": "thielecpu/cross_layer_manifest.py",
      "weight": 140
    },
    {
      "src": "coq/thielemachine/coqproofs/BellInequality.v",
      "dst": "experiments/qd3_literature_comparison.py",
      "weight": 117
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "coq/thielemachine/coqproofs/BellInequality.v",
      "weight": 117
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "coq/kernel/CrossLayerManifest.v",
      "weight": 116
    },
    {
      "src": "coq/kernel/CrossLayerManifest.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 113
    },
    {
      "src": "experiments/qd3_literature_comparison.py",
      "dst": "coq/thielemachine/coqproofs/BellInequality.v",
      "weight": 107
    },
    {
      "src": "thielecpu/dsl/executor.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 103
    },
    {
      "src": "thielecpu/cross_layer_manifest.py",
      "dst": "coq/thielemachine/coqproofs/BellInequality.v",
      "weight": 101
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "thielecpu/dsl/executor.py",
      "weight": 97
    },
    {
      "src": "coq/kernel/MuGravity.v",
      "dst": "scripts/validate_mu_gravity_calibration.py",
      "weight": 86
    },
    {
      "src": "coq/thielemachine/coqproofs/CoreSemantics.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 86
    },
    {
      "src": "coq/kernel/VMState.v",
      "dst": "thielecpu/hardware/rtl/cross_layer_defs.vh",
      "weight": 82
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "coq/thielemachine/coqproofs/CoreSemantics.v",
      "weight": 82
    },
    {
      "src": "thielecpu/hardware/rtl/cross_layer_defs.vh",
      "dst": "coq/kernel/VMState.v",
      "weight": 81
    },
    {
      "src": "coq/kernel/SemanticMuCost.v",
      "dst": "thielecpu/semantic_mu_coq_isomorphic.py",
      "weight": 78
    },
    {
      "src": "thielecpu/semantic_mu_coq_isomorphic.py",
      "dst": "coq/kernel/SemanticMuCost.v",
      "weight": 78
    },
    {
      "src": "coq/thielemachine/verification/BridgeDefinitions.v",
      "dst": "thielecpu/cross_layer_manifest.py",
      "weight": 77
    },
    {
      "src": "scripts/validate_mu_gravity_calibration.py",
      "dst": "coq/kernel/MuGravity.v",
      "weight": 77
    },
    {
      "src": "coq/thielemachine/coqproofs/ThieleSpaceland.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 76
    },
    {
      "src": "thielecpu/cross_layer_manifest.py",
      "dst": "coq/thielemachine/verification/BridgeDefinitions.v",
      "weight": 72
    },
    {
      "src": "thielecpu/mu_fixed.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 70
    },
    {
      "src": "coq/kernel/VMEncoding.v",
      "dst": "thielecpu/hardware/rtl/cross_layer_defs.vh",
      "weight": 69
    },
    {
      "src": "coq/kernel/ReceiptIntegrity.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 68
    },
    {
      "src": "coq/isomorphism/coqproofs/Universe.v",
      "dst": "scripts/inquisitor.py",
      "weight": 62
    },
    {
      "src": "scripts/inquisitor.py",
      "dst": "coq/isomorphism/coqproofs/Universe.v",
      "weight": 62
    },
    {
      "src": "coq/kernel/VMEncoding.v",
      "dst": "thielecpu/isa.py",
      "weight": 61
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "coq/kernel/ReceiptIntegrity.v",
      "weight": 61
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "coq/thielemachine/coqproofs/ThieleSpaceland.v",
      "weight": 61
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "thielecpu/mu_fixed.py",
      "weight": 61
    },
    {
      "src": "coq/kernel/CrossLayerManifest.v",
      "dst": "thielecpu/cross_layer_manifest.py",
      "weight": 60
    },
    {
      "src": "experiments/mu_audited_bell_test.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 60
    },
    {
      "src": "thielecpu/cross_layer_manifest.py",
      "dst": "coq/kernel/CrossLayerManifest.v",
      "weight": 60
    },
    {
      "src": "thielecpu/hardware/rtl/cross_layer_defs.vh",
      "dst": "coq/kernel/VMEncoding.v",
      "weight": 60
    },
    {
      "src": "thielecpu/hardware/rtl/receipt_integrity_checker.v",
      "dst": "thielecpu/receipts.py",
      "weight": 60
    },
    {
      "src": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "dst": "experiments/mu_audited_bell_test.py",
      "weight": 60
    },
    {
      "src": "thielecpu/receipts.py",
      "dst": "thielecpu/hardware/rtl/receipt_integrity_checker.v",
      "weight": 60
    },
    {
      "src": "coq/thielemachine/coqproofs/AbstractLTS.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 59
    },
    {
      "src": "coq/thielemachine/coqproofs/ThieleMachine.v",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 59
    },
    {
      "src": "thielecpu/thesis_verify.py",
      "dst": "thielecpu/hardware/rtl/thiele_cpu_unified.v",
      "weight": 59
    },
    {
      "src": "coq/thielemachine/coqproofs/Oracle.v",
      "dst": "thielecpu/cross_layer_manifest.py",
      "weight": 57
    },
    {
      "src": "thielecpu/cross_layer_manifest.py",
      "dst": "thielecpu/hardware/rtl/partition_core.v",
      "weight": 57
    }
  ]
}
```

## Companion Outputs

Atlas run also writes machine-readable analysis and diagram sources under `artifacts/atlas/`.

| Exported path |
|---|
| artifacts/atlas/atlas_definition_of_done.json |
| artifacts/atlas/atlas_edges.csv |
| artifacts/atlas/atlas_file_metrics.csv |
| artifacts/atlas/atlas_inquisitor_summary.json |
| artifacts/atlas/atlas_latex_coverage.json |
| artifacts/atlas/atlas_partial_triads.csv |
| artifacts/atlas/atlas_priority_plan.json |
| artifacts/atlas/atlas_proof_documentation.csv |
| artifacts/atlas/atlas_summary.json |
| artifacts/atlas/atlas_symbols.csv |
| artifacts/atlas/atlas_test_verification.csv |
| artifacts/atlas/atlas_triads.csv |
| artifacts/atlas/file_action_breakdown.mmd |
| artifacts/atlas/layer_flow.mmd |
| artifacts/atlas/python_rtl_focus.mmd |
| artifacts/atlas/symbol_class_breakdown.mmd |
| artifacts/atlas/top_file_links.mmd |
| artifacts/atlas/triad_topology.mmd |

Rendered image files:

| Image path |
|---|
| artifacts/atlas/cross_layer_matrix.png |
| artifacts/atlas/file_action_breakdown.png |
| artifacts/atlas/layer_symbol_counts.png |
| artifacts/atlas/symbol_class_breakdown.png |

## Notes

- This atlas is intentionally integration-biased and conservative on removals.
- Use triads + top file links as the primary map for cross-layer completion work.
- Keep Coq-only or proof-heavy files in the pipeline unless independently deprecated.
