# Kernel

**Mission:** Core structural constraint proofs, optimization bounds, and bisimulation results for the Thiele Machine kernel.

## Structure

- `AlgebraicCoherence.v` - Algebraic Coherence - Defines: Correlators; Key results: Qabs_bound, chsh_bound_4, symmetric_tsirelson_bound (+14 more)
- `ArrowOfTimeSynthesis.v` - Arrow Of Time Synthesis - Defines: ThermodynamicTransition, ArrowOfTime; Key results: instr_cost_nonneg, empty_trace_zero_cost, trace_cost_additive (+12 more)
- `AssumptionBundle.v` - Assumption Bundle - Defines: HardMathFacts
- `BornRule.v` - Born Rule - Key results: probs_nonneg, probs_sum_to_one, pure_state_zero_cost (+7 more)
- `BornRuleFromSymmetry.v` - Born Rule From Symmetry - Key results: born_identity_eigenstate, born_identity_normalization, born_identity_tensor (+1 more)
- `BoxCHSH.v` - Box CHSH - Key results: E_expand, normalized_E_bound, Qabs_triangle_4 (+4 more)
- `CHSH.v` - CHSH - Defines: Trial, LocalStrategy; Key results: is_bit_true_cases, count_setting_trials_of_local, expectation_trials_of_local (+1 more)
- `CHSHExtraction.v` - CHSHExtraction - Defines: CHSHTrial; Key results: trial_partition, filter_length_le, Qabs_4_triangle (+3 more)
- `CausalSetAxioms.v` - Causal Set Axioms - Defines: CausalSetAxioms; Key results: causal_reflexive, causal_transitive, graph_module_ids_finite (+8 more)
- `CertCheck.v` - Cert Check - Defines: dimacs_cnf, lrat_step
- `Certification.v` - Certification - Key results: tsirelson_bound_q_sq_gt_8, reveal_charges_mu, chsh_trials_non_forgeable (+7 more)
- `ClassicalBound.v` - Classical Bound - Key results: classical_program_mu_zero, classical_bound_achieved
- `Closure.v` - Closure - Key results: KernelMaximalClosure
- `Composition.v` - Composition - Key results: pr_kernel_nonneg, pr_kernel_normalized, pr_compose_not_coherent (+2 more)
- `ConeAlgebra.v` - Cone Algebra - Defines: case, case; Key results: cone_composition, cone_monotonic, cone_idempotent (+11 more)
- `ConeDerivation.v` - Cone Derivation - Defines: case; Key results: Cone_Structure_Unique, cone_monotone
- `ConstantDerivationStrength.v` - Constant Derivation Strength - Defines: SubstrateParams, DerivationLevel, OptimalSubstrate (+1 more); Key results: ln2_positive, derived_c_positive, derived_E_bit_positive (+11 more)
- `ConstantUnification.v` - Constant Unification - Key results: tau_mu_pos, d_mu_pos, k_B_pos (+3 more)
- `ConstructivePSD.v` - Constructive PSD - Key results: sum_fin5_unfold, quad5_unfold, Rabs_le_inv (+20 more)
- `Definitions.v` - Definitions - Definitions: Trace, Weight, weight_empty (+9 more)
- `DerivedTime.v` - Derived Time - Key results: mdlacc_preserves_all_regions, Time_Is_Not_Fundamental, trace_equiv_region_stutter
- `DiscreteGaussBonnet.v` - Discrete Gauss Bonnet - Key results: equilateral_triangle_angle, three_equilateral_angles_sum_pi, sum_of_vertex_degrees_equals_3F (+5 more)
- `DiscreteTopology.v` - Discrete Topology - Key results: empty_graph_euler_char_0, V_nonneg, E_nonneg (+15 more)
- `EinsteinEmergence.v` - Einstein Emergence - Key results: coupling_constant_positive, information_creates_curvature, curvature_quantization (+2 more)
- `EinsteinEquations4D.v` - Einstein Equations4D - Key results: einstein_field_equations, computational_scale_positive, metric_diagonal_proportional_to_mass (+35 more)
- `EntropyImpossibility.v` - Entropy Impossibility - Key results: tweak_regs_region_equiv, tweak_regs_injective, region_equiv_class_infinite (+1 more)
- `FalsifiablePrediction.v` - Falsifiable Prediction - Defines: ExperimentalTrial; Key results: mu_monotonic_step, mu_cost_additive
- `FiniteInformation.v` - Finite Information - Key results: existsb_spec, nodup_list_NoDup, in_nodup_list (+14 more)
- `FourDSimplicialComplex.v` - Four DSimplicial Complex - Defines: Simplex4D, Cell3D, Face2D (+2 more); Key results: empty_4d_complex_euler_zero, single_vertex_euler_one, extracted_edges_well_formed (+8 more)
- `GeodesicCompleteness.v` - Geodesic Completeness - Key results: execution_cost_equals_distance, geodesic_inequality, every_execution_is_geodesic (+5 more)
- `HardAssumptions.v` - Hard Assumptions - Key results: symmetric_coherence_bound, tsirelson_from_algebraic_coherence
- `HardMathFactsProven.v` - Hard Math Facts Proven - Defines: HardMathFactsCorrected; Key results: norm_E_bound_proven, valid_S_4_proven, local_S_2_proven (+4 more)
- `HardwareBisimulation.v` - Hardware Bisimulation - Defines: HardwareState, PythonState; Key results: hw_initial_correspondence, hw_step_preserves_pc, hw_step_preserves_mu (+7 more)
- `InformationCausality.v` - Information Causality - Defines: ICScenario, MuScenario; Key results: information_causality_is_mu_cost, ic_zero_communication_bound, ic_zero_implies_tsirelson (+10 more)
- `InverseSquareLaw.v` - Inverse Square Law - Defines: graph_path; Key results: adjacent_symmetric, graph_path_snoc, graph_path_symmetric (+9 more)
- `Kernel.v` - Kernel - Defines: state, direction, instruction
- `KernelBenchmarks.v` - Kernel Benchmarks - Defines: BenchmarkPNEW, BenchmarkPSPLIT; Key results: pnew_linear, psplit_linear, pmerge_linear_worst (+2 more)
- `KernelNoether.v` - Kernel Noether - Key results: z_action_identity, z_action_composition, z_action_inverse (+9 more)
- `KernelPhysics.v` - Kernel Physics - Key results: obs_equiv_refl, obs_equiv_sym, obs_equiv_trans (+20 more)
- `KernelTM.v` - Kernel TM - Defines: TuringMachine; Key results: tm_is_turing_complete
- `KernelThiele.v` - Kernel Thiele - Definitions: step_thiele, run_thiele
- `L2Derivation.v` - L2Derivation - Key results: sqrt2_gt_1, inv_sqrt2_lt_1, l1_no_continuous_group (+6 more)
- `LocalInfoLoss.v` - Local Info Loss - Defines: exec_trace; Key results: pnew_module_count_change, psplit_module_count_change, pmerge_module_count_change (+5 more)
- `Locality.v` - Locality - Key results: wf_graph_lookup_implies_below, all_ids_below_lookup_implies_below, graph_pnew_preserves_lookup (+11 more)
- `LorentzNotForced.v` - Lorentz Not Forced - Key results: Lorentz_Not_Forced, causal_cone_stutter, Cone_Symmetry_Underdetermined
- `LorentzSignature.v` - Lorentz Signature - Key results: signature_temporal, signature_spatial_1, signature_spatial_2 (+14 more)
- `MasterSummary.v` - Master Summary - Key results: master_tsirelson, master_quantum_foundations, master_non_circularity (+2 more)
- `MetricFromMuCosts.v` - Metric From Mu Costs - Key results: mu_tensor_metric_nonneg, zero_tensor_gives_zero_metric, edge_length_nonneg (+10 more)
- `MinimalE.v` - Minimal E - Key results: Qopp_0_le, minimal_normalized_E_bound
- `MinorConstraints.v` - Minor Constraints - Key results: sum_n_le, sum_n_scale, sum_n_plus (+9 more)
- `ModularObservation.v` - Modular Observation - Key results: full_observe_eq_implies_agrees, nodup_local_NoDup, in_nodup_local (+1 more)
- `MuChaitin.v` - Mu Chaitin - Key results: mu_info_nat_ge_from_mu_total, supra_cert_implies_mu_info_nat_lower_bound, supra_cert_implies_mu_bounds_cert_payload
- `MuComplexity.v` - Mu Complexity - Defines: Trace; Key results: mu_compositional, mu_monotonic, mu_subadditive (+2 more)
- `MuCostDerivation.v` - Mu Cost Derivation - Defines: StateSpaceChange, LASSERTChange, ReversibleOp; Key results: log2_subtraction_valid, state_reduction_is_erasure, lassert_cost_determined (+7 more)
- `MuCostModel.v` - Mu Cost Model - Key results: partition_ops_mu_free, reveal_costs_one, nth_error_none_propagates (+4 more)
- `MuGeometry.v` - Mu Geometry - Key results: mu_distance_nonneg, mu_distance_refl, mu_distance_sym (+2 more)
- `MuGravity.v` - Mu Gravity - Defines: calibration_safe_instruction; Key results: ln2_pos, mu_module_distance_nonneg, mu_module_distance_refl (+103 more)
- `MuGravity_BridgeTheorems.v` - Mu Gravity Bridge Theorems - Key results: curvature_bridge_interface
- `MuGravity_ConstructiveBridges.v` - Mu Gravity Constructive Bridges
- `MuGravity_Definitions.v` - Mu Gravity Definitions - Key results: residual_rank_zero_exactly_residual_zero
- `MuGravity_Emergence.v` - Mu Gravity Emergence - Key results: full_gravity_path_scheduler_contract
- `MuInformation.v` - Mu Information - Key results: mu_info_z_vm_apply, run_vm_mu_total_decomposes, mu_info_z_run_vm_is_ledger_sum
- `MuInitiality.v` - Mu Initiality - Defines: reachable, trace_reaches, CostFunctional; Key results: init_state_mu_zero, exec_trace_correct, trace_reaches_exec (+11 more)
- `MuLedgerConservation.v` - Mu Ledger Conservation - Key results: bounded_run_head, vm_apply_mu, ledger_conserved_tail (+15 more)
- `MuNecessity.v` - Mu Necessity - Key results: mu_is_landauer_valid, landauer_valid_bounds_total_loss, mu_tight_for_pmerge (+1 more)
- `MuNoFreeInsightQuantitative.v` - Mu No Free Insight Quantitative - Key results: vm_exec_mu_monotone, trace_run_mu_monotone, cert_preserved_if_not_cert_setterb (+3 more)
- `NPAMomentMatrix.v` - NPAMoment Matrix - Defines: NPAOperator, CHSHCorrelations, NPAMomentMatrix; Key results: npa_diagonal_one, npa_E00_position, npa_E01_position (+4 more)
- `NPMuCostBound.v` - NPMu Cost Bound - Defines: VerificationInstance, PredicateStrength, MuCostGap (+1 more); Key results: verification_requires_structure, stronger_predicate_costs_more, sorted_zero_cost (+6 more)
- `NoArbitrage.v` - No Arbitrage - Defines: COp; Key results: Potential_from_MinCost, asymmetric_additive, asymmetric_cost_pos (+2 more)
- `NoCloning.v` - No Cloning - Defines: CloningOperation, DeletionOperation; Key results: no_cloning_from_conservation, approximate_cloning_bound, symmetric_optimal_cloning (+2 more)
- `NoCloningFromMuMonotonicity.v` - No Cloning From Mu Monotonicity - Defines: MachineCloneOp, MachineDeleteOp; Key results: no_cloning_mu_monotonicity, approximate_cloning_zero_cost, no_deletion_mu
- `NoFreeInsight.v` - No Free Insight - Key results: trace_run_run_vm, no_free_insight_general, strengthening_requires_structure_addition
- `NoGo.v` - No Go - Key results: w_scale_empty, w_scale_sequential, w_scale_disjoint_commutes (+8 more)
- `NoGoSensitivity.v` - No Go Sensitivity - Key results: w_pow_empty, w_pow_sequential, w_pow_multiplicative (+1 more)
- `NonCircularityAudit.v` - Non Circularity Audit - Defines: mu_cost_rule; Key results: mu_cost_is_physics_free, chsh_formula_physics_free, classical_bound_is_derived_not_assumed (+12 more)
- `ObserverDerivation.v` - Observer Derivation - Defines: with, Observer; Key results: observer_le_refl, observer_le_trans, obs_equiv_implies_region_equiv (+4 more)
- `OracleImpossibility.v` - Oracle Impossibility - Key results: anti_diagonal_differs, no_row_is_antidiagonal, halting_undecidable (+4 more)
- `PDISCOVERIntegration.v` - PDISCOVERIntegration - Defines: GeometricSignature, StructureVerdict; Key results: pdiscern_deterministic, structured_implies_low_variation, proves (+4 more)
- `PNEWTopologyChange.v` - PNEWTopology Change - Key results: graph_add_module_increases_F, pnew_fresh_increases_F, pnew_fresh_triangle_changes_topology (+4 more)
- `POVMBridge.v` - POVMBridge - Defines: MeasurementOutcome, CompleteMeasurement, POVMBridgeProperties; Key results: fold_left_add_ge, fold_left_add_mono, measurement_cost_bounds_info (+5 more)
- `PartitionSeparation.v` - Partition Separation - Defines: TMTransition, ThieleTransition; Key results: initial_module_count, graph_add_module_increases_count, partition_based_separation (+1 more)
- `Persistence.v` - Persistence - Defines: FuelState, fuel_step, game_stepC (+1 more); Key results: in_pnew_choices_0, uniform_bet_zero_when_choices_exceed_fuel, Uniform_Strategy_Dies
- `PhysicsClosure.v` - Physics Closure - Key results: Physics_Closure
- `PoissonEquation.v` - Poisson Equation - Defines: graph_connected; Key results: laplacian_constant_zero, fold_left_sum_scale, laplacian_potential_equals_half_laplacian_mass (+6 more)
- `ProbabilityImpossibility.v` - Probability Impossibility - Key results: w_len_compositional, w_len2_compositional, Born_Rule_Unique_Fails_Without_More_Structure
- `ProperSubsumption.v` - Proper Subsumption - Defines: Tape, Direction, TM_Transition (+3 more); Key results: thiele_simulates_turing_gen, thiele_simulates_turing, thiele_run_mu_bound (+2 more)
- `Purification.v` - Purification - Key results: pure_is_mixed, purity_nonneg, mixed_has_deficit (+3 more)
- `PythonBisimulation.v` - Python Bisimulation - Defines: PythonState; Key results: initial_correspondence, step_preserves_pc, step_preserves_mu (+1 more)
- `QuantumBound.v` - Quantum Bound - Key results: quantum_tsirelson_bound, csr_set_err_preserves_cert_addr, csr_set_status_preserves_cert_addr (+5 more)
- `QuantumEquivalence.v` - Quantum Equivalence - Defines: AbstractCorrelation; Key results: quantum_implies_mu_zero, mu_zero_implies_quantum, quantum_requires_no_revelation (+7 more)
- `ReceiptCore.v` - Receipt Core - Defines: Receipt; Key results: decodes_to_refl
- `ReceiptIntegrity.v` - Receipt Integrity - Defines: Receipt; Key results: mu_in_range_b_correct, receipt_mu_consistent_b_correct, receipt_mu_in_range_b_correct (+14 more)
- `RevelationRequirement.v` - Revelation Requirement - Key results: uses_revelation_decidable, supra_cert_implies_structure_addition_in_run, non_cert_setter_preserves_cert (+1 more)
- `RiemannTensor4D.v` - Riemann Tensor4D - Definitions: metric_component, discrete_derivative, christoffel (+4 more)
- `SemanticComplexityIsomorphism.v` - Semantic Complexity Isomorphism - Key results: python_log2_matches_coq, python_semantic_complexity_matches_coq, verilog_enforces_monotonicity (+6 more)
- `SemanticMuCost.v` - Semantic Mu Cost - Defines: ConstraintVar, ArithExpr, CompOp (+2 more); Key results: log2_nat_ge_1_of_ge_2, semantic_complexity_nonzero
- `SemidefiniteProgramming.v` - Semidefinite Programming - Key results: PSD_diagonal_nonneg, I_is_PSD, schur_2x2_criterion (+2 more)
- `SimulationProof.v` - Simulation Proof - Defines: vm_exec; Key results: states_related_implies_encoding, states_related_implies_pc, states_related_implies_mu (+26 more)
- `SpacetimeEmergence.v` - Spacetime Emergence - Defines: reaches, exec_trace; Key results: reaches_one, reaches_trans, step_rel_no_signaling (+20 more)
- `StateSpaceCounting.v` - State Space Counting - Key results: lassert_cost_bounds_formula_length, mu_increase_bounds_axiom_bits, nofreeinsight_quantitative_lower_bound (+4 more)
- `StressEnergyDynamics.v` - Stress Energy Dynamics - Defines: execution_trace; Key results: pnew_increases_mu_cost, pnew_trace_length_correlates, stress_energy_drives_pnew_frequency (+2 more)
- `Subsumption.v` - Subsumption - Key results: witness_is_sighted, witness_not_turing, main_subsumption
- `TOE.v` - TOE - Key results: KernelTOE_FinalOutcome
- `TOEDecision.v` - TOEDecision - Key results: KernelNoGoForTOE_Decision, Physics_Requires_Extra_Structure, Kernel_Physics_Closure (+1 more)
- `Test.v` - Test
- `TestTripartite.v` - Test Tripartite - Definitions: pr_box, has_valid_extension
- `ThreeLayerIsomorphism.v` - Three Layer Isomorphism - Defines: WireSpec, FullWireSpec; Key results: vm_apply_total, instruction_exhaustive, advance_state_mu (+16 more)
- `Tier1Proofs.v` - Tier1Proofs - Key results: bit_sign_0, bit_sign_1, E_expand (+3 more)
- `TopologyCurvatureBridge.v` - Topology Curvature Bridge - Key results: delta_chi_implies_delta_curvature, local_curvature_changes_sum_to_global
- `TsirelsonComputation.v` - Tsirelson Computation - Key results: four_inv_sqrt2
- `TsirelsonDerivation.v` - Tsirelson Derivation - Key results: nonzero_mu_implies_exceeds_bound, Qgt_minus_pos, tsirelson_from_correlation_mu_zero (+1 more)
- `TsirelsonFromAlgebra.v` - Tsirelson From Algebra - Key results: chsh_gap_is_sum_of_squares, sq_nonneg_local, cauchy_schwarz_chsh (+8 more)
- `TsirelsonGeneral.v` - Tsirelson General - Key results: sq_nonneg, cauchy_schwarz_chsh, tsirelson_from_row_bounds (+9 more)
- `TsirelsonLowerBound.v` - Tsirelson Lower Bound - Key results: tsirelson_program_mu_zero, tsirelson_lower_bound
- `TsirelsonUniqueness.v` - Tsirelson Uniqueness - Key results: mu_zero_algebraic_bound
- `TsirelsonUpperBound.v` - Tsirelson Upper Bound - Key results: mu_zero_no_lassert_from_pc, mu_zero_no_lassert, mu_zero_no_ljoin_from_pc (+14 more)
- `Unitarity.v` - Unitarity - Defines: Evolution; Key results: trace_preserved_by_normalization, unitary_preserves_positivity, nonunitary_requires_mu (+3 more)
- `VMEncoding.v` - VMEncoding - Key results: decode_nat_correct, decode_bool_correct, decode_ascii_correct (+12 more)
- `VMState.v` - VMState - Defines: ModuleState, PartitionGraph, CSRState (+1 more); Key results: normalize_region_nodup, normalize_region_idempotent, empty_graph_well_formed (+29 more)
- `VMStep.v` - VMStep - Defines: lassert_certificate, vm_instruction, vm_step
- `ValidCorrelation.v` - Valid Correlation - Key results: bell_math_deterministic

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `AlgebraicCoherence.v` | 0 | ✅ |
| `ArrowOfTimeSynthesis.v` | 0 | ✅ |
| `AssumptionBundle.v` | 0 | ✅ |
| `BornRule.v` | 0 | ✅ |
| `BornRuleFromSymmetry.v` | 0 | ✅ |
| `BoxCHSH.v` | 0 | ✅ |
| `CHSH.v` | 0 | ✅ |
| `CHSHExtraction.v` | 0 | ✅ |
| `CausalSetAxioms.v` | 0 | ✅ |
| `CertCheck.v` | 0 | ✅ |
| `Certification.v` | 0 | ✅ |
| `ClassicalBound.v` | 0 | ✅ |
| `Closure.v` | 0 | ✅ |
| `Composition.v` | 0 | ✅ |
| `ConeAlgebra.v` | 0 | ✅ |
| `ConeDerivation.v` | 0 | ✅ |
| `ConstantDerivationStrength.v` | 0 | ✅ |
| `ConstantUnification.v` | 0 | ✅ |
| `ConstructivePSD.v` | 0 | ✅ |
| `Definitions.v` | 0 | ✅ |
| `DerivedTime.v` | 0 | ✅ |
| `DiscreteGaussBonnet.v` | 0 | ✅ |
| `DiscreteTopology.v` | 0 | ✅ |
| `EinsteinEmergence.v` | 0 | ✅ |
| `EinsteinEquations4D.v` | 0 | ✅ |
| `EntropyImpossibility.v` | 0 | ✅ |
| `FalsifiablePrediction.v` | 0 | ✅ |
| `FiniteInformation.v` | 0 | ✅ |
| `FourDSimplicialComplex.v` | 0 | ✅ |
| `GeodesicCompleteness.v` | 0 | ✅ |
| `HardAssumptions.v` | 0 | ✅ |
| `HardMathFactsProven.v` | 0 | ✅ |
| `HardwareBisimulation.v` | 0 | ✅ |
| `InformationCausality.v` | 0 | ✅ |
| `InverseSquareLaw.v` | 0 | ✅ |
| `Kernel.v` | 0 | ✅ |
| `KernelBenchmarks.v` | 0 | ✅ |
| `KernelNoether.v` | 0 | ✅ |
| `KernelPhysics.v` | 0 | ✅ |
| `KernelTM.v` | 0 | ✅ |
| `KernelThiele.v` | 0 | ✅ |
| `L2Derivation.v` | 0 | ✅ |
| `LocalInfoLoss.v` | 0 | ✅ |
| `Locality.v` | 0 | ✅ |
| `LorentzNotForced.v` | 0 | ✅ |
| `LorentzSignature.v` | 0 | ✅ |
| `MasterSummary.v` | 0 | ✅ |
| `MetricFromMuCosts.v` | 0 | ✅ |
| `MinimalE.v` | 0 | ✅ |
| `MinorConstraints.v` | 0 | ✅ |
| `ModularObservation.v` | 0 | ✅ |
| `MuChaitin.v` | 0 | ✅ |
| `MuComplexity.v` | 0 | ✅ |
| `MuCostDerivation.v` | 0 | ✅ |
| `MuCostModel.v` | 0 | ✅ |
| `MuGeometry.v` | 0 | ✅ |
| `MuGravity.v` | 0 | ✅ |
| `MuGravity_BridgeTheorems.v` | 0 | ✅ |
| `MuGravity_ConstructiveBridges.v` | 0 | ✅ |
| `MuGravity_Definitions.v` | 0 | ✅ |
| `MuGravity_Emergence.v` | 0 | ✅ |
| `MuInformation.v` | 0 | ✅ |
| `MuInitiality.v` | 0 | ✅ |
| `MuLedgerConservation.v` | 0 | ✅ |
| `MuNecessity.v` | 0 | ✅ |
| `MuNoFreeInsightQuantitative.v` | 0 | ✅ |
| `NPAMomentMatrix.v` | 0 | ✅ |
| `NPMuCostBound.v` | 0 | ✅ |
| `NoArbitrage.v` | 0 | ✅ |
| `NoCloning.v` | 0 | ✅ |
| `NoCloningFromMuMonotonicity.v` | 0 | ✅ |
| `NoFreeInsight.v` | 0 | ✅ |
| `NoGo.v` | 0 | ✅ |
| `NoGoSensitivity.v` | 0 | ✅ |
| `NonCircularityAudit.v` | 0 | ✅ |
| `ObserverDerivation.v` | 0 | ✅ |
| `OracleImpossibility.v` | 0 | ✅ |
| `PDISCOVERIntegration.v` | 0 | ✅ |
| `PNEWTopologyChange.v` | 0 | ✅ |
| `POVMBridge.v` | 0 | ✅ |
| `PartitionSeparation.v` | 0 | ✅ |
| `Persistence.v` | 0 | ✅ |
| `PhysicsClosure.v` | 0 | ✅ |
| `PoissonEquation.v` | 0 | ✅ |
| `ProbabilityImpossibility.v` | 0 | ✅ |
| `ProperSubsumption.v` | 0 | ✅ |
| `Purification.v` | 0 | ✅ |
| `PythonBisimulation.v` | 0 | ✅ |
| `QuantumBound.v` | 0 | ✅ |
| `QuantumEquivalence.v` | 0 | ✅ |
| `ReceiptCore.v` | 0 | ✅ |
| `ReceiptIntegrity.v` | 0 | ✅ |
| `RevelationRequirement.v` | 0 | ✅ |
| `RiemannTensor4D.v` | 0 | ✅ |
| `SemanticComplexityIsomorphism.v` | 0 | ✅ |
| `SemanticMuCost.v` | 0 | ✅ |
| `SemidefiniteProgramming.v` | 0 | ✅ |
| `SimulationProof.v` | 0 | ✅ |
| `SpacetimeEmergence.v` | 0 | ✅ |
| `StateSpaceCounting.v` | 0 | ✅ |
| `StressEnergyDynamics.v` | 0 | ✅ |
| `Subsumption.v` | 0 | ✅ |
| `TOE.v` | 0 | ✅ |
| `TOEDecision.v` | 0 | ✅ |
| `Test.v` | 0 | ✅ |
| `TestTripartite.v` | 0 | ✅ |
| `ThreeLayerIsomorphism.v` | 0 | ✅ |
| `Tier1Proofs.v` | 0 | ✅ |
| `TopologyCurvatureBridge.v` | 0 | ✅ |
| `TsirelsonComputation.v` | 0 | ✅ |
| `TsirelsonDerivation.v` | 0 | ✅ |
| `TsirelsonFromAlgebra.v` | 0 | ✅ |
| `TsirelsonGeneral.v` | 0 | ✅ |
| `TsirelsonLowerBound.v` | 0 | ✅ |
| `TsirelsonUniqueness.v` | 0 | ✅ |
| `TsirelsonUpperBound.v` | 0 | ✅ |
| `Unitarity.v` | 0 | ✅ |
| `VMEncoding.v` | 0 | ✅ |
| `VMState.v` | 0 | ✅ |
| `VMStep.v` | 0 | ✅ |
| `ValidCorrelation.v` | 0 | ✅ |

**Result:** All 121 files verified with 0 admits.
