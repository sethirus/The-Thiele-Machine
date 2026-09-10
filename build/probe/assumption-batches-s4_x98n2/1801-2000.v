(** Comprehensive Print Assumptions probe — every addressable proof-bearing
    declaration across every .v file in the repository (excluding vendor/kami,
    coq/archive/). Generated; do not edit. Functor and Module-Type interiors
    are skipped here and recorded separately in the inventory. *)

Require Extraction.
Require IntrinsicLevelHierarchy.
Require MuCodingTheorem.
Require MuDirectSum.
Require NecessityOfMuLedger.
Require PhysicsConditionalClosure.
Require ReceiptTheorem.
Require ThieleMachineComplete.
Require VerifierEscape_Hardness.
Require VerifierEscape_Interaction.
Require VerifierEscape_Substrate.
Require VerifierExhaustiveness.
Require VerifierImpossibility.
Require VerifierModel.
Require KamiHW.Abstraction.
Require KamiHW.CanonicalCPUProof.
Require KamiHW.Compatibility.
Require KamiHW.EmbedStep.
Require KamiHW.EmbedStep_WF.
Require KamiHW.F4_BModulesTranslation.
Require KamiHW.F4_VerilogEvaluator.
Require KamiHW.FullAbstraction.
Require KamiHW.FullEmbedStep.
Require KamiHW.FullStep.
Require KamiHW.GraphReconstructionBridge.
Require KamiHW.HardwareShadowBridge.
Require KamiHW.KamiExtraction.
Require KamiHW.LogicEngineEquivalence.
Require KamiHW.RTLCorrectnessInstantiation.
Require KamiHW.RTLGapRegistry.
Require KamiHW.RichStateCommutation.
Require KamiHW.ShadowDevice.
Require KamiHW.ShadowDeviceTrace.
Require KamiHW.ShadowEmbedStep.
Require KamiHW.ThieleCPUBusTop.
Require KamiHW.ThieleCPUCore.
Require KamiHW.ThieleCanonicality.
Require KamiHW.ThieleTypes.
Require KamiHW.VerilogRefinement.
Require KamiHW.VerilogSemantics.
Require Kernel.Closure.
Require Kernel.FalsifiablePrediction.
Require Kernel.MasterSummary.
Require Kernel.NonCircularityAudit.
Require Kernel.PDISCOVERIntegration.
Require Kernel.TOE.
Require Kernel.ThieleGenesis.
Require Kernel.UnificationProbeBridges.
Require Kernel.UnificationProbePattern.
Require Kernel.AlgebraicCoherence.
Require Kernel.CategoryBridge.
Require Kernel.CategoryLaws.
Require Kernel.CategoryMonoidal.
Require Kernel.ConstantUnification.
Require Kernel.AffineEFEClosure.
Require Kernel.CurvedTensorPipeline.
Require Kernel.DiscreteGaussBonnet.
Require Kernel.DiscreteRaychaudhuri.
Require Kernel.DiscreteSimplicialGeometry.
Require Kernel.DiscreteTopology.
Require Kernel.EinsteinEmergence.
Require Kernel.EinsteinEquations4D.
Require Kernel.EinsteinEquationsFull.
Require Kernel.FourDSimplicialComplex.
Require Kernel.JacobsonBridgeComponents.
Require Kernel.KernelNoether.
Require Kernel.KernelPhysics.
Require Kernel.LocalMorphismSemantics.
Require Kernel.LorentzNotForced.
Require Kernel.LorentzianTensorPipeline.
Require Kernel.MatrixAlgebra4.
Require Kernel.MetricForcing.
Require Kernel.MetricFromMuCosts.
Require Kernel.MuGravity.
Require Kernel.NoFIToEinstein.
Require Kernel.PNEWTopologyChange.
Require Kernel.PhysicalSubstrate.
Require Kernel.PhysicsClosure.
Require Kernel.RaychaudhuriFluxBridge.
Require Kernel.RiemannTensor4D.
Require Kernel.SpacetimeEmergence.
Require Kernel.StressEnergyDynamics.
Require Kernel.SymmetricDerivative4D.
Require Kernel.TopologyCurvatureBridge.
Require Kernel.ClassicalBound.
Require Kernel.ClassicalConservativity.
Require Kernel.DagRestriction.
Require Kernel.Definitions.
Require Kernel.Kernel.
Require Kernel.KernelTM.
Require Kernel.KernelThiele.
Require Kernel.Locality.
Require Kernel.MuCostModel.
Require Kernel.MuLedgerConservation.
Require Kernel.NatSubstrateInstance.
Require Kernel.PartitionSeparation.
Require Kernel.Persistence.
Require Kernel.ProperSubsumption.
Require Kernel.SimulationProof.
Require Kernel.StateSpaceCounting.
Require Kernel.Substrate.
Require Kernel.Subsumption.
Require Kernel.TuringClassicalEmbedding.
Require Kernel.TuringCompletenessISA.
Require Kernel.TuringStrictness.
Require Kernel.VMEncoding.
Require Kernel.VMInstructionEncoding.
Require Kernel.VMState.
Require Kernel.VMStep.
Require Kernel.VMSubstrateInstance.
Require Kernel.VMUnboundedExec.
Require Kernel.F1_AbstractedBridge.
Require Kernel.F1_LogicalErasure.
Require Kernel.F1_StrongForm.
Require Kernel.F1_TraceLevelA2.
Require Kernel.F2_MinorFromWitnessLocality.
Require Kernel.F2_MinorIndependence.
Require Kernel.F2_PerMinorFromCostCoherent.
Require Kernel.F3_CrossLink.
Require Kernel.F3_MuLaplacianSum.
Require Kernel.F3_PartitionTopologyCrossLink.
Require Kernel.F3_PlusOneStructural.
Require Kernel.F3_TripleCrossLink.
Require Kernel.ObservationPolicy.
Require Kernel.PointerObservable.
Require Kernel.PointerObservableCounterexamples.
Require Kernel.PointerObservableReductions.
Require Kernel.TraceStateDescent.
Require Kernel.HardwareBisimulation.
Require Kernel.OCamlExtractionBridge.
Require Kernel.PythonBisimulation.
Require Kernel.ThreeLayerIsomorphism.
Require Kernel.VerilogRTLCorrespondence.
Require Kernel.ConeAlgebra.
Require Kernel.ConeDerivation.
Require Kernel.SemanticMuCost.
Require Kernel.KernelBenchmarks.
Require Kernel.MuChaitin.
Require Kernel.MuComplexity.
Require Kernel.MuCostDerivation.
Require Kernel.MuGeometry.
Require Kernel.MuHierarchyTheorem.
Require Kernel.MuInformation.
Require Kernel.MuInitiality.
Require Kernel.MuNoFreeInsightQuantitative.
Require Kernel.MuShannonBridge.
Require Kernel.MuShannonQuantitative.
Require Kernel.QuantitativeNoFI.
Require Kernel.A2LoadBearing.
Require Kernel.A2Payoff.
Require Kernel.AbstractNoFI.
Require Kernel.CertCheck.
Require Kernel.Certification.
Require Kernel.CommitmentCostDecomposition.
Require Kernel.CommitmentPredicateAdequacy.
Require Kernel.CommitmentVsErasure.
Require Kernel.HonestCostTracking.
Require Kernel.HonestMeasurement.
Require Kernel.HonestNoFI.
Require Kernel.HonestNoFI_TheoremsWithoutAssumptions.
Require Kernel.InformationGainToStrengthening.
Require Kernel.InsightTaxonomy.
Require Kernel.LandauerDerivation.
Require Kernel.MeasurementExtraction.
Require Kernel.MuLedgerQuantumBridge.
Require Kernel.MuRunIncompleteness.
Require Kernel.NecessityAbstract.
Require Kernel.NoFreeInsight.
Require Kernel.NonAdaptiveLowerBound.
Require Kernel.PartitionRefinementNoFI.
Require Kernel.PrimeAxiom.
Require Kernel.ReceiptCore.
Require Kernel.ReceiptIntegrity.
Require Kernel.RevelationRequirement.
Require Kernel.SimpleMorphShortcut.
Require Kernel.StructuralAdvantage.
Require Kernel.StructuralAdvantageCertifiedShortcut.
Require Kernel.StructuralAdvantageObservedShortcut.
Require Kernel.StructuralAdvantageObservedShortcutResult.
Require Kernel.StructuralAxisOrthogonality.
Require Kernel.StructuralAxisRelativization.
Require Kernel.StructuralUndecidability.
Require Kernel.ThermodynamicStructuralAdvantage.
Require Kernel.ThieleInitiality.
Require Kernel.UniversalCertificationCost.
Require Kernel.UniversalShortcutLifting.
Require Kernel.VMSubstrateEncoded.
Require Kernel.VerificationCostSeparation.
Require Kernel.BornRule.
Require Kernel.BornRuleLinearity.
Require Kernel.BoxCHSH.
Require Kernel.CHSH.
Require Kernel.CHSHCouplingBridge.
Require Kernel.CHSHExtraction.
Require Kernel.CHSHStatisticalBridge.
Require Kernel.ConstructivePSD.
Require Kernel.ElliptopeCompletion.
Require Kernel.ElliptopeGate.
Require Kernel.EntanglementEntropy.
Require Kernel.GenRealizability.
Require Kernel.HolevoDimensional.
Require Kernel.HolevoGeneralD.
Require Kernel.HolevoTwoQubit.
Require Kernel.HonestMeasurementImpliesNPA.
Require Kernel.InformationCausality.
Require Kernel.MinorConstraints.
Require Kernel.NPAMomentMatrix.
Require Kernel.NoCloning.
Require Kernel.OperatorAlgebra.
Require Kernel.PRBoxIsDishonest.
Require Kernel.ProbabilityImpossibility.
Require Kernel.Purification.
Require Kernel.QuantumBound.
Require Kernel.QuantumEquivalence.
Require Kernel.QuantumPartitionPSD.
Require Kernel.QuantumPartitionPSD_1AB.
Require Kernel.SemidefiniteProgramming.
Require Kernel.TsirelsonFromAlgebra.
Require Kernel.TsirelsonFromIC.
Require Kernel.TsirelsonFromMu.
Require Kernel.TsirelsonGeneral.
Require Kernel.TsirelsonQuantumModel.
Require Kernel.TsirelsonUniqueness.
Require Kernel.TsirelsonUpperBound.
Require Kernel.Unitarity.
Require Kernel.ValidCorrelation.
Require Kernel.GasMetering.
Require Kernel.PoSFinality.
Require Kernel.ProofCarryingVerifier.
Require Kernel.TEEAttestation.
Require Kernel.TransparencyLog.
Require Kernel.AdditionalProbes.
Require Kernel.BekensteinBound.
Require Kernel.BekensteinCalibration.
Require Kernel.ClausiusFromEntropyArea.
Require Kernel.DimensionalGapTheorem.
Require Kernel.EntropyImpossibility.
Require Kernel.FiniteInformation.
Require Kernel.LocalInfoLoss.
Require Kernel.SecondLawBoltzmannWall.
Require Kernel.ThermoEinsteinBridge.
Require Kernel.BlindnessRepresentation.
Require Kernel.DerivedTime.
Require Kernel.InformationTopology.
Require Kernel.ObserverDerivation.
Require Kernel.ProjectionNonExistence.
Require Kernel.ShadowProjection.
Require Kernel.ThieleTraceProjection.
Require Kernel.WitnessInsightGeneral.
Require Kernel.WitnessPreservationImpossibility.
Require NoFI.Instance_Kernel.
Require NoFI.MuChaitinTheory_Interface.
Require NoFI.MuChaitinTheory_Theorem.
Require NoFI.NoFreeInsight_Interface.
Require NoFI.NoFreeInsight_Theorem.
Require Physics.DiscreteModel.
Require Physics.DissipativeModel.
Require Physics.PreregSplit.
Require Physics.TriangularLattice.
Require Physics.WaveModel.
Require SelfReference.AdversarialChallenge.
Require SelfReference.InductiveTrust.
Require SelfReference.MuThresholdDisobedience.
Require SelfReference.NeuralSymbolicBridge.
Require SelfReference.NonInterference.
Require SelfReference.RefinementInvariant.
Require SelfReference.SelfCertifyingDecider.
Require SelfReference.SelfReference.
Require SelfReference.TilingChain.
Require Spacetime.Spacetime.
Require TestFixtures.VacuitySmoke.
Require Tests.ClaimBoundaryRegression.
Require Tests.CloseoutVerification.
Require Tests.TestNecessity.
Require Tests.WFDrivenRunRegression.
Require Tests.verify_nofi_load_bearing.
Require Tests.verify_zero_admits.
Require Thermodynamic.LandauerDerived.
Require Thermodynamic.LandauerJoules.
Require Thermodynamic.ThermodynamicBridge.
Require ThieleManifold.PhysicalConstants.
Require ThieleManifold.PhysicsIsomorphism.
Require ThieleManifold.ThieleManifold.
Require ThieleManifold.ThieleManifoldBridge.
Require ThieleMachine.ThieleMachine.
Require ThieleMachine.ThieleProc.

(* === Extraction : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.thiele_strictly_extends_turing.
Print Assumptions Kernel.SimulationProof.encoding_implies_states_related.
Print Assumptions Kernel.SimulationProof.firstn_succ_nth_error_Some.
Print Assumptions Kernel.SimulationProof.firstn_succ_nth_error_None.
Print Assumptions Kernel.SimulationProof.length_concat_firstn_succ_Some.
Print Assumptions Kernel.SimulationProof.length_concat_firstn_succ_None.
Print Assumptions Kernel.SimulationProof.skipn_nth_error_cons.
Print Assumptions Kernel.SimulationProof.nth_error_concat_first_hd.
Print Assumptions Kernel.SimulationProof.compile_instruction_head.
Print Assumptions Kernel.SimulationProof.compile_trace_start_pos_correct.
Print Assumptions Kernel.SimulationProof.compile_trace_nth.
Print Assumptions Kernel.SimulationProof.vm_step_vm_apply.
Print Assumptions Kernel.SimulationProof.vm_step_deterministic.
Print Assumptions Kernel.SimulationProof.vm_step_pc_advance.
Print Assumptions Kernel.SimulationProof.vm_step_mu_ge.
Print Assumptions Kernel.SimulationProof.vm_step_mu.
Print Assumptions Kernel.SimulationProof.vm_exec_run_vm.
Print Assumptions Kernel.SimulationProof.vm_exec_deterministic.
Print Assumptions Kernel.SimulationProof.step_thiele_hclaim_tm_state.
Print Assumptions Kernel.SimulationProof.step_thiele_hclaim_mu.
Print Assumptions Kernel.SimulationProof.fetch_compile_trace.
Print Assumptions Kernel.SimulationProof.compile_increment_pc_correct.
Print Assumptions Kernel.SimulationProof.compile_add_mu_correct.
Print Assumptions Kernel.SimulationProof.decode_vm_state_update_err.
Print Assumptions Kernel.SimulationProof.compile_update_err_correct.
Print Assumptions Kernel.SimulationProof.vm_step_kernel_simulation.
Print Assumptions Kernel.SimulationProof.vm_exec_simulation.
Print Assumptions Kernel.SimulationProof.vm_is_a_correct_refinement_of_kernel.
Print Assumptions Kernel.SimulationProof.pnew_mu_exact.
Print Assumptions Kernel.SimulationProof.vm_apply_pnew_graph.
Print Assumptions Kernel.SimulationProof.graph_add_module_next_id_nondec.
Print Assumptions Kernel.SimulationProof.vm_apply_pnew_graph_nondec.
Print Assumptions Kernel.SimulationProof.vm_apply_pnew_noninterference.
Print Assumptions Kernel.SimulationProof.pnew_chain_mu.
Print Assumptions Kernel.SimulationProof.pnew_chain_noninterference.
Print Assumptions Kernel.SimulationProof.vm_lob_bypass.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.lassert_cost_includes_formula_length.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.mu_increase_bounds_axiom_bits.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.nofreeinsight_quantitative_lower_bound.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.mu_increase_bounds_actual_formula_bits.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.pow2_ge_1.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.log2_pow2.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.nofreeinsight_information_theoretic_bound.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.no_free_insight_quantitative.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.lassert_honest_cost.
Print Assumptions Kernel.StateSpaceCounting.StateSpaceCounting.lassert_honest_mu_cost.
Print Assumptions Kernel.Substrate.prog_equiv_sym.
Print Assumptions Kernel.Substrate.prog_equiv_trans.
Print Assumptions Kernel.Substrate.mu_monotone_chain.
Print Assumptions Kernel.Subsumption.witness_is_sighted.
Print Assumptions Kernel.Subsumption.witness_not_turing.
Print Assumptions Kernel.Subsumption.sighted_program_not_turing_witness.
Print Assumptions Kernel.TuringClassicalEmbedding.D2_faithfulness.
Print Assumptions Kernel.TuringClassicalEmbedding.unpack_shadow_proj.
Print Assumptions Kernel.TuringClassicalEmbedding.shadow_advance_state.
Print Assumptions Kernel.TuringClassicalEmbedding.shadow_advance_state_rm.
Print Assumptions Kernel.TuringClassicalEmbedding.shadow_jump_state.
Print Assumptions Kernel.TuringClassicalEmbedding.shadow_jump_state_rm.
Print Assumptions Kernel.TuringClassicalEmbedding.classical_step_shadow_compat.
Print Assumptions Kernel.TuringClassicalEmbedding.classical_step_csrs_compat.
Print Assumptions Kernel.TuringClassicalEmbedding.classical_step_compat.
Print Assumptions Kernel.TuringClassicalEmbedding.classical_trace_compat.
Print Assumptions Kernel.TuringClassicalEmbedding.D2_classical_shadow_preserved.
Print Assumptions Kernel.TuringClassicalEmbedding.shadow_proj_kernel_is_eq_on_classical_shadow.
Print Assumptions Kernel.TuringClassicalEmbedding.degenerate_projection_theorem.
Print Assumptions Kernel.TuringClassicalEmbedding.shadow_inequivalent_states_distinguishable.
Print Assumptions Kernel.TuringCompletenessISA.firstn_nth_aux.
Print Assumptions Kernel.TuringCompletenessISA.skipn_nth_aux.
Print Assumptions Kernel.TuringCompletenessISA.read_write_same.
Print Assumptions Kernel.TuringCompletenessISA.read_write_other.
Print Assumptions Kernel.TuringCompletenessISA.length_write_reg.
Print Assumptions Kernel.TuringCompletenessISA.word64_1.
Print Assumptions Kernel.TuringCompletenessISA.word64_idempotent.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_load_imm.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_add.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_sub.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jnez.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jump.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_halt.
Print Assumptions Kernel.TuringCompletenessISA.advance_state_rm_pc.
Print Assumptions Kernel.TuringCompletenessISA.advance_state_rm_regs.
Print Assumptions Kernel.TuringCompletenessISA.advance_state_pc.
Print Assumptions Kernel.TuringCompletenessISA.advance_state_regs.
Print Assumptions Kernel.TuringCompletenessISA.jump_state_pc.
Print Assumptions Kernel.TuringCompletenessISA.jump_state_regs.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_load_imm_reg.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_load_imm_other.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_load_imm_pc.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_add_reg.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_add_other.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_add_pc.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_sub_reg.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_sub_other.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_sub_pc.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jnez_zero_pc.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jnez_nonzero_pc.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jnez_regs.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jump_pc.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_jump_regs.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_preserves_reg_length_load_imm.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_preserves_reg_length_add.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_preserves_reg_length_sub.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_preserves_reg_length_jnez.
Print Assumptions Kernel.TuringCompletenessISA.vm_apply_preserves_reg_length_jump.
Print Assumptions Kernel.TuringCompletenessISA.inc_via_vm_apply.
Print Assumptions Kernel.TuringCompletenessISA.jzdec_zero_via_vm_apply.
Print Assumptions Kernel.TuringCompletenessISA.jzdec_nonzero_via_vm_apply.
Print Assumptions Kernel.TuringStrictness.D4_thiele_changes_graph.
Print Assumptions Kernel.TuringStrictness.D4_classical_preserves_next_id.
Print Assumptions Kernel.TuringStrictness.D4_strictness.
Print Assumptions Kernel.TuringStrictness.D5_thiele_strictly_extends_classical.
Print Assumptions Kernel.VMEncoding.decode_nat_correct.
Print Assumptions Kernel.VMEncoding.decode_bool_correct.
Print Assumptions Kernel.VMEncoding.decode_ascii_correct.
Print Assumptions Kernel.VMEncoding.decode_list_payload_correct.
Print Assumptions Kernel.VMEncoding.decode_sequence_correct.
Print Assumptions Kernel.VMEncoding.decode_string_correct.
Print Assumptions Kernel.VMEncoding.decode_nat_list_correct.
Print Assumptions Kernel.VMEncoding.decode_string_list_correct.
Print Assumptions Kernel.VMEncoding.decode_module_state_correct.
Print Assumptions Kernel.VMEncoding.decode_module_entry_correct.
Print Assumptions Kernel.VMEncoding.decode_nat_pair_correct.
Print Assumptions Kernel.VMEncoding.decode_coupling_data_correct.
Print Assumptions Kernel.VMEncoding.decode_morphism_state_correct.
Print Assumptions Kernel.VMEncoding.decode_morphism_entry_correct.
Print Assumptions Kernel.VMEncoding.decode_partition_graph_correct.
Print Assumptions Kernel.VMEncoding.decode_csr_correct.
Print Assumptions Kernel.VMEncoding.decode_vm_state_correct.
Print Assumptions Kernel.VMEncoding.encode_decode_vm_state_roundtrip.
Print Assumptions Kernel.VMEncoding.update_pc_preserves_other_fields.
Print Assumptions Kernel.VMInstructionEncoding.decode_vm_instruction_correct.
Print Assumptions Kernel.VMInstructionEncoding.decode_program_correct.
Print Assumptions Kernel.VMInstructionEncoding.pos_to_bools_to_pos.
Print Assumptions Kernel.VMInstructionEncoding.bools_to_pos_to_bools.
Print Assumptions Kernel.VMInstructionEncoding.bools_to_nat_pos.
Print Assumptions Kernel.VMInstructionEncoding.nat_to_bools_to_nat.
Print Assumptions Kernel.VMInstructionEncoding.nat_to_program_program_to_nat.
Print Assumptions Kernel.VMInstructionEncoding.program_to_nat_injective.
Print Assumptions Kernel.VMInstructionEncoding.program_to_nat_preserves_instruction_cost.
Print Assumptions Kernel.VMState.normalize_region_nodup.
Print Assumptions Kernel.VMState.normalize_region_idempotent.
Print Assumptions Kernel.VMState.empty_graph_well_formed.
Print Assumptions Kernel.VMState.graph_add_module_lookup_other.
Print Assumptions Kernel.VMState.graph_certify_morphism_lookup.
Print Assumptions Kernel.VMState.graph_cascade_delete_morphisms_preserves_modules.
Print Assumptions Kernel.VMState.graph_cascade_delete_morphisms_preserves_next_id.
Print Assumptions Kernel.VMState.graph_cascade_delete_morphisms_preserves_next_morph_id.
Print Assumptions Kernel.VMState.graph_cascade_delete_morphisms_lookup.
Print Assumptions Kernel.VMState.graph_cascade_delete_morphisms_preserves_wf.
Print Assumptions Kernel.VMState.graph_add_morphism_preserves_lookup.
Print Assumptions Kernel.VMState.graph_add_identity_preserves_lookup.
Print Assumptions Kernel.VMState.graph_delete_morphism_preserves_lookup.
Print Assumptions Kernel.VMState.compose_certified_morphisms_cost_zero.
Print Assumptions Kernel.VMState.graph_compose_morphisms_preserves_lookup.
Print Assumptions Kernel.VMState.graph_tensor_morphisms_preserves_lookup.
Print Assumptions Kernel.VMState.all_ids_below_weaken.
Print Assumptions Kernel.VMState.graph_add_module_preserves_wf.
Print Assumptions Kernel.VMState.graph_remove_modules_preserves_all_ids_below.
Print Assumptions Kernel.VMState.graph_remove_modules_preserves_other_in.
Print Assumptions Kernel.VMState.graph_remove_preserves_wf.
Print Assumptions Kernel.VMState.cascade_then_remove_endpoints_valid.
Print Assumptions Kernel.VMState.graph_remove_after_cascade_preserves_wf.
Print Assumptions Kernel.VMState.remove_no_ref_endpoints_valid.
Print Assumptions Kernel.VMState.graph_remove_no_ref_preserves_wf.
Print Assumptions Kernel.VMState.double_cascade_no_ref.
Print Assumptions Kernel.VMState.pmerge_second_remove_preserves_wf.
Print Assumptions Kernel.VMState.graph_lookup_modules_in.
Print Assumptions Kernel.VMState.in_modules_graph_lookup.
Print Assumptions Kernel.VMState.all_morph_endpoints_valid_In.
Print Assumptions Kernel.VMState.graph_lookup_morphism_list_In.
Print Assumptions Kernel.VMState.graph_add_morphism_preserves_wf.
Print Assumptions Kernel.VMState.graph_compose_morphisms_preserves_wf.
Print Assumptions Kernel.VMState.graph_add_identity_preserves_wf.
Print Assumptions Kernel.VMState.graph_delete_morphism_preserves_wf.
Print Assumptions Kernel.VMState.graph_tensor_morphisms_preserves_wf.
Print Assumptions Kernel.VMState.graph_add_morphism_next_id_same.
Print Assumptions Kernel.VMState.graph_add_identity_next_id_same.
Print Assumptions Kernel.VMState.graph_compose_morphisms_next_id_same.
Print Assumptions Kernel.VMState.graph_delete_morphism_next_id_same.
Print Assumptions Kernel.VMState.graph_tensor_morphisms_next_id_same.
Print Assumptions Kernel.VMState.graph_add_module_length.
Print Assumptions Kernel.VMState.graph_remove_modules_length.
Print Assumptions Kernel.VMState.graph_remove_length.
Print Assumptions Kernel.VMState.graph_insert_modules_length.
Print Assumptions Kernel.VMState.graph_insert_modules_existing_length.
Print Assumptions Kernel.VMState.graph_insert_modules_preserves_in_map.
Print Assumptions Kernel.VMState.graph_update_length.
Print Assumptions Kernel.VMState.graph_add_axiom_length.
Print Assumptions Kernel.VMState.graph_add_axiom_preserves_length.
Print Assumptions Kernel.VMState.graph_add_axioms_preserves_length.
Print Assumptions Kernel.VMState.graph_record_discovery_preserves_length.
Print Assumptions Kernel.VMState.graph_update_existing_length.
Print Assumptions Kernel.VMState.graph_insert_modules_lookup_same.
Print Assumptions Kernel.VMState.graph_update_lookup_same.
Print Assumptions Kernel.VMState.graph_insert_modules_preserves_unrelated.
Print Assumptions Kernel.VMState.graph_update_preserves_unrelated.
Print Assumptions Kernel.VMState.all_ids_below_implies_lookup_none.
Print Assumptions Kernel.VMState.graph_remove_preserves_next_id.
Print Assumptions Kernel.VMState.graph_remove_preserves_unrelated.
Print Assumptions Kernel.VMState.wf_graph_lookup_beyond_next_id.
Quit.
