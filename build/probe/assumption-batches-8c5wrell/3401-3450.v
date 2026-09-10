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
Print Assumptions Kernel.SemidefiniteProgramming.PSD_cauchy_schwarz.
Print Assumptions Kernel.SemidefiniteProgramming.PSD_off_diagonal_bound.
Print Assumptions Kernel.TsirelsonFromAlgebra.chsh_gap_is_sum_of_squares.
Print Assumptions Kernel.TsirelsonFromAlgebra.sq_nonneg_local.
Print Assumptions Kernel.TsirelsonFromAlgebra.cauchy_schwarz_chsh.
Print Assumptions Kernel.TsirelsonFromAlgebra.tsirelson_squared.
Print Assumptions Kernel.TsirelsonFromAlgebra.sqrt8_eq_2sqrt2.
Print Assumptions Kernel.TsirelsonFromAlgebra.optimal_correlator_squared.
Print Assumptions Kernel.TsirelsonFromAlgebra.optimal_satisfies_row_bound.
Print Assumptions Kernel.TsirelsonFromAlgebra.optimal_chsh.
Print Assumptions Kernel.TsirelsonFromAlgebra.four_e_eq_sqrt8.
Print Assumptions Kernel.TsirelsonFromAlgebra.tsirelson_tight.
Print Assumptions Kernel.TsirelsonFromAlgebra.rational_tsirelson_bound.
Print Assumptions Kernel.TsirelsonFromIC.IC_implies_A3.
Print Assumptions Kernel.TsirelsonFromIC.tsirelson_bound_from_IC.
Print Assumptions Kernel.TsirelsonFromIC.pr_box_violates_IC.
Print Assumptions Kernel.TsirelsonFromMu.tsirelson_bound_from_A3.
Print Assumptions Kernel.TsirelsonFromMu.pr_box_violates_A3.
Print Assumptions Kernel.TsirelsonGeneral.sq_nonneg.
Print Assumptions Kernel.TsirelsonGeneral.cauchy_schwarz_chsh.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_from_row_bounds.
Print Assumptions Kernel.TsirelsonGeneral.vm_step_invariant_tsirelson_bound.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_bound_squared.
Print Assumptions Kernel.TsirelsonGeneral.sqrt8_squared.
Print Assumptions Kernel.TsirelsonGeneral.sqrt8_positive.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_bound_abs.
Print Assumptions Kernel.TsirelsonGeneral.sqrt2_pos.
Print Assumptions Kernel.TsirelsonGeneral.sqrt2inv_squared.
Print Assumptions Kernel.TsirelsonGeneral.optimal_chsh_value.
Print Assumptions Kernel.TsirelsonGeneral.four_over_sqrt2.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_achievable.
Print Assumptions Kernel.TsirelsonGeneral.minor_implies_row_bound.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_from_minors.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_from_minors_abs.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_run_vm_extract_invariant_at_stuck.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_run_vm_correlators_invariant_at_stuck.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_quantum_model_invariant.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_quantum_bridge_coherent_invariant.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_quantum_bridge_coherent_implies_quantum_model.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_quantum_bridge_coherent_implies_tsirelson_squared.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_quantum_bridge_coherent_implies_tsirelson_abs.
Print Assumptions Kernel.TsirelsonQuantumModel.trace_quantum_model_connection_closed.
Print Assumptions Kernel.TsirelsonQuantumModel.c4_direct_tsirelson_from_quantum_realizable.
Print Assumptions Kernel.TsirelsonQuantumModel.c4_direct_tsirelson_abs_from_quantum_realizable.
Print Assumptions Kernel.TsirelsonQuantumModel.c4_direct_tsirelson_from_quantum_realizable_invariant.
Print Assumptions Kernel.TsirelsonQuantumModel.c4_direct_tsirelson_abs_from_quantum_realizable_invariant.
Print Assumptions Kernel.TsirelsonUniqueness.mu_zero_algebraic_bound.
Print Assumptions Kernel.TsirelsonUpperBound.mu_zero_no_lassert_from_pc.
Print Assumptions Kernel.TsirelsonUpperBound.mu_zero_no_lassert.
Print Assumptions Kernel.TsirelsonUpperBound.mu_zero_no_ljoin_from_pc.
Quit.
