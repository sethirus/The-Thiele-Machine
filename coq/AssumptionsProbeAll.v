(** Comprehensive Print Assumptions probe: every addressable proof-bearing
    declaration across every .v file in the repository (excluding vendor/,
    coq/archive/). Generated; do not edit. Functor and Module-Type interiors
    are skipped here and recorded separately in the inventory. *)

Require Kernel.AlgebraicCoherence.
Require Kernel.AxCgkAxis.
Require Kernel.AxCgkBoundary.
Require Kernel.AxCgkGuest.
Require Kernel.AxCgkHost.
Require Kernel.AxCgkLang.
Require Kernel.AxCgkRun.
Require Kernel.AxChain.
Require Kernel.AxComplete.
Require Kernel.AxComplete2.
Require Kernel.AxCore.
Require Kernel.AxDgFixed.
Require Kernel.AxDgLoops.
Require Kernel.AxDgPhase.
Require Kernel.AxDgPre.
Require Kernel.AxHost.
Require Kernel.AxHostClaims.
Require Kernel.AxInfinite.
Require Kernel.AxLatch.
Require Kernel.AxLatch2.
Require Kernel.AxMerge.
Require Kernel.AxNecessity.
Require Kernel.AxProb.
Require Kernel.AxRice.
Require Kernel.AxShadow.
Require Kernel.AxSmall.
Require Kernel.AxTwoPoint.
Require Kernel.AxUniversal.
Require Kernel.AxWindow.
Require Kernel.CmpBlocks.
Require Kernel.CmpCompile.
Require Kernel.CmpExpr.
Require Kernel.CmpFinal.
Require Kernel.CmpFlat.
Require Kernel.CmpGuest.
Require Kernel.CmpHost.
Require Kernel.CmpInline.
Require Kernel.CmpLang.
Require Kernel.CmpMM.
Require Kernel.CmpPipeline.
Require Kernel.CmpRun.
Require Kernel.CompilerChecker.
Require Kernel.CompilerCodes.
Require Kernel.CompilerGuest.
Require Kernel.CompilerGuestRun.
Require Kernel.CompilerIcomp.
Require Kernel.CompilerInstrument.
Require Kernel.CompilerLifts.
Require Kernel.CompilerRaBridge.
Require Kernel.CrossBaseGranularity.
Require Kernel.CrossBaseGranularityCore.
Require Kernel.CrossBaseGranularityL.
Require Kernel.CrossBaseGranularityRAM.
Require Kernel.CrossBaseGranularityTransCore.
Require Kernel.CzCS.
Require Kernel.CzCat.
Require Kernel.CzCounter.
Require Kernel.CzFollow.
Require Kernel.CzLoad.
Require Kernel.CzProd.
Require Kernel.CzProdTC.
Require Kernel.CzSelf.
Require Kernel.CzSeq.
Require Kernel.CzShadow.
Require Kernel.CzTower.
Require Kernel.CzWin.
Require Kernel.EarnedCoreLinks.
Require Kernel.EarnedGenericLinks.
Require Kernel.FiniteSums.
Require Kernel.GrowingRecord.
Require Kernel.GrowingRecordCore.
Require Kernel.Kernel.
Require Kernel.KernelTM.
Require Kernel.LRecursion.
Require Kernel.LiftAxis.
Require Kernel.LiftExec.
Require Kernel.LiftHeadline.
Require Kernel.LiftModels.
Require Kernel.LiftModelsAll.
Require Kernel.LiftRAM.
Require Kernel.MM2ComplementUndec.
Require Kernel.NatSubstrateInstance.
Require Kernel.NecEChsh.
Require Kernel.NecEChshEquality.
Require Kernel.NecEChshInt.
Require Kernel.NecEFine.
Require Kernel.NecEHost.
Require Kernel.NecFCalorimeter.
Require Kernel.NecFCounter.
Require Kernel.NecFCups.
Require Kernel.NecFEntropy.
Require Kernel.NecFEntropyTight.
Require Kernel.NecFExtra.
Require Kernel.NecFFloor.
Require Kernel.NecFGibbs.
Require Kernel.NecFGrade.
Require Kernel.NecFMerge.
Require Kernel.NecFNarrowing.
Require Kernel.NecFPaperToys.
Require Kernel.NecFPhysics.
Require Kernel.NecFQuant.
Require Kernel.NecFRepeat.
Require Kernel.NecFSqueeze.
Require Kernel.NecFSqueezeLog.
Require Kernel.NecFThreeState.
Require Kernel.NecSMisc.
Require Kernel.NecSPoints.
Require Kernel.NecSPresented.
Require Kernel.NecSU.
Require Kernel.NecSUndec.
Require Kernel.NecWArgued.
Require Kernel.NecWCT.
Require Kernel.NecWCasper.
Require Kernel.NecWDiagonal.
Require Kernel.NecWGrowing.
Require Kernel.NecWLRice.
Require Kernel.NecWLatch.
Require Kernel.NecWModels.
Require Kernel.NecWPointer.
Require Kernel.NecWWindow.
Require Kernel.Presentation.
Require Kernel.PresentedDemo.
Require Kernel.PresentedUniversal.
Require Kernel.PricedHostLinks.
Require Kernel.ProbabilisticRecord.
Require Kernel.ProbabilisticRecordCore.
Require Kernel.ProperSubsumption.
Require Kernel.Realize.
Require Kernel.RealizeCompact.
Require Kernel.RealizeNames.
Require Kernel.RealizePriced.
Require Kernel.RealizePrograms.
Require Kernel.RecordAxisDiscrimination.
Require Kernel.SmBlock.
Require Kernel.SmChain.
Require Kernel.SmDecider.
Require Kernel.SmEvalL.
Require Kernel.SmFixed.
Require Kernel.SmFixedPoint.
Require Kernel.SmFuel.
Require Kernel.SmGuestRice.
Require Kernel.SmHostRice.
Require Kernel.SmKleene.
Require Kernel.SmMMAHost.
Require Kernel.SmMMAOff.
Require Kernel.SmNoExact.
Require Kernel.SmSmnAll.
Require Kernel.SmTallyL.
Require Kernel.SmallChshLinks.
Require Kernel.StructuralClockSync.
Require Kernel.StructuralCore.
Require Kernel.StructuralCoreAnyBase.
Require Kernel.StructuralCoreCover.
Require Kernel.StructuralRecordAxis.
Require Kernel.Substrate.
Require Kernel.Tc2Plain.
Require Kernel.Tc2PlainAdd.
Require Kernel.TcBridge.
Require Kernel.TcCodes.
Require Kernel.TcCompile.
Require Kernel.TcCompile0.
Require Kernel.TcCompose.
Require Kernel.TcEpi.
Require Kernel.TcEvalL.
Require Kernel.TcFuel.
Require Kernel.TcGadget.
Require Kernel.TcGodel.
Require Kernel.TcInterp.
Require Kernel.TcMod.
Require Kernel.TcNoFine.
Require Kernel.TcNorm.
Require Kernel.TcPacked.
Require Kernel.TcPackedMMA.
Require Kernel.TcPlain.
Require Kernel.TcPrefix.
Require Kernel.TcRice.
Require Kernel.TcRiceMM.
Require Kernel.UniversalBlocks.
Require Kernel.UniversalBridge.
Require Kernel.UniversalInterpreterLinks.
Require Kernel.UniversalLayout.
Require Kernel.UniversalPBlocks.
Require Kernel.UniversalPBridge.
Require Kernel.UniversalPCodes.
Require Kernel.UniversalPLayout.
Require Kernel.UniversalPPhases.
Require Kernel.UniversalPRun.
Require Kernel.UniversalPSim.
Require Kernel.UniversalPhases.
Require Kernel.UniversalRun.
Require Kernel.UniversalSim.
Require Kernel.UniversalThieleLinks.
Require Kernel.EcosystemGame.
Require Kernel.EcosystemGameTarget.
Require Kernel.ObservationPolicy.
Require Kernel.PointerObservable.
Require Kernel.PointerObservableCounterexamples.
Require Kernel.PointerObservableReductions.
Require Kernel.RecordProliferationSurvey.
Require Kernel.RecordProliferationSurveyTarget.
Require Kernel.CommitmentPredicateAdequacy.
Require Kernel.CommitmentVsErasure.
Require Kernel.CostFrameworks.
Require Kernel.CostSemanticsComparison.
Require Kernel.DecisionTreeBound.
Require Kernel.FiniteCertMachine.
Require Kernel.HonestCostTracking.
Require Kernel.KnowledgeNarrowing.
Require Kernel.KnowledgeNarrowingIncremental.
Require Kernel.KnowledgeNarrowingMinimal.
Require Kernel.PermanentCertification.
Require Kernel.PermanentCertificationEntropy.
Require Kernel.PermanentRecordPricing.
Require Kernel.PricingOnePremise.
Require Kernel.PricingPhysicsAudit.
Require Kernel.PricingPhysicsTarget.
Require Kernel.QuantitativeNoFI.
Require Kernel.ShadowPricing.
Require Kernel.StructuralUndecidability.
Require Kernel.UniversalCertificationCost.
Require Kernel.ArcsineBoundary.
Require Kernel.BoxCHSH.
Require Kernel.CHSHColumnCheck.
Require Kernel.CHSHCouplingBridge.
Require Kernel.CHSHStatisticalBridge.
Require Kernel.ConstructivePSD.
Require Kernel.ElliptopeCompletion.
Require Kernel.ElliptopeGate.
Require Kernel.GenRealizability.
Require Kernel.MinorConstraints.
Require Kernel.NPAMomentMatrix.
Require Kernel.QuantumPartitionPSD_1AB.
Require Kernel.QuantumStrategies.
Require Kernel.QuantumStrategiesComplex.
Require Kernel.SchurComplement.
Require Kernel.SmallChshCheck.
Require Kernel.SmallChshMachine.
Require Kernel.TsirelsonAlgebraic.
Require Kernel.TsirelsonFromAlgebra.
Require Kernel.TsirelsonGeneral.
Require Kernel.TsirelsonRepresentation.
Require Kernel.ValidCorrelation.
Require Kernel.CasperFFG.
Require Kernel.CasperForkWitness.
Require Kernel.CasperRecordReading.
Require Kernel.ConcreteRAM.
Require Kernel.ConcreteRAMTarget.
Require Kernel.ConcreteRecordMachines.
Require Kernel.ConcreteRecordMachinesTarget.
Require Kernel.EVMStorageGas.
Require Kernel.GasMetering.
Require Kernel.NeculaPCC.
Require Kernel.NeculaPCCTarget.
Require Kernel.PoSFinality.
Require Kernel.RFC9162Merkle.
Require Kernel.RFC9162MerkleTarget.
Require Kernel.RealSystemConsequences.
Require Kernel.RealSystemConsequencesTarget.
Require Kernel.TPMQuoteAuthenticity.
Require Kernel.TPMQuoteAuthenticityTarget.
Require Kernel.TPMQuoteGap.
Require Kernel.CalorimeterProtocol.
Require Kernel.CalorimeterProtocolTarget.
Require Kernel.RelaxationContinuous.
Require Kernel.RelaxationContinuousLimit.
Require Kernel.RelaxationConvergence.
Require Kernel.RelaxationEntropy.
Require Kernel.RelaxationStretch.
Require Kernel.RelaxationStretchContinuous.
Require TestFixtures.VacuitySmoke.
Require Minimal.AxDgBlock.
Require Minimal.BitSearch2.
Require Minimal.BitSearchMember2.
Require Minimal.BitSearchObserved2.
Require Minimal.CompressionSmall2.
Require Minimal.ConsensusSeparation.
Require Minimal.CoveringNeeded2.
Require Minimal.CzLink.
Require Minimal.CzShared.
Require Minimal.EarnedCore.
Require Minimal.EarnedGeneric.
Require Minimal.EarnedMulti.
Require Minimal.EarnedMultiPriced.
Require Minimal.EarnedPriced.
Require Minimal.EntitlementMore2.
Require Minimal.EntitlementSmall.
Require Minimal.FragmentSmall.
Require Minimal.LiftConverse.
Require Minimal.LiftCore.
Require Minimal.LiftMacro.
Require Minimal.LiftOneCounter.
Require Minimal.LiftPigeon.
Require Minimal.MonotoneConsensus.
Require Minimal.MultiThiele2.
Require Minimal.NecEEnt.
Require Minimal.NecESearch.
Require Minimal.NecSChain.
Require Minimal.NecSClean.
Require Minimal.NecSHost.
Require Minimal.NecSNoCopy.
Require Minimal.NecSWindow.
Require Minimal.NecTEarned.
Require Minimal.NecTGeneric.
Require Minimal.NecTLoop.
Require Minimal.NecTLoose.
Require Minimal.NecTPartition.
Require Minimal.NecTToll.
Require Minimal.NecTUnclean.
Require Minimal.NecTVerifier.
Require Minimal.PartitionReading.
Require Minimal.PayFree.
Require Minimal.Presented.
Require Minimal.PricedComplete.
Require Minimal.RecordMerge.
Require Minimal.SmCodes.
Require Minimal.SmHostBlocks.
Require Minimal.SmInterp.
Require Minimal.SmLoops.
Require Minimal.SmLoops2.
Require Minimal.SmLoops3.
Require Minimal.SmTally.
Require Minimal.SmallConsensus.
Require Minimal.Tc2Am.
Require Minimal.Tc2Chain.
Require Minimal.Tc2Collision.
Require Minimal.Tc2Embed.
Require Minimal.Tc2Forced.
Require Minimal.Tc2Mult.
Require Minimal.Tc2Pow.
Require Minimal.Tc2Stage.
Require Minimal.TcBlocks.
Require Minimal.ThieleComplete.
Require Minimal.ThieleCompleteIndependent.
Require Minimal.ThieleCompleteScaled.
Require Minimal.ThieleCompleteWindow.
Require Minimal.TimeTax2.
Require Minimal.UniversalCodes.
Require Minimal.UniversalNoCopy.
Require Minimal.UniversalThiele.
Require Minimal.VerifierSmall.

(* === Kernel.AlgebraicCoherence : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AlgebraicCoherence.Qabs_bound.
Print Assumptions Kernel.AlgebraicCoherence.chsh_bound_4.
Print Assumptions Kernel.AlgebraicCoherence.symmetric_tsirelson_bound.
Print Assumptions Kernel.AlgebraicCoherence.tsirelson_from_algebraic_coherence.
Print Assumptions Kernel.AlgebraicCoherence.algebraic_max_not_coherent.
Print Assumptions Kernel.AlgebraicCoherence.sum_6_squares_nonneg.
Print Assumptions Kernel.AlgebraicCoherence.cauchy_schwarz_chsh.
Print Assumptions Kernel.AlgebraicCoherence.correlation_squares_bound.
Print Assumptions Kernel.AlgebraicCoherence.chsh_weak_bound.
Print Assumptions Kernel.AlgebraicCoherence.chsh_squared_bound_from_correlations.
Print Assumptions Kernel.AlgebraicCoherence.symmetric_minor_implies_sum_bound.
Print Assumptions Kernel.AlgebraicCoherence.symmetric_case_implies_tsirelson.
Print Assumptions Kernel.AlgebraicCoherence.chsh_general_bound.
Print Assumptions Kernel.AlgebraicCoherence.tsirelson_config_S.
Print Assumptions Kernel.AlgebraicCoherence.tsirelson_achieving_coherent.
Print Assumptions Kernel.AlgebraicCoherence.tsirelson_achieving_value.
Print Assumptions Kernel.AlgebraicCoherence.tsirelson_rational_lower_witness.
Print Assumptions Kernel.AlgebraicCoherence.algebraically_coherent_tsirelson_general.
Print Assumptions Kernel.AlgebraicCoherence.algebraically_coherent_tsirelson_abs.
(* === Kernel.AxCgkAxis : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCgkAxis.ax_height_iff.
Print Assumptions Kernel.AxCgkAxis.ax_chain_run.
Print Assumptions Kernel.AxCgkAxis.ax_cgk_prun_mono.
Print Assumptions Kernel.AxCgkAxis.ax_chain_levels.
Print Assumptions Kernel.AxCgkAxis.ax_threshold_chain_host.
(* === Kernel.AxCgkBoundary : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCgkBoundary.ax_pr_run_cap.
Print Assumptions Kernel.AxCgkBoundary.ax_guest_facts_cap.
Print Assumptions Kernel.AxCgkBoundary.ax_cm_first_halt.
Print Assumptions Kernel.AxCgkBoundary.ax_thermo_bounded.
Print Assumptions Kernel.AxCgkBoundary.ax_chain_boundary.
(* === Kernel.AxCgkGuest : 78 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCgkGuest.ax_cgk_maxreg_in.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_xmax_in.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_cons.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_app.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_here1.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_here.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_in.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_set_rf.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_Pn_spec.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_Ps_spec.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_Pc_spec.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_Pr_spec.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_T_ge.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_T_fresh.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_src_reg.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_jmp0.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_next.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_dech.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_tr1.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_step.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_cost.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_erI.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_erS.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_tr2.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_jmp1.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_trE.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_incI0.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_erT.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_read.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_decB.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_earn.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_incI.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_decC1.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_decC2.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_decC3.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_jmpL.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_decI.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_trX.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_erT2.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_pl.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_pay.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_jmp3.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_sc_halt.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_k_gt.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_rf_high.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_rf_spare.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_eqv_zero_high.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_eqv_spare.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_in1.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_in2.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_block.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_block_p.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_one.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_dec0.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_decS.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_inc.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_pay.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_earn.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_dec_next.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_erase.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_transfert.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_payloop.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_set2_rf.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_move.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_halt.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_noraise.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_read2.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_setup.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_exit.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_loop.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_ltb_sub.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_check.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_e0_rf.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_e0_high.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_cert_max.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_prologue.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_step.
Print Assumptions Kernel.AxCgkGuest.ax_cgk_x_stop.
(* === Kernel.AxCgkHost : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCgkHost.ax_cgk_grun_guest.
Print Assumptions Kernel.AxCgkHost.ax_cgk_host_match.
Print Assumptions Kernel.AxCgkHost.ax_cgk_grec_point.
Print Assumptions Kernel.AxCgkHost.ax_cgk_host_points.
Print Assumptions Kernel.AxCgkHost.ax_cgk_host_levels.
Print Assumptions Kernel.AxCgkHost.ax_cgk_host_halting.
Print Assumptions Kernel.AxCgkHost.ax_cgk_host_halt_point.
(* === Kernel.AxCgkLang : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCgkLang.ax_cgk_xstep_fun.
Print Assumptions Kernel.AxCgkLang.ax_cgk_lift_mm.
Print Assumptions Kernel.AxCgkLang.ax_cgk_simul_counter.
Print Assumptions Kernel.AxCgkLang.ax_cgk_yexec_chk.
Print Assumptions Kernel.AxCgkLang.ax_cgk_yexec_cmt.
Print Assumptions Kernel.AxCgkLang.ax_cgk_icomp_sound.
Print Assumptions Kernel.AxCgkLang.ax_cgk_compile_sound.
Print Assumptions Kernel.AxCgkLang.ax_cgk_simul_start.
Print Assumptions Kernel.AxCgkLang.ax_cgk_compile_steps.
Print Assumptions Kernel.AxCgkLang.ax_cgk_compile_start.
(* === Kernel.AxCgkRun : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCgkRun.ax_cgk_y_phase.
Print Assumptions Kernel.AxCgkRun.ax_cgk_fetch_at.
Print Assumptions Kernel.AxCgkRun.ax_cgk_fetch_halt.
Print Assumptions Kernel.AxCgkRun.ax_cgk_head_instr.
Print Assumptions Kernel.AxCgkRun.ax_cgk_fetch_head.
Print Assumptions Kernel.AxCgkRun.ax_cgk_ystart_simul.
Print Assumptions Kernel.AxCgkRun.ax_cgk_y_head.
Print Assumptions Kernel.AxCgkRun.ax_cgk_point_facts.
Print Assumptions Kernel.AxCgkRun.ax_cgk_point_live.
Print Assumptions Kernel.AxCgkRun.ax_cgk_y_stop.
Print Assumptions Kernel.AxCgkRun.ax_cgk_yhalt_facts.
Print Assumptions Kernel.AxCgkRun.ax_cgk_yhalt_err.
Print Assumptions Kernel.AxCgkRun.ax_cgk_first_halt.
Print Assumptions Kernel.AxCgkRun.ax_cgk_cover.
Print Assumptions Kernel.AxCgkRun.ax_cgk_guest_matching_points.
Print Assumptions Kernel.AxCgkRun.ax_cgk_guest_halts_at.
Print Assumptions Kernel.AxCgkRun.ax_cgk_guest_halting_iff.
Print Assumptions Kernel.AxCgkRun.ax_cgk_guest_facts_le.
(* === Kernel.AxChain : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxChain.ax_cm_read_val_code.
Print Assumptions Kernel.AxChain.ax_cm_run_halted.
Print Assumptions Kernel.AxChain.ax_cm_run_add.
Print Assumptions Kernel.AxChain.ax_cm_run_succ.
Print Assumptions Kernel.AxChain.ax_cm_ledger_succ.
Print Assumptions Kernel.AxChain.ax_cm_lat_ge_h.
Print Assumptions Kernel.AxChain.ax_cm_lat_ge_start.
Print Assumptions Kernel.AxChain.ax_cm_lat_succ.
Print Assumptions Kernel.AxChain.ax_cm_lat_le.
Print Assumptions Kernel.AxChain.ax_cm_run_some.
Print Assumptions Kernel.AxChain.ax_cm_lat_iff.
Print Assumptions Kernel.AxChain.ax_cm_bounded_of.
Print Assumptions Kernel.AxChain.ax_cm_lat_le_from.
Print Assumptions Kernel.AxChain.ax_cm_lat_mono.
Print Assumptions Kernel.AxChain.ax_cm_gledger_ge.
Print Assumptions Kernel.AxChain.ax_cm_gledger_le.
Print Assumptions Kernel.AxChain.ax_cm_surcharge_le.
(* === Kernel.AxComplete : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxComplete.am_run_nil.
Print Assumptions Kernel.AxComplete.am_run_cons.
Print Assumptions Kernel.AxComplete.am_run_app.
Print Assumptions Kernel.AxComplete.am_run_snoc.
Print Assumptions Kernel.AxComplete.run_pt.
Print Assumptions Kernel.AxComplete.am_axsys_run.
Print Assumptions Kernel.AxComplete.ax_run_grows.
Print Assumptions Kernel.AxComplete.ax_tc_a2.
Print Assumptions Kernel.AxComplete.ax_record_moves_app.
Print Assumptions Kernel.AxComplete.ax_tc_ledger_counts.
Print Assumptions Kernel.AxComplete.ax_first_exit.
Print Assumptions Kernel.AxComplete.flag_true_iff.
Print Assumptions Kernel.AxComplete.flag_false_iff.
Print Assumptions Kernel.AxComplete.r_ext.
Print Assumptions Kernel.AxComplete.ax_witness_nontrivial.
Print Assumptions Kernel.AxComplete.ax_pt_view_complete.
(* === Kernel.AxComplete2 : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxComplete2.flag_fn_Hr.
Print Assumptions Kernel.AxComplete2.flag_fn_false.
Print Assumptions Kernel.AxComplete2.ax_flag_view_complete.
Print Assumptions Kernel.AxComplete2.rm_eq.
Print Assumptions Kernel.AxComplete2.ax_tc_certificate_three.
Print Assumptions Kernel.AxComplete2.ax_tc_every_point_priced.
Print Assumptions Kernel.AxComplete2.ax_tc_committed_claim_true.
Print Assumptions Kernel.AxComplete2.ax_window_run.
Print Assumptions Kernel.AxComplete2.ax_base_moves_blind.
Print Assumptions Kernel.AxComplete2.ax_base_run_blind.
Print Assumptions Kernel.AxComplete2.ax_tc_collision.
Print Assumptions Kernel.AxComplete2.ax_tc_independence.
Print Assumptions Kernel.AxComplete2.ax_tc_ledger_independence.
Print Assumptions Kernel.AxComplete2.ax_tc_every_window_printed.
Print Assumptions Kernel.AxComplete2.ax_tc_conservative.
Print Assumptions Kernel.AxComplete2.ax_tc_halting_correspondence.
Print Assumptions Kernel.AxComplete2.ax_tc_no_verifier.
(* === Kernel.AxCore : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxCore.bp_le_refl.
Print Assumptions Kernel.AxCore.bp_le_trans.
Print Assumptions Kernel.AxCore.two_le.
Print Assumptions Kernel.AxCore.two_antisym.
Print Assumptions Kernel.AxCore.nat_pre_le.
Print Assumptions Kernel.AxCore.ax_run_app.
Print Assumptions Kernel.AxCore.ax_total_app.
Print Assumptions Kernel.AxCore.ax_floor_iff_a2.
Print Assumptions Kernel.AxCore.ax_cost_ge_exits.
Print Assumptions Kernel.AxCore.ax_exit_is_strict_rise.
Print Assumptions Kernel.AxCore.ax_view_a2.
Print Assumptions Kernel.AxCore.cs_axsys_run.
Print Assumptions Kernel.AxCore.cs_axsys_total.
Print Assumptions Kernel.AxCore.cs_axsys_a2.
Print Assumptions Kernel.AxCore.two_point_nfi.
Print Assumptions Kernel.AxCore.bp_thresholds_determine.
Print Assumptions Kernel.AxCore.thresholds_fail_on_preorder.
(* === Kernel.AxDgFixed : 25 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxDgFixed.ax_dg_obs_sym.
Print Assumptions Kernel.AxDgFixed.ax_dg_equiv_sym.
Print Assumptions Kernel.AxDgFixed.ax_dg_obs_sm2.
Print Assumptions Kernel.AxDgFixed.ax_dg_obs_hagree.
Print Assumptions Kernel.AxDgFixed.ax_dg_fb_mono.
Print Assumptions Kernel.AxDgFixed.ax_dg_Rb_MMA.
Print Assumptions Kernel.AxDgFixed.ax_dg_enter.
Print Assumptions Kernel.AxDgFixed.ax_dg_assemble.
Print Assumptions Kernel.AxDgFixed.ax_dg_fixed.
Print Assumptions Kernel.AxDgFixed.ax_dg_equiv_record.
Print Assumptions Kernel.AxDgFixed.ax_dg_reads_of_obs.
Print Assumptions Kernel.AxDgFixed.ax_dg_reads_hagree.
Print Assumptions Kernel.AxDgFixed.ax_dg_diagonal_record.
Print Assumptions Kernel.AxDgFixed.ax_dg_diagonal_threshold.
Print Assumptions Kernel.AxDgFixed.ax_dg_ceqb_spec.
Print Assumptions Kernel.AxDgFixed.ax_dg_incl_spec.
Print Assumptions Kernel.AxDgFixed.ax_dg_claims_reads.
Print Assumptions Kernel.AxDgFixed.ax_dg_claims_not_level2.
Print Assumptions Kernel.AxDgFixed.ax_dg_pt_floor.
Print Assumptions Kernel.AxDgFixed.ax_dg_step_check.
Print Assumptions Kernel.AxDgFixed.ax_dg_pclaim_ends.
Print Assumptions Kernel.AxDgFixed.ax_dg_pclaim_reaches.
Print Assumptions Kernel.AxDgFixed.ax_dg_halt_floor.
Print Assumptions Kernel.AxDgFixed.ax_dg_claim_undecidable.
Print Assumptions Kernel.AxDgFixed.ax_dg_claim_diagonal.
(* === Kernel.AxDgLoops : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxDgLoops.ax_dg_clean_ext.
Print Assumptions Kernel.AxDgLoops.ax_dg_clean_pc.
Print Assumptions Kernel.AxDgLoops.ax_dg_step_inc.
Print Assumptions Kernel.AxDgLoops.ax_dg_step_dec_pos.
Print Assumptions Kernel.AxDgLoops.ax_dg_step_dec_zero.
Print Assumptions Kernel.AxDgLoops.ax_dg_move_gen.
Print Assumptions Kernel.AxDgLoops.ax_dg_move.
Print Assumptions Kernel.AxDgLoops.ax_dg_clear_gen.
Print Assumptions Kernel.AxDgLoops.ax_dg_clear.
Print Assumptions Kernel.AxDgLoops.ax_dg_clears.
Print Assumptions Kernel.AxDgLoops.ax_dg_mma_instr.
Print Assumptions Kernel.AxDgLoops.ax_dg_xstep.
Print Assumptions Kernel.AxDgLoops.ax_dg_xrun.
Print Assumptions Kernel.AxDgLoops.ax_dg_mma_out.
(* === Kernel.AxDgPhase : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxDgPhase.ax_dg_N_ge.
Print Assumptions Kernel.AxDgPhase.ax_dg_phaseA.
Print Assumptions Kernel.AxDgPhase.ax_dg_phaseB.
Print Assumptions Kernel.AxDgPhase.ax_dg_phaseC.
Print Assumptions Kernel.AxDgPhase.ax_dg_phaseD.
Print Assumptions Kernel.AxDgPhase.ax_dg_vD_eval.
Print Assumptions Kernel.AxDgPhase.ax_dg_phaseE0.
Print Assumptions Kernel.AxDgPhase.ax_dg_phaseE1.
Print Assumptions Kernel.AxDgPhase.ax_dg_prelude.
(* === Kernel.AxDgPre : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxDgPre.ax_dg_seq.
Print Assumptions Kernel.AxDgPre.ax_dg_rj_one.
Print Assumptions Kernel.AxDgPre.ax_dg_plain_run.
Print Assumptions Kernel.AxDgPre.ax_dg_halted_out.
Print Assumptions Kernel.AxDgPre.ax_dg_lp_len.
Print Assumptions Kernel.AxDgPre.ax_dg_Cl_len.
Print Assumptions Kernel.AxDgPre.ax_dg_Pfx_len.
Print Assumptions Kernel.AxDgPre.ax_dg_V_len.
Print Assumptions Kernel.AxDgPre.ax_dg_fetch_pfx.
Print Assumptions Kernel.AxDgPre.ax_dg_fetch_app_right.
Print Assumptions Kernel.AxDgPre.ax_dg_fetch_A.
Print Assumptions Kernel.AxDgPre.ax_dg_fetch_Cl.
Print Assumptions Kernel.AxDgPre.ax_dg_fetch_D.
Print Assumptions Kernel.AxDgPre.ax_dg_fetch_E.
Print Assumptions Kernel.AxDgPre.ax_dg_embeds_pre.
Print Assumptions Kernel.AxDgPre.ax_dg_embeds_no.
Print Assumptions Kernel.AxDgPre.ax_dg_embeds_yes.
Print Assumptions Kernel.AxDgPre.ax_dg_exit_no.
Print Assumptions Kernel.AxDgPre.ax_dg_exit_yes.
(* === Kernel.AxHost : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxHost.ax_rec_of_tables.
Print Assumptions Kernel.AxHost.ax_universal_record.
Print Assumptions Kernel.AxHost.ax_universal_content.
Print Assumptions Kernel.AxHost.ax_chain_a2.
Print Assumptions Kernel.AxHost.ax_chain_grows.
Print Assumptions Kernel.AxHost.ax_prun_chain.
Print Assumptions Kernel.AxHost.ax_chain_first_raise.
Print Assumptions Kernel.AxHost.ax_surcharge_two_tight.
Print Assumptions Kernel.AxHost.ax_surcharge_three_floor.
(* === Kernel.AxHostClaims : 29 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxHostClaims.ax_fetch_in.
Print Assumptions Kernel.AxHostClaims.ax_next_in.
Print Assumptions Kernel.AxHostClaims.ax_claims_named_step.
Print Assumptions Kernel.AxHostClaims.ax_claims_named_run.
Print Assumptions Kernel.AxHostClaims.ax_claims_named.
Print Assumptions Kernel.AxHostClaims.ax_cap_claims.
Print Assumptions Kernel.AxHostClaims.ax_existsb_in.
Print Assumptions Kernel.AxHostClaims.ax_map_eq_in.
Print Assumptions Kernel.AxHostClaims.ax_vec_equiv.
Print Assumptions Kernel.AxHostClaims.ax_nodup_map_pairs.
Print Assumptions Kernel.AxHostClaims.ax_fixed_program_few.
Print Assumptions Kernel.AxHostClaims.ax_fixed_program_no_infinite.
Print Assumptions Kernel.AxHostClaims.ax_mem_snoc.
Print Assumptions Kernel.AxHostClaims.ax_i1_zero.
Print Assumptions Kernel.AxHostClaims.ax_nth_split.
Print Assumptions Kernel.AxHostClaims.ax_fetch_inc.
Print Assumptions Kernel.AxHostClaims.ax_i1_step.
Print Assumptions Kernel.AxHostClaims.ax_i1_run.
Print Assumptions Kernel.AxHostClaims.ax_i2_base.
Print Assumptions Kernel.AxHostClaims.ax_fetch_chk2.
Print Assumptions Kernel.AxHostClaims.ax_fetch_halt2.
Print Assumptions Kernel.AxHostClaims.ax_i2_step.
Print Assumptions Kernel.AxHostClaims.ax_i2_run.
Print Assumptions Kernel.AxHostClaims.ax_chain_realized.
Print Assumptions Kernel.AxHostClaims.ax_nodup_len_le.
Print Assumptions Kernel.AxHostClaims.ax_strict_len.
Print Assumptions Kernel.AxHostClaims.ax_chain_at_most_16.
Print Assumptions Kernel.AxHostClaims.ax_chain_of_16_realized.
Print Assumptions Kernel.AxHostClaims.ax_single_run_boundary.
(* === Kernel.AxInfinite : 42 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxInfinite.ax_priced_spots.
Print Assumptions Kernel.AxInfinite.ax_spots_priced.
Print Assumptions Kernel.AxInfinite.ax_fibre_loss_nonneg.
Print Assumptions Kernel.AxInfinite.ax_fibre_loss_split.
Print Assumptions Kernel.AxInfinite.ax_inf_loss_bits.
Print Assumptions Kernel.AxInfinite.ax_loss_n_succ.
Print Assumptions Kernel.AxInfinite.ax_mass_n_succ.
Print Assumptions Kernel.AxInfinite.ax_loss_n_growing.
Print Assumptions Kernel.AxInfinite.ax_loss_n_le.
Print Assumptions Kernel.AxInfinite.ax_inf_loss_series.
Print Assumptions Kernel.AxInfinite.ax_chain_rule.
Print Assumptions Kernel.AxInfinite.ax_entropy_split.
Print Assumptions Kernel.AxInfinite.ax_infinite_entropy_survives.
Print Assumptions Kernel.AxInfinite.ax_code_term.
Print Assumptions Kernel.AxInfinite.ax_gibbs_code.
Print Assumptions Kernel.AxInfinite.ax_gibbs_code_uniform.
Print Assumptions Kernel.AxInfinite.ax_collapse_unpriceable.
Print Assumptions Kernel.AxInfinite.ax_ln2_pos.
Print Assumptions Kernel.AxInfinite.ax_rsum_app.
Print Assumptions Kernel.AxInfinite.ax_rsum_seq_succ.
Print Assumptions Kernel.AxInfinite.ax_inr_pow2_succ.
Print Assumptions Kernel.AxInfinite.ax_inr_pow2_pos.
Print Assumptions Kernel.AxInfinite.ax_pow2_gt.
Print Assumptions Kernel.AxInfinite.ax_inv_pow2_cv.
Print Assumptions Kernel.AxInfinite.ax_geo_mass_n.
Print Assumptions Kernel.AxInfinite.ax_geometric_mass.
Print Assumptions Kernel.AxInfinite.ax_geo_moment.
Print Assumptions Kernel.AxInfinite.ax_geometric_loss.
Print Assumptions Kernel.AxInfinite.ax_rsum_flat_map.
Print Assumptions Kernel.AxInfinite.ax_rsum_map.
Print Assumptions Kernel.AxInfinite.ax_nb_pos.
Print Assumptions Kernel.AxInfinite.ax_mb_pos.
Print Assumptions Kernel.AxInfinite.ax_mb_le_1.
Print Assumptions Kernel.AxInfinite.ax_pb_in.
Print Assumptions Kernel.AxInfinite.ax_blk_sum.
Print Assumptions Kernel.AxInfinite.ax_block_mass_n.
Print Assumptions Kernel.AxInfinite.ax_pb_nonneg.
Print Assumptions Kernel.AxInfinite.ax_pow2_quad.
Print Assumptions Kernel.AxInfinite.ax_block_term.
Print Assumptions Kernel.AxInfinite.ax_block_loss_unbounded.
Print Assumptions Kernel.AxInfinite.ax_block_no_toll.
Print Assumptions Kernel.AxInfinite.ax_toll_covers_landauer_minimum.
(* === Kernel.AxLatch : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxLatch.ax_driven_determined.
Print Assumptions Kernel.AxLatch.ax_decompose.
Print Assumptions Kernel.AxLatch.ax_factor_grows.
Print Assumptions Kernel.AxLatch.ax_factor_determined.
Print Assumptions Kernel.AxLatch.ax_factor_determined_up_to_equiv.
Print Assumptions Kernel.AxLatch.ax_a2_iff_views.
Print Assumptions Kernel.AxLatch.ax_a2_threshold_form.
Print Assumptions Kernel.AxLatch.toggle_no_factorization.
Print Assumptions Kernel.AxLatch.clock_no_factorization.
Print Assumptions Kernel.AxLatch.indiscrete_loses_record.
Print Assumptions Kernel.AxLatch.two_point_is_join_latch.
Print Assumptions Kernel.AxLatch.two_point_record_axis_is_latch.
Print Assumptions Kernel.AxLatch.chain3_not_join_latch.
(* === Kernel.AxLatch2 : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxLatch2.product_pair_is_two_latches.
Print Assumptions Kernel.AxLatch2.nth_repeat_false.
Print Assumptions Kernel.AxLatch2.chain_vec_nth.
Print Assumptions Kernel.AxLatch2.chain_vec_length.
Print Assumptions Kernel.AxLatch2.chain_vec_le.
Print Assumptions Kernel.AxLatch2.chain_vec_inj.
Print Assumptions Kernel.AxLatch2.chain_seq_chain.
Print Assumptions Kernel.AxLatch2.chain_bits_tight.
Print Assumptions Kernel.AxLatch2.chain_bits_exact.
(* === Kernel.AxMerge : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxMerge.ax_NoDup_map_inj.
Print Assumptions Kernel.AxMerge.ax_up_spec.
Print Assumptions Kernel.AxMerge.ax_up_nodup.
Print Assumptions Kernel.AxMerge.ax_exit_merges_or_revokes.
Print Assumptions Kernel.AxMerge.ax_growth_exit_merges.
Print Assumptions Kernel.AxMerge.ax_a2_from_merge_price.
Print Assumptions Kernel.AxMerge.ax_a2_iff_flipping_merges_priced.
Print Assumptions Kernel.AxMerge.ax_nodup_app_disjoint.
Print Assumptions Kernel.AxMerge.ax_flips_compression_bound.
Print Assumptions Kernel.AxMerge.ax_a2_from_compression.
Print Assumptions Kernel.AxMerge.two_point_permanent_flip_merges.
Print Assumptions Kernel.AxMerge.history_escape.
Print Assumptions Kernel.AxMerge.toggle_escape.
Print Assumptions Kernel.AxMerge.free_merge_escape.
(* === Kernel.AxNecessity : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxNecessity.ax_clock_weakly_complete.
Print Assumptions Kernel.AxNecessity.ax_tc_has_free_move.
Print Assumptions Kernel.AxNecessity.ax_clock_not_tc.
Print Assumptions Kernel.AxNecessity.ax_clock_not_complete.
Print Assumptions Kernel.AxNecessity.ax_nec_earned_chain.
Print Assumptions Kernel.AxNecessity.ax_nec_toll_cost.
Print Assumptions Kernel.AxNecessity.ax_nec_toll_ledger.
Print Assumptions Kernel.AxNecessity.ax_nec_sound_check.
Print Assumptions Kernel.AxNecessity.ax_nec_respect_same.
Print Assumptions Kernel.AxNecessity.ax_nb_not_tc.
Print Assumptions Kernel.AxNecessity.ax_nec_base.
(* === Kernel.AxProb : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxProb.ax_rsum_app_cons.
Print Assumptions Kernel.AxProb.ax_rsum_le.
Print Assumptions Kernel.AxProb.ax_rsum_ext.
Print Assumptions Kernel.AxProb.ax_rsum_const.
Print Assumptions Kernel.AxProb.ax_rsum_plus.
Print Assumptions Kernel.AxProb.ax_rsum_minus.
Print Assumptions Kernel.AxProb.ax_rsum_scal.
Print Assumptions Kernel.AxProb.ax_rsum_scal_r.
Print Assumptions Kernel.AxProb.ax_rsum_nonneg.
Print Assumptions Kernel.AxProb.ax_rsum_ge_elt.
Print Assumptions Kernel.AxProb.ax_ln_le_sub.
Print Assumptions Kernel.AxProb.ax_ln_mono.
Print Assumptions Kernel.AxProb.ax_gibbs_term.
Print Assumptions Kernel.AxProb.ax_fibre_gibbs.
Print Assumptions Kernel.AxProb.ax_fibre_loss_empty.
Print Assumptions Kernel.AxProb.ax_loss_le.
Print Assumptions Kernel.AxProb.ax_uniform_loss_exact.
Print Assumptions Kernel.AxProb.ax_ln_pow2.
Print Assumptions Kernel.AxProb.ax_priced_loss_tight.
Print Assumptions Kernel.AxProb.ax_priced_loss_bits.
(* === Kernel.AxRice : 40 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxRice.ax_req_sym.
Print Assumptions Kernel.AxRice.ax_reach_req.
Print Assumptions Kernel.AxRice.ax_reach_equiv_sym.
Print Assumptions Kernel.AxRice.ax_record_equiv_sym.
Print Assumptions Kernel.AxRice.ax_record_equiv_reach.
Print Assumptions Kernel.AxRice.ax_hequiv_record.
Print Assumptions Kernel.AxRice.ax_obs_equiv_record.
Print Assumptions Kernel.AxRice.ax_obs_hagree.
Print Assumptions Kernel.AxRice.ax_rice_threshold.
Print Assumptions Kernel.AxRice.ax_rice_record.
Print Assumptions Kernel.AxRice.ax_diagonal_record.
Print Assumptions Kernel.AxRice.ax_diagonal_threshold.
Print Assumptions Kernel.AxRice.ax_reaches_ext.
Print Assumptions Kernel.AxRice.ax_reach_undecidable.
Print Assumptions Kernel.AxRice.ax_pair_le.
Print Assumptions Kernel.AxRice.ax_host_rec_obs.
Print Assumptions Kernel.AxRice.ax_host_rec_hagree.
Print Assumptions Kernel.AxRice.ax_host_floor_start.
Print Assumptions Kernel.AxRice.ax_pt_facts_leb.
Print Assumptions Kernel.AxRice.ax_facts_cap_run.
Print Assumptions Kernel.AxRice.ax_facts_cap.
Print Assumptions Kernel.AxRice.ax_facts_17_unreached.
Print Assumptions Kernel.AxRice.ax_nth_repeat.
Print Assumptions Kernel.AxRice.ax_fetch_chk.
Print Assumptions Kernel.AxRice.ax_fetch_halt.
Print Assumptions Kernel.AxRice.ax_inv_zero.
Print Assumptions Kernel.AxRice.ax_inv_step.
Print Assumptions Kernel.AxRice.ax_inv_run.
Print Assumptions Kernel.AxRice.ax_facts_reach.
Print Assumptions Kernel.AxRice.ax_prog_flag_ends.
Print Assumptions Kernel.AxRice.ax_prog_chan_ends.
Print Assumptions Kernel.AxRice.ax_prog_trap_ends.
Print Assumptions Kernel.AxRice.ax_host_point_undecidable.
Print Assumptions Kernel.AxRice.ax_host_point_diagonal.
Print Assumptions Kernel.AxRice.ax_flag_undecidable.
Print Assumptions Kernel.AxRice.ax_chan_undecidable.
Print Assumptions Kernel.AxRice.ax_trap_undecidable.
Print Assumptions Kernel.AxRice.ax_facts_undecidable.
Print Assumptions Kernel.AxRice.ax_flag_diagonal.
Print Assumptions Kernel.AxRice.ax_facts_17_trivial.
(* === Kernel.AxShadow : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxShadow.ax_nodup_map_collision.
Print Assumptions Kernel.AxShadow.ax_exit_collision.
Print Assumptions Kernel.AxShadow.merge_in_fibre.
Print Assumptions Kernel.AxShadow.ax_fibre_collapse_exit.
Print Assumptions Kernel.AxShadow.ax_step_fibre_in_fibre.
Print Assumptions Kernel.AxShadow.ax_eqb_spec.
Print Assumptions Kernel.AxShadow.ax_filter_nodup_le.
Print Assumptions Kernel.AxShadow.ax_compression_iff_fibres.
Print Assumptions Kernel.AxShadow.shadow_merge_escape.
Print Assumptions Kernel.AxShadow.ax_thresholds_separate.
Print Assumptions Kernel.AxShadow.ax_threshold_view_separates.
(* === Kernel.AxSmall : 32 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxSmall.aclaim_eqb_eq.
Print Assumptions Kernel.AxSmall.set_leb_spec.
Print Assumptions Kernel.AxSmall.claims_le.
Print Assumptions Kernel.AxSmall.claims_lub_cons.
Print Assumptions Kernel.AxSmall.as_run_core.
Print Assumptions Kernel.AxSmall.as_exec_cases.
Print Assumptions Kernel.AxSmall.as_set_grows.
Print Assumptions Kernel.AxSmall.sm_base.
Print Assumptions Kernel.AxSmall.sm_earned_exit.
Print Assumptions Kernel.AxSmall.sm_earned.
Print Assumptions Kernel.AxSmall.sm_toll.
Print Assumptions Kernel.AxSmall.sm_chain_set.
Print Assumptions Kernel.AxSmall.sm_chain_err.
Print Assumptions Kernel.AxSmall.small_every_claim.
Print Assumptions Kernel.AxSmall.sm_nonvac.
Print Assumptions Kernel.AxSmall.small_axis_thiele_complete.
Print Assumptions Kernel.AxSmall.small_record_is_join.
Print Assumptions Kernel.AxSmall.sm_flag_inv.
Print Assumptions Kernel.AxSmall.small_flag_agrees.
Print Assumptions Kernel.AxSmall.small_projection_commutes.
Print Assumptions Kernel.AxSmall.small_infinite_fibre.
Print Assumptions Kernel.AxSmall.over_mono.
Print Assumptions Kernel.AxSmall.over_exit_set_exit.
Print Assumptions Kernel.AxSmall.as_set_nonfire.
Print Assumptions Kernel.AxSmall.over_nec_join.
Print Assumptions Kernel.AxSmall.err_stays.
Print Assumptions Kernel.AxSmall.err_base.
Print Assumptions Kernel.AxSmall.trap_rec_ok.
Print Assumptions Kernel.AxSmall.trap_rec_err.
Print Assumptions Kernel.AxSmall.sm_chain_trap.
Print Assumptions Kernel.AxSmall.sm_chain_facts.
Print Assumptions Kernel.AxSmall.trap_nec_growth.
(* === Kernel.AxTwoPoint : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxTwoPoint.run_lift.
Print Assumptions Kernel.AxTwoPoint.run_keeps_true.
Print Assumptions Kernel.AxTwoPoint.two_exit.
Print Assumptions Kernel.AxTwoPoint.two_not_le_false.
Print Assumptions Kernel.AxTwoPoint.two_le_true_l.
Print Assumptions Kernel.AxTwoPoint.two_le_iff.
Print Assumptions Kernel.AxTwoPoint.lift_base_iff.
Print Assumptions Kernel.AxTwoPoint.lift_toll_iff.
Print Assumptions Kernel.AxTwoPoint.lift_nonvac_iff.
Print Assumptions Kernel.AxTwoPoint.lift_earned_iff.
Print Assumptions Kernel.AxTwoPoint.ax_tc_two_point_iff.
(* === Kernel.AxUniversal : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxUniversal.ax_view_run.
Print Assumptions Kernel.AxUniversal.ax_view_ledger.
Print Assumptions Kernel.AxUniversal.ax_prun_grows.
Print Assumptions Kernel.AxUniversal.ax_prun_mono.
Print Assumptions Kernel.AxUniversal.ax_view_latch_iff.
Print Assumptions Kernel.AxUniversal.ax_latches_determine_record.
Print Assumptions Kernel.AxUniversal.ax_view_surcharge_le_two.
Print Assumptions Kernel.AxUniversal.ax_threshold_universal.
(* === Kernel.AxWindow : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxWindow.ax_window_collision_overcharges.
Print Assumptions Kernel.AxWindow.ax_window_no_exact_price.
Print Assumptions Kernel.AxWindow.ax_step_price_exact.
Print Assumptions Kernel.AxWindow.ax_window_sees_record_exact.
Print Assumptions Kernel.AxWindow.ax_window_exact_iff_no_collision.
Print Assumptions Kernel.AxWindow.ax_overcharge_lower.
Print Assumptions Kernel.AxWindow.ax_overcharge_tight.
Print Assumptions Kernel.AxWindow.ax_exact_without_position.
Print Assumptions Kernel.AxWindow.ax_threshold_window_blind.
Print Assumptions Kernel.AxWindow.two_point_shadow_cannot_price_exactly.
(* === Kernel.CmpBlocks : 39 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpBlocks.cmp_get_env.
Print Assumptions Kernel.CmpBlocks.cmp_set_env.
Print Assumptions Kernel.CmpBlocks.cmp_mmstep_ext.
Print Assumptions Kernel.CmpBlocks.cmp_mmc_ext.
Print Assumptions Kernel.CmpBlocks.cmp_reach0_refl.
Print Assumptions Kernel.CmpBlocks.cmp_reach0_eq.
Print Assumptions Kernel.CmpBlocks.cmp_reach0_at.
Print Assumptions Kernel.CmpBlocks.cmp_reach0_trans.
Print Assumptions Kernel.CmpBlocks.cmp_reach_eq.
Print Assumptions Kernel.CmpBlocks.cmp_reach_at.
Print Assumptions Kernel.CmpBlocks.cmp_reach_reach0.
Print Assumptions Kernel.CmpBlocks.cmp_reach_trans0.
Print Assumptions Kernel.CmpBlocks.cmp_reach0_trans_reach.
Print Assumptions Kernel.CmpBlocks.cmp_reach_trans.
Print Assumptions Kernel.CmpBlocks.cmp_stp_inc.
Print Assumptions Kernel.CmpBlocks.cmp_stp_dec0.
Print Assumptions Kernel.CmpBlocks.cmp_stp_decS.
Print Assumptions Kernel.CmpBlocks.cmp_ins_at.
Print Assumptions Kernel.CmpBlocks.cmp_sc_l.
Print Assumptions Kernel.CmpBlocks.cmp_sc_r.
Print Assumptions Kernel.CmpBlocks.cmp_clear_len.
Print Assumptions Kernel.CmpBlocks.cmp_addmv_len.
Print Assumptions Kernel.CmpBlocks.cmp_copy_len.
Print Assumptions Kernel.CmpBlocks.cmp_sub_len.
Print Assumptions Kernel.CmpBlocks.cmp_fin_len.
Print Assumptions Kernel.CmpBlocks.cmp_eqblk_len.
Print Assumptions Kernel.CmpBlocks.cmp_ltblk_len.
Print Assumptions Kernel.CmpBlocks.cmp_blk_clear.
Print Assumptions Kernel.CmpBlocks.cmp_loop_addmv.
Print Assumptions Kernel.CmpBlocks.cmp_blk_addmv.
Print Assumptions Kernel.CmpBlocks.cmp_loop_copy1.
Print Assumptions Kernel.CmpBlocks.cmp_blk_copy.
Print Assumptions Kernel.CmpBlocks.cmp_loop_sub.
Print Assumptions Kernel.CmpBlocks.cmp_blk_sub.
Print Assumptions Kernel.CmpBlocks.cmp_blk_fin.
Print Assumptions Kernel.CmpBlocks.cmp_loop_eq.
Print Assumptions Kernel.CmpBlocks.cmp_blk_eq.
Print Assumptions Kernel.CmpBlocks.cmp_loop_lt.
Print Assumptions Kernel.CmpBlocks.cmp_blk_lt.
(* === Kernel.CmpCompile : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpCompile.cmp_mm_load_simul.
Print Assumptions Kernel.CmpCompile.cmp_flat_length.
Print Assumptions Kernel.CmpCompile.cmp_stageA_fwd.
Print Assumptions Kernel.CmpCompile.cmp_stageA_bwd.
Print Assumptions Kernel.CmpCompile.cmp_stageA.
(* === Kernel.CmpExpr : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpExpr.cmp_cexp_len.
Print Assumptions Kernel.CmpExpr.cmp_blk_incs.
Print Assumptions Kernel.CmpExpr.cmp_cexp_spec.
Print Assumptions Kernel.CmpExpr.cmp_cb_len.
Print Assumptions Kernel.CmpExpr.cmp_cmp_spec.
Print Assumptions Kernel.CmpExpr.cmp_cb_spec.
(* === Kernel.CmpFinal : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpFinal.cmp_exec_iff.
Print Assumptions Kernel.CmpFinal.cmp_final.
(* === Kernel.CmpFlat : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpFlat.cmp_fi_ok_jmp.
Print Assumptions Kernel.CmpFlat.cmp_fstep_fun.
Print Assumptions Kernel.CmpFlat.cmp_fstep_total.
Print Assumptions Kernel.CmpFlat.cmp_fc_length.
Print Assumptions Kernel.CmpFlat.cmp_sub_left.
Print Assumptions Kernel.CmpFlat.cmp_sub_right.
Print Assumptions Kernel.CmpFlat.cmp_instr_at.
Print Assumptions Kernel.CmpFlat.cmp_instr_sub.
Print Assumptions Kernel.CmpFlat.cmp_step_then.
Print Assumptions Kernel.CmpFlat.cmp_fc_fwd.
Print Assumptions Kernel.CmpFlat.cmp_one_step.
Print Assumptions Kernel.CmpFlat.cmp_first_step.
Print Assumptions Kernel.CmpFlat.cmp_steps_fun.
Print Assumptions Kernel.CmpFlat.cmp_fc_bwd.
(* === Kernel.CmpGuest : 25 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpGuest.cmp_gicomp_length.
Print Assumptions Kernel.CmpGuest.cmp_gstep_total.
Print Assumptions Kernel.CmpGuest.cmp_gicomp_sound.
Print Assumptions Kernel.CmpGuest.cmp_gwrap_map.
Print Assumptions Kernel.CmpGuest.cmp_gwrap_length.
Print Assumptions Kernel.CmpGuest.cmp_length_compiler_map.
Print Assumptions Kernel.CmpGuest.cmp_link_map.
Print Assumptions Kernel.CmpGuest.cmp_linker_map.
Print Assumptions Kernel.CmpGuest.cmp_comp_map.
Print Assumptions Kernel.CmpGuest.cmp_gerr_eq.
Print Assumptions Kernel.CmpGuest.cmp_glink_eq.
Print Assumptions Kernel.CmpGuest.cmp_gcode_eq.
Print Assumptions Kernel.CmpGuest.cmp_gstep_lift.
Print Assumptions Kernel.CmpGuest.cmp_g_complete.
Print Assumptions Kernel.CmpGuest.cmp_xunlift.
Print Assumptions Kernel.CmpGuest.cmp_icomp_xmm_map.
Print Assumptions Kernel.CmpGuest.cmp_comp_ymma.
Print Assumptions Kernel.CmpGuest.cmp_gcode_ymma.
Print Assumptions Kernel.CmpGuest.cmp_ystep_ex.
Print Assumptions Kernel.CmpGuest.cmp_pr_halted_out.
Print Assumptions Kernel.CmpGuest.cmp_lift_run_conv.
Print Assumptions Kernel.CmpGuest.cmp_pr_out_halted.
Print Assumptions Kernel.CmpGuest.cmp_guest_final_of.
Print Assumptions Kernel.CmpGuest.cmp_guest_fwd.
Print Assumptions Kernel.CmpGuest.cmp_guest_bwd.
(* === Kernel.CmpHost : 31 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpHost.cmp_hstep_fun.
Print Assumptions Kernel.CmpHost.cmp_hcomp_length.
Print Assumptions Kernel.CmpHost.cmp_hprog_one.
Print Assumptions Kernel.CmpHost.cmp_hcomp_sound.
Print Assumptions Kernel.CmpHost.cmp_mm_total.
Print Assumptions Kernel.CmpHost.cmp_mm_fun2.
Print Assumptions Kernel.CmpHost.cmp_hcode_length.
Print Assumptions Kernel.CmpHost.cmp_hlink_start.
Print Assumptions Kernel.CmpHost.cmp_hlink_out.
Print Assumptions Kernel.CmpHost.cmp_hsubcode.
Print Assumptions Kernel.CmpHost.cmp_host_sound.
Print Assumptions Kernel.CmpHost.cmp_host_complete.
Print Assumptions Kernel.CmpHost.cmp_host_output.
Print Assumptions Kernel.CmpHost.cmp_host_output_conv.
Print Assumptions Kernel.CmpHost.cmp_mm_hstep_total.
Print Assumptions Kernel.CmpHost.cmp_hsame_refl.
Print Assumptions Kernel.CmpHost.cmp_hsame_trans.
Print Assumptions Kernel.CmpHost.cmp_hfetch.
Print Assumptions Kernel.CmpHost.cmp_hfetch_none.
Print Assumptions Kernel.CmpHost.cmp_hfetch_some.
Print Assumptions Kernel.CmpHost.cmp_cexec_inc.
Print Assumptions Kernel.CmpHost.cmp_cexec_dec.
Print Assumptions Kernel.CmpHost.cmp_hstep_run.
Print Assumptions Kernel.CmpHost.cmp_hhalted.
Print Assumptions Kernel.CmpHost.cmp_hhalted_out.
Print Assumptions Kernel.CmpHost.cmp_host_run_fwd.
Print Assumptions Kernel.CmpHost.cmp_host_run_bwd.
Print Assumptions Kernel.CmpHost.cmp_hrel_start.
Print Assumptions Kernel.CmpHost.cmp_host_final_of.
Print Assumptions Kernel.CmpHost.cmp_host_fwd.
Print Assumptions Kernel.CmpHost.cmp_host_bwd.
(* === Kernel.CmpInline : 35 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpInline.cmp_ashift_eval.
Print Assumptions Kernel.CmpInline.cmp_bshift_eval.
Print Assumptions Kernel.CmpInline.cmp_ashift_max.
Print Assumptions Kernel.CmpInline.cmp_bshift_max.
Print Assumptions Kernel.CmpInline.cmp_aeval_below.
Print Assumptions Kernel.CmpInline.cmp_beval_below.
Print Assumptions Kernel.CmpInline.cmp_seqs_eval.
Print Assumptions Kernel.CmpInline.cmp_seqs_inv.
Print Assumptions Kernel.CmpInline.cmp_runa_app.
Print Assumptions Kernel.CmpInline.cmp_runa_cons.
Print Assumptions Kernel.CmpInline.cmp_runa_block_out.
Print Assumptions Kernel.CmpInline.cmp_runa_block_in.
Print Assumptions Kernel.CmpInline.cmp_seqs_nocall.
Print Assumptions Kernel.CmpInline.cmp_inl_nocall.
Print Assumptions Kernel.CmpInline.cmp_lmax_ge.
Print Assumptions Kernel.CmpInline.cmp_nth_avmax.
Print Assumptions Kernel.CmpInline.cmp_procsz_np.
Print Assumptions Kernel.CmpInline.cmp_pre_spec.
Print Assumptions Kernel.CmpInline.cmp_post_spec.
Print Assumptions Kernel.CmpInline.cmp_frame_aeval.
Print Assumptions Kernel.CmpInline.cmp_frame_beval.
Print Assumptions Kernel.CmpInline.cmp_wfs_mono.
Print Assumptions Kernel.CmpInline.cmp_assigns_agree.
Print Assumptions Kernel.CmpInline.cmp_inl_skip.
Print Assumptions Kernel.CmpInline.cmp_inl_assign.
Print Assumptions Kernel.CmpInline.cmp_inl_seq.
Print Assumptions Kernel.CmpInline.cmp_inl_if.
Print Assumptions Kernel.CmpInline.cmp_inl_while.
Print Assumptions Kernel.CmpInline.cmp_inl_call.
Print Assumptions Kernel.CmpInline.cmp_call_pre_frame.
Print Assumptions Kernel.CmpInline.cmp_call_post_frame.
Print Assumptions Kernel.CmpInline.cmp_inl_fwd.
Print Assumptions Kernel.CmpInline.cmp_inl_bwd_aux.
Print Assumptions Kernel.CmpInline.cmp_inl_bwd_all.
Print Assumptions Kernel.CmpInline.cmp_inl_bwd.
(* === Kernel.CmpLang : 24 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpLang.cmp_upd_same.
Print Assumptions Kernel.CmpLang.cmp_upd_other.
Print Assumptions Kernel.CmpLang.cmp_eqv_refl.
Print Assumptions Kernel.CmpLang.cmp_eqv_sym.
Print Assumptions Kernel.CmpLang.cmp_eqv_trans.
Print Assumptions Kernel.CmpLang.cmp_upd_eqv.
Print Assumptions Kernel.CmpLang.cmp_aeval_eqv.
Print Assumptions Kernel.CmpLang.cmp_beval_eqv.
Print Assumptions Kernel.CmpLang.cmp_assigns_eqv.
Print Assumptions Kernel.CmpLang.cmp_args_eqv.
Print Assumptions Kernel.CmpLang.cmp_ceval_ext.
Print Assumptions Kernel.CmpLang.cmp_ceval_det.
Print Assumptions Kernel.CmpLang.cmp_ceval_skip_inv.
Print Assumptions Kernel.CmpLang.cmp_ceval_assign_inv.
Print Assumptions Kernel.CmpLang.cmp_ceval_seq_inv.
Print Assumptions Kernel.CmpLang.cmp_ceval_if_inv.
Print Assumptions Kernel.CmpLang.cmp_ceval_while_inv.
Print Assumptions Kernel.CmpLang.cmp_ceval_call_inv.
Print Assumptions Kernel.CmpLang.cmp_lget_lset.
Print Assumptions Kernel.CmpLang.cmp_lget_lset_eqv.
Print Assumptions Kernel.CmpLang.cmp_lassigns_eqv.
Print Assumptions Kernel.CmpLang.cmp_largs_eqv.
Print Assumptions Kernel.CmpLang.cmp_interp_sound.
Print Assumptions Kernel.CmpLang.cmp_interp_complete.
(* === Kernel.CmpMM : 25 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpMM.cmp_blen_pos.
Print Assumptions Kernel.CmpMM.cmp_icomp_length.
Print Assumptions Kernel.CmpMM.cmp_fi_ok_true.
Print Assumptions Kernel.CmpMM.cmp_aeval_simul.
Print Assumptions Kernel.CmpMM.cmp_beval_simul.
Print Assumptions Kernel.CmpMM.cmp_icomp_assign_core.
Print Assumptions Kernel.CmpMM.cmp_icomp_jmpf_core.
Print Assumptions Kernel.CmpMM.cmp_nop_prog.
Print Assumptions Kernel.CmpMM.cmp_icomp_assign_eq.
Print Assumptions Kernel.CmpMM.cmp_icomp_jmpf_eq.
Print Assumptions Kernel.CmpMM.cmp_icomp_nop_eq.
Print Assumptions Kernel.CmpMM.cmp_simul_pw.
Print Assumptions Kernel.CmpMM.cmp_sound_nop.
Print Assumptions Kernel.CmpMM.cmp_sound_assign.
Print Assumptions Kernel.CmpMM.cmp_sound_jmpf.
Print Assumptions Kernel.CmpMM.cmp_icomp_sound.
Print Assumptions Kernel.CmpMM.cmp_mm_fun.
Print Assumptions Kernel.CmpMM.cmp_code_length.
Print Assumptions Kernel.CmpMM.cmp_link_start.
Print Assumptions Kernel.CmpMM.cmp_link_out.
Print Assumptions Kernel.CmpMM.cmp_mm_subcode.
Print Assumptions Kernel.CmpMM.cmp_mm_sound.
Print Assumptions Kernel.CmpMM.cmp_mm_complete.
Print Assumptions Kernel.CmpMM.cmp_mm_output.
Print Assumptions Kernel.CmpMM.cmp_mm_output_conv.
(* === Kernel.CmpPipeline : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpPipeline.cmp_prog_regs_lt.
Print Assumptions Kernel.CmpPipeline.cmp_gk_wf.
Print Assumptions Kernel.CmpPipeline.cmp_load_zero.
Print Assumptions Kernel.CmpPipeline.cmp_pipeline_host.
Print Assumptions Kernel.CmpPipeline.cmp_guest_at_eq.
Print Assumptions Kernel.CmpPipeline.cmp_out_lt_gk.
Print Assumptions Kernel.CmpPipeline.cmp_out_lt_nv0.
Print Assumptions Kernel.CmpPipeline.cmp_pipeline_guest.
Print Assumptions Kernel.CmpPipeline.cmp_pipeline_guest_final.
Print Assumptions Kernel.CmpPipeline.cmp_pipeline_U.
Print Assumptions Kernel.CmpPipeline.cmp_pipeline.
(* === Kernel.CmpRun : 33 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CmpRun.cr_get_0.
Print Assumptions Kernel.CmpRun.cr_get_S.
Print Assumptions Kernel.CmpRun.cr_divmod.
Print Assumptions Kernel.CmpRun.cr_get_set_f.
Print Assumptions Kernel.CmpRun.cr_get_set.
Print Assumptions Kernel.CmpRun.cr_build_out.
Print Assumptions Kernel.CmpRun.cr_build_in.
Print Assumptions Kernel.CmpRun.cr_ptab_get.
Print Assumptions Kernel.CmpRun.cr_ptab_none.
Print Assumptions Kernel.CmpRun.cr_ptab_some.
Print Assumptions Kernel.CmpRun.cr_rget_rset.
Print Assumptions Kernel.CmpRun.cr_rel_set.
Print Assumptions Kernel.CmpRun.cr_loadf_get.
Print Assumptions Kernel.CmpRun.cr_load_rel.
Print Assumptions Kernel.CmpRun.cr_run_none.
Print Assumptions Kernel.CmpRun.cr_run_zero.
Print Assumptions Kernel.CmpRun.cr_run_some.
Print Assumptions Kernel.CmpRun.cr_next_spec.
Print Assumptions Kernel.CmpRun.cr_step_inv.
Print Assumptions Kernel.CmpRun.cr_step_of.
Print Assumptions Kernel.CmpRun.cr_run_steps.
Print Assumptions Kernel.CmpRun.cr_in_code_of.
Print Assumptions Kernel.CmpRun.cr_run_sound.
Print Assumptions Kernel.CmpRun.cmp_wfs_b_spec.
Print Assumptions Kernel.CmpRun.cmp_wfp_from_spec.
Print Assumptions Kernel.CmpRun.cmp_wf_b_spec.
Print Assumptions Kernel.CmpRun.cmp_hostprog_eq.
Print Assumptions Kernel.CmpRun.cmp_exec_run.
Print Assumptions Kernel.CmpRun.cmp_exec_machine.
Print Assumptions Kernel.CmpRun.cmp_exec_sound.
Print Assumptions Kernel.CmpRun.cmp_exec_complete.
Print Assumptions Kernel.CmpRun.cmp_exec_unhalted.
Print Assumptions Kernel.CmpRun.cmp_exec_agrees.
(* === Kernel.CompilerChecker : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerChecker.cg_uprop_eqb_eq.
Print Assumptions Kernel.CompilerChecker.cg_out_codeb_spec.
Print Assumptions Kernel.CompilerChecker.cg_ueval_total.
Print Assumptions Kernel.CompilerChecker.cg_ueval_iff.
Print Assumptions Kernel.CompilerChecker.cg_env_chk_spare.
Print Assumptions Kernel.CompilerChecker.cg_mm_sss_env_fun.
Print Assumptions Kernel.CompilerChecker.cg_routine_end_out.
Print Assumptions Kernel.CompilerChecker.cg_routine_output.
Print Assumptions Kernel.CompilerChecker.cg_checker_sound.
Print Assumptions Kernel.CompilerChecker.cg_env_chk_gk.
Print Assumptions Kernel.CompilerChecker.cg_checker_exact_run.
Print Assumptions Kernel.CompilerChecker.cg_checker_exact.
(* === Kernel.CompilerCodes : 34 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerCodes.cg_divides_mod.
Print Assumptions Kernel.CompilerCodes.cg_expo_fuel_spec.
Print Assumptions Kernel.CompilerCodes.cg_expo_spec.
Print Assumptions Kernel.CompilerCodes.cg_qs_prime.
Print Assumptions Kernel.CompilerCodes.cg_qs_gt1.
Print Assumptions Kernel.CompilerCodes.cg_gk_pos.
Print Assumptions Kernel.CompilerCodes.cg_gk_ext.
Print Assumptions Kernel.CompilerCodes.cg_gk_not_div.
Print Assumptions Kernel.CompilerCodes.cg_gk_split.
Print Assumptions Kernel.CompilerCodes.cg_expo_gk.
Print Assumptions Kernel.CompilerCodes.cg_expo_gk_zero.
Print Assumptions Kernel.CompilerCodes.cg_gk_inj.
Print Assumptions Kernel.CompilerCodes.cg_get_env.
Print Assumptions Kernel.CompilerCodes.cg_set_env_eq.
Print Assumptions Kernel.CompilerCodes.cg_set_env_neq.
Print Assumptions Kernel.CompilerCodes.cg_zero_at_set.
Print Assumptions Kernel.CompilerCodes.cg_gk_inc.
Print Assumptions Kernel.CompilerCodes.cg_gk_dec.
Print Assumptions Kernel.CompilerCodes.cg_gk_zero_not_div.
Print Assumptions Kernel.CompilerCodes.cg_idec_icode.
Print Assumptions Kernel.CompilerCodes.cg_pdec_penc.
Print Assumptions Kernel.CompilerCodes.cg_rdec_renc.
Print Assumptions Kernel.CompilerCodes.cg_mme_exec_sound.
Print Assumptions Kernel.CompilerCodes.cg_mme_fetch_some.
Print Assumptions Kernel.CompilerCodes.cg_mme_fetch_at.
Print Assumptions Kernel.CompilerCodes.cg_mme_fetch_none.
Print Assumptions Kernel.CompilerCodes.cg_mme_step_sound.
Print Assumptions Kernel.CompilerCodes.cg_mme_step_complete.
Print Assumptions Kernel.CompilerCodes.cg_mme_step_none.
Print Assumptions Kernel.CompilerCodes.cg_mme_run_fuel_sound.
Print Assumptions Kernel.CompilerCodes.cg_mme_run_fuel_complete.
Print Assumptions Kernel.CompilerCodes.cg_mme_run_fuel_output.
Print Assumptions Kernel.CompilerCodes.cg_mme_exec_ext.
Print Assumptions Kernel.CompilerCodes.cg_mme_run_ext.
(* === Kernel.CompilerGuest : 74 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerGuest.cg_maxreg_in.
Print Assumptions Kernel.CompilerGuest.cg_xmax_in.
Print Assumptions Kernel.CompilerGuest.cg_sc_cons.
Print Assumptions Kernel.CompilerGuest.cg_sc_app.
Print Assumptions Kernel.CompilerGuest.cg_sc_here1.
Print Assumptions Kernel.CompilerGuest.cg_sc_here.
Print Assumptions Kernel.CompilerGuest.cg_sc_in.
Print Assumptions Kernel.CompilerGuest.cg_set_rf.
Print Assumptions Kernel.CompilerGuest.cg_Pn_spec.
Print Assumptions Kernel.CompilerGuest.cg_Ps_spec.
Print Assumptions Kernel.CompilerGuest.cg_Pc_spec.
Print Assumptions Kernel.CompilerGuest.cg_Pr_spec.
Print Assumptions Kernel.CompilerGuest.cg_T_ge.
Print Assumptions Kernel.CompilerGuest.cg_T_fresh.
Print Assumptions Kernel.CompilerGuest.cg_src_reg.
Print Assumptions Kernel.CompilerGuest.cg_sc_jmp0.
Print Assumptions Kernel.CompilerGuest.cg_sc_next.
Print Assumptions Kernel.CompilerGuest.cg_sc_dech.
Print Assumptions Kernel.CompilerGuest.cg_sc_tr1.
Print Assumptions Kernel.CompilerGuest.cg_sc_step.
Print Assumptions Kernel.CompilerGuest.cg_sc_cost.
Print Assumptions Kernel.CompilerGuest.cg_sc_erI.
Print Assumptions Kernel.CompilerGuest.cg_sc_erS.
Print Assumptions Kernel.CompilerGuest.cg_sc_tr2.
Print Assumptions Kernel.CompilerGuest.cg_sc_jmp1.
Print Assumptions Kernel.CompilerGuest.cg_sc_erT.
Print Assumptions Kernel.CompilerGuest.cg_sc_read.
Print Assumptions Kernel.CompilerGuest.cg_sc_decB.
Print Assumptions Kernel.CompilerGuest.cg_sc_decE.
Print Assumptions Kernel.CompilerGuest.cg_sc_incE1.
Print Assumptions Kernel.CompilerGuest.cg_sc_jmp2.
Print Assumptions Kernel.CompilerGuest.cg_sc_earn.
Print Assumptions Kernel.CompilerGuest.cg_sc_incE2.
Print Assumptions Kernel.CompilerGuest.cg_sc_decC1.
Print Assumptions Kernel.CompilerGuest.cg_sc_decC2.
Print Assumptions Kernel.CompilerGuest.cg_sc_decC3.
Print Assumptions Kernel.CompilerGuest.cg_sc_erT2.
Print Assumptions Kernel.CompilerGuest.cg_sc_pl.
Print Assumptions Kernel.CompilerGuest.cg_sc_pay.
Print Assumptions Kernel.CompilerGuest.cg_sc_jmp3.
Print Assumptions Kernel.CompilerGuest.cg_sc_halt.
Print Assumptions Kernel.CompilerGuest.cg_k_gt.
Print Assumptions Kernel.CompilerGuest.cg_rf_high.
Print Assumptions Kernel.CompilerGuest.cg_rf_spare.
Print Assumptions Kernel.CompilerGuest.cg_eqv_zero_high.
Print Assumptions Kernel.CompilerGuest.cg_eqv_spare.
Print Assumptions Kernel.CompilerGuest.cg_in1.
Print Assumptions Kernel.CompilerGuest.cg_in2.
Print Assumptions Kernel.CompilerGuest.cg_x_block.
Print Assumptions Kernel.CompilerGuest.cg_x_block_p.
Print Assumptions Kernel.CompilerGuest.cg_x_one.
Print Assumptions Kernel.CompilerGuest.cg_x_dec0.
Print Assumptions Kernel.CompilerGuest.cg_x_decS.
Print Assumptions Kernel.CompilerGuest.cg_x_inc.
Print Assumptions Kernel.CompilerGuest.cg_x_pay.
Print Assumptions Kernel.CompilerGuest.cg_x_earn.
Print Assumptions Kernel.CompilerGuest.cg_x_dec_next.
Print Assumptions Kernel.CompilerGuest.cg_x_erase.
Print Assumptions Kernel.CompilerGuest.cg_x_transfert.
Print Assumptions Kernel.CompilerGuest.cg_x_payloop.
Print Assumptions Kernel.CompilerGuest.cg_set2_rf.
Print Assumptions Kernel.CompilerGuest.cg_x_move.
Print Assumptions Kernel.CompilerGuest.cg_x_halt.
Print Assumptions Kernel.CompilerGuest.cg_x_read.
Print Assumptions Kernel.CompilerGuest.cg_x_noraise.
Print Assumptions Kernel.CompilerGuest.cg_x_tail_new.
Print Assumptions Kernel.CompilerGuest.cg_x_tail.
Print Assumptions Kernel.CompilerGuest.cg_x_check.
Print Assumptions Kernel.CompilerGuest.cg_x_to_new.
Print Assumptions Kernel.CompilerGuest.cg_e0_rf.
Print Assumptions Kernel.CompilerGuest.cg_e0_high.
Print Assumptions Kernel.CompilerGuest.cg_x_prologue.
Print Assumptions Kernel.CompilerGuest.cg_x_step.
Print Assumptions Kernel.CompilerGuest.cg_x_stop.
(* === Kernel.CompilerGuestRun : 37 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerGuestRun.cg_compile_steps.
Print Assumptions Kernel.CompilerGuestRun.cg_run_prog_add.
Print Assumptions Kernel.CompilerGuestRun.cg_run_prog_stay.
Print Assumptions Kernel.CompilerGuestRun.cg_cert_mono.
Print Assumptions Kernel.CompilerGuestRun.cg_trace_succ.
Print Assumptions Kernel.CompilerGuestRun.cg_passing_app.
Print Assumptions Kernel.CompilerGuestRun.cg_passing_sum.
Print Assumptions Kernel.CompilerGuestRun.cg_psum_mono.
Print Assumptions Kernel.CompilerGuestRun.cg_psum_ge.
Print Assumptions Kernel.CompilerGuestRun.cg_psum_two.
Print Assumptions Kernel.CompilerGuestRun.cg_y_phase.
Print Assumptions Kernel.CompilerGuestRun.cg_fetch_at.
Print Assumptions Kernel.CompilerGuestRun.cg_fetch_halt.
Print Assumptions Kernel.CompilerGuestRun.cg_fetch_new.
Print Assumptions Kernel.CompilerGuestRun.cg_head_instr.
Print Assumptions Kernel.CompilerGuestRun.cg_fetch_head.
Print Assumptions Kernel.CompilerGuestRun.cg_ystart_simul.
Print Assumptions Kernel.CompilerGuestRun.cg_y_head.
Print Assumptions Kernel.CompilerGuestRun.cg_point_facts.
Print Assumptions Kernel.CompilerGuestRun.cg_point_live.
Print Assumptions Kernel.CompilerGuestRun.cg_y_stop.
Print Assumptions Kernel.CompilerGuestRun.cg_yhalt_facts.
Print Assumptions Kernel.CompilerGuestRun.cg_first_halt.
Print Assumptions Kernel.CompilerGuestRun.cg_cover.
Print Assumptions Kernel.CompilerGuestRun.cg_guest_matching_points.
Print Assumptions Kernel.CompilerGuestRun.cg_guest_halts_at.
Print Assumptions Kernel.CompilerGuestRun.cg_guest_halting_iff.
Print Assumptions Kernel.CompilerGuestRun.cg_guest_flag_iff.
Print Assumptions Kernel.CompilerGuestRun.cg_first_true.
Print Assumptions Kernel.CompilerGuestRun.cg_not_halted_before.
Print Assumptions Kernel.CompilerGuestRun.cg_latch_before.
Print Assumptions Kernel.CompilerGuestRun.cg_y_new.
Print Assumptions Kernel.CompilerGuestRun.cg_guest_earned.
Print Assumptions Kernel.CompilerGuestRun.cg_x_reach_head.
Print Assumptions Kernel.CompilerGuestRun.cg_x_halted.
Print Assumptions Kernel.CompilerGuestRun.cg_source_halts_of_guest.
Print Assumptions Kernel.CompilerGuestRun.cg_source_certifies_of_guest.
(* === Kernel.CompilerIcomp : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerIcomp.cg_icomp_length.
Print Assumptions Kernel.CompilerIcomp.cg_yexec_pay.
Print Assumptions Kernel.CompilerIcomp.cg_yexec_chk.
Print Assumptions Kernel.CompilerIcomp.cg_yexec_cmt.
Print Assumptions Kernel.CompilerIcomp.cg_yexec_crt.
Print Assumptions Kernel.CompilerIcomp.cg_ystep_code.
Print Assumptions Kernel.CompilerIcomp.cg_pos10.
Print Assumptions Kernel.CompilerIcomp.cg_qs_pos.
Print Assumptions Kernel.CompilerIcomp.cg_simul_counter.
Print Assumptions Kernel.CompilerIcomp.cg_icomp_sound.
Print Assumptions Kernel.CompilerIcomp.cg_compile_sound.
Print Assumptions Kernel.CompilerIcomp.cg_link_start.
Print Assumptions Kernel.CompilerIcomp.cg_code_length.
Print Assumptions Kernel.CompilerIcomp.cg_link_out.
Print Assumptions Kernel.CompilerIcomp.cg_compile_output.
Print Assumptions Kernel.CompilerIcomp.cg_simul_start.
Print Assumptions Kernel.CompilerIcomp.cg_compile_start.
(* === Kernel.CompilerInstrument : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerInstrument.cg_sss_step_in.
Print Assumptions Kernel.CompilerInstrument.cg_frame_step.
Print Assumptions Kernel.CompilerInstrument.cg_frame.
Print Assumptions Kernel.CompilerInstrument.cg_cicomp_length.
Print Assumptions Kernel.CompilerInstrument.cg_two_steps.
Print Assumptions Kernel.CompilerInstrument.cg_cicomp_sound.
Print Assumptions Kernel.CompilerInstrument.cg_count_lsum.
Print Assumptions Kernel.CompilerInstrument.cg_count_code_length.
Print Assumptions Kernel.CompilerInstrument.cg_count_steps.
Print Assumptions Kernel.CompilerInstrument.cg_steps_count.
Print Assumptions Kernel.CompilerInstrument.cg_count_link_start.
Print Assumptions Kernel.CompilerInstrument.cg_count_link_out.
Print Assumptions Kernel.CompilerInstrument.cg_read_T_spec.
Print Assumptions Kernel.CompilerInstrument.cg_read_T_unique.
(* === Kernel.CompilerLifts : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerLifts.cg_sss_lift.
Print Assumptions Kernel.CompilerLifts.cg_xstep_fun.
Print Assumptions Kernel.CompilerLifts.cg_lift_mm.
Print Assumptions Kernel.CompilerLifts.cg_ystep_fun.
Print Assumptions Kernel.CompilerLifts.cg_ystep_intro.
Print Assumptions Kernel.CompilerLifts.cg_keep_refl.
Print Assumptions Kernel.CompilerLifts.cg_keep_trans.
Print Assumptions Kernel.CompilerLifts.cg_pos2_cases.
Print Assumptions Kernel.CompilerLifts.cg_vec2_ex.
Print Assumptions Kernel.CompilerLifts.cg_lift_mma2_step.
Print Assumptions Kernel.CompilerLifts.cg_lift_mma2.
Print Assumptions Kernel.CompilerLifts.cg_lift_mma2_progress.
Print Assumptions Kernel.CompilerLifts.cg_at_pc.
Print Assumptions Kernel.CompilerLifts.cg_pr_step_at.
Print Assumptions Kernel.CompilerLifts.cg_lift_run.
(* === Kernel.CompilerRaBridge : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CompilerRaBridge.cg_routine_of_ra.
Print Assumptions Kernel.CompilerRaBridge.cg_routine_exists.
Print Assumptions Kernel.CompilerRaBridge.cg_checker_sound_ra.
(* === Kernel.CrossBaseGranularity : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CrossBaseGranularity.weak_base_equiv_refl_holds.
Print Assumptions Kernel.CrossBaseGranularity.weak_base_equiv_sym_holds.
Print Assumptions Kernel.CrossBaseGranularity.weak_match_left_runs.
Print Assumptions Kernel.CrossBaseGranularity.weak_match_right_runs.
Print Assumptions Kernel.CrossBaseGranularity.weak_base_equiv_trans_holds.
Print Assumptions Kernel.CrossBaseGranularity.weak_equiv_preserves_record_latch_holds.
Print Assumptions Kernel.CrossBaseGranularity.record_axis_is_latch_on_tm_holds.
(* === Kernel.CrossBaseGranularityL : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CrossBaseGranularityL.l_step_fun_value.
Print Assumptions Kernel.CrossBaseGranularityL.l_step_fun_sound.
Print Assumptions Kernel.CrossBaseGranularityL.l_step_fun_complete.
Print Assumptions Kernel.CrossBaseGranularityL.l_step_fun_correct.
Print Assumptions Kernel.CrossBaseGranularityL.l_base_next_is_step.
Print Assumptions Kernel.CrossBaseGranularityL.l_base_halted_iff_irreducible.
Print Assumptions Kernel.CrossBaseGranularityL.l_base_next_cases.
Print Assumptions Kernel.CrossBaseGranularityL.l_base_run_is_star.
Print Assumptions Kernel.CrossBaseGranularityL.star_is_l_base_run.
Print Assumptions Kernel.CrossBaseGranularityL.record_axis_is_latch_on_l_holds.
(* === Kernel.CrossBaseGranularityRAM : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CrossBaseGranularityRAM.set_reg_same.
Print Assumptions Kernel.CrossBaseGranularityRAM.set_reg_other.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_store_indirect_writes.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_load_indirect_reads.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_store_indirect_frame.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_store_then_load.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_jump_pos_taken.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_jump_pos_not_taken.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_halted_stutters.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_base_halted_stutters.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_base_run_is_ram_run.
Print Assumptions Kernel.CrossBaseGranularityRAM.ram_base_has_initial.
Print Assumptions Kernel.CrossBaseGranularityRAM.record_axis_is_latch_on_ram_holds.
(* === Kernel.CzCS : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzCS.cmpz_cs_run.
Print Assumptions Kernel.CzCS.cmpz_cs_total_eq.
Print Assumptions Kernel.CzCS.cmpz_cs_or_run.
Print Assumptions Kernel.CzCS.cmpz_cs_and_run.
Print Assumptions Kernel.CzCS.cmpz_cs_or_total.
Print Assumptions Kernel.CzCS.cmpz_cs_and_total.
Print Assumptions Kernel.CzCS.cmpz_cs_or_floor.
Print Assumptions Kernel.CzCS.cmpz_cs_and_floor.
Print Assumptions Kernel.CzCS.cmpz_cs_and_tight.
(* === Kernel.CzCat : 33 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzCat.cmpz_hom_eq_refl.
Print Assumptions Kernel.CzCat.cmpz_hom_eq_sym.
Print Assumptions Kernel.CzCat.cmpz_hom_eq_trans.
Print Assumptions Kernel.CzCat.cmpz_hom_eq_rec.
Print Assumptions Kernel.CzCat.cmpz_hom_trace.
Print Assumptions Kernel.CzCat.cmpz_hom_id_left.
Print Assumptions Kernel.CzCat.cmpz_hom_id_right.
Print Assumptions Kernel.CzCat.cmpz_hom_assoc.
Print Assumptions Kernel.CzCat.cmpz_hom_comp_cong.
Print Assumptions Kernel.CzCat.cmpz_prod_universal.
Print Assumptions Kernel.CzCat.cmpz_unit_terminal.
Print Assumptions Kernel.CzCat.cmpz_unit_not_tc.
Print Assumptions Kernel.CzCat.cmpz_id_cost_exact.
Print Assumptions Kernel.CzCat.cmpz_id_cost_ge.
Print Assumptions Kernel.CzCat.cmpz_hom_trace_cost_ge.
Print Assumptions Kernel.CzCat.cmpz_hom_trace_cost_exact.
Print Assumptions Kernel.CzCat.cmpz_comp_cost_ge.
Print Assumptions Kernel.CzCat.cmpz_comp_cost_exact.
Print Assumptions Kernel.CzCat.cmpz_tensor_id.
Print Assumptions Kernel.CzCat.cmpz_tensor_comp.
Print Assumptions Kernel.CzCat.cmpz_tensor_cost_ge.
Print Assumptions Kernel.CzCat.cmpz_swap_inv.
Print Assumptions Kernel.CzCat.cmpz_assoc_iso.
Print Assumptions Kernel.CzCat.cmpz_unit_r_iso.
Print Assumptions Kernel.CzCat.cmpz_pentagon.
Print Assumptions Kernel.CzCat.cmpz_triangle.
Print Assumptions Kernel.CzCat.cmpz_hexagon.
Print Assumptions Kernel.CzCat.cmpz_swap_cost_exact.
Print Assumptions Kernel.CzCat.cmpz_assoc_cost_exact.
Print Assumptions Kernel.CzCat.cmpz_unit_r_cost_exact.
Print Assumptions Kernel.CzCat.cmpz_cost_total.
Print Assumptions Kernel.CzCat.cmpz_sim_exit_cost.
Print Assumptions Kernel.CzCat.cmpz_sim_cost_ge_exits.
(* === Kernel.CzCounter : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzCounter.cmpz_interleaving_invariant.
Print Assumptions Kernel.CzCounter.cmpz_or_weakly_complete.
Print Assumptions Kernel.CzCounter.cmpz_or_clocks_not_complete.
Print Assumptions Kernel.CzCounter.cmpz_sum_record_loses.
(* === Kernel.CzFollow : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzFollow.cmpz_follow_exists.
Print Assumptions Kernel.CzFollow.cmpz_follow_reaches.
Print Assumptions Kernel.CzFollow.cmpz_follow_cost_ge_exits.
Print Assumptions Kernel.CzFollow.cmpz_bit_a2.
Print Assumptions Kernel.CzFollow.cmpz_end_only_not_enough.
(* === Kernel.CzLoad : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzLoad.cmpz_ld_load.
Print Assumptions Kernel.CzLoad.cmpz_load_floor.
Print Assumptions Kernel.CzLoad.cmpz_ld_running.
Print Assumptions Kernel.CzLoad.cmpz_ld_running_stays.
Print Assumptions Kernel.CzLoad.cmpz_ld_view_run.
Print Assumptions Kernel.CzLoad.cmpz_ld_split.
Print Assumptions Kernel.CzLoad.cmpz_ld_clean_run.
Print Assumptions Kernel.CzLoad.cmpz_ld_inl_no_exit.
Print Assumptions Kernel.CzLoad.cmpz_ld_prefix.
Print Assumptions Kernel.CzLoad.cmpz_ld_earned.
Print Assumptions Kernel.CzLoad.cmpz_ld_tc.
Print Assumptions Kernel.CzLoad.cmpz_ld_late_load_ignored.
Print Assumptions Kernel.CzLoad.cmpz_ld_order_matters.
(* === Kernel.CzProd : 21 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzProd.cmpz_pair_le.
Print Assumptions Kernel.CzProd.cmpz_pair_antisym.
Print Assumptions Kernel.CzProd.cmpz_lefts_app.
Print Assumptions Kernel.CzProd.cmpz_rights_app.
Print Assumptions Kernel.CzProd.cmpz_lefts_split.
Print Assumptions Kernel.CzProd.cmpz_rights_split.
Print Assumptions Kernel.CzProd.cmpz_run_prod.
Print Assumptions Kernel.CzProd.cmpz_run_prod_fst.
Print Assumptions Kernel.CzProd.cmpz_run_prod_snd.
Print Assumptions Kernel.CzProd.cmpz_rec_prod.
Print Assumptions Kernel.CzProd.cmpz_cost_app.
Print Assumptions Kernel.CzProd.cmpz_cost_prod.
Print Assumptions Kernel.CzProd.cmpz_exits_inl_iff.
Print Assumptions Kernel.CzProd.cmpz_exits_inr_iff.
Print Assumptions Kernel.CzProd.cmpz_exit_count_prod.
Print Assumptions Kernel.CzProd.cmpz_prod_a2_if.
Print Assumptions Kernel.CzProd.cmpz_prod_a2_only_if.
Print Assumptions Kernel.CzProd.cmpz_prod_a2_only_if_right.
Print Assumptions Kernel.CzProd.cmpz_prod_a2_iff.
Print Assumptions Kernel.CzProd.cmpz_prod_exit_cost.
Print Assumptions Kernel.CzProd.cmpz_prod_floor.
(* === Kernel.CzProdTC : 26 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzProdTC.cmpz_mapk_base_iff.
Print Assumptions Kernel.CzProdTC.cmpz_lub_left.
Print Assumptions Kernel.CzProdTC.cmpz_lub_right.
Print Assumptions Kernel.CzProdTC.cmpz_load.
Print Assumptions Kernel.CzProdTC.cmpz_record_move_inl.
Print Assumptions Kernel.CzProdTC.cmpz_record_move_inr.
Print Assumptions Kernel.CzProdTC.cmpz_earned_left.
Print Assumptions Kernel.CzProdTC.cmpz_earned_right.
Print Assumptions Kernel.CzProdTC.cmpz_prod_tc.
Print Assumptions Kernel.CzProdTC.cmpz_prod_ledger_counts.
Print Assumptions Kernel.CzProdTC.cmpz_record_moves_prod.
Print Assumptions Kernel.CzProdTC.cmpz_prod_joint_certificate.
Print Assumptions Kernel.CzProdTC.cmpz_prod_joint_certificate_tight.
Print Assumptions Kernel.CzProdTC.cmpz_prod_thiele_complete.
Print Assumptions Kernel.CzProdTC.cmpz_or_bit_iff.
Print Assumptions Kernel.CzProdTC.cmpz_or_view_complete.
Print Assumptions Kernel.CzProdTC.cmpz_record_moves_le_length.
Print Assumptions Kernel.CzProdTC.cmpz_and_costs_six.
Print Assumptions Kernel.CzProdTC.cmpz_and_not_complete.
Print Assumptions Kernel.CzProdTC.cmpz_prog_trace.
Print Assumptions Kernel.CzProdTC.cmpz_lefts_map_inl.
Print Assumptions Kernel.CzProdTC.cmpz_rights_map_inl.
Print Assumptions Kernel.CzProdTC.cmpz_lefts_map_inr.
Print Assumptions Kernel.CzProdTC.cmpz_rights_map_inr.
Print Assumptions Kernel.CzProdTC.cmpz_prod_runs_two.
Print Assumptions Kernel.CzProdTC.cmpz_or_thiele_complete.
(* === Kernel.CzSelf : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzSelf.cmpz_closed_prod.
Print Assumptions Kernel.CzSelf.cmpz_closed_seq.
Print Assumptions Kernel.CzSelf.cmpz_tower_self_similar.
(* === Kernel.CzSeq : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzSeq.cmpz_seq_tc.
Print Assumptions Kernel.CzSeq.cmpz_seq_cost.
Print Assumptions Kernel.CzSeq.cmpz_seq_joint_certificate.
Print Assumptions Kernel.CzSeq.cmpz_wired_moves_inl.
Print Assumptions Kernel.CzSeq.cmpz_wired_moves_n.
Print Assumptions Kernel.CzSeq.cmpz_seq_composes.
Print Assumptions Kernel.CzSeq.cmpz_seq_composes_halting.
Print Assumptions Kernel.CzSeq.cmpz_ld_a2_if.
Print Assumptions Kernel.CzSeq.cmpz_ld_a2_only_if.
Print Assumptions Kernel.CzSeq.cmpz_ld_unclean.
(* === Kernel.CzShadow : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzShadow.cmpz_prod_shadow_theorem.
Print Assumptions Kernel.CzShadow.cmpz_pair_independence_left.
Print Assumptions Kernel.CzShadow.cmpz_pair_independence_right.
Print Assumptions Kernel.CzShadow.cmpz_pair_ledger_independence.
Print Assumptions Kernel.CzShadow.cmpz_pair_every_window_printed.
(* === Kernel.CzTower : 33 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzTower.cmpz_mlatch_rd.
Print Assumptions Kernel.CzTower.cmpz_bool_absorb.
Print Assumptions Kernel.CzTower.cmpz_pres_run.
Print Assumptions Kernel.CzTower.cmpz_presented_run_halted.
Print Assumptions Kernel.CzTower.cmpz_mledger_halted.
Print Assumptions Kernel.CzTower.cmpz_mlatch_halted.
Print Assumptions Kernel.CzTower.cmpz_surcharge_halted.
Print Assumptions Kernel.CzTower.cmpz_not_halted_before.
Print Assumptions Kernel.CzTower.cmpz_surcharge_exact_two.
Print Assumptions Kernel.CzTower.cmpz_surcharge_start_up.
Print Assumptions Kernel.CzTower.cmpz_guest_run_eq.
Print Assumptions Kernel.CzTower.cmpz_host_run_eq.
Print Assumptions Kernel.CzTower.cmpz_guest_halted_iff.
Print Assumptions Kernel.CzTower.cmpz_host_halted_iff.
Print Assumptions Kernel.CzTower.cmpz_priced_link.
Print Assumptions Kernel.CzTower.cmpz_compile_points.
Print Assumptions Kernel.CzTower.cmpz_pres_halted_iff.
Print Assumptions Kernel.CzTower.cmpz_pres_rec.
Print Assumptions Kernel.CzTower.cmpz_pres_led.
Print Assumptions Kernel.CzTower.cmpz_pres_state.
Print Assumptions Kernel.CzTower.cmpz_compile_link.
Print Assumptions Kernel.CzTower.cmpz_host_link.
Print Assumptions Kernel.CzTower.cmpz_host_link_le_two.
Print Assumptions Kernel.CzTower.cmpz_host_link_exact.
Print Assumptions Kernel.CzTower.cmpz_host_link_start_up.
Print Assumptions Kernel.CzTower.cmpz_presents_link.
Print Assumptions Kernel.CzTower.cmpz_host_cost_le_one.
Print Assumptions Kernel.CzTower.cmpz_presents_host_start.
Print Assumptions Kernel.CzTower.cmpz_presents_host_cost.
Print Assumptions Kernel.CzTower.cmpz_level_link.
Print Assumptions Kernel.CzTower.cmpz_tower_presented.
Print Assumptions Kernel.CzTower.cmpz_exact_sum.
Print Assumptions Kernel.CzTower.cmpz_tower_presented_exact.
(* === Kernel.CzWin : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CzWin.cmpz_win_collision_iff.
Print Assumptions Kernel.CzWin.cmpz_win_collision_left.
Print Assumptions Kernel.CzWin.cmpz_win_collision_right.
Print Assumptions Kernel.CzWin.cmpz_win_blind_left.
Print Assumptions Kernel.CzWin.cmpz_win_blind_right.
Print Assumptions Kernel.CzWin.cmpz_window_sees_record.
Print Assumptions Kernel.CzWin.cmpz_ex_M_exits.
Print Assumptions Kernel.CzWin.cmpz_ex_M_no_collision.
Print Assumptions Kernel.CzWin.cmpz_ex_N_no_collision.
Print Assumptions Kernel.CzWin.cmpz_ex_M_price.
Print Assumptions Kernel.CzWin.cmpz_ex_N_price.
Print Assumptions Kernel.CzWin.cmpz_exactness_not_preserved.
Print Assumptions Kernel.CzWin.cmpz_exactness_not_preserved_price.
(* === Kernel.EarnedCoreLinks : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.EarnedCoreLinks.mm2_instr_at_iff.
Print Assumptions Kernel.EarnedCoreLinks.mm2_step_iff.
Print Assumptions Kernel.EarnedCoreLinks.mm2_stop_iff.
Print Assumptions Kernel.EarnedCoreLinks.mm2_terminates_iff.
Print Assumptions Kernel.EarnedCoreLinks.mm2_halting_iff.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_halting_undecidable.
Print Assumptions Kernel.EarnedCoreLinks.cs_run_is_run.
Print Assumptions Kernel.EarnedCoreLinks.cs_total_cost_is_total_cost.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_floor.
Print Assumptions Kernel.EarnedCoreLinks.earned_rc_run.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_ledger.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_a2.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_permanent.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_record_write.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_adequate.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_honest.
Print Assumptions Kernel.EarnedCoreLinks.earned_core_is_latch.
(* === Kernel.EarnedGenericLinks : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.EarnedGenericLinks.generic_cs_run.
Print Assumptions Kernel.EarnedGenericLinks.generic_cs_cost.
Print Assumptions Kernel.EarnedGenericLinks.earned_generic_floor.
Print Assumptions Kernel.EarnedGenericLinks.earned_generic_certified_floor.
Print Assumptions Kernel.EarnedGenericLinks.earned_generic_cs_sound.
Print Assumptions Kernel.EarnedGenericLinks.sorted_machine_floor.
Print Assumptions Kernel.EarnedGenericLinks.sorted_certified_floor.
Print Assumptions Kernel.EarnedGenericLinks.sorted_cs_sound.
Print Assumptions Kernel.EarnedGenericLinks.sorted_cs_demo_certifies.
Print Assumptions Kernel.EarnedGenericLinks.sorted_cs_demo_refused.
Print Assumptions Kernel.EarnedGenericLinks.complete_cs_run.
Print Assumptions Kernel.EarnedGenericLinks.thiele_complete_floor.
Print Assumptions Kernel.EarnedGenericLinks.earned_complete_agrees.
Print Assumptions Kernel.EarnedGenericLinks.generic_complete_agrees.
Print Assumptions Kernel.EarnedGenericLinks.sorted_complete_agrees.
Print Assumptions Kernel.EarnedGenericLinks.complete_cs_window_blind.
(* === Kernel.FiniteSums : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.FiniteSums.sumL_nil.
Print Assumptions Kernel.FiniteSums.sumL_cons.
Print Assumptions Kernel.FiniteSums.sumL_ext.
Print Assumptions Kernel.FiniteSums.sumL_plus.
Print Assumptions Kernel.FiniteSums.sumL_minus.
Print Assumptions Kernel.FiniteSums.sumL_scale_l.
Print Assumptions Kernel.FiniteSums.sumL_scale_r.
Print Assumptions Kernel.FiniteSums.sumL_zero.
Print Assumptions Kernel.FiniteSums.sumL_swap.
Print Assumptions Kernel.FiniteSums.sumL_mult.
Print Assumptions Kernel.FiniteSums.sumL_nonneg.
Print Assumptions Kernel.FiniteSums.sumL_delta.
Print Assumptions Kernel.FiniteSums.sumL_app.
Print Assumptions Kernel.FiniteSums.sumL_map.
Print Assumptions Kernel.FiniteSums.sumL_prod.
Print Assumptions Kernel.FiniteSums.sq_nonneg.
Print Assumptions Kernel.FiniteSums.le_of_sq_le.
Print Assumptions Kernel.FiniteSums.sumL_cauchy_schwarz.
(* === Kernel.GrowingRecord : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.GrowingRecord.growing_record_decomposes_holds.
Print Assumptions Kernel.GrowingRecord.thresholds_determine_record_holds.
Print Assumptions Kernel.GrowingRecord.record_price_iff_threshold_price_holds.
Print Assumptions Kernel.GrowingRecord.three_honest.
Print Assumptions Kernel.GrowingRecord.one_latch_refuted.
Print Assumptions Kernel.GrowingRecord.bits_le_trans.
Print Assumptions Kernel.GrowingRecord.bits_le_tails.
Print Assumptions Kernel.GrowingRecord.bits_le_count_le.
Print Assumptions Kernel.GrowingRecord.bits_le_count_eq.
Print Assumptions Kernel.GrowingRecord.bits_chain_head.
Print Assumptions Kernel.GrowingRecord.bits_chain_tail.
Print Assumptions Kernel.GrowingRecord.bits_chain_counts_nodup.
Print Assumptions Kernel.GrowingRecord.bit_count_le_length.
Print Assumptions Kernel.GrowingRecord.chain_needs_bits_holds.
(* === Kernel.KernelTM : 1 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.KernelTM.tm_is_turing_complete.
(* === Kernel.LRecursion : 46 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LRecursion.bound_mono.
Print Assumptions Kernel.LRecursion.subst_bound.
Print Assumptions Kernel.LRecursion.subst_closed.
Print Assumptions Kernel.LRecursion.bound_subst.
Print Assumptions Kernel.LRecursion.value_no_step.
Print Assumptions Kernel.LRecursion.step_deterministic.
Print Assumptions Kernel.LRecursion.star_one.
Print Assumptions Kernel.LRecursion.star_trans.
Print Assumptions Kernel.LRecursion.star_appL.
Print Assumptions Kernel.LRecursion.star_appR.
Print Assumptions Kernel.LRecursion.star_app.
Print Assumptions Kernel.LRecursion.star_value_confluent.
Print Assumptions Kernel.LRecursion.equiv_sym.
Print Assumptions Kernel.LRecursion.equiv_trans.
Print Assumptions Kernel.LRecursion.star_equiv.
Print Assumptions Kernel.LRecursion.encn_closed.
Print Assumptions Kernel.LRecursion.enc_closed.
Print Assumptions Kernel.LRecursion.encn_value.
Print Assumptions Kernel.LRecursion.enc_value.
Print Assumptions Kernel.LRecursion.mk_lam_spec.
Print Assumptions Kernel.LRecursion.mk_var_spec.
Print Assumptions Kernel.LRecursion.mk_app_spec.
Print Assumptions Kernel.LRecursion.mk_app_enc.
Print Assumptions Kernel.LRecursion.mk_lam_eval.
Print Assumptions Kernel.LRecursion.mk_app_eval.
Print Assumptions Kernel.LRecursion.W_closed.
Print Assumptions Kernel.LRecursion.rec_closed.
Print Assumptions Kernel.LRecursion.rec_spec.
Print Assumptions Kernel.LRecursion.Fn_closed.
Print Assumptions Kernel.LRecursion.Qn_closed.
Print Assumptions Kernel.LRecursion.Qn_spec.
Print Assumptions Kernel.LRecursion.Fq_closed.
Print Assumptions Kernel.LRecursion.Q_closed.
Print Assumptions Kernel.LRecursion.EV_closed.
Print Assumptions Kernel.LRecursion.Q_spec.
Print Assumptions Kernel.LRecursion.second_recursion.
Print Assumptions Kernel.LRecursion.L_recursion_theorem.
Print Assumptions Kernel.LRecursion.flip_term_closed.
Print Assumptions Kernel.LRecursion.flip_true.
Print Assumptions Kernel.LRecursion.flip_false.
Print Assumptions Kernel.LRecursion.L_rice.
Print Assumptions Kernel.LRecursion.L_structural_shortcut_undecidable.
Print Assumptions Kernel.LRecursion.Omega_step.
Print Assumptions Kernel.LRecursion.Omega_diverges.
Print Assumptions Kernel.LRecursion.halts_extensional.
Print Assumptions Kernel.LRecursion.L_halting_undecidable.
(* === Kernel.LiftAxis : 24 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LiftAxis.lift_lax_run_fst.
Print Assumptions Kernel.LiftAxis.lift_lax_next_cases.
Print Assumptions Kernel.LiftAxis.lift_lax_grows.
Print Assumptions Kernel.LiftAxis.lift_lax_step_eq.
Print Assumptions Kernel.LiftAxis.lift_lax_next_certify_ok.
Print Assumptions Kernel.LiftAxis.lift_lax_next_certify_no.
Print Assumptions Kernel.LiftAxis.lift_lax_base_clause.
Print Assumptions Kernel.LiftAxis.lift_lax_earned_exit.
Print Assumptions Kernel.LiftAxis.lift_lax_earned_clause.
Print Assumptions Kernel.LiftAxis.lift_lax_toll_clause.
Print Assumptions Kernel.LiftAxis.lift_lax_chain_true.
Print Assumptions Kernel.LiftAxis.lift_lax_chain_false.
Print Assumptions Kernel.LiftAxis.lift_lax_nonvac_clause.
Print Assumptions Kernel.LiftAxis.lift_lax_thiele_complete_with.
Print Assumptions Kernel.LiftAxis.lift_lax_thiele_complete.
Print Assumptions Kernel.LiftAxis.lift_wcn_eqb_eq.
Print Assumptions Kernel.LiftAxis.lift_lax_window_thiele_complete.
Print Assumptions Kernel.LiftAxis.lift_ax_tc_point_above_floor.
Print Assumptions Kernel.LiftAxis.lift_ax_indiscrete_no_machine.
Print Assumptions Kernel.LiftAxis.lift_ax_tc_exit_is_lub.
Print Assumptions Kernel.LiftAxis.lift_V_no_join.
Print Assumptions Kernel.LiftAxis.lift_V_not_a_lift_axis.
Print Assumptions Kernel.LiftAxis.lift_V_record_stays_x.
Print Assumptions Kernel.LiftAxis.lift_lax_flag_view.
(* === Kernel.LiftExec : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LiftExec.lift_ex_sdec_scode.
Print Assumptions Kernel.LiftExec.lift_ex_f_exec.
Print Assumptions Kernel.LiftExec.lift_ex_sim.
Print Assumptions Kernel.LiftExec.lift_ex_L_computable.
(* === Kernel.LiftHeadline : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LiftHeadline.lift_presented_from_computable.
Print Assumptions Kernel.LiftHeadline.lift_presented_runs_on_U.
Print Assumptions Kernel.LiftHeadline.lift_computable_runs_on_U.
Print Assumptions Kernel.LiftHeadline.lift_model_independence.
(* === Kernel.LiftModels : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LiftModels.lift_ex_thiele_complete.
Print Assumptions Kernel.LiftModels.lift_ram_thiele_complete.
Print Assumptions Kernel.LiftModels.lift_ex_in_L.
Print Assumptions Kernel.LiftModels.lift_ex_in_MMA.
Print Assumptions Kernel.LiftModels.lift_mm2_instr_at_cm.
Print Assumptions Kernel.LiftModels.lift_cm_fetch_map.
Print Assumptions Kernel.LiftModels.lift_mm2_step_cm.
Print Assumptions Kernel.LiftModels.lift_mm2_stop_cm.
Print Assumptions Kernel.LiftModels.lift_mm2_terminates_cm.
Print Assumptions Kernel.LiftModels.lift_mm2_halting_cm.
Print Assumptions Kernel.LiftModels.lift_cm_halting_undecidable.
Print Assumptions Kernel.LiftModels.lift_no_oc_translation.
Print Assumptions Kernel.LiftModels.lift_no_oc_translation_undecidability.
(* === Kernel.LiftModelsAll : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LiftModelsAll.lift_L_in_all_models.
Print Assumptions Kernel.LiftModelsAll.lift_num_models_agree.
Print Assumptions Kernel.LiftModelsAll.lift_ex_in_all_models.
Print Assumptions Kernel.LiftModelsAll.lift_numeric_base.
Print Assumptions Kernel.LiftModelsAll.lift_classic_bases.
(* === Kernel.LiftRAM : 1 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LiftRAM.lift_ram_sim.
(* === Kernel.MM2ComplementUndec : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.MM2ComplementUndec.PCPb_to_MM2.
Print Assumptions Kernel.MM2ComplementUndec.MM2_HALTING_compl_undec.
(* === Kernel.NatSubstrateInstance : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NatSubstrateInstance.nat_mu_monotone.
Print Assumptions Kernel.NatSubstrateInstance.nat_encode_decode.
Print Assumptions Kernel.NatSubstrateInstance.nat_recursion_theorem.
Print Assumptions Kernel.NatSubstrateInstance.nat_no_refuses.
Print Assumptions Kernel.NatSubstrateInstance.nat_admits_extensional.
Print Assumptions Kernel.NatSubstrateInstance.nat_structural_shortcut_undecidable.
Print Assumptions Kernel.NatSubstrateInstance.nat_self_undecidable.
(* === Kernel.NecEChsh : 30 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecEChsh.nec_e_sq2_descent.
Print Assumptions Kernel.NecEChsh.nec_e_no_sqrt8.
Print Assumptions Kernel.NecEChsh.nec_e_corr_frac.
Print Assumptions Kernel.NecEChsh.nec_e_check_strict.
Print Assumptions Kernel.NecEChsh.nec_e_check_never_tsirelson.
Print Assumptions Kernel.NecEChsh.nec_e_near_check.
Print Assumptions Kernel.NecEChsh.nec_e_near_score.
Print Assumptions Kernel.NecEChsh.nec_e_check_sharp.
Print Assumptions Kernel.NecEChsh.nec_e_pinned_tsirelson_tight.
Print Assumptions Kernel.NecEChsh.nec_e_sampled_needed.
Print Assumptions Kernel.NecEChsh.nec_e_facts_needed_for_meaning.
Print Assumptions Kernel.NecEChsh.nec_e_clear_needs_positive.
Print Assumptions Kernel.NecEChsh.nec_e_marginals_psd_not_contractive.
Print Assumptions Kernel.NecEChsh.nec_e_marginals_contractive_not_psd.
Print Assumptions Kernel.NecEChsh.nec_e_contractive_independent.
Print Assumptions Kernel.NecEChsh.nec_e_row_bounds_needed.
Print Assumptions Kernel.NecEChsh.nec_e_deterministic_not_pinned_psd.
Print Assumptions Kernel.NecEChsh.nec_e_psd2_iff.
Print Assumptions Kernel.NecEChsh.nec_e_discriminant_converse_false.
Print Assumptions Kernel.NecEChsh.nec_e_sbc_31.
Print Assumptions Kernel.NecEChsh.nec_e_sbc_13.
Print Assumptions Kernel.NecEChsh.nec_e_gzero_tight.
Print Assumptions Kernel.NecEChsh.nec_e_flag_needs_clean.
Print Assumptions Kernel.NecEChsh.nec_e_g12345_stronger.
Print Assumptions Kernel.NecEChsh.nec_e_tol_check_zero.
Print Assumptions Kernel.NecEChsh.nec_e_tol_clear.
Print Assumptions Kernel.NecEChsh.nec_e_tol_check_sound.
Print Assumptions Kernel.NecEChsh.nec_e_tol_contractive_norm.
Print Assumptions Kernel.NecEChsh.nec_e_tol_check_norm.
Print Assumptions Kernel.NecEChsh.nec_e_tol_check_bound.
(* === Kernel.NecEChshEquality : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecEChshEquality.nec_e_equality_forces_point.
Print Assumptions Kernel.NecEChshEquality.nec_e_equality_two_points.
Print Assumptions Kernel.NecEChshEquality.nec_e_no_rational_half_square.
Print Assumptions Kernel.NecEChshEquality.nec_e_worked_cascade_passes.
Print Assumptions Kernel.NecEChshEquality.nec_e_worked_cascade_fails_at_zero.
Print Assumptions Kernel.NecEChshEquality.nec_e_worked_level1_passes.
Print Assumptions Kernel.NecEChshEquality.nec_e_singular_level1_passes.
Print Assumptions Kernel.NecEChshEquality.nec_e_singular_full_fails.
(* === Kernel.NecEChshInt : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecEChshInt.nec_e_check_split.
Print Assumptions Kernel.NecEChshInt.nec_e_check_iff_facts.
Print Assumptions Kernel.NecEChshInt.nec_e_check_facts_irredundant.
Print Assumptions Kernel.NecEChshInt.nec_e_d_sq.
Print Assumptions Kernel.NecEChshInt.nec_e_check_refuses_deterministic.
Print Assumptions Kernel.NecEChshInt.nec_e_check_refuses_all_plans.
Print Assumptions Kernel.NecEChshInt.nec_e_local_bound_attained.
Print Assumptions Kernel.NecEChshInt.nec_e_local_bound_needs_sampling.
Print Assumptions Kernel.NecEChshInt.nec_e_local_bound_needs_bits.
Print Assumptions Kernel.NecEChshInt.nec_e_violation_any_labels.
Print Assumptions Kernel.NecEChshInt.nec_e_deterministic_tight.
(* === Kernel.NecEFine : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecEFine.nec_e_sum_n_lin.
Print Assumptions Kernel.NecEFine.nec_e_sum_n_4.
Print Assumptions Kernel.NecEFine.nec_e_sum_n_ext.
Print Assumptions Kernel.NecEFine.nec_e_sum_n_bound.
Print Assumptions Kernel.NecEFine.nec_e_factorizable_variant_bound.
Print Assumptions Kernel.NecEFine.nec_e_fine_converse_false.
Print Assumptions Kernel.NecEFine.nec_e_sum_n_comb.
Print Assumptions Kernel.NecEFine.nec_e_sum_n_boundK.
Print Assumptions Kernel.NecEFine.nec_e_det_term.
Print Assumptions Kernel.NecEFine.nec_e_factorizable_linear.
Print Assumptions Kernel.NecEFine.nec_e_fine_necessary.
Print Assumptions Kernel.NecEFine.nec_e_pos_nonneg.
Print Assumptions Kernel.NecEFine.nec_e_pos_diff.
Print Assumptions Kernel.NecEFine.nec_e_pos_sum.
Print Assumptions Kernel.NecEFine.nec_e_abs_cases.
Print Assumptions Kernel.NecEFine.nec_e_fine_iff.
(* === Kernel.NecEHost : 26 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecEHost.nec_e_hfun_det.
Print Assumptions Kernel.NecEHost.nec_e_inc0_out.
Print Assumptions Kernel.NecEHost.nec_e_is0_out.
Print Assumptions Kernel.NecEHost.nec_e_hcode_nil.
Print Assumptions Kernel.NecEHost.nec_e_nil_halt_same.
Print Assumptions Kernel.NecEHost.nec_e_nil_halt_hequiv.
Print Assumptions Kernel.NecEHost.nec_e_wall_needs_nontrivial.
Print Assumptions Kernel.NecEHost.nec_e_wall_needs_extensional.
Print Assumptions Kernel.NecEHost.nec_e_dec_const.
Print Assumptions Kernel.NecEHost.nec_e_dec_nil.
Print Assumptions Kernel.NecEHost.nec_e_rice_needs_nontrivial.
Print Assumptions Kernel.NecEHost.nec_e_rice_needs_extensional.
Print Assumptions Kernel.NecEHost.nec_e_guest_rice_needs_nontrivial.
Print Assumptions Kernel.NecEHost.nec_e_guest_rice_needs_extensional.
Print Assumptions Kernel.NecEHost.nec_e_trap_absorbs.
Print Assumptions Kernel.NecEHost.nec_e_ff_MMA.
Print Assumptions Kernel.NecEHost.nec_e_ff_program.
Print Assumptions Kernel.NecEHost.nec_e_ff_computed.
Print Assumptions Kernel.NecEHost.nec_e_noreg_cexec.
Print Assumptions Kernel.NecEHost.nec_e_noreg_run.
Print Assumptions Kernel.NecEHost.nec_e_ends_noreg.
Print Assumptions Kernel.NecEHost.nec_e_ff_run_r.
Print Assumptions Kernel.NecEHost.nec_e_ff_run.
Print Assumptions Kernel.NecEHost.nec_e_no_fixed_point_facts.
Print Assumptions Kernel.NecEHost.nec_e_no_fixed_point_versions.
Print Assumptions Kernel.NecEHost.nec_e_kleene_needs_computable.
(* === Kernel.NecFCalorimeter : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFCalorimeter.nec_f_smaller_gap_iff.
Print Assumptions Kernel.NecFCalorimeter.nec_f_smaller_gap_negative_pair.
Print Assumptions Kernel.NecFCalorimeter.nec_f_heat_determines_gap.
Print Assumptions Kernel.NecFCalorimeter.nec_f_landauer_gap_unique.
Print Assumptions Kernel.NecFCalorimeter.nec_f_scales_always_disagree.
(* === Kernel.NecFCounter : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFCounter.nec_f_conservation.
Print Assumptions Kernel.NecFCounter.nec_f_counter_monotone.
Print Assumptions Kernel.NecFCounter.nec_f_initiality_reachable_rule.
Print Assumptions Kernel.NecFCounter.nec_f_initiality.
Print Assumptions Kernel.NecFCounter.nec_f_initiality_iff.
Print Assumptions Kernel.NecFCounter.nec_f_conservation_iff_rule.
Print Assumptions Kernel.NecFCounter.nec_f_finite_counter_charges_nothing.
Print Assumptions Kernel.NecFCounter.nec_f_initiality_needs_zero_start.
Print Assumptions Kernel.NecFCounter.nec_f_initiality_needs_reachable.
Print Assumptions Kernel.NecFCounter.nec_f_fold_unique.
Print Assumptions Kernel.NecFCounter.nec_f_additive_is_price.
Print Assumptions Kernel.NecFCounter.nec_f_factor_gives_descent.
Print Assumptions Kernel.NecFCounter.nec_f_descent_iff_functional.
Print Assumptions Kernel.NecFCounter.nec_f_descent_fails_for_history.
Print Assumptions Kernel.NecFCounter.nec_f_potential_bound_iff.
Print Assumptions Kernel.NecFCounter.nec_f_potential_bound_exact.
Print Assumptions Kernel.NecFCounter.nec_f_potential_one_attained.
(* === Kernel.NecFCups : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFCups.nec_f_same_rung_same_cups.
Print Assumptions Kernel.NecFCups.nec_f_non_partial_cups_fail.
Print Assumptions Kernel.NecFCups.nec_f_cups_iff_partial.
(* === Kernel.NecFEntropy : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFEntropy.nec_f_uniform_pair_pos.
Print Assumptions Kernel.NecFEntropy.nec_f_entropy_invariant_iff_injective.
Print Assumptions Kernel.NecFEntropy.nec_f_drop_zero_of_support_injective.
Print Assumptions Kernel.NecFEntropy.nec_f_drop_pos_iff_support_merge.
Print Assumptions Kernel.NecFEntropy.nec_f_zero_drop_every_move_iff_one_state.
Print Assumptions Kernel.NecFEntropy.nec_f_entropy_toll_needs_finite.
Print Assumptions Kernel.NecFEntropy.nec_f_entropy_toll_needs_permanent.
Print Assumptions Kernel.NecFEntropy.nec_f_a2_without_entropy_pricing.
Print Assumptions Kernel.NecFEntropy.nec_f_heat_positive_needs_kT.
Print Assumptions Kernel.NecFEntropy.nec_f_full_support_needs_yes.
Print Assumptions Kernel.NecFEntropy.nec_f_full_support_needs_s.
(* === Kernel.NecFEntropyTight : 28 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFEntropyTight.nec_f_filter_prod_fst.
Print Assumptions Kernel.NecFEntropyTight.nec_f_zero_count.
Print Assumptions Kernel.NecFEntropyTight.nec_f_filter_none.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_finite.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_permanent.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_all_length.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_C_length.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_F_length.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_flip_list.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_CF_full.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_CF_nodup.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_count.
Print Assumptions Kernel.NecFEntropyTight.nec_f_gn_push.
Print Assumptions Kernel.NecFEntropyTight.nec_f_log2_div.
Print Assumptions Kernel.NecFEntropyTight.nec_f_entropy_bounds_attained.
Print Assumptions Kernel.NecFEntropyTight.nec_f_heat_floor_attained.
Print Assumptions Kernel.NecFEntropyTight.nec_f_three_finite.
Print Assumptions Kernel.NecFEntropyTight.nec_f_three_C.
Print Assumptions Kernel.NecFEntropyTight.nec_f_three_push.
Print Assumptions Kernel.NecFEntropyTight.nec_f_three_entropy_q.
Print Assumptions Kernel.NecFEntropyTight.nec_f_three_entropy_p.
Print Assumptions Kernel.NecFEntropyTight.nec_f_heat_floor_needs_nonneg_kT.
Print Assumptions Kernel.NecFEntropyTight.nec_f_surprisal_half.
Print Assumptions Kernel.NecFEntropyTight.nec_f_surprisal_zero.
Print Assumptions Kernel.NecFEntropyTight.nec_f_surprisal_one.
Print Assumptions Kernel.NecFEntropyTight.nec_f_invariance_needs_complete_list.
Print Assumptions Kernel.NecFEntropyTight.nec_f_invariance_needs_nodup.
Print Assumptions Kernel.NecFEntropyTight.nec_f_ceiling_needs_permanent.
(* === Kernel.NecFExtra : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFExtra.nec_f_fin_cost_minimal.
Print Assumptions Kernel.NecFExtra.nec_f_fin_merge_pricing_jump_one.
Print Assumptions Kernel.NecFExtra.nec_f_finite_injective_undoable.
Print Assumptions Kernel.NecFExtra.nec_f_small_machine_infinite.
(* === Kernel.NecFFloor : 22 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFFloor.nec_f_run_app.
Print Assumptions Kernel.NecFFloor.nec_f_total_app.
Print Assumptions Kernel.NecFFloor.nec_f_floor_iff_a2.
Print Assumptions Kernel.NecFFloor.nec_f_free_reach_run.
Print Assumptions Kernel.NecFFloor.nec_f_floor_at_iff_free_reach.
Print Assumptions Kernel.NecFFloor.nec_f_floor_at_from_reachable_a2.
Print Assumptions Kernel.NecFFloor.nec_f_cost_ge_rises.
Print Assumptions Kernel.NecFFloor.nec_f_rises_pos.
Print Assumptions Kernel.NecFFloor.nec_f_rises_iff_a2.
Print Assumptions Kernel.NecFFloor.nec_f_rises_exact_iff.
Print Assumptions Kernel.NecFFloor.nec_f_cs_run_is_run.
Print Assumptions Kernel.NecFFloor.nec_f_cs_total_is_total.
Print Assumptions Kernel.NecFFloor.nec_f_cs_cost_ge_rises.
Print Assumptions Kernel.NecFFloor.nec_f_bit_a2.
Print Assumptions Kernel.NecFFloor.nec_f_bit_rises_exact.
Print Assumptions Kernel.NecFFloor.nec_f_bit_recertify_costs_two.
Print Assumptions Kernel.NecFFloor.nec_f_floor_one_attained.
Print Assumptions Kernel.NecFFloor.nec_f_floor_needs_no_start.
Print Assumptions Kernel.NecFFloor.nec_f_free_stamp_floor_fails.
Print Assumptions Kernel.NecFFloor.nec_f_door_free_reach_A.
Print Assumptions Kernel.NecFFloor.nec_f_paid_door_floor.
Print Assumptions Kernel.NecFFloor.nec_f_paid_door_not_a2.
(* === Kernel.NecFGibbs : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFGibbs.nec_f_ln_strict.
Print Assumptions Kernel.NecFGibbs.nec_f_entropy_eq_log_support.
Print Assumptions Kernel.NecFGibbs.nec_f_uniform_drop_exact_only_if_divides.
Print Assumptions Kernel.NecFGibbs.nec_f_uniform_drop_strict_unless_divides.
Print Assumptions Kernel.NecFGibbs.nec_f_step_entropy_invariant_uniform.
(* === Kernel.NecFGrade : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFGrade.nec_f_grade_exact.
Print Assumptions Kernel.NecFGrade.nec_f_small_conservation.
Print Assumptions Kernel.NecFGrade.nec_f_grade_exact_small.
Print Assumptions Kernel.NecFGrade.nec_f_iter_pay.
Print Assumptions Kernel.NecFGrade.nec_f_loop_cost.
Print Assumptions Kernel.NecFGrade.nec_f_loop_no_fixed_grade.
Print Assumptions Kernel.NecFGrade.nec_f_loop_input_grade.
(* === Kernel.NecFMerge : 29 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFMerge.nec_f_yes_list_of_finite.
Print Assumptions Kernel.NecFMerge.nec_f_flip_not_injective_on_yes_and_s.
Print Assumptions Kernel.NecFMerge.nec_f_perm_flip_merges_yes_finite.
Print Assumptions Kernel.NecFMerge.nec_f_flip_collision_in_yes_and_s.
Print Assumptions Kernel.NecFMerge.nec_f_merge_or_revoke_yes_finite.
Print Assumptions Kernel.NecFMerge.nec_f_toll_from_merges_yes_finite.
Print Assumptions Kernel.NecFMerge.nec_f_a2_iff_flipping_merges_priced.
Print Assumptions Kernel.NecFMerge.nec_f_merging_priced_weakens.
Print Assumptions Kernel.NecFMerge.nec_f_repo_perm_flip_from_yes_finite.
Print Assumptions Kernel.NecFMerge.nec_f_no_flip_no_merge.
Print Assumptions Kernel.NecFMerge.nec_f_jump_merges_never_flips.
Print Assumptions Kernel.NecFMerge.nec_f_collision_avoids_s.
Print Assumptions Kernel.NecFMerge.nec_f_toll_needs_finite.
Print Assumptions Kernel.NecFMerge.nec_f_toll_needs_permanent.
Print Assumptions Kernel.NecFMerge.nec_f_a2_without_merge_pricing.
Print Assumptions Kernel.NecFMerge.nec_f_merge_or_revoke_needs_finite.
Print Assumptions Kernel.NecFMerge.nec_f_merge_only_flip.
Print Assumptions Kernel.NecFMerge.nec_f_revoke_only_flip.
Print Assumptions Kernel.NecFMerge.nec_f_merge_and_revoke_flip.
Print Assumptions Kernel.NecFMerge.nec_f_forced_iff_merges_isolated.
Print Assumptions Kernel.NecFMerge.nec_f_merges_forced.
Print Assumptions Kernel.NecFMerge.nec_f_seen_true_zero.
Print Assumptions Kernel.NecFMerge.nec_f_seen_true_ge.
Print Assumptions Kernel.NecFMerge.nec_f_zero_seq_injective.
Print Assumptions Kernel.NecFMerge.nec_f_true_seq_merges.
Print Assumptions Kernel.NecFMerge.nec_f_forced_without_merge_under_continuity.
Print Assumptions Kernel.NecFMerge.nec_f_forced_iff_merges_needs_decidability.
Print Assumptions Kernel.NecFMerge.nec_f_forced_needs_finite.
Print Assumptions Kernel.NecFMerge.nec_f_forced_needs_permanent.
(* === Kernel.NecFNarrowing : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFNarrowing.nec_f_log_of_mul.
Print Assumptions Kernel.NecFNarrowing.nec_f_halving_gives_bit_price.
Print Assumptions Kernel.NecFNarrowing.nec_f_fiber_image_le_one.
Print Assumptions Kernel.NecFNarrowing.nec_f_bit_price_gives_halving.
Print Assumptions Kernel.NecFNarrowing.nec_f_bit_price_iff_halving.
Print Assumptions Kernel.NecFNarrowing.nec_f_run_narrowing_bit.
Print Assumptions Kernel.NecFNarrowing.nec_f_machine_narrowing_iff_halving.
Print Assumptions Kernel.NecFNarrowing.nec_f_narrowing_needs_nodup.
Print Assumptions Kernel.NecFNarrowing.nec_f_narrowing_equality.
Print Assumptions Kernel.NecFNarrowing.nec_f_wipe_under_merge_pricing.
Print Assumptions Kernel.NecFNarrowing.nec_f_wipe_one_attained.
Print Assumptions Kernel.NecFNarrowing.nec_f_two_state_observer_free.
Print Assumptions Kernel.NecFNarrowing.nec_f_one_state_observer_priced.
Print Assumptions Kernel.NecFNarrowing.nec_f_seen_head.
Print Assumptions Kernel.NecFNarrowing.nec_f_view_first_differs.
Print Assumptions Kernel.NecFNarrowing.nec_f_view_constant.
Print Assumptions Kernel.NecFNarrowing.nec_f_view_self.
Print Assumptions Kernel.NecFNarrowing.nec_f_two_states_never_teach.
(* === Kernel.NecFPaperToys : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFPaperToys.nec_f_board_toll.
Print Assumptions Kernel.NecFPaperToys.nec_f_board_raw_free.
Print Assumptions Kernel.NecFPaperToys.nec_f_board_floor.
Print Assumptions Kernel.NecFPaperToys.nec_f_board_floor_flat.
Print Assumptions Kernel.NecFPaperToys.nec_f_board_no_wait.
Print Assumptions Kernel.NecFPaperToys.nec_f_history_infinite.
(* === Kernel.NecFPhysics : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFPhysics.nec_f_dec_one_way.
Print Assumptions Kernel.NecFPhysics.nec_f_dec_merges_false_with_true.
Print Assumptions Kernel.NecFPhysics.nec_f_dec_collapses.
Print Assumptions Kernel.NecFPhysics.nec_f_one_way_injective.
Print Assumptions Kernel.NecFPhysics.nec_f_small_one_way_pair_fails.
Print Assumptions Kernel.NecFPhysics.nec_f_pigeonhole.
Print Assumptions Kernel.NecFPhysics.nec_f_finite_one_way_merges.
Print Assumptions Kernel.NecFPhysics.nec_f_small_premise_pair_fails.
Print Assumptions Kernel.NecFPhysics.nec_f_small_free_collapse_is_merge.
Print Assumptions Kernel.NecFPhysics.nec_f_small_premise_pair_on_flag.
Print Assumptions Kernel.NecFPhysics.nec_f_nodup_map_inj.
Print Assumptions Kernel.NecFPhysics.nec_f_finite_lift_forces_injective.
Print Assumptions Kernel.NecFPhysics.nec_f_history_step_facts.
(* === Kernel.NecFQuant : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFQuant.nec_f_raw_telescoping.
Print Assumptions Kernel.NecFQuant.nec_f_qfloor_from_any_witness.
Print Assumptions Kernel.NecFQuant.nec_f_qfloor_raw.
Print Assumptions Kernel.NecFQuant.nec_f_cs_run_eq.
Print Assumptions Kernel.NecFQuant.nec_f_cs_total_eq.
Print Assumptions Kernel.NecFQuant.nec_f_repo_quantitative_from_raw.
Print Assumptions Kernel.NecFQuant.nec_f_inc_run.
Print Assumptions Kernel.NecFQuant.nec_f_inc_total.
Print Assumptions Kernel.NecFQuant.nec_f_quant_tight.
Print Assumptions Kernel.NecFQuant.nec_f_quant_needs_a6.
Print Assumptions Kernel.NecFQuant.nec_f_quant_needs_a3.
Print Assumptions Kernel.NecFQuant.nec_f_quant_needs_a5.
(* === Kernel.NecFRepeat : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFRepeat.nec_f_orbit_add.
Print Assumptions Kernel.NecFRepeat.nec_f_bounded_search.
Print Assumptions Kernel.NecFRepeat.nec_f_prefix_length.
Print Assumptions Kernel.NecFRepeat.nec_f_prefix_in.
Print Assumptions Kernel.NecFRepeat.nec_f_dup_or_nodup.
Print Assumptions Kernel.NecFRepeat.nec_f_orbit_repeats.
Print Assumptions Kernel.NecFRepeat.nec_f_orbit_periodic.
Print Assumptions Kernel.NecFRepeat.nec_f_start_never_returns.
Print Assumptions Kernel.NecFRepeat.nec_f_walk_back.
Print Assumptions Kernel.NecFRepeat.nec_f_orbit_merges_visited.
Print Assumptions Kernel.NecFRepeat.nec_f_repeat_merges_visited.
Print Assumptions Kernel.NecFRepeat.nec_f_closed_merges_visited.
Print Assumptions Kernel.NecFRepeat.nec_f_run_app.
Print Assumptions Kernel.NecFRepeat.nec_f_reps_orbit.
Print Assumptions Kernel.NecFRepeat.nec_f_word_first_meet.
Print Assumptions Kernel.NecFRepeat.nec_f_word_merges_visited.
Print Assumptions Kernel.NecFRepeat.nec_f_outside_moves_no_merge.
(* === Kernel.NecFSqueeze : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFSqueeze.nec_f_fin_eq.
Print Assumptions Kernel.NecFSqueeze.nec_f_collect_values.
Print Assumptions Kernel.NecFSqueeze.nec_f_enum_values.
Print Assumptions Kernel.NecFSqueeze.nec_f_enum_length.
Print Assumptions Kernel.NecFSqueeze.nec_f_enum_nodup.
Print Assumptions Kernel.NecFSqueeze.nec_f_enum_full.
Print Assumptions Kernel.NecFSqueeze.nec_f_nodup_prod.
Print Assumptions Kernel.NecFSqueeze.nec_f_filter_prod_snd.
Print Assumptions Kernel.NecFSqueeze.nec_f_nodup_map_on.
Print Assumptions Kernel.NecFSqueeze.nec_f_pow_pos.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_finite.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_permanent.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_fiber.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_halving.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_flips_spec.
Print Assumptions Kernel.NecFSqueeze.nec_f_col0_count.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_yes_count.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_flips_count.
Print Assumptions Kernel.NecFSqueeze.nec_f_squeeze_tight.
Print Assumptions Kernel.NecFSqueeze.nec_f_in_firstn.
Print Assumptions Kernel.NecFSqueeze.nec_f_squeeze_tight_every_k.
Print Assumptions Kernel.NecFSqueeze.nec_f_grid_cost_least.
Print Assumptions Kernel.NecFSqueeze.nec_f_injective_halving_free.
Print Assumptions Kernel.NecFSqueeze.nec_f_squeeze_needs_finite.
Print Assumptions Kernel.NecFSqueeze.nec_f_squeeze_needs_permanent.
Print Assumptions Kernel.NecFSqueeze.nec_f_squeeze_needs_halving.
Print Assumptions Kernel.NecFSqueeze.nec_f_rounded_log_form_weaker.
(* === Kernel.NecFSqueezeLog : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFSqueezeLog.nec_f_ln_le_iff.
Print Assumptions Kernel.NecFSqueezeLog.nec_f_squeeze_real_iff.
Print Assumptions Kernel.NecFSqueezeLog.nec_f_least_cost_is_ceiling.
Print Assumptions Kernel.NecFSqueezeLog.nec_f_least_cost_exists.
Print Assumptions Kernel.NecFSqueezeLog.nec_f_one_halving_iff.
Print Assumptions Kernel.NecFSqueezeLog.nec_f_thinner_squeeze_below_one_bit.
(* === Kernel.NecFThreeState : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecFThreeState.nec_f_record_ceiling_unique.
Print Assumptions Kernel.NecFThreeState.nec_f_three_both_merge.
Print Assumptions Kernel.NecFThreeState.nec_f_three_automorphism_id.
Print Assumptions Kernel.NecFThreeState.nec_f_three_total_app.
Print Assumptions Kernel.NecFThreeState.nec_f_three_common.
Print Assumptions Kernel.NecFThreeState.nec_f_three_toll_meets.
Print Assumptions Kernel.NecFThreeState.nec_f_three_merge_meets.
Print Assumptions Kernel.NecFThreeState.nec_f_three_bills_differ.
Print Assumptions Kernel.NecFThreeState.nec_f_three_ceiling_picks_toll.
Print Assumptions Kernel.NecFThreeState.nec_f_three_merge_fails_ceiling.
Print Assumptions Kernel.NecFThreeState.nec_f_three_cs_costs.
Print Assumptions Kernel.NecFThreeState.nec_f_three_cs_floor.
(* === Kernel.NecSMisc : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecSMisc.nec_s_commit_traps_iff.
Print Assumptions Kernel.NecSMisc.nec_s_certify_traps_iff.
Print Assumptions Kernel.NecSMisc.nec_s_frag_needs_live.
Print Assumptions Kernel.NecSMisc.nec_s_frag_toll_attained.
Print Assumptions Kernel.NecSMisc.nec_s_loop_blank_run.
Print Assumptions Kernel.NecSMisc.nec_s_tm_ledger_not_function_of_config.
Print Assumptions Kernel.NecSMisc.nec_s_loop_one_run.
Print Assumptions Kernel.NecSMisc.nec_s_tm_cost_bound_attained.
(* === Kernel.NecSPoints : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecSPoints.nec_s_first_stop.
Print Assumptions Kernel.NecSPoints.nec_s_after_stop.
Print Assumptions Kernel.NecSPoints.nec_s_presented_points_every_n.
Print Assumptions Kernel.NecSPoints.nec_s_presented_within_two_every_n.
(* === Kernel.NecSPresented : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecSPresented.nec_s_never_toll.
Print Assumptions Kernel.NecSPresented.nec_s_presented_all_iff_ct.
Print Assumptions Kernel.NecSPresented.nec_s_host_at_floor.
Print Assumptions Kernel.NecSPresented.nec_s_within_two_needs_no_start.
Print Assumptions Kernel.NecSPresented.nec_s_flip_toll.
Print Assumptions Kernel.NecSPresented.nec_s_flip_read_spec.
Print Assumptions Kernel.NecSPresented.nec_s_within_two_attained.
Print Assumptions Kernel.NecSPresented.nec_s_first_raise_latch.
Print Assumptions Kernel.NecSPresented.nec_s_surcharge_zero_iff.
Print Assumptions Kernel.NecSPresented.nec_s_pays.
Print Assumptions Kernel.NecSPresented.nec_s_exact_host_iff_bool.
Print Assumptions Kernel.NecSPresented.nec_s_exact_host_iff.
Print Assumptions Kernel.NecSPresented.nec_s_pay_is_record_move.
(* === Kernel.NecSU : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecSU.nec_s_U_complete_floor_three.
Print Assumptions Kernel.NecSU.nec_s_witness_halts.
Print Assumptions Kernel.NecSU.nec_s_U_floor_three_attained.
Print Assumptions Kernel.NecSU.nec_s_grun_mu_step.
Print Assumptions Kernel.NecSU.nec_s_host_ledger_is_guest_ledger.
Print Assumptions Kernel.NecSU.nec_s_U_sim_bound_attained.
Print Assumptions Kernel.NecSU.nec_s_U_earned_needs_load.
(* === Kernel.NecSUndec : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecSUndec.nec_s_halting_decidable_classically.
Print Assumptions Kernel.NecSUndec.nec_s_undecidable_is_relative.
(* === Kernel.NecWArgued : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWArgued.nec_w_forgetful_window_no_counter.
Print Assumptions Kernel.NecWArgued.nec_w_forgetful_window_no_flag.
Print Assumptions Kernel.NecWArgued.nec_w_forget_needs_settable.
Print Assumptions Kernel.NecWArgued.nec_w_billed_run.
Print Assumptions Kernel.NecWArgued.nec_w_billed_step_cost.
Print Assumptions Kernel.NecWArgued.nec_w_billed_honest.
Print Assumptions Kernel.NecWArgued.nec_w_billed_same_latch.
Print Assumptions Kernel.NecWArgued.nec_w_billed_same_up_to_schedule.
Print Assumptions Kernel.NecWArgued.nec_w_observed_implies_schedule_bisim.
Print Assumptions Kernel.NecWArgued.nec_w_outside_decider.
(* === Kernel.NecWCT : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWCT.nec_w_inclusion_rejects_beyond.
Print Assumptions Kernel.NecWCT.nec_w_ct_fold_step.
Print Assumptions Kernel.NecWCT.nec_w_div2_le.
Print Assumptions Kernel.NecWCT.nec_w_div2_lt.
Print Assumptions Kernel.NecWCT.nec_w_shift_snd_le.
Print Assumptions Kernel.NecWCT.nec_w_ct_nxt_decreases.
Print Assumptions Kernel.NecWCT.nec_w_ct_fill_reaches_zero.
Print Assumptions Kernel.NecWCT.nec_w_inclusion_accepts_iff.
Print Assumptions Kernel.NecWCT.nec_w_inclusion_accepts_iff_symbolic.
(* === Kernel.NecWCasper : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWCasper.nec_w_anc_base.
Print Assumptions Kernel.NecWCasper.nec_w_anc_concat.
Print Assumptions Kernel.NecWCasper.nec_w_anc_other.
Print Assumptions Kernel.NecWCasper.nec_w_nth_anc.
Print Assumptions Kernel.NecWCasper.nec_w_link_epochs.
Print Assumptions Kernel.NecWCasper.nec_w_link_anc.
Print Assumptions Kernel.NecWCasper.nec_w_two_link_not_slashed.
Print Assumptions Kernel.NecWCasper.nec_w_both_votes.
Print Assumptions Kernel.NecWCasper.nec_w_dbl_vote_case.
Print Assumptions Kernel.NecWCasper.nec_w_surround_case.
Print Assumptions Kernel.NecWCasper.nec_w_crossing_link.
Print Assumptions Kernel.NecWCasper.nec_w_same_epoch_distinct.
Print Assumptions Kernel.NecWCasper.nec_w_distinct_justified_same_epoch.
Print Assumptions Kernel.NecWCasper.nec_w_non_equal_case_ind.
Print Assumptions Kernel.NecWCasper.nec_w_accountable_safety_no_parent_premise.
Print Assumptions Kernel.NecWCasper.nec_w_nth_of_repo.
Print Assumptions Kernel.NecWCasper.nec_w_link_of_repo.
Print Assumptions Kernel.NecWCasper.nec_w_just_of_repo.
Print Assumptions Kernel.NecWCasper.nec_w_fork_of_repo.
Print Assumptions Kernel.NecWCasper.nec_w_accountable_safety_repo.
Print Assumptions Kernel.NecWCasper.nec_w_only_a_third.
Print Assumptions Kernel.NecWCasper.nec_w_only_c_third.
Print Assumptions Kernel.NecWCasper.nec_w_third_nonempty.
Print Assumptions Kernel.NecWCasper.nec_w_casper_first_class_one_third.
Print Assumptions Kernel.NecWCasper.nec_w_vote_vb_slashed_only.
Print Assumptions Kernel.NecWCasper.nec_w_two_thirds_two_members.
Print Assumptions Kernel.NecWCasper.nec_w_casper_second_class_two_thirds.
(* === Kernel.NecWDiagonal : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWDiagonal.nec_w_constant_true_predicate_decided.
Print Assumptions Kernel.NecWDiagonal.nec_w_constant_false_predicate_decided.
Print Assumptions Kernel.NecWDiagonal.nec_w_brun_equiv.
Print Assumptions Kernel.NecWDiagonal.nec_w_rep_needed.
Print Assumptions Kernel.NecWDiagonal.nec_w_extensional_needed.
Print Assumptions Kernel.NecWDiagonal.nec_w_recursion_needed.
Print Assumptions Kernel.NecWDiagonal.nec_w_nat_family_wrong_at_two.
Print Assumptions Kernel.NecWDiagonal.nec_w_nat_family_one_error_tight.
(* === Kernel.NecWGrowing : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWGrowing.nec_w_growing_from_driven_grows.
Print Assumptions Kernel.NecWGrowing.nec_w_threshold_factor_implies_grows.
Print Assumptions Kernel.NecWGrowing.nec_w_threshold_factor_relationally_driven.
Print Assumptions Kernel.NecWGrowing.nec_w_clock_no_threshold_factorization.
Print Assumptions Kernel.NecWGrowing.nec_w_two_valued_one_latch.
Print Assumptions Kernel.NecWGrowing.nec_w_price_iff_needs_grows.
Print Assumptions Kernel.NecWGrowing.nec_w_word_nth.
Print Assumptions Kernel.NecWGrowing.nec_w_word_length.
Print Assumptions Kernel.NecWGrowing.nec_w_up_head.
Print Assumptions Kernel.NecWGrowing.nec_w_up_in.
Print Assumptions Kernel.NecWGrowing.nec_w_up_length.
Print Assumptions Kernel.NecWGrowing.nec_w_word_inj.
Print Assumptions Kernel.NecWGrowing.nec_w_chain_attained.
Print Assumptions Kernel.NecWGrowing.nec_w_chain_bound_tight.
Print Assumptions Kernel.NecWGrowing.nec_w_det_latch_iff_no_branching.
Print Assumptions Kernel.NecWGrowing.nec_w_schedule_not_normalized_probability.
Print Assumptions Kernel.NecWGrowing.nec_w_weight_single.
Print Assumptions Kernel.NecWGrowing.nec_w_no_branching_schedule_fixes_probability.
(* === Kernel.NecWLRice : 24 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWLRice.nec_w_second_recursion_any_closed.
Print Assumptions Kernel.NecWLRice.nec_w_recursion_theorem_any_closed.
Print Assumptions Kernel.NecWLRice.nec_w_step_closed.
Print Assumptions Kernel.NecWLRice.nec_w_star_closed.
Print Assumptions Kernel.NecWLRice.nec_w_second_recursion_needs_closed.
Print Assumptions Kernel.NecWLRice.nec_w_const_decider.
Print Assumptions Kernel.NecWLRice.nec_w_ltrue_closed.
Print Assumptions Kernel.NecWLRice.nec_w_lfalse_closed.
Print Assumptions Kernel.NecWLRice.nec_w_rice_needs_both_witnesses.
Print Assumptions Kernel.NecWLRice.nec_w_enc_case.
Print Assumptions Kernel.NecWLRice.nec_w_is_lam_decider_run.
Print Assumptions Kernel.NecWLRice.nec_w_rice_needs_extensional.
Print Assumptions Kernel.NecWLRice.nec_w_app_halts_inv.
Print Assumptions Kernel.NecWLRice.nec_w_px_halts.
Print Assumptions Kernel.NecWLRice.nec_w_px_value_halts.
Print Assumptions Kernel.NecWLRice.nec_w_no_value_equiv_omega.
Print Assumptions Kernel.NecWLRice.nec_w_mk_app_closed.
Print Assumptions Kernel.NecWLRice.nec_w_hbody_bound.
Print Assumptions Kernel.NecWLRice.nec_w_hbody_subst.
Print Assumptions Kernel.NecWLRice.nec_w_hbody_run.
Print Assumptions Kernel.NecWLRice.nec_w_ltrue_select.
Print Assumptions Kernel.NecWLRice.nec_w_lfalse_select.
Print Assumptions Kernel.NecWLRice.nec_w_rice_any_witnesses.
Print Assumptions Kernel.NecWLRice.nec_w_L_rice_corollary.
(* === Kernel.NecWLatch : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWLatch.nec_w_latch_from_driven_permanent.
Print Assumptions Kernel.NecWLatch.nec_w_latch_iff.
Print Assumptions Kernel.NecWLatch.nec_w_record_axis_is_latch.
Print Assumptions Kernel.NecWLatch.nec_w_toggle_meets_rest.
Print Assumptions Kernel.NecWLatch.nec_w_clock_meets_rest.
Print Assumptions Kernel.NecWLatch.nec_w_latch_event_determined.
Print Assumptions Kernel.NecWLatch.nec_w_latch_event_not_unique.
Print Assumptions Kernel.NecWLatch.nec_w_latch_honest_iff.
Print Assumptions Kernel.NecWLatch.nec_w_latch_never_not_honest.
Print Assumptions Kernel.NecWLatch.nec_w_history_honest_iff.
Print Assumptions Kernel.NecWLatch.nec_w_history_injective_iff.
Print Assumptions Kernel.NecWLatch.nec_w_reversible_needs_finite.
Print Assumptions Kernel.NecWLatch.nec_w_reversible_needs_permanent.
Print Assumptions Kernel.NecWLatch.nec_w_reversible_needs_injective.
Print Assumptions Kernel.NecWLatch.nec_w_pair_iff.
Print Assumptions Kernel.NecWLatch.nec_w_pair_toggle_not_two_latches.
Print Assumptions Kernel.NecWLatch.nec_w_event_free_choice.
(* === Kernel.NecWModels : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWModels.nec_w_warm_empty_invariant.
Print Assumptions Kernel.NecWModels.nec_w_sstore_fresh_bound_exact.
Print Assumptions Kernel.NecWModels.nec_w_sstore_empty_bound_exact.
Print Assumptions Kernel.NecWModels.nec_w_one_step_free_iff_uncharged.
Print Assumptions Kernel.NecWModels.nec_w_toy_universal_floor.
Print Assumptions Kernel.NecWModels.nec_w_gas_clause_premises_needed.
Print Assumptions Kernel.NecWModels.nec_w_no_overcharge_iff_pointwise.
Print Assumptions Kernel.NecWModels.nec_w_quantitative_floor_iff_pointwise.
Print Assumptions Kernel.NecWModels.nec_w_nn_forall_in.
Print Assumptions Kernel.NecWModels.nec_w_nn_pairwise_dec.
Print Assumptions Kernel.NecWModels.nec_w_in_dec.
Print Assumptions Kernel.NecWModels.nec_w_nodup_cover.
Print Assumptions Kernel.NecWModels.nec_w_logical_payment_cover_list.
Print Assumptions Kernel.NecWModels.nec_w_logical_payment_premises_needed.
Print Assumptions Kernel.NecWModels.nec_w_quote_decides_iff_digest.
Print Assumptions Kernel.NecWModels.nec_w_vc_iff_certificate.
Print Assumptions Kernel.NecWModels.nec_w_pcc_limit_tight.
(* === Kernel.NecWPointer : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWPointer.nec_w_toy_observers_iff.
Print Assumptions Kernel.NecWPointer.nec_w_blind_needs_in_range.
Print Assumptions Kernel.NecWPointer.nec_w_blind_needs_event.
Print Assumptions Kernel.NecWPointer.nec_w_blind_converse_refuted.
Print Assumptions Kernel.NecWPointer.nec_w_wrong_observer_blocks.
Print Assumptions Kernel.NecWPointer.nec_w_one_durable_observer_enough.
Print Assumptions Kernel.NecWPointer.nec_w_durable_corollary.
Print Assumptions Kernel.NecWPointer.nec_w_durable_premises_needed.
Print Assumptions Kernel.NecWPointer.nec_w_durable_iff_permanent.
(* === Kernel.NecWWindow : 21 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NecWWindow.nec_w_fibre_converse_fails_without_section.
Print Assumptions Kernel.NecWWindow.nec_w_decoder_iff_fibre_and_partial_section.
Print Assumptions Kernel.NecWWindow.nec_w_fibre_iff_partial_section.
Print Assumptions Kernel.NecWWindow.nec_w_fibre_section_corollary.
Print Assumptions Kernel.NecWWindow.nec_w_surjective_converse_iff_unique_choice.
Print Assumptions Kernel.NecWWindow.nec_w_exact_iff_flip_factors.
Print Assumptions Kernel.NecWWindow.nec_w_factor_no_collision.
Print Assumptions Kernel.NecWWindow.nec_w_shadowed_step_overcharged.
Print Assumptions Kernel.NecWWindow.nec_w_oeqb_spec.
Print Assumptions Kernel.NecWWindow.nec_w_flip_transition_spec.
Print Assumptions Kernel.NecWWindow.nec_w_least_price_spec.
Print Assumptions Kernel.NecWWindow.nec_w_finite_exact_iff_no_collision.
Print Assumptions Kernel.NecWWindow.nec_w_run_overcharge_tight.
Print Assumptions Kernel.NecWWindow.nec_w_general_converse_gives_wlem.
Print Assumptions Kernel.NecWWindow.nec_w_exact_without_reading_in_view.
Print Assumptions Kernel.NecWWindow.nec_w_commitment_escape_iff.
Print Assumptions Kernel.NecWWindow.nec_w_unchecked_contract_iff.
Print Assumptions Kernel.NecWWindow.nec_w_response_escape_iff.
Print Assumptions Kernel.NecWWindow.nec_w_response_needs_transcript.
Print Assumptions Kernel.NecWWindow.nec_w_verifier_iff_no_collision.
Print Assumptions Kernel.NecWWindow.nec_w_factoring_verifier_iff_no_collision.
(* === Kernel.Presentation : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.Presentation.cg_read_val_code.
Print Assumptions Kernel.Presentation.cg_read_val_junk.
Print Assumptions Kernel.Presentation.cg_mlatch_succ.
Print Assumptions Kernel.Presentation.cg_mlatch_false_rd.
Print Assumptions Kernel.Presentation.cg_first_raise_succ.
Print Assumptions Kernel.Presentation.cg_account_step.
Print Assumptions Kernel.Presentation.cg_account_start.
(* === Kernel.PresentedDemo : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PresentedDemo.pu_demo_toll.
Print Assumptions Kernel.PresentedDemo.pu_demo_idec.
Print Assumptions Kernel.PresentedDemo.pu_ra_comp.
Print Assumptions Kernel.PresentedDemo.pu_ra_rec1.
Print Assumptions Kernel.PresentedDemo.pu_ra_cst1.
Print Assumptions Kernel.PresentedDemo.pu_ra_proj0.
Print Assumptions Kernel.PresentedDemo.pu_ra_pred_spec.
Print Assumptions Kernel.PresentedDemo.pu_ra_sg_spec.
Print Assumptions Kernel.PresentedDemo.pu_demo_read_val.
Print Assumptions Kernel.PresentedDemo.pu_demo_read_spec.
Print Assumptions Kernel.PresentedDemo.pu_demo_computably_presented.
Print Assumptions Kernel.PresentedDemo.pu_demo_run.
Print Assumptions Kernel.PresentedDemo.pu_demo_ledger.
Print Assumptions Kernel.PresentedDemo.pu_demo_running.
Print Assumptions Kernel.PresentedDemo.pu_demo_first_raise.
Print Assumptions Kernel.PresentedDemo.pu_demo_universal.
Print Assumptions Kernel.PresentedDemo.pu_demo_never_halts.
Print Assumptions Kernel.PresentedDemo.pu_demo_flag_rises.
Print Assumptions Kernel.PresentedDemo.pu_demo_exact.
Print Assumptions Kernel.PresentedDemo.pu_demo_earned.
(* === Kernel.PresentedUniversal : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PresentedUniversal.pu_trace_next.
Print Assumptions Kernel.PresentedUniversal.pu_host_match.
Print Assumptions Kernel.PresentedUniversal.pu_grun_guest.
Print Assumptions Kernel.PresentedUniversal.presented_universal_halting.
Print Assumptions Kernel.PresentedUniversal.presented_universal_points.
Print Assumptions Kernel.PresentedUniversal.presented_universal_halt_point.
Print Assumptions Kernel.PresentedUniversal.presented_universal_flag_iff.
Print Assumptions Kernel.PresentedUniversal.presented_universal_earned.
Print Assumptions Kernel.PresentedUniversal.presented_universal.
Print Assumptions Kernel.PresentedUniversal.presented_universal_exact.
Print Assumptions Kernel.PresentedUniversal.presented_universal_surcharge_le_two.
Print Assumptions Kernel.PresentedUniversal.presented_universal_no_exact_below_three.
Print Assumptions Kernel.PresentedUniversal.presented_universal_U_no_exact_below_three.
(* === Kernel.PricedHostLinks : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PricedHostLinks.pu_multi_cs_run.
Print Assumptions Kernel.PricedHostLinks.pu_multi_cs_cost.
Print Assumptions Kernel.PricedHostLinks.pu_multi_cs_floor.
Print Assumptions Kernel.PricedHostLinks.priced_interp_cs_runs_U_P.
Print Assumptions Kernel.PricedHostLinks.priced_interp_U_P_certified_floor.
Print Assumptions Kernel.PricedHostLinks.priced_interp_halting_iff.
Print Assumptions Kernel.PricedHostLinks.cm_of_mm2_agrees.
Print Assumptions Kernel.PricedHostLinks.priced_next_compiled.
Print Assumptions Kernel.PricedHostLinks.priced_run_prog_is_prog_run.
Print Assumptions Kernel.PricedHostLinks.priced_halted_is_prog_halted.
Print Assumptions Kernel.PricedHostLinks.priced_guest_halting_correspondence.
Print Assumptions Kernel.PricedHostLinks.priced_guest_halting_undecidable.
Print Assumptions Kernel.PricedHostLinks.priced_interp_halting_undecidable.
Print Assumptions Kernel.PricedHostLinks.priced_interp_complete_agrees.
Print Assumptions Kernel.PricedHostLinks.priced_interp_U_P_complete_floor.
(* === Kernel.ProbabilisticRecord : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ProbabilisticRecord.fair_branch_honest.
Print Assumptions Kernel.ProbabilisticRecord.biased_branch_honest.
Print Assumptions Kernel.ProbabilisticRecord.deterministic_latch_handles_branching_refuted.
Print Assumptions Kernel.ProbabilisticRecord.branch_kernels_same_support.
Print Assumptions Kernel.ProbabilisticRecord.schedule_determines_probabilities_refuted.
Print Assumptions Kernel.ProbabilisticRecord.probability_preserving_equivalence_reflexive_holds.
(* === Kernel.ProperSubsumption : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.thiele_simulates_turing_gen.
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.thiele_simulates_turing.
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.turing_computable_implies_thiele_computable.
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.thiele_run_mu_bound.
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.cost_certificate_valid.
Print Assumptions Kernel.ProperSubsumption.ProperSubsumption.thiele_strictly_extends_turing.
(* === Kernel.Realize : 35 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.Realize.rlz_small_exec_is.
Print Assumptions Kernel.Realize.rlz_small_run_is.
Print Assumptions Kernel.Realize.rlz_small_step_is.
Print Assumptions Kernel.Realize.rlz_small_run_prog_is.
Print Assumptions Kernel.Realize.rlz_small_trace_of_is.
Print Assumptions Kernel.Realize.rlz_small_compile_is.
Print Assumptions Kernel.Realize.rlz_small_start_is.
Print Assumptions Kernel.Realize.rlz_small_halting_correspondence.
Print Assumptions Kernel.Realize.rlz_small_mu_conservation_trace.
Print Assumptions Kernel.Realize.rlz_small_run_prog_trace.
Print Assumptions Kernel.Realize.rlz_multi_run_prog_is.
Print Assumptions Kernel.Realize.rlz_multi_step_is.
Print Assumptions Kernel.Realize.rlz_multi_exec_is.
Print Assumptions Kernel.Realize.rlz_multi_run_is.
Print Assumptions Kernel.Realize.rlz_multi_mu_conservation_trace.
Print Assumptions Kernel.Realize.rlz_pmulti_run_prog_is.
Print Assumptions Kernel.Realize.rlz_pmulti_step_is.
Print Assumptions Kernel.Realize.rlz_pmulti_exec_is.
Print Assumptions Kernel.Realize.rlz_pmulti_run_is.
Print Assumptions Kernel.Realize.rlz_pgen_extends_gen.
Print Assumptions Kernel.Realize.rlz_pair_is.
Print Assumptions Kernel.Realize.rlz_unp_is.
Print Assumptions Kernel.Realize.rlz_unpair_is.
Print Assumptions Kernel.Realize.rlz_pcode_is.
Print Assumptions Kernel.Realize.rlz_pdec_is.
Print Assumptions Kernel.Realize.rlz_ccode_is.
Print Assumptions Kernel.Realize.rlz_icode_is.
Print Assumptions Kernel.Realize.rlz_prog_code_is.
Print Assumptions Kernel.Realize.rlz_host_prop_eqb_is.
Print Assumptions Kernel.Realize.rlz_host_eval_is.
Print Assumptions Kernel.Realize.rlz_host_program_is.
Print Assumptions Kernel.Realize.rlz_host_regs_is.
Print Assumptions Kernel.Realize.rlz_host_load_is.
Print Assumptions Kernel.Realize.rlz_host_run_prog_is.
Print Assumptions Kernel.Realize.rlz_host_at_is.
(* === Kernel.RealizeCompact : 60 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RealizeCompact.rlz_core_eqv_refl.
Print Assumptions Kernel.RealizeCompact.rlz_core_eqv_trans.
Print Assumptions Kernel.RealizeCompact.rlz_eqv_refl.
Print Assumptions Kernel.RealizeCompact.rlz_eqv_trans.
Print Assumptions Kernel.RealizeCompact.rlz_claim_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_check_ok_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_commit_ok_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_certify_ok_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_write_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_goto_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_trap_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_record_fact_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_commit_to_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_cexec_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_fires_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_exec_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_next_instr_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_step_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_run_prog_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_next_in.
Print Assumptions Kernel.RealizeCompact.rlz_cexec_inv.
Print Assumptions Kernel.RealizeCompact.rlz_step_inv.
Print Assumptions Kernel.RealizeCompact.rlz_nth_tab.
Print Assumptions Kernel.RealizeCompact.rlz_compact_eqv.
Print Assumptions Kernel.RealizeCompact.rlz_compact_inv.
Print Assumptions Kernel.RealizeCompact.rlz_sched_sound.
Print Assumptions Kernel.RealizeCompact.rlzp_core_eqv_refl.
Print Assumptions Kernel.RealizeCompact.rlzp_core_eqv_trans.
Print Assumptions Kernel.RealizeCompact.rlzp_eqv_refl.
Print Assumptions Kernel.RealizeCompact.rlzp_eqv_trans.
Print Assumptions Kernel.RealizeCompact.rlzp_claim_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_check_ok_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_commit_ok_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_certify_ok_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_write_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_goto_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_trap_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_record_fact_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_commit_to_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_cexec_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_fires_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_exec_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_next_instr_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_step_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_run_prog_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_next_in.
Print Assumptions Kernel.RealizeCompact.rlzp_cexec_inv.
Print Assumptions Kernel.RealizeCompact.rlzp_step_inv.
Print Assumptions Kernel.RealizeCompact.rlzp_nth_tab.
Print Assumptions Kernel.RealizeCompact.rlzp_compact_eqv.
Print Assumptions Kernel.RealizeCompact.rlzp_compact_inv.
Print Assumptions Kernel.RealizeCompact.rlzp_sched_sound.
Print Assumptions Kernel.RealizeCompact.rlz_host_program_below.
Print Assumptions Kernel.RealizeCompact.rlz_phost_program_below.
Print Assumptions Kernel.RealizeCompact.rlz_host_sched_app.
Print Assumptions Kernel.RealizeCompact.rlz_phost_sched_app.
Print Assumptions Kernel.RealizeCompact.rlz_host_sched_sound.
Print Assumptions Kernel.RealizeCompact.rlz_phost_sched_sound.
Print Assumptions Kernel.RealizeCompact.rlz_host_sched_sound_original.
Print Assumptions Kernel.RealizeCompact.rlz_phost_sched_sound_original.
(* === Kernel.RealizePriced : 41 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RealizePriced.rlz_nxtprime_le.
Print Assumptions Kernel.RealizePriced.rlz_scan_ok.
Print Assumptions Kernel.RealizePriced.rlz_nxtprime_with_eq.
Print Assumptions Kernel.RealizePriced.rlz_nxtprime_eq.
Print Assumptions Kernel.RealizePriced.rlz_iter_ext.
Print Assumptions Kernel.RealizePriced.rlz_qs_with_eq.
Print Assumptions Kernel.RealizePriced.rlz_qs_eq.
Print Assumptions Kernel.RealizePriced.rlz_expo_fuel_eq.
Print Assumptions Kernel.RealizePriced.rlz_expo_eq.
Print Assumptions Kernel.RealizePriced.rlz_idec_eq.
Print Assumptions Kernel.RealizePriced.rlz_pdec_list_eq.
Print Assumptions Kernel.RealizePriced.rlz_pdec_prog_eq.
Print Assumptions Kernel.RealizePriced.rlz_rdec_eq.
Print Assumptions Kernel.RealizePriced.rlz_exec_sim.
Print Assumptions Kernel.RealizePriced.rlz_run_fuel_sim.
Print Assumptions Kernel.RealizePriced.rlz_out_codeb_eq.
Print Assumptions Kernel.RealizePriced.rlz_ueval_with_eq.
Print Assumptions Kernel.RealizePriced.rlz_ueval_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_prop_eqb_is.
Print Assumptions Kernel.RealizePriced.rlz_pu_pdec_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_heval_with_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_heval_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_check_ok_ext.
Print Assumptions Kernel.RealizePriced.rlz_pu_cexec_ext.
Print Assumptions Kernel.RealizePriced.rlz_pu_exec_ext.
Print Assumptions Kernel.RealizePriced.rlz_pu_run_prog_ext.
Print Assumptions Kernel.RealizePriced.rlz_pr_check_ok_ext.
Print Assumptions Kernel.RealizePriced.rlz_pr_cexec_ext.
Print Assumptions Kernel.RealizePriced.rlz_pr_exec_ext.
Print Assumptions Kernel.RealizePriced.rlz_pr_run_prog_ext.
Print Assumptions Kernel.RealizePriced.rlz_phost_program_is.
Print Assumptions Kernel.RealizePriced.rlz_pu_ccode_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_cpcode_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_pcode_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_icode_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_prog_code_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_load_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_run_prog_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_at_eq.
Print Assumptions Kernel.RealizePriced.rlz_pguest_run_prog_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_run_prog_with_eq.
(* === Kernel.RealizePrograms : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RealizePrograms.rlz_host_program_is.
Print Assumptions Kernel.RealizePrograms.rlz_phost_program_is.
(* === Kernel.RecordAxisDiscrimination : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RecordAxisDiscrimination.latch_core_honest.
Print Assumptions Kernel.RecordAxisDiscrimination.history_latch_injective.
Print Assumptions Kernel.RecordAxisDiscrimination.history_latch_honest.
Print Assumptions Kernel.RecordAxisDiscrimination.finite_reversible_cannot_write.
(* === Kernel.SmBlock : 1 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmBlock.sm2_bint_of_MMA.
(* === Kernel.SmChain : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmChain.sm2_in2_big.
Print Assumptions Kernel.SmChain.sm2_N3.
Print Assumptions Kernel.SmChain.sm2_dsx_nodup.
Print Assumptions Kernel.SmChain.sm2_dsc_nodup.
Print Assumptions Kernel.SmChain.sm2_dsx_notin.
Print Assumptions Kernel.SmChain.sm2_dsc_notin.
Print Assumptions Kernel.SmChain.sm2_win_count.
Print Assumptions Kernel.SmChain.sm2_fans.
Print Assumptions Kernel.SmChain.sm2_win_vals.
Print Assumptions Kernel.SmChain.sm2_setup.
Print Assumptions Kernel.SmChain.sm2_setup_halt.
Print Assumptions Kernel.SmChain.sm2_heval1.
Print Assumptions Kernel.SmChain.sm2_repeat_in.
Print Assumptions Kernel.SmChain.sm2_fetch_end.
Print Assumptions Kernel.SmChain.sm2_replay.
(* === Kernel.SmDecider : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmDecider.sm_flipf_mono.
Print Assumptions Kernel.SmDecider.sm_flip_MMA.
Print Assumptions Kernel.SmDecider.sm_flip_program.
Print Assumptions Kernel.SmDecider.sm_no_host_decider.
(* === Kernel.SmFixed : 30 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmFixed.sm2_len_gdx.
Print Assumptions Kernel.SmFixed.sm2_len_gdc.
Print Assumptions Kernel.SmFixed.sm2_len_gb0.
Print Assumptions Kernel.SmFixed.sm2_len_gb1.
Print Assumptions Kernel.SmFixed.sm2_len_gb2.
Print Assumptions Kernel.SmFixed.sm2_len_gb3.
Print Assumptions Kernel.SmFixed.sm2_len_gb4.
Print Assumptions Kernel.SmFixed.sm2_len_ginc.
Print Assumptions Kernel.SmFixed.sm2_len_gchk.
Print Assumptions Kernel.SmFixed.sm2_len_gcmt.
Print Assumptions Kernel.SmFixed.sm2_len_gcer.
Print Assumptions Kernel.SmFixed.sm2_len_gout.
Print Assumptions Kernel.SmFixed.sm2_len_gtrap.
Print Assumptions Kernel.SmFixed.sm2_VGq1.
Print Assumptions Kernel.SmFixed.sm2_VGq2.
Print Assumptions Kernel.SmFixed.sm2_VGq3.
Print Assumptions Kernel.SmFixed.sm2_VGq4.
Print Assumptions Kernel.SmFixed.sm2_VGq5.
Print Assumptions Kernel.SmFixed.sm2_VGq6.
Print Assumptions Kernel.SmFixed.sm2_VGq7.
Print Assumptions Kernel.SmFixed.sm2_VGq8.
Print Assumptions Kernel.SmFixed.sm2_VGq9.
Print Assumptions Kernel.SmFixed.sm2_VGq10.
Print Assumptions Kernel.SmFixed.sm2_VGq11.
Print Assumptions Kernel.SmFixed.sm2_VGq12.
Print Assumptions Kernel.SmFixed.sm2_VGq13.
Print Assumptions Kernel.SmFixed.sm2_VG_length.
Print Assumptions Kernel.SmFixed.sm2_VG_fetch8.
Print Assumptions Kernel.SmFixed.sm2_VG_forward.
Print Assumptions Kernel.SmFixed.sm2_VG_halt.
(* === Kernel.SmFixedPoint : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmFixedPoint.sm2_spec_ends.
Print Assumptions Kernel.SmFixedPoint.sm2_spec_start.
Print Assumptions Kernel.SmFixedPoint.sm2_obs_of_numbers.
Print Assumptions Kernel.SmFixedPoint.sm2_fwd_core.
Print Assumptions Kernel.SmFixedPoint.sm2_bwd_core.
Print Assumptions Kernel.SmFixedPoint.sm2_kleene_obs.
Print Assumptions Kernel.SmFixedPoint.sm2_kleene_fun.
(* === Kernel.SmFuel : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmFuel.sm_mu_option_proc.
Print Assumptions Kernel.SmFuel.sm_mu_option_equiv.
Print Assumptions Kernel.SmFuel.sm_f2_total.
Print Assumptions Kernel.SmFuel.sm_L_computable_fuel2.
Print Assumptions Kernel.SmFuel.sm_ev_MMA.
Print Assumptions Kernel.SmFuel.sm_uev_MMA.
(* === Kernel.SmGuestRice : 55 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmGuestRice.sm_gagree_sym.
Print Assumptions Kernel.SmGuestRice.sm_gequiv_sym.
Print Assumptions Kernel.SmGuestRice.sm_grun_succ.
Print Assumptions Kernel.SmGuestRice.sm_grun_add.
Print Assumptions Kernel.SmGuestRice.sm_ghalted_after.
Print Assumptions Kernel.SmGuestRice.sm_greloc_length.
Print Assumptions Kernel.SmGuestRice.sm_gembeds_app.
Print Assumptions Kernel.SmGuestRice.sm_gfetch_range.
Print Assumptions Kernel.SmGuestRice.sm_gfetch_out.
Print Assumptions Kernel.SmGuestRice.sm_eqb_add.
Print Assumptions Kernel.SmGuestRice.sm_fsh_eqb.
Print Assumptions Kernel.SmGuestRice.sm_existsb_fsh.
Print Assumptions Kernel.SmGuestRice.sm_fsh_zero.
Print Assumptions Kernel.SmGuestRice.sm_fsh_opt_zero.
Print Assumptions Kernel.SmGuestRice.sm_gnext_some.
Print Assumptions Kernel.SmGuestRice.sm_gnext_intro.
Print Assumptions Kernel.SmGuestRice.sm_gri_halt.
Print Assumptions Kernel.SmGuestRice.sm_gcrel_val.
Print Assumptions Kernel.SmGuestRice.sm_gcrel_claim.
Print Assumptions Kernel.SmGuestRice.sm_gblock_cstep.
Print Assumptions Kernel.SmGuestRice.sm_gblock_step.
Print Assumptions Kernel.SmGuestRice.sm_gblock_run_mid.
Print Assumptions Kernel.SmGuestRice.sm_gblock_not_halted.
Print Assumptions Kernel.SmGuestRice.sm_gblock_halted.
Print Assumptions Kernel.SmGuestRice.sm_gblock_run_final.
Print Assumptions Kernel.SmGuestRice.sm_gincs_length.
Print Assumptions Kernel.SmGuestRice.sm_gplain_exec.
Print Assumptions Kernel.SmGuestRice.sm_gincs_run.
Print Assumptions Kernel.SmGuestRice.sm_gclear_run.
Print Assumptions Kernel.SmGuestRice.sm_compile_run.
Print Assumptions Kernel.SmGuestRice.sm_grice_pre_length.
Print Assumptions Kernel.SmGuestRice.sm_gfetch_app_left.
Print Assumptions Kernel.SmGuestRice.sm_gfetch_app_right.
Print Assumptions Kernel.SmGuestRice.sm_grice_prog_split.
Print Assumptions Kernel.SmGuestRice.sm_grice_fetch_a.
Print Assumptions Kernel.SmGuestRice.sm_grice_fetch_b.
Print Assumptions Kernel.SmGuestRice.sm_grice_embeds_h.
Print Assumptions Kernel.SmGuestRice.sm_grice_fetch_clear1.
Print Assumptions Kernel.SmGuestRice.sm_grice_fetch_clear2.
Print Assumptions Kernel.SmGuestRice.sm_grice_embeds_p.
Print Assumptions Kernel.SmGuestRice.sm_grice_length.
Print Assumptions Kernel.SmGuestRice.sm_ghblock_no_halt.
Print Assumptions Kernel.SmGuestRice.sm_grice_phase1.
Print Assumptions Kernel.SmGuestRice.sm_gat1_rel.
Print Assumptions Kernel.SmGuestRice.sm_gfinal_equiv.
Print Assumptions Kernel.SmGuestRice.sm_option_dec'.
Print Assumptions Kernel.SmGuestRice.sm_grice_prog_halts.
Print Assumptions Kernel.SmGuestRice.sm_grice_prog_diverges.
Print Assumptions Kernel.SmGuestRice.sm_gloop_runs.
Print Assumptions Kernel.SmGuestRice.sm_gloop_diverges.
Print Assumptions Kernel.SmGuestRice.sm_gnever_equiv.
Print Assumptions Kernel.SmGuestRice.sm_gext_compl.
Print Assumptions Kernel.SmGuestRice.sm_guest_rice_loop.
Print Assumptions Kernel.SmGuestRice.sm_guest_rice.
Print Assumptions Kernel.SmGuestRice.sm_guest_halting_clean_undecidable.
(* === Kernel.SmHostRice : 38 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmHostRice.sm_mm2_instr_at_iff.
Print Assumptions Kernel.SmHostRice.sm_mm2_step_iff.
Print Assumptions Kernel.SmHostRice.sm_mm2_stop_iff.
Print Assumptions Kernel.SmHostRice.sm_mm2_terminates_iff.
Print Assumptions Kernel.SmHostRice.sm_least.
Print Assumptions Kernel.SmHostRice.sm_mk_plain.
Print Assumptions Kernel.SmHostRice.sm_mk_step.
Print Assumptions Kernel.SmHostRice.sm_mk_run.
Print Assumptions Kernel.SmHostRice.sm_mk_halted.
Print Assumptions Kernel.SmHostRice.sm_regs_bound_spec.
Print Assumptions Kernel.SmHostRice.sm_rice_pre_length.
Print Assumptions Kernel.SmHostRice.sm_rice_fetch_a.
Print Assumptions Kernel.SmHostRice.sm_rice_fetch_b.
Print Assumptions Kernel.SmHostRice.sm_rice_embeds_h.
Print Assumptions Kernel.SmHostRice.sm_fetch_app_right.
Print Assumptions Kernel.SmHostRice.sm_rice_prog_split.
Print Assumptions Kernel.SmHostRice.sm_rice_fetch_clear1.
Print Assumptions Kernel.SmHostRice.sm_rice_fetch_clear2.
Print Assumptions Kernel.SmHostRice.sm_rice_embeds_p.
Print Assumptions Kernel.SmHostRice.sm_rice_length.
Print Assumptions Kernel.SmHostRice.sm_within_fresh.
Print Assumptions Kernel.SmHostRice.sm_within_all.
Print Assumptions Kernel.SmHostRice.sm_hblock_no_halt.
Print Assumptions Kernel.SmHostRice.sm_rice_phase1.
Print Assumptions Kernel.SmHostRice.sm_at1_rel.
Print Assumptions Kernel.SmHostRice.sm_srel_agree.
Print Assumptions Kernel.SmHostRice.sm_final_hequiv.
Print Assumptions Kernel.SmHostRice.sm_option_dec.
Print Assumptions Kernel.SmHostRice.sm_fetch_none_out.
Print Assumptions Kernel.SmHostRice.sm_rice_reach.
Print Assumptions Kernel.SmHostRice.sm_rice_prog_halts.
Print Assumptions Kernel.SmHostRice.sm_rice_prog_diverges.
Print Assumptions Kernel.SmHostRice.sm_hloop_runs.
Print Assumptions Kernel.SmHostRice.sm_hloop_diverges.
Print Assumptions Kernel.SmHostRice.sm_never_hequiv.
Print Assumptions Kernel.SmHostRice.sm_hext_compl.
Print Assumptions Kernel.SmHostRice.sm_host_rice_loop.
Print Assumptions Kernel.SmHostRice.sm_host_rice.
(* === Kernel.SmKleene : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmKleene.sm_vec_pos_const.
Print Assumptions Kernel.SmKleene.sm_v0_pos.
Print Assumptions Kernel.SmKleene.sm_mmatch_in2.
Print Assumptions Kernel.SmKleene.sm_spec_phase1.
Print Assumptions Kernel.SmKleene.sm_spec_embeds.
Print Assumptions Kernel.SmKleene.sm_spec_length.
Print Assumptions Kernel.SmKleene.sm_spec_hfun.
Print Assumptions Kernel.SmKleene.sm_vrel_step.
Print Assumptions Kernel.SmKleene.sm_vrel_run.
Print Assumptions Kernel.SmKleene.sm_vrel_halted.
Print Assumptions Kernel.SmKleene.sm_vrel_sym.
Print Assumptions Kernel.SmKleene.sm_smn.
Print Assumptions Kernel.SmKleene.sm_mma_two.
Print Assumptions Kernel.SmKleene.sm_mma_plain.
Print Assumptions Kernel.SmKleene.sm_host_universal.
Print Assumptions Kernel.SmKleene.sm_second_recursion.
Print Assumptions Kernel.SmKleene.sm_kleene.
Print Assumptions Kernel.SmKleene.sm_kleene_codes.
Print Assumptions Kernel.SmKleene.sm_no_inside_decider.
Print Assumptions Kernel.SmKleene.sm_host_rice_fun.
(* === Kernel.SmMMAHost : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmMMAHost.sm_mma_fetch.
Print Assumptions Kernel.SmMMAHost.sm_write_match.
Print Assumptions Kernel.SmMMAHost.sm_mma_step.
Print Assumptions Kernel.SmMMAHost.sm_mma_out_halted.
Print Assumptions Kernel.SmMMAHost.sm_mma_forward.
Print Assumptions Kernel.SmMMAHost.sm_crun_halted.
Print Assumptions Kernel.SmMMAHost.sm_mma_backward.
Print Assumptions Kernel.SmMMAHost.sm_mma_host_out.
(* === Kernel.SmMMAOff : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmMMAOff.sm2_RR_lift.
Print Assumptions Kernel.SmMMAOff.sm2_mmfr_refl.
Print Assumptions Kernel.SmMMAOff.sm2_mmfr_trans.
Print Assumptions Kernel.SmMMAOff.sm2_mma_fetch.
Print Assumptions Kernel.SmMMAOff.sm2_pos_outside.
Print Assumptions Kernel.SmMMAOff.sm2_mma_step.
Print Assumptions Kernel.SmMMAOff.sm2_mma_out_halted.
Print Assumptions Kernel.SmMMAOff.sm2_mma_forward.
Print Assumptions Kernel.SmMMAOff.sm2_mma_backward.
Print Assumptions Kernel.SmMMAOff.sm2_mma_ctx.
Print Assumptions Kernel.SmMMAOff.sm2_bsearch.
Print Assumptions Kernel.SmMMAOff.sm2_next_dec.
Print Assumptions Kernel.SmMMAOff.sm2_mma_ctx_halt.
(* === Kernel.SmNoExact : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmNoExact.sm2_lt_pow2.
Print Assumptions Kernel.SmNoExact.sm2_pair_ge_l.
Print Assumptions Kernel.SmNoExact.sm2_kcode_reg.
Print Assumptions Kernel.SmNoExact.sm2_hcode_cons.
Print Assumptions Kernel.SmNoExact.sm2_reg_bound.
Print Assumptions Kernel.SmNoExact.sm2_next_in.
Print Assumptions Kernel.SmNoExact.sm2_trace_in.
Print Assumptions Kernel.SmNoExact.sm2_prog_frame.
Print Assumptions Kernel.SmNoExact.sm2_imp_MMA.
Print Assumptions Kernel.SmNoExact.sm2_imp_program.
Print Assumptions Kernel.SmNoExact.sm2_imp_code.
Print Assumptions Kernel.SmNoExact.sm2_no_exact.
(* === Kernel.SmSmnAll : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmSmnAll.sm2_shf_inj.
Print Assumptions Kernel.SmSmnAll.sm2_existsb_shf.
Print Assumptions Kernel.SmSmnAll.sm2_wrel_step.
Print Assumptions Kernel.SmSmnAll.sm2_wrel_run.
Print Assumptions Kernel.SmSmnAll.sm2_wrel_halted.
Print Assumptions Kernel.SmSmnAll.sm2_wrel_halted'.
Print Assumptions Kernel.SmSmnAll.sm2_incs_vers.
Print Assumptions Kernel.SmSmnAll.sm2_spec_vers2.
Print Assumptions Kernel.SmSmnAll.sm2_smn_all.
(* === Kernel.SmTallyL : 1 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmTallyL.sm2_ev_MMA.
(* === Kernel.SmallChshLinks : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmallChshLinks.small_chsh_cs_floor.
Print Assumptions Kernel.SmallChshLinks.small_chsh_certified_floor.
Print Assumptions Kernel.SmallChshLinks.small_chsh_chain_cost.
(* === Kernel.StructuralClockSync : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.StructuralClockSync.record_axis_is_latch_r1_r4.
Print Assumptions Kernel.StructuralClockSync.driven_reachably_driven.
Print Assumptions Kernel.StructuralClockSync.record_axis_is_latch_reachable.
Print Assumptions Kernel.StructuralClockSync.clock_not_reachably_driven.
Print Assumptions Kernel.StructuralClockSync.sync_clock_in_step.
Print Assumptions Kernel.StructuralClockSync.sync_clock_not_driven.
Print Assumptions Kernel.StructuralClockSync.sync_clock_reachably_driven.
Print Assumptions Kernel.StructuralClockSync.sync_clock_reachable_latch.
Print Assumptions Kernel.StructuralClockSync.sync_clock_record_permanent.
(* === Kernel.StructuralRecordAxis : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.StructuralRecordAxis.record_axis_is_latch_holds.
Print Assumptions Kernel.StructuralRecordAxis.record_pair_is_two_latches_holds.
Print Assumptions Kernel.StructuralRecordAxis.toggle_computation_driven.
Print Assumptions Kernel.StructuralRecordAxis.toggle_not_permanent.
Print Assumptions Kernel.StructuralRecordAxis.toggle_not_latch.
Print Assumptions Kernel.StructuralRecordAxis.clock_record_permanent.
Print Assumptions Kernel.StructuralRecordAxis.clock_record_not_driven.
(* === Kernel.Substrate : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.Substrate.prog_equiv_sym.
Print Assumptions Kernel.Substrate.prog_equiv_trans.
Print Assumptions Kernel.Substrate.mu_monotone_chain.
(* === Kernel.Tc2Plain : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.Tc2Plain.tc2_plain_pf.
Print Assumptions Kernel.Tc2Plain.tc2_mulprog_fun.
Print Assumptions Kernel.Tc2Plain.tc2_cx_eq.
Print Assumptions Kernel.Tc2Plain.tc2_fx_mono.
Print Assumptions Kernel.Tc2Plain.tc2_fx_MMA.
Print Assumptions Kernel.Tc2Plain.tc2_fcode_pcode.
Print Assumptions Kernel.Tc2Plain.tc2_F_computed.
Print Assumptions Kernel.Tc2Plain.tc2_plain_recursion_false.
Print Assumptions Kernel.Tc2Plain.tc2_plain_recursion_refuted.
Print Assumptions Kernel.Tc2Plain.tc2_plain_recursion_needs_LL.
(* === Kernel.Tc2PlainAdd : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.Tc2PlainAdd.tc2_krep_eq.
Print Assumptions Kernel.Tc2PlainAdd.tc2_addfx_mono.
Print Assumptions Kernel.Tc2PlainAdd.tc2_addfx_MMA.
Print Assumptions Kernel.Tc2PlainAdd.tc2_addcode_pcode.
Print Assumptions Kernel.Tc2PlainAdd.tc2_Fadd_computed.
Print Assumptions Kernel.Tc2PlainAdd.tc2_plain_recursion_needs_LL0.
(* === Kernel.TcBridge : 23 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcBridge.tc_vec2.
Print Assumptions Kernel.TcBridge.tc_vec2_ex.
Print Assumptions Kernel.TcBridge.tc_ofvec_tovec.
Print Assumptions Kernel.TcBridge.tc_ofvec_inj.
Print Assumptions Kernel.TcBridge.tc_mstep_fetch.
Print Assumptions Kernel.TcBridge.tc_mstep_none.
Print Assumptions Kernel.TcBridge.tc_mstep_none_iff.
Print Assumptions Kernel.TcBridge.tc_ctr_0.
Print Assumptions Kernel.TcBridge.tc_ctr_1.
Print Assumptions Kernel.TcBridge.tc_inst_forward.
Print Assumptions Kernel.TcBridge.tc_inst_back.
Print Assumptions Kernel.TcBridge.tc_fetch_conv.
Print Assumptions Kernel.TcBridge.tc_step_iff.
Print Assumptions Kernel.TcBridge.tc_steps_mrun.
Print Assumptions Kernel.TcBridge.tc_mrun_steps.
Print Assumptions Kernel.TcBridge.tc_steps_app.
Print Assumptions Kernel.TcBridge.tc_steps_fwd.
Print Assumptions Kernel.TcBridge.tc_steps_bwd.
Print Assumptions Kernel.TcBridge.tc_steps_iff.
Print Assumptions Kernel.TcBridge.tc_fetch_none_iff.
Print Assumptions Kernel.TcBridge.tc_output_iff.
Print Assumptions Kernel.TcBridge.tc_terminates_iff.
Print Assumptions Kernel.TcBridge.tc_nonterm_never_stops.
(* === Kernel.TcCodes : 31 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcCodes.tc_hb_correct.
Print Assumptions Kernel.TcCodes.tc_hb_unique.
Print Assumptions Kernel.TcCodes.tc_hb_spec.
Print Assumptions Kernel.TcCodes.tc_unp_eq.
Print Assumptions Kernel.TcCodes.tc_unpair_eq.
Print Assumptions Kernel.TcCodes.tc_unpair_pair.
Print Assumptions Kernel.TcCodes.tc_pair_ge.
Print Assumptions Kernel.TcCodes.tc_lencode_ge.
Print Assumptions Kernel.TcCodes.tc_ldec_encode.
Print Assumptions Kernel.TcCodes.tc_ldecode_encode.
Print Assumptions Kernel.TcCodes.tc_lencode_G.
Print Assumptions Kernel.TcCodes.tc_kdec_kcode.
Print Assumptions Kernel.TcCodes.tc_kpdec_kpcode.
Print Assumptions Kernel.TcCodes.tc_cdec_ccode.
Print Assumptions Kernel.TcCodes.tc_of_to_ki.
Print Assumptions Kernel.TcCodes.tc_kcode_icode.
Print Assumptions Kernel.TcCodes.tc_map_of_to.
Print Assumptions Kernel.TcCodes.tc_pdec_pcode.
Print Assumptions Kernel.TcCodes.tc_pcode_prog_code.
Print Assumptions Kernel.TcCodes.tc_pcode_inj.
Print Assumptions Kernel.TcCodes.tc_pcode_of.
Print Assumptions Kernel.TcCodes.tc_kreloc_of.
Print Assumptions Kernel.TcCodes.tc_vchain_length.
Print Assumptions Kernel.TcCodes.tc_vchain_run.
Print Assumptions Kernel.TcCodes.tc_incs_repeat.
Print Assumptions Kernel.TcCodes.tc_kmulblock_eq.
Print Assumptions Kernel.TcCodes.tc_kmulchain_eq.
Print Assumptions Kernel.TcCodes.tc_knorm_eq.
Print Assumptions Kernel.TcCodes.tc_spec_length_prefix.
Print Assumptions Kernel.TcCodes.tc_kspec_prog_of.
Print Assumptions Kernel.TcCodes.tc_kspec_code.
(* === Kernel.TcCompile : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcCompile.gcr_succ.
Print Assumptions Kernel.TcCompile.gcr_not_div.
Print Assumptions Kernel.TcCompile.pr_not_zero.
Print Assumptions Kernel.TcCompile.icomp_length_eq.
Print Assumptions Kernel.TcCompile.icomp_eq_1.
Print Assumptions Kernel.TcCompile.icomp_eq_2.
Print Assumptions Kernel.TcCompile.icomp_eq_3.
Print Assumptions Kernel.TcCompile.icomp_eq_4.
Print Assumptions Kernel.TcCompile.icomp_sound.
(* === Kernel.TcCompile0 : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcCompile0.icomp0_len.
Print Assumptions Kernel.TcCompile0.gcr_succ.
Print Assumptions Kernel.TcCompile0.gcr_not_div.
Print Assumptions Kernel.TcCompile0.vec_change_back.
Print Assumptions Kernel.TcCompile0.icomp0_sound.
Print Assumptions Kernel.TcCompile0.tc_code0_indep.
Print Assumptions Kernel.TcCompile0.tc_comp0_halts.
Print Assumptions Kernel.TcCompile0.tc_comp0_terminates.
Print Assumptions Kernel.TcCompile0.tc_comp0_complete.
(* === Kernel.TcCompose : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcCompose.tc_compose_halts.
Print Assumptions Kernel.TcCompose.tc_compile_ends.
Print Assumptions Kernel.TcCompose.tc_ends_compile.
(* === Kernel.TcEpi : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcEpi.tc_L_in.
Print Assumptions Kernel.TcEpi.tc_epi_length.
Print Assumptions Kernel.TcEpi.tc_epi_run.
Print Assumptions Kernel.TcEpi.tc_cast_output.
Print Assumptions Kernel.TcEpi.tc_cast_terminates.
(* === Kernel.TcFuel : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcFuel.tc_mu_option_proc.
Print Assumptions Kernel.TcFuel.tc_mu_option_equiv.
Print Assumptions Kernel.TcFuel.tc_f2_total.
Print Assumptions Kernel.TcFuel.tc_L_computable_fuel2.
Print Assumptions Kernel.TcFuel.tc_ev_MMA.
Print Assumptions Kernel.TcFuel.tc_uev_MMA.
(* === Kernel.TcGadget : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcGadget.tc_AB.
Print Assumptions Kernel.TcGadget.tc_change_A.
Print Assumptions Kernel.TcGadget.tc_change_B.
Print Assumptions Kernel.TcGadget.tc_posA.
Print Assumptions Kernel.TcGadget.tc_posB.
Print Assumptions Kernel.TcGadget.tc_mult.
Print Assumptions Kernel.TcGadget.tc_incs.
Print Assumptions Kernel.TcGadget.tc_decs.
Print Assumptions Kernel.TcGadget.tc_div_yes.
Print Assumptions Kernel.TcGadget.tc_div_no.
Print Assumptions Kernel.TcGadget.tc_div_loop.
(* === Kernel.TcGodel : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcGodel.tc_gcd_1_r.
Print Assumptions Kernel.TcGodel.tc_gcd_mul.
Print Assumptions Kernel.TcGodel.tc_gcd_pow.
Print Assumptions Kernel.TcGodel.tc_cons_pos0.
Print Assumptions Kernel.TcGodel.tc_cons_nxt.
Print Assumptions Kernel.TcGodel.tc_cons_inv.
Print Assumptions Kernel.TcGodel.tc_enc_cons.
Print Assumptions Kernel.TcGodel.tc_pow_pos.
Print Assumptions Kernel.TcGodel.tc_enc_pos.
Print Assumptions Kernel.TcGodel.tc_gcd_enc.
Print Assumptions Kernel.TcGodel.tc_enc_succ.
Print Assumptions Kernel.TcGodel.tc_enc_not_div.
Print Assumptions Kernel.TcGodel.tc_prod_pos.
Print Assumptions Kernel.TcGodel.tc_prod_div.
Print Assumptions Kernel.TcGodel.tc_gcd_succ.
Print Assumptions Kernel.TcGodel.tc_moduli_exist.
(* === Kernel.TcInterp : 26 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcInterp.tc_keval_eq.
Print Assumptions Kernel.TcInterp.tc_kfeq_eq.
Print Assumptions Kernel.TcInterp.tc_kmem_eq.
Print Assumptions Kernel.TcInterp.tc_fetch_of.
Print Assumptions Kernel.TcInterp.tc_krel_halted.
Print Assumptions Kernel.TcInterp.tc_val_rel.
Print Assumptions Kernel.TcInterp.tc_ver_rel.
Print Assumptions Kernel.TcInterp.tc_krel_step.
Print Assumptions Kernel.TcInterp.tc_krel_run.
Print Assumptions Kernel.TcInterp.tc_krel_start.
Print Assumptions Kernel.TcInterp.tc_kout_ends.
Print Assumptions Kernel.TcInterp.tc_kstep_halted.
Print Assumptions Kernel.TcInterp.tc_krun_halted.
Print Assumptions Kernel.TcInterp.tc_krun_add.
Print Assumptions Kernel.TcInterp.tc_kout_mono.
Print Assumptions Kernel.TcInterp.tc_klog_go_sound.
Print Assumptions Kernel.TcInterp.tc_lt_pow2.
Print Assumptions Kernel.TcInterp.tc_klog_go_complete.
Print Assumptions Kernel.TcInterp.tc_klog_pow.
Print Assumptions Kernel.TcInterp.tc_klog_sound.
Print Assumptions Kernel.TcInterp.tc_kpk_mono.
Print Assumptions Kernel.TcInterp.tc_kpk_pk.
Print Assumptions Kernel.TcInterp.tc_uev_spec.
Print Assumptions Kernel.TcInterp.tc_uev_mono.
Print Assumptions Kernel.TcInterp.tc_ev_mono.
Print Assumptions Kernel.TcInterp.tc_ev_spec.
(* === Kernel.TcMod : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcMod.tc_ok_cons.
Print Assumptions Kernel.TcMod.tc_moduli6.
Print Assumptions Kernel.TcMod.tc_moduli_for.
Print Assumptions Kernel.TcMod.tc_enc_zero.
Print Assumptions Kernel.TcMod.tc_enc_three.
(* === Kernel.TcNoFine : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcNoFine.tc_inv_step.
Print Assumptions Kernel.TcNoFine.tc_inv_run.
Print Assumptions Kernel.TcNoFine.tc_inv_start.
Print Assumptions Kernel.TcNoFine.tc_pair_gt.
Print Assumptions Kernel.TcNoFine.tc_pair_gt_l.
Print Assumptions Kernel.TcNoFine.tc_lencode_gt.
Print Assumptions Kernel.TcNoFine.tc_check_operand.
Print Assumptions Kernel.TcNoFine.tc_fprog_records.
Print Assumptions Kernel.TcNoFine.tc_no_fine_fixed_point.
Print Assumptions Kernel.TcNoFine.tc_chkf_fuel_free.
Print Assumptions Kernel.TcNoFine.tc_chk_MMA.
Print Assumptions Kernel.TcNoFine.tc_pcode_fprog.
Print Assumptions Kernel.TcNoFine.tc_no_fine_kleene.
(* === Kernel.TcNorm : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcNorm.nicomp_len.
Print Assumptions Kernel.TcNorm.nicomp_sound.
Print Assumptions Kernel.TcNorm.tc_normcode_halts.
Print Assumptions Kernel.TcNorm.tc_normcode_terminates.
(* === Kernel.TcPacked : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcPacked.tc_ends_unique.
Print Assumptions Kernel.TcPacked.tc_pk_unique.
Print Assumptions Kernel.TcPacked.tc_pk2_unique.
Print Assumptions Kernel.TcPacked.tc_const_zero.
Print Assumptions Kernel.TcPacked.tc_MMA_to_packed.
Print Assumptions Kernel.TcPacked.tc_universal.
Print Assumptions Kernel.TcPacked.tc_smn.
Print Assumptions Kernel.TcPacked.tc_second_recursion.
Print Assumptions Kernel.TcPacked.tc_kleene.
Print Assumptions Kernel.TcPacked.tc_kleene_codes.
(* === Kernel.TcPackedMMA : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcPackedMMA.tc_Pp_length.
Print Assumptions Kernel.TcPackedMMA.tc_Pp_halts.
Print Assumptions Kernel.TcPackedMMA.tc_Pp_terminates.
Print Assumptions Kernel.TcPackedMMA.tc_Pp_output.
Print Assumptions Kernel.TcPackedMMA.tc_unit1_shape.
Print Assumptions Kernel.TcPackedMMA.tc_mma_packed.
(* === Kernel.TcPlain : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcPlain.tc_plain_is_packed.
Print Assumptions Kernel.TcPlain.tc_rice_packed_fun.
Print Assumptions Kernel.TcPlain.tc_adder_run.
Print Assumptions Kernel.TcPlain.tc_adder_ends.
Print Assumptions Kernel.TcPlain.tc_plain_fixed_point_additive.
Print Assumptions Kernel.TcPlain.tc_plain_recursion_needs_LL.
Print Assumptions Kernel.TcPlain.tc_plain_recursion_self_adder.
(* === Kernel.TcPrefix : 28 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcPrefix.tc_gcd2_res.
Print Assumptions Kernel.TcPrefix.tc_gcd3_res.
Print Assumptions Kernel.TcPrefix.tc_res_hyp.
Print Assumptions Kernel.TcPrefix.tc_coprime_not_div.
Print Assumptions Kernel.TcPrefix.tc_gcd_pow3.
Print Assumptions Kernel.TcPrefix.tc_not2.
Print Assumptions Kernel.TcPrefix.tc_not3.
Print Assumptions Kernel.TcPrefix.tc_p1_len.
Print Assumptions Kernel.TcPrefix.tc_p2_len.
Print Assumptions Kernel.TcPrefix.tc_p3_len.
Print Assumptions Kernel.TcPrefix.tc_p5_len.
Print Assumptions Kernel.TcPrefix.tc_p6_len.
Print Assumptions Kernel.TcPrefix.tc_p7_len.
Print Assumptions Kernel.TcPrefix.tc_p8_len.
Print Assumptions Kernel.TcPrefix.tc_pre_length.
Print Assumptions Kernel.TcPrefix.tc_sc.
Print Assumptions Kernel.TcPrefix.tc_sc1.
Print Assumptions Kernel.TcPrefix.tc_sc2.
Print Assumptions Kernel.TcPrefix.tc_sc3.
Print Assumptions Kernel.TcPrefix.tc_sc4.
Print Assumptions Kernel.TcPrefix.tc_sc5.
Print Assumptions Kernel.TcPrefix.tc_sc6.
Print Assumptions Kernel.TcPrefix.tc_sc7.
Print Assumptions Kernel.TcPrefix.tc_sc8.
Print Assumptions Kernel.TcPrefix.tc_phase1.
Print Assumptions Kernel.TcPrefix.tc_phase3.
Print Assumptions Kernel.TcPrefix.tc_pre_halts.
Print Assumptions Kernel.TcPrefix.tc_pre_diverges.
(* === Kernel.TcRice : 38 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcRice.tc_PCPb_to_MMA2.
Print Assumptions Kernel.TcRice.tc_MMA2_HALTING_compl_undec.
Print Assumptions Kernel.TcRice.tc_agree_sym.
Print Assumptions Kernel.TcRice.tc_equiv_sym.
Print Assumptions Kernel.TcRice.tc_shape_fsh.
Print Assumptions Kernel.TcRice.tc_gsrel_agree.
Print Assumptions Kernel.TcRice.tc_gfinal_two.
Print Assumptions Kernel.TcRice.tc_gfinal_one.
Print Assumptions Kernel.TcRice.tc_gloop_runs.
Print Assumptions Kernel.TcRice.tc_gloop_diverges.
Print Assumptions Kernel.TcRice.tc_never_equiv.
Print Assumptions Kernel.TcRice.tc_prefix_next.
Print Assumptions Kernel.TcRice.tc_prefix_run.
Print Assumptions Kernel.TcRice.tc_eprog_length.
Print Assumptions Kernel.TcRice.tc_rice_prog_length.
Print Assumptions Kernel.TcRice.tc_rice_embeds.
Print Assumptions Kernel.TcRice.tc_not_stopped.
Print Assumptions Kernel.TcRice.tc_steps_inside.
Print Assumptions Kernel.TcRice.tc_start_window.
Print Assumptions Kernel.TcRice.tc_rel_start.
Print Assumptions Kernel.TcRice.tc_prog_halts.
Print Assumptions Kernel.TcRice.tc_prog_diverges.
Print Assumptions Kernel.TcRice.tc_prog_equiv_y.
Print Assumptions Kernel.TcRice.tc_prog_equiv_loop.
Print Assumptions Kernel.TcRice.tc_ext_compl.
Print Assumptions Kernel.TcRice.tc_rice_loop.
Print Assumptions Kernel.TcRice.tc_rice.
Print Assumptions Kernel.TcRice.tc_rice_plain.
Print Assumptions Kernel.TcRice.tc_rice_packed.
Print Assumptions Kernel.TcRice.tc_rice_clean.
Print Assumptions Kernel.TcRice.tc_equiv_mono.
Print Assumptions Kernel.TcRice.tc_ext_mono.
Print Assumptions Kernel.TcRice.tc_rice_dichotomy.
Print Assumptions Kernel.TcRice.tc_halts_all_undecidable.
Print Assumptions Kernel.TcRice.tc_halt_only_halted.
Print Assumptions Kernel.TcRice.tc_halt_only_ends.
Print Assumptions Kernel.TcRice.tc_inc_halt_ends.
Print Assumptions Kernel.TcRice.tc_identity_undecidable.
(* === Kernel.TcRiceMM : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TcRiceMM.tc_ms_ok.
Print Assumptions Kernel.TcRiceMM.tc_gc2_one.
Print Assumptions Kernel.TcRiceMM.tc_code_tovec.
Print Assumptions Kernel.TcRiceMM.tc_simul_iff.
Print Assumptions Kernel.TcRiceMM.tc_Q_halts.
Print Assumptions Kernel.TcRiceMM.tc_Q_diverges.
(* === Kernel.UniversalBlocks : 68 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalBlocks.sc_app_l.
Print Assumptions Kernel.UniversalBlocks.sc_app_r.
Print Assumptions Kernel.UniversalBlocks.sc_cons_l.
Print Assumptions Kernel.UniversalBlocks.sc_cons_r.
Print Assumptions Kernel.UniversalBlocks.sc_pos.
Print Assumptions Kernel.UniversalBlocks.hstep1.
Print Assumptions Kernel.UniversalBlocks.hexec_plain_sub.
Print Assumptions Kernel.UniversalBlocks.p01_2.
Print Assumptions Kernel.UniversalBlocks.p01.
Print Assumptions Kernel.UniversalBlocks.p02.
Print Assumptions Kernel.UniversalBlocks.p12.
Print Assumptions Kernel.UniversalBlocks.nd1.
Print Assumptions Kernel.UniversalBlocks.nd2.
Print Assumptions Kernel.UniversalBlocks.nd3.
Print Assumptions Kernel.UniversalBlocks.hINC_spec.
Print Assumptions Kernel.UniversalBlocks.hDEC_spec.
Print Assumptions Kernel.UniversalBlocks.hJMP_length.
Print Assumptions Kernel.UniversalBlocks.hJZ_length.
Print Assumptions Kernel.UniversalBlocks.hZERO_length.
Print Assumptions Kernel.UniversalBlocks.hMOVE_length.
Print Assumptions Kernel.UniversalBlocks.hMOVE2_length.
Print Assumptions Kernel.UniversalBlocks.hPACK_length.
Print Assumptions Kernel.UniversalBlocks.hHALF_length.
Print Assumptions Kernel.UniversalBlocks.hUNPACK_length.
Print Assumptions Kernel.UniversalBlocks.hJMP_spec.
Print Assumptions Kernel.UniversalBlocks.hJZ_spec.
Print Assumptions Kernel.UniversalBlocks.hZERO_spec.
Print Assumptions Kernel.UniversalBlocks.hMOVE_spec.
Print Assumptions Kernel.UniversalBlocks.hMOVE2_spec.
Print Assumptions Kernel.UniversalBlocks.hPACK_spec.
Print Assumptions Kernel.UniversalBlocks.hHALF_spec.
Print Assumptions Kernel.UniversalBlocks.hUNPACK_spec.
Print Assumptions Kernel.UniversalBlocks.hUNPACK0_spec.
Print Assumptions Kernel.UniversalBlocks.hrun_err.
Print Assumptions Kernel.UniversalBlocks.hCOPY_length.
Print Assumptions Kernel.UniversalBlocks.hCOPY_spec.
Print Assumptions Kernel.UniversalBlocks.hDISP_length.
Print Assumptions Kernel.UniversalBlocks.hDISP_spec.
Print Assumptions Kernel.UniversalBlocks.hEQC_length.
Print Assumptions Kernel.UniversalBlocks.nth_repeat_last.
Print Assumptions Kernel.UniversalBlocks.hEQC_spec.
Print Assumptions Kernel.UniversalBlocks.hEQR_length.
Print Assumptions Kernel.UniversalBlocks.hEQR_loop.
Print Assumptions Kernel.UniversalBlocks.hEQR_spec.
Print Assumptions Kernel.UniversalBlocks.hFETCH_length.
Print Assumptions Kernel.UniversalBlocks.fetch_code_zero.
Print Assumptions Kernel.UniversalBlocks.fetch_code_0.
Print Assumptions Kernel.UniversalBlocks.hFETCH_loop.
Print Assumptions Kernel.UniversalBlocks.hFETCH_spec.
Print Assumptions Kernel.UniversalBlocks.hFETCH_guest.
Print Assumptions Kernel.UniversalBlocks.hFETCH_guest_pc0.
Print Assumptions Kernel.UniversalBlocks.hBUMP_length.
Print Assumptions Kernel.UniversalBlocks.hBUMP_spec.
Print Assumptions Kernel.UniversalBlocks.hCHECK_step.
Print Assumptions Kernel.UniversalBlocks.hCOMMIT_step.
Print Assumptions Kernel.UniversalBlocks.hCERTIFY_step.
Print Assumptions Kernel.UniversalBlocks.hCHECK_pass.
Print Assumptions Kernel.UniversalBlocks.hCHECK_pass_fields.
Print Assumptions Kernel.UniversalBlocks.hCHECK_fail.
Print Assumptions Kernel.UniversalBlocks.hCHECK_fail_holds.
Print Assumptions Kernel.UniversalBlocks.hCHECK_fail_cap.
Print Assumptions Kernel.UniversalBlocks.hCHECK_fail_zero.
Print Assumptions Kernel.UniversalBlocks.hCOMMIT_pass.
Print Assumptions Kernel.UniversalBlocks.hCOMMIT_pass_fields.
Print Assumptions Kernel.UniversalBlocks.hCOMMIT_fail.
Print Assumptions Kernel.UniversalBlocks.hCERTIFY_pass.
Print Assumptions Kernel.UniversalBlocks.hCERTIFY_fail.
Print Assumptions Kernel.UniversalBlocks.trap_fields.
(* === Kernel.UniversalBridge : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalBridge.vec_pos_inj.
Print Assumptions Kernel.UniversalBridge.vec_pos_not_in.
Print Assumptions Kernel.UniversalBridge.agree_hvec.
Print Assumptions Kernel.UniversalBridge.trace_of_halted.
Print Assumptions Kernel.UniversalBridge.trace_of_add.
Print Assumptions Kernel.UniversalBridge.run_vers_mono.
Print Assumptions Kernel.UniversalBridge.run_same_ver_same_val.
Print Assumptions Kernel.UniversalBridge.hrun_refl.
Print Assumptions Kernel.UniversalBridge.hrun_trans.
Print Assumptions Kernel.UniversalBridge.hrun_same_sub.
Print Assumptions Kernel.UniversalBridge.hrun_vers_mono.
Print Assumptions Kernel.UniversalBridge.hrun_val_moved.
Print Assumptions Kernel.UniversalBridge.hframe_refl.
Print Assumptions Kernel.UniversalBridge.hframe_trans.
Print Assumptions Kernel.UniversalBridge.hframe_incl.
Print Assumptions Kernel.UniversalBridge.subcode_fetch.
Print Assumptions Kernel.UniversalBridge.host_step_fetch.
Print Assumptions Kernel.UniversalBridge.host_step_at.
Print Assumptions Kernel.UniversalBridge.host_trace_at.
Print Assumptions Kernel.UniversalBridge.lift_plain.
Print Assumptions Kernel.UniversalBridge.lift_not_halt.
Print Assumptions Kernel.UniversalBridge.lift_mentions_out.
Print Assumptions Kernel.UniversalBridge.lift_cexec.
Print Assumptions Kernel.UniversalBridge.lift_steps.
Print Assumptions Kernel.UniversalBridge.mma_compute_host.
Print Assumptions Kernel.UniversalBridge.mma_compute_host_regs.
Print Assumptions Kernel.UniversalBridge.mma_block_host.
(* === Kernel.UniversalInterpreterLinks : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalInterpreterLinks.multi_cs_run.
Print Assumptions Kernel.UniversalInterpreterLinks.multi_cs_cost.
Print Assumptions Kernel.UniversalInterpreterLinks.multi_cs_floor.
Print Assumptions Kernel.UniversalInterpreterLinks.interp_cs_runs_U.
Print Assumptions Kernel.UniversalInterpreterLinks.interp_U_certified_floor.
Print Assumptions Kernel.UniversalInterpreterLinks.interp_halting_iff.
Print Assumptions Kernel.UniversalInterpreterLinks.interp_halting_undecidable.
Print Assumptions Kernel.UniversalInterpreterLinks.interp_complete_agrees.
Print Assumptions Kernel.UniversalInterpreterLinks.interp_U_complete_floor.
Print Assumptions Kernel.UniversalInterpreterLinks.multi_cs_no_exact_copy.
(* === Kernel.UniversalLayout : 67 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalLayout.greg_CA.
Print Assumptions Kernel.UniversalLayout.greg_CB.
Print Assumptions Kernel.UniversalLayout.scratch_cases.
Print Assumptions Kernel.UniversalLayout.in_mp_MP.
Print Assumptions Kernel.UniversalLayout.in_slots_SLOT.
Print Assumptions Kernel.UniversalLayout.in_mp_inv.
Print Assumptions Kernel.UniversalLayout.in_slots_inv.
Print Assumptions Kernel.UniversalLayout.fam_length.
Print Assumptions Kernel.UniversalLayout.fam_sub.
Print Assumptions Kernel.UniversalLayout.fam_sub0.
Print Assumptions Kernel.UniversalLayout.icode_op_arg.
Print Assumptions Kernel.UniversalLayout.op_of_lt.
Print Assumptions Kernel.UniversalLayout.hHEAD_length.
Print Assumptions Kernel.UniversalLayout.hHALTB_length.
Print Assumptions Kernel.UniversalLayout.hCD_length.
Print Assumptions Kernel.UniversalLayout.hUCD_length.
Print Assumptions Kernel.UniversalLayout.hBUMPS_length.
Print Assumptions Kernel.UniversalLayout.hINCH_length.
Print Assumptions Kernel.UniversalLayout.hDECH_length.
Print Assumptions Kernel.UniversalLayout.hCKS_length.
Print Assumptions Kernel.UniversalLayout.hCKH_length.
Print Assumptions Kernel.UniversalLayout.hCMS_length.
Print Assumptions Kernel.UniversalLayout.hEQRS_length.
Print Assumptions Kernel.UniversalLayout.hCMH_length.
Print Assumptions Kernel.UniversalLayout.hCERTH_length.
Print Assumptions Kernel.UniversalLayout.label_values.
Print Assumptions Kernel.UniversalLayout.block_len_values.
Print Assumptions Kernel.UniversalLayout.U_length.
Print Assumptions Kernel.UniversalLayout.concat_split.
Print Assumptions Kernel.UniversalLayout.sc_concat.
Print Assumptions Kernel.UniversalLayout.U_HEAD.
Print Assumptions Kernel.UniversalLayout.U_HALTB.
Print Assumptions Kernel.UniversalLayout.U_INCD.
Print Assumptions Kernel.UniversalLayout.U_INCH.
Print Assumptions Kernel.UniversalLayout.U_DECD.
Print Assumptions Kernel.UniversalLayout.U_DECH.
Print Assumptions Kernel.UniversalLayout.U_CKD.
Print Assumptions Kernel.UniversalLayout.U_CKH.
Print Assumptions Kernel.UniversalLayout.U_CMD.
Print Assumptions Kernel.UniversalLayout.U_CMH.
Print Assumptions Kernel.UniversalLayout.U_CERTH.
Print Assumptions Kernel.UniversalLayout.U_BUMPS_inc.
Print Assumptions Kernel.UniversalLayout.U_BUMPS_dec.
Print Assumptions Kernel.UniversalLayout.U_CKH_slots.
Print Assumptions Kernel.UniversalLayout.U_CKS.
Print Assumptions Kernel.UniversalLayout.U_CKH_dead.
Print Assumptions Kernel.UniversalLayout.U_EQRS.
Print Assumptions Kernel.UniversalLayout.U_CMH_dead.
Print Assumptions Kernel.UniversalLayout.U_CMH_slots.
Print Assumptions Kernel.UniversalLayout.U_CMS.
Print Assumptions Kernel.UniversalLayout.U_fetch_stop.
Print Assumptions Kernel.UniversalLayout.sites_In.
Print Assumptions Kernel.UniversalLayout.sites_fetch.
Print Assumptions Kernel.UniversalLayout.U_slot_sites.
Print Assumptions Kernel.UniversalLayout.U_dead_sites.
Print Assumptions Kernel.UniversalLayout.U_slot_mentions.
Print Assumptions Kernel.UniversalLayout.U_slot_sites_fetch.
Print Assumptions Kernel.UniversalLayout.U_slot_dec_next.
Print Assumptions Kernel.UniversalLayout.U_slot_kinds.
Print Assumptions Kernel.UniversalLayout.paid_sites_length.
Print Assumptions Kernel.UniversalLayout.U_paid_sites.
Print Assumptions Kernel.UniversalLayout.cost_le_1.
Print Assumptions Kernel.UniversalLayout.U_paid.
Print Assumptions Kernel.UniversalLayout.U_free.
Print Assumptions Kernel.UniversalLayout.U_halt_sites.
Print Assumptions Kernel.UniversalLayout.mentions_ireg.
Print Assumptions Kernel.UniversalLayout.U_regs_bound.
(* === Kernel.UniversalPBlocks : 70 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPBlocks.pu_sc_app_l.
Print Assumptions Kernel.UniversalPBlocks.pu_sc_app_r.
Print Assumptions Kernel.UniversalPBlocks.pu_sc_cons_l.
Print Assumptions Kernel.UniversalPBlocks.pu_sc_cons_r.
Print Assumptions Kernel.UniversalPBlocks.pu_sc_pos.
Print Assumptions Kernel.UniversalPBlocks.pu_hstep1.
Print Assumptions Kernel.UniversalPBlocks.pu_hexec_plain_sub.
Print Assumptions Kernel.UniversalPBlocks.pu_p01_2.
Print Assumptions Kernel.UniversalPBlocks.pu_p01.
Print Assumptions Kernel.UniversalPBlocks.pu_p02.
Print Assumptions Kernel.UniversalPBlocks.pu_p12.
Print Assumptions Kernel.UniversalPBlocks.pu_nd1.
Print Assumptions Kernel.UniversalPBlocks.pu_nd2.
Print Assumptions Kernel.UniversalPBlocks.pu_nd3.
Print Assumptions Kernel.UniversalPBlocks.pu_hINC_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hDEC_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hJMP_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hJZ_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hZERO_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hMOVE_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hMOVE2_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hPACK_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hHALF_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hUNPACK_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hJMP_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hJZ_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hZERO_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hMOVE_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hMOVE2_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hPACK_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hHALF_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hUNPACK_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hUNPACK0_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hrun_err.
Print Assumptions Kernel.UniversalPBlocks.pu_hCOPY_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hCOPY_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hDISP_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hDISP_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hEQC_length.
Print Assumptions Kernel.UniversalPBlocks.pu_nth_repeat_last.
Print Assumptions Kernel.UniversalPBlocks.pu_hEQC_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hEQR_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hEQR_loop.
Print Assumptions Kernel.UniversalPBlocks.pu_hEQR_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hFETCH_length.
Print Assumptions Kernel.UniversalPBlocks.pu_fetch_code_zero.
Print Assumptions Kernel.UniversalPBlocks.pu_fetch_code_0.
Print Assumptions Kernel.UniversalPBlocks.pu_hFETCH_loop.
Print Assumptions Kernel.UniversalPBlocks.pu_hFETCH_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hFETCH_guest.
Print Assumptions Kernel.UniversalPBlocks.pu_hFETCH_guest_pc0.
Print Assumptions Kernel.UniversalPBlocks.pu_hBUMP_length.
Print Assumptions Kernel.UniversalPBlocks.pu_hBUMP_spec.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_step.
Print Assumptions Kernel.UniversalPBlocks.pu_hCOMMIT_step.
Print Assumptions Kernel.UniversalPBlocks.pu_hCERTIFY_step.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_pass.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_pass_fields.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_fail.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_fail_holds.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_fail_cap.
Print Assumptions Kernel.UniversalPBlocks.pu_hCHECK_fail_zero.
Print Assumptions Kernel.UniversalPBlocks.pu_hCOMMIT_pass.
Print Assumptions Kernel.UniversalPBlocks.pu_hCOMMIT_pass_fields.
Print Assumptions Kernel.UniversalPBlocks.pu_hCOMMIT_fail.
Print Assumptions Kernel.UniversalPBlocks.pu_hCERTIFY_pass.
Print Assumptions Kernel.UniversalPBlocks.pu_hCERTIFY_fail.
Print Assumptions Kernel.UniversalPBlocks.pu_hPAY_step.
Print Assumptions Kernel.UniversalPBlocks.pu_hPAY_pass.
Print Assumptions Kernel.UniversalPBlocks.pu_trap_fields.
(* === Kernel.UniversalPBridge : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPBridge.pu_vec_pos_inj.
Print Assumptions Kernel.UniversalPBridge.pu_vec_pos_not_in.
Print Assumptions Kernel.UniversalPBridge.pu_agree_hvec.
Print Assumptions Kernel.UniversalPBridge.pu_trace_of_halted.
Print Assumptions Kernel.UniversalPBridge.pu_trace_of_add.
Print Assumptions Kernel.UniversalPBridge.pu_run_vers_mono.
Print Assumptions Kernel.UniversalPBridge.pu_run_same_ver_same_val.
Print Assumptions Kernel.UniversalPBridge.pu_hrun_refl.
Print Assumptions Kernel.UniversalPBridge.pu_hrun_trans.
Print Assumptions Kernel.UniversalPBridge.pu_hrun_same_sub.
Print Assumptions Kernel.UniversalPBridge.pu_hrun_vers_mono.
Print Assumptions Kernel.UniversalPBridge.pu_hrun_val_moved.
Print Assumptions Kernel.UniversalPBridge.pu_hframe_refl.
Print Assumptions Kernel.UniversalPBridge.pu_hframe_trans.
Print Assumptions Kernel.UniversalPBridge.pu_hframe_incl.
Print Assumptions Kernel.UniversalPBridge.pu_subcode_fetch.
Print Assumptions Kernel.UniversalPBridge.pu_host_step_fetch.
Print Assumptions Kernel.UniversalPBridge.pu_host_step_at.
Print Assumptions Kernel.UniversalPBridge.pu_host_trace_at.
Print Assumptions Kernel.UniversalPBridge.pu_lift_plain.
Print Assumptions Kernel.UniversalPBridge.pu_lift_not_halt.
Print Assumptions Kernel.UniversalPBridge.pu_lift_mentions_out.
Print Assumptions Kernel.UniversalPBridge.pu_lift_cexec.
Print Assumptions Kernel.UniversalPBridge.pu_lift_steps.
Print Assumptions Kernel.UniversalPBridge.pu_mma_compute_host.
Print Assumptions Kernel.UniversalPBridge.pu_mma_compute_host_regs.
Print Assumptions Kernel.UniversalPBridge.pu_mma_block_host.
(* === Kernel.UniversalPCodes : 61 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPCodes.pu_g_err_write.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_zero.
Print Assumptions Kernel.UniversalPCodes.pu_pow2_pos.
Print Assumptions Kernel.UniversalPCodes.pu_pair_pos.
Print Assumptions Kernel.UniversalPCodes.pu_pair_S.
Print Assumptions Kernel.UniversalPCodes.pu_pair_0.
Print Assumptions Kernel.UniversalPCodes.pu_unp_fuel.
Print Assumptions Kernel.UniversalPCodes.pu_unp_odd.
Print Assumptions Kernel.UniversalPCodes.pu_unp_even.
Print Assumptions Kernel.UniversalPCodes.pu_unp_pair.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_pair.
Print Assumptions Kernel.UniversalPCodes.pu_pair_inj.
Print Assumptions Kernel.UniversalPCodes.pu_pair_onto.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_some.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_none.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_sound.
Print Assumptions Kernel.UniversalPCodes.pu_pair_encode.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_encode_nil.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_encode_cons.
Print Assumptions Kernel.UniversalPCodes.pu_cpdec_cpcode.
Print Assumptions Kernel.UniversalPCodes.pu_cpcode_cpdec.
Print Assumptions Kernel.UniversalPCodes.pu_even_double.
Print Assumptions Kernel.UniversalPCodes.pu_even_sdouble.
Print Assumptions Kernel.UniversalPCodes.pu_pdec_pcode.
Print Assumptions Kernel.UniversalPCodes.pu_pcode_pdec.
Print Assumptions Kernel.UniversalPCodes.pu_pcode_inj.
Print Assumptions Kernel.UniversalPCodes.pu_cdec_ccode.
Print Assumptions Kernel.UniversalPCodes.pu_cdec_sound.
Print Assumptions Kernel.UniversalPCodes.pu_ccode_inj.
Print Assumptions Kernel.UniversalPCodes.pu_ccode_lt.
Print Assumptions Kernel.UniversalPCodes.pu_hprop_eqb_eq.
Print Assumptions Kernel.UniversalPCodes.pu_heval_iff.
Print Assumptions Kernel.UniversalPCodes.pu_heval_pair.
Print Assumptions Kernel.UniversalPCodes.pu_hholds_pair.
Print Assumptions Kernel.UniversalPCodes.pu_heval_zero.
Print Assumptions Kernel.UniversalPCodes.pu_hholds_iff.
Print Assumptions Kernel.UniversalPCodes.pu_idecode_icode.
Print Assumptions Kernel.UniversalPCodes.pu_idecode_sound.
Print Assumptions Kernel.UniversalPCodes.pu_icode_inj.
Print Assumptions Kernel.UniversalPCodes.pu_icode_pos.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_icode.
Print Assumptions Kernel.UniversalPCodes.pu_prog_code_decode.
Print Assumptions Kernel.UniversalPCodes.pu_prog_code_nil.
Print Assumptions Kernel.UniversalPCodes.pu_prog_code_cons.
Print Assumptions Kernel.UniversalPCodes.pu_prog_code_inj.
Print Assumptions Kernel.UniversalPCodes.pu_skip_code_S.
Print Assumptions Kernel.UniversalPCodes.pu_fetch_code_S.
Print Assumptions Kernel.UniversalPCodes.pu_fetch_code_skip.
Print Assumptions Kernel.UniversalPCodes.pu_skip_code_encode.
Print Assumptions Kernel.UniversalPCodes.pu_fetch_code_encode.
Print Assumptions Kernel.UniversalPCodes.pu_nth_error_map_opt.
Print Assumptions Kernel.UniversalPCodes.pu_skipn_map_comm.
Print Assumptions Kernel.UniversalPCodes.pu_fetch_code_prog.
Print Assumptions Kernel.UniversalPCodes.pu_skip_code_prog.
Print Assumptions Kernel.UniversalPCodes.pu_unpair_skip_prog.
Print Assumptions Kernel.UniversalPCodes.pu_skip_prog_past_end.
Print Assumptions Kernel.UniversalPCodes.pu_fetch_decode_prog.
Print Assumptions Kernel.UniversalPCodes.pu_guest_fetch_code.
Print Assumptions Kernel.UniversalPCodes.pu_host_earned_certification_provenance.
Print Assumptions Kernel.UniversalPCodes.pu_host_slot_soundness.
Print Assumptions Kernel.UniversalPCodes.pu_host_committed_slot_holds.
(* === Kernel.UniversalPLayout : 69 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPLayout.pu_greg_CA.
Print Assumptions Kernel.UniversalPLayout.pu_greg_CB.
Print Assumptions Kernel.UniversalPLayout.pu_scratch_cases.
Print Assumptions Kernel.UniversalPLayout.pu_in_mp_MP.
Print Assumptions Kernel.UniversalPLayout.pu_in_slots_SLOT.
Print Assumptions Kernel.UniversalPLayout.pu_in_mp_inv.
Print Assumptions Kernel.UniversalPLayout.pu_in_slots_inv.
Print Assumptions Kernel.UniversalPLayout.pu_fam_length.
Print Assumptions Kernel.UniversalPLayout.pu_fam_sub.
Print Assumptions Kernel.UniversalPLayout.pu_fam_sub0.
Print Assumptions Kernel.UniversalPLayout.pu_icode_op_arg.
Print Assumptions Kernel.UniversalPLayout.pu_op_of_lt.
Print Assumptions Kernel.UniversalPLayout.pu_hHEAD_length.
Print Assumptions Kernel.UniversalPLayout.pu_hHALTB_length.
Print Assumptions Kernel.UniversalPLayout.pu_hCD_length.
Print Assumptions Kernel.UniversalPLayout.pu_hUCD_length.
Print Assumptions Kernel.UniversalPLayout.pu_hBUMPS_length.
Print Assumptions Kernel.UniversalPLayout.pu_hINCH_length.
Print Assumptions Kernel.UniversalPLayout.pu_hDECH_length.
Print Assumptions Kernel.UniversalPLayout.pu_hCKS_length.
Print Assumptions Kernel.UniversalPLayout.pu_hCKH_length.
Print Assumptions Kernel.UniversalPLayout.pu_hCMS_length.
Print Assumptions Kernel.UniversalPLayout.pu_hEQRS_length.
Print Assumptions Kernel.UniversalPLayout.pu_hCMH_length.
Print Assumptions Kernel.UniversalPLayout.pu_hCERTH_length.
Print Assumptions Kernel.UniversalPLayout.pu_hPAYH_length.
Print Assumptions Kernel.UniversalPLayout.pu_label_values.
Print Assumptions Kernel.UniversalPLayout.pu_block_len_values.
Print Assumptions Kernel.UniversalPLayout.pu_U_length.
Print Assumptions Kernel.UniversalPLayout.pu_concat_split.
Print Assumptions Kernel.UniversalPLayout.pu_sc_concat.
Print Assumptions Kernel.UniversalPLayout.pu_U_HEAD.
Print Assumptions Kernel.UniversalPLayout.pu_U_HALTB.
Print Assumptions Kernel.UniversalPLayout.pu_U_INCD.
Print Assumptions Kernel.UniversalPLayout.pu_U_INCH.
Print Assumptions Kernel.UniversalPLayout.pu_U_DECD.
Print Assumptions Kernel.UniversalPLayout.pu_U_DECH.
Print Assumptions Kernel.UniversalPLayout.pu_U_CKD.
Print Assumptions Kernel.UniversalPLayout.pu_U_CKH.
Print Assumptions Kernel.UniversalPLayout.pu_U_CMD.
Print Assumptions Kernel.UniversalPLayout.pu_U_CMH.
Print Assumptions Kernel.UniversalPLayout.pu_U_CERTH.
Print Assumptions Kernel.UniversalPLayout.pu_U_PAYH.
Print Assumptions Kernel.UniversalPLayout.pu_U_BUMPS_inc.
Print Assumptions Kernel.UniversalPLayout.pu_U_BUMPS_dec.
Print Assumptions Kernel.UniversalPLayout.pu_U_CKH_slots.
Print Assumptions Kernel.UniversalPLayout.pu_U_CKS.
Print Assumptions Kernel.UniversalPLayout.pu_U_CKH_dead.
Print Assumptions Kernel.UniversalPLayout.pu_U_EQRS.
Print Assumptions Kernel.UniversalPLayout.pu_U_CMH_dead.
Print Assumptions Kernel.UniversalPLayout.pu_U_CMH_slots.
Print Assumptions Kernel.UniversalPLayout.pu_U_CMS.
Print Assumptions Kernel.UniversalPLayout.pu_U_fetch_stop.
Print Assumptions Kernel.UniversalPLayout.pu_sites_In.
Print Assumptions Kernel.UniversalPLayout.pu_sites_fetch.
Print Assumptions Kernel.UniversalPLayout.pu_U_slot_sites.
Print Assumptions Kernel.UniversalPLayout.pu_U_dead_sites.
Print Assumptions Kernel.UniversalPLayout.pu_U_slot_mentions.
Print Assumptions Kernel.UniversalPLayout.pu_U_slot_sites_fetch.
Print Assumptions Kernel.UniversalPLayout.pu_U_slot_dec_next.
Print Assumptions Kernel.UniversalPLayout.pu_U_slot_kinds.
Print Assumptions Kernel.UniversalPLayout.pu_paid_sites_length.
Print Assumptions Kernel.UniversalPLayout.pu_U_paid_sites.
Print Assumptions Kernel.UniversalPLayout.pu_cost_le_1.
Print Assumptions Kernel.UniversalPLayout.pu_U_paid.
Print Assumptions Kernel.UniversalPLayout.pu_U_free.
Print Assumptions Kernel.UniversalPLayout.pu_U_halt_sites.
Print Assumptions Kernel.UniversalPLayout.pu_mentions_ireg.
Print Assumptions Kernel.UniversalPLayout.pu_U_regs_bound.
(* === Kernel.UniversalPPhases : 55 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPPhases.pu_hframe_keep_vfr.
Print Assumptions Kernel.UniversalPPhases.pu_hframe_hfr.
Print Assumptions Kernel.UniversalPPhases.pu_all_same_hframe.
Print Assumptions Kernel.UniversalPPhases.pu_nd_fetch.
Print Assumptions Kernel.UniversalPPhases.pu_nd_eqr.
Print Assumptions Kernel.UniversalPPhases.pu_cpick_nth.
Print Assumptions Kernel.UniversalPPhases.pu_nth_map_seq.
Print Assumptions Kernel.UniversalPPhases.pu_Hrun_hreach.
Print Assumptions Kernel.UniversalPPhases.pu_hreach_trans.
Print Assumptions Kernel.UniversalPPhases.pu_hreach_one.
Print Assumptions Kernel.UniversalPPhases.pu_hCD_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hUCD_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hBUMPS_gen.
Print Assumptions Kernel.UniversalPPhases.pu_hBUMPS_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hEQRS_gen.
Print Assumptions Kernel.UniversalPPhases.pu_hEQRS_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hHALTB_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hHEAD_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hINCH_spec.
Print Assumptions Kernel.UniversalPPhases.pu_hDECH_zero.
Print Assumptions Kernel.UniversalPPhases.pu_hDECH_taken.
Print Assumptions Kernel.UniversalPPhases.pu_hCKH_disp.
Print Assumptions Kernel.UniversalPPhases.pu_hCKS_pre.
Print Assumptions Kernel.UniversalPPhases.pu_hCKS_post.
Print Assumptions Kernel.UniversalPPhases.pu_hCMH_search.
Print Assumptions Kernel.UniversalPPhases.pu_hCMS_post.
Print Assumptions Kernel.UniversalPPhases.pu_hCERTH_post.
Print Assumptions Kernel.UniversalPPhases.pu_U_CHK.
Print Assumptions Kernel.UniversalPPhases.pu_U_CMT.
Print Assumptions Kernel.UniversalPPhases.pu_U_CERT.
Print Assumptions Kernel.UniversalPPhases.pu_halted_at_stop.
Print Assumptions Kernel.UniversalPPhases.pu_scratch_dec.
Print Assumptions Kernel.UniversalPPhases.pu_scratch_all.
Print Assumptions Kernel.UniversalPPhases.pu_at_head_zero.
Print Assumptions Kernel.UniversalPPhases.pu_phase_decode.
Print Assumptions Kernel.UniversalPPhases.pu_phase_stop.
Print Assumptions Kernel.UniversalPPhases.pu_phase_pc0.
Print Assumptions Kernel.UniversalPPhases.pu_phase_out.
Print Assumptions Kernel.UniversalPPhases.pu_phase_halt.
Print Assumptions Kernel.UniversalPPhases.pu_phase_inc.
Print Assumptions Kernel.UniversalPPhases.pu_phase_dec_taken.
Print Assumptions Kernel.UniversalPPhases.pu_phase_dec_zero.
Print Assumptions Kernel.UniversalPPhases.pu_check_to_slot.
Print Assumptions Kernel.UniversalPPhases.pu_phase_check_pass.
Print Assumptions Kernel.UniversalPPhases.pu_phase_check_fail.
Print Assumptions Kernel.UniversalPPhases.pu_phase_check_dead.
Print Assumptions Kernel.UniversalPPhases.pu_commit_search.
Print Assumptions Kernel.UniversalPPhases.pu_phase_commit_pass.
Print Assumptions Kernel.UniversalPPhases.pu_phase_commit_stale.
Print Assumptions Kernel.UniversalPPhases.pu_phase_commit_none.
Print Assumptions Kernel.UniversalPPhases.pu_phase_certify_pass.
Print Assumptions Kernel.UniversalPPhases.pu_phase_certify_fail.
Print Assumptions Kernel.UniversalPPhases.pu_hPAYH_post.
Print Assumptions Kernel.UniversalPPhases.pu_U_PAY.
Print Assumptions Kernel.UniversalPPhases.pu_phase_pay.
(* === Kernel.UniversalPRun : 42 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPRun.pu_hmu_mono.
Print Assumptions Kernel.UniversalPRun.pu_hmu_le.
Print Assumptions Kernel.UniversalPRun.pu_hcert_mono.
Print Assumptions Kernel.UniversalPRun.pu_hcert_le.
Print Assumptions Kernel.UniversalPRun.pu_hhalted_stay.
Print Assumptions Kernel.UniversalPRun.pu_hhalted_unique.
Print Assumptions Kernel.UniversalPRun.pu_hchan_const.
Print Assumptions Kernel.UniversalPRun.pu_htrace_prefix.
Print Assumptions Kernel.UniversalPRun.pu_hsame_point.
Print Assumptions Kernel.UniversalPRun.pu_grun_succ.
Print Assumptions Kernel.UniversalPRun.pu_grun_add.
Print Assumptions Kernel.UniversalPRun.pu_gstep_halted.
Print Assumptions Kernel.UniversalPRun.pu_gtrace_prefix.
Print Assumptions Kernel.UniversalPRun.pu_gtrace_succ.
Print Assumptions Kernel.UniversalPRun.pu_grun_same_ver.
Print Assumptions Kernel.UniversalPRun.pu_gsame_point.
Print Assumptions Kernel.UniversalPRun.pu_gnext_fetch.
Print Assumptions Kernel.UniversalPRun.pu_hrun_add.
Print Assumptions Kernel.UniversalPRun.pu_grun_halted_succ.
Print Assumptions Kernel.UniversalPRun.pu_sim_points.
Print Assumptions Kernel.UniversalPRun.pu_U_simulation.
Print Assumptions Kernel.UniversalPRun.pu_halt_point.
Print Assumptions Kernel.UniversalPRun.pu_universal_halting.
Print Assumptions Kernel.UniversalPRun.pu_universal_output.
Print Assumptions Kernel.UniversalPRun.pu_universal_flag_iff.
Print Assumptions Kernel.UniversalPRun.pu_universal_ledger_exact.
Print Assumptions Kernel.UniversalPRun.pu_cert_switch.
Print Assumptions Kernel.UniversalPRun.pu_universal_earned.
Print Assumptions Kernel.UniversalPRun.pu_run_host.
Print Assumptions Kernel.UniversalPRun.pu_U_run_on_host_machine.
Print Assumptions Kernel.UniversalPRun.pu_host_sim.
Print Assumptions Kernel.UniversalPRun.pu_host_untouched_prefix.
Print Assumptions Kernel.UniversalPRun.pu_host_chain_holds.
Print Assumptions Kernel.UniversalPRun.pu_host_chain_iff.
Print Assumptions Kernel.UniversalPRun.pu_hholds_one.
Print Assumptions Kernel.UniversalPRun.pu_hholds_zero.
Print Assumptions Kernel.UniversalPRun.pu_host_thiele_complete_with.
Print Assumptions Kernel.UniversalPRun.pu_universal_thiele_complete.
Print Assumptions Kernel.UniversalPRun.pu_claim_eqb_spec.
Print Assumptions Kernel.UniversalPRun.pu_same_keeps.
Print Assumptions Kernel.UniversalPRun.pu_host_check_sound.
Print Assumptions Kernel.UniversalPRun.pu_universal_thiele_complete_over.
(* === Kernel.UniversalPSim : 82 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPSim.pu_hload_high.
Print Assumptions Kernel.UniversalPSim.pu_greg_ne_gpc.
Print Assumptions Kernel.UniversalPSim.pu_greg_ne_t2.
Print Assumptions Kernel.UniversalPSim.pu_greg_inj.
Print Assumptions Kernel.UniversalPSim.pu_greg_not_mp.
Print Assumptions Kernel.UniversalPSim.pu_gpc_not_mp.
Print Assumptions Kernel.UniversalPSim.pu_nc_ne_greg.
Print Assumptions Kernel.UniversalPSim.pu_nc_ne_gpc.
Print Assumptions Kernel.UniversalPSim.pu_nc_not_mp.
Print Assumptions Kernel.UniversalPSim.pu_nc_inj.
Print Assumptions Kernel.UniversalPSim.pu_slot_ne_greg.
Print Assumptions Kernel.UniversalPSim.pu_slot_ne_gpc.
Print Assumptions Kernel.UniversalPSim.pu_slot_ne_nc.
Print Assumptions Kernel.UniversalPSim.pu_slot_not_mp.
Print Assumptions Kernel.UniversalPSim.pu_slot_ge.
Print Assumptions Kernel.UniversalPSim.pu_slot_not_in.
Print Assumptions Kernel.UniversalPSim.pu_slot_inj.
Print Assumptions Kernel.UniversalPSim.pu_slot_ne_mp.
Print Assumptions Kernel.UniversalPSim.pu_slot_ne_dead.
Print Assumptions Kernel.UniversalPSim.pu_mp_ne_greg.
Print Assumptions Kernel.UniversalPSim.pu_mp_ne_gpc.
Print Assumptions Kernel.UniversalPSim.pu_mp_ne_nc.
Print Assumptions Kernel.UniversalPSim.pu_mp_not_in.
Print Assumptions Kernel.UniversalPSim.pu_mp_inj.
Print Assumptions Kernel.UniversalPSim.pu_mp_ne_dead.
Print Assumptions Kernel.UniversalPSim.pu_dead_ne_greg.
Print Assumptions Kernel.UniversalPSim.pu_dead_ne_gpc.
Print Assumptions Kernel.UniversalPSim.pu_dead_ne_nc.
Print Assumptions Kernel.UniversalPSim.pu_dead_ne_t2.
Print Assumptions Kernel.UniversalPSim.pu_dead_not_mp.
Print Assumptions Kernel.UniversalPSim.pu_dead_ge.
Print Assumptions Kernel.UniversalPSim.pu_dead_not_slots.
Print Assumptions Kernel.UniversalPSim.pu_ra_ne_t2.
Print Assumptions Kernel.UniversalPSim.pu_rb_ne_t2.
Print Assumptions Kernel.UniversalPSim.pu_ra_ne_slot.
Print Assumptions Kernel.UniversalPSim.pu_rb_ne_slot.
Print Assumptions Kernel.UniversalPSim.pu_ra_ne_t7.
Print Assumptions Kernel.UniversalPSim.pu_rb_ne_t7.
Print Assumptions Kernel.UniversalPSim.pu_ctr_dec.
Print Assumptions Kernel.UniversalPSim.pu_ctr_eqb_eq.
Print Assumptions Kernel.UniversalPSim.pu_ctr_eqb_neq.
Print Assumptions Kernel.UniversalPSim.pu_ctr_eqb_refl.
Print Assumptions Kernel.UniversalPSim.pu_gval_write.
Print Assumptions Kernel.UniversalPSim.pu_gpc_write.
Print Assumptions Kernel.UniversalPSim.pu_gkeep_record.
Print Assumptions Kernel.UniversalPSim.pu_gkeep_commit.
Print Assumptions Kernel.UniversalPSim.pu_gkeep_goto.
Print Assumptions Kernel.UniversalPSim.pu_gkeep_trap.
Print Assumptions Kernel.UniversalPSim.pu_gstep_exec.
Print Assumptions Kernel.UniversalPSim.pu_ghalted_iff.
Print Assumptions Kernel.UniversalPSim.pu_ghalted_trap.
Print Assumptions Kernel.UniversalPSim.pu_gexec_noerr.
Print Assumptions Kernel.UniversalPSim.pu_count_cons.
Print Assumptions Kernel.UniversalPSim.pu_count_le_length.
Print Assumptions Kernel.UniversalPSim.pu_fresh_slot.
Print Assumptions Kernel.UniversalPSim.pu_occ_dec.
Print Assumptions Kernel.UniversalPSim.pu_in_map_gfact.
Print Assumptions Kernel.UniversalPSim.pu_gfact_eq.
Print Assumptions Kernel.UniversalPSim.pu_rec_ok_frame.
Print Assumptions Kernel.UniversalPSim.pu_rec_ok_bump.
Print Assumptions Kernel.UniversalPSim.pu_hload_rel.
Print Assumptions Kernel.UniversalPSim.pu_hreach_step.
Print Assumptions Kernel.UniversalPSim.pu_host_at_head_not_halted.
Print Assumptions Kernel.UniversalPSim.pu_rel_halt_trap.
Print Assumptions Kernel.UniversalPSim.pu_R_fetch.
Print Assumptions Kernel.UniversalPSim.pu_R_ra.
Print Assumptions Kernel.UniversalPSim.pu_R_rb.
Print Assumptions Kernel.UniversalPSim.pu_R_corr.
Print Assumptions Kernel.UniversalPSim.pu_ustep_stop.
Print Assumptions Kernel.UniversalPSim.pu_ustep_inc.
Print Assumptions Kernel.UniversalPSim.pu_ustep_dec_taken.
Print Assumptions Kernel.UniversalPSim.pu_rel_keep.
Print Assumptions Kernel.UniversalPSim.pu_ustep_dec_zero.
Print Assumptions Kernel.UniversalPSim.pu_ustep_check.
Print Assumptions Kernel.UniversalPSim.pu_first_match.
Print Assumptions Kernel.UniversalPSim.pu_ustep_commit.
Print Assumptions Kernel.UniversalPSim.pu_ustep_certify.
Print Assumptions Kernel.UniversalPSim.pu_ustep_pay.
Print Assumptions Kernel.UniversalPSim.pu_gnot_halted.
Print Assumptions Kernel.UniversalPSim.pu_U_step_with.
Print Assumptions Kernel.UniversalPSim.pu_U_step.
Print Assumptions Kernel.UniversalPSim.pu_rel_host_running.
(* === Kernel.UniversalPhases : 52 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalPhases.hframe_keep_vfr.
Print Assumptions Kernel.UniversalPhases.hframe_hfr.
Print Assumptions Kernel.UniversalPhases.all_same_hframe.
Print Assumptions Kernel.UniversalPhases.nd_fetch.
Print Assumptions Kernel.UniversalPhases.nd_eqr.
Print Assumptions Kernel.UniversalPhases.cpick_nth.
Print Assumptions Kernel.UniversalPhases.nth_map_seq.
Print Assumptions Kernel.UniversalPhases.Hrun_hreach.
Print Assumptions Kernel.UniversalPhases.hreach_trans.
Print Assumptions Kernel.UniversalPhases.hreach_one.
Print Assumptions Kernel.UniversalPhases.hCD_spec.
Print Assumptions Kernel.UniversalPhases.hUCD_spec.
Print Assumptions Kernel.UniversalPhases.hBUMPS_gen.
Print Assumptions Kernel.UniversalPhases.hBUMPS_spec.
Print Assumptions Kernel.UniversalPhases.hEQRS_gen.
Print Assumptions Kernel.UniversalPhases.hEQRS_spec.
Print Assumptions Kernel.UniversalPhases.hHALTB_spec.
Print Assumptions Kernel.UniversalPhases.hHEAD_spec.
Print Assumptions Kernel.UniversalPhases.hINCH_spec.
Print Assumptions Kernel.UniversalPhases.hDECH_zero.
Print Assumptions Kernel.UniversalPhases.hDECH_taken.
Print Assumptions Kernel.UniversalPhases.hCKH_disp.
Print Assumptions Kernel.UniversalPhases.hCKS_pre.
Print Assumptions Kernel.UniversalPhases.hCKS_post.
Print Assumptions Kernel.UniversalPhases.hCMH_search.
Print Assumptions Kernel.UniversalPhases.hCMS_post.
Print Assumptions Kernel.UniversalPhases.hCERTH_post.
Print Assumptions Kernel.UniversalPhases.U_CHK.
Print Assumptions Kernel.UniversalPhases.U_CMT.
Print Assumptions Kernel.UniversalPhases.U_CERT.
Print Assumptions Kernel.UniversalPhases.halted_at_stop.
Print Assumptions Kernel.UniversalPhases.scratch_dec.
Print Assumptions Kernel.UniversalPhases.scratch_all.
Print Assumptions Kernel.UniversalPhases.at_head_zero.
Print Assumptions Kernel.UniversalPhases.phase_decode.
Print Assumptions Kernel.UniversalPhases.phase_stop.
Print Assumptions Kernel.UniversalPhases.phase_pc0.
Print Assumptions Kernel.UniversalPhases.phase_out.
Print Assumptions Kernel.UniversalPhases.phase_halt.
Print Assumptions Kernel.UniversalPhases.phase_inc.
Print Assumptions Kernel.UniversalPhases.phase_dec_taken.
Print Assumptions Kernel.UniversalPhases.phase_dec_zero.
Print Assumptions Kernel.UniversalPhases.check_to_slot.
Print Assumptions Kernel.UniversalPhases.phase_check_pass.
Print Assumptions Kernel.UniversalPhases.phase_check_fail.
Print Assumptions Kernel.UniversalPhases.phase_check_dead.
Print Assumptions Kernel.UniversalPhases.commit_search.
Print Assumptions Kernel.UniversalPhases.phase_commit_pass.
Print Assumptions Kernel.UniversalPhases.phase_commit_stale.
Print Assumptions Kernel.UniversalPhases.phase_commit_none.
Print Assumptions Kernel.UniversalPhases.phase_certify_pass.
Print Assumptions Kernel.UniversalPhases.phase_certify_fail.
(* === Kernel.UniversalRun : 42 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalRun.hmu_mono.
Print Assumptions Kernel.UniversalRun.hmu_le.
Print Assumptions Kernel.UniversalRun.hcert_mono.
Print Assumptions Kernel.UniversalRun.hcert_le.
Print Assumptions Kernel.UniversalRun.hhalted_stay.
Print Assumptions Kernel.UniversalRun.hhalted_unique.
Print Assumptions Kernel.UniversalRun.hchan_const.
Print Assumptions Kernel.UniversalRun.htrace_prefix.
Print Assumptions Kernel.UniversalRun.hsame_point.
Print Assumptions Kernel.UniversalRun.grun_succ.
Print Assumptions Kernel.UniversalRun.grun_add.
Print Assumptions Kernel.UniversalRun.gstep_halted.
Print Assumptions Kernel.UniversalRun.gtrace_prefix.
Print Assumptions Kernel.UniversalRun.gtrace_succ.
Print Assumptions Kernel.UniversalRun.grun_same_ver.
Print Assumptions Kernel.UniversalRun.gsame_point.
Print Assumptions Kernel.UniversalRun.gnext_fetch.
Print Assumptions Kernel.UniversalRun.hrun_add.
Print Assumptions Kernel.UniversalRun.grun_halted_succ.
Print Assumptions Kernel.UniversalRun.sim_points.
Print Assumptions Kernel.UniversalRun.U_simulation.
Print Assumptions Kernel.UniversalRun.halt_point.
Print Assumptions Kernel.UniversalRun.universal_halting.
Print Assumptions Kernel.UniversalRun.universal_output.
Print Assumptions Kernel.UniversalRun.universal_flag_iff.
Print Assumptions Kernel.UniversalRun.universal_ledger_exact.
Print Assumptions Kernel.UniversalRun.cert_switch.
Print Assumptions Kernel.UniversalRun.universal_earned.
Print Assumptions Kernel.UniversalRun.run_host.
Print Assumptions Kernel.UniversalRun.U_run_on_host_machine.
Print Assumptions Kernel.UniversalRun.host_sim.
Print Assumptions Kernel.UniversalRun.host_untouched_prefix.
Print Assumptions Kernel.UniversalRun.host_chain_holds.
Print Assumptions Kernel.UniversalRun.host_chain_iff.
Print Assumptions Kernel.UniversalRun.hholds_one.
Print Assumptions Kernel.UniversalRun.hholds_zero.
Print Assumptions Kernel.UniversalRun.host_thiele_complete_with.
Print Assumptions Kernel.UniversalRun.universal_thiele_complete.
Print Assumptions Kernel.UniversalRun.host_claim_eqb_spec.
Print Assumptions Kernel.UniversalRun.host_same_keeps.
Print Assumptions Kernel.UniversalRun.host_check_sound.
Print Assumptions Kernel.UniversalRun.universal_thiele_complete_over.
(* === Kernel.UniversalSim : 81 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalSim.hload_high.
Print Assumptions Kernel.UniversalSim.greg_ne_gpc.
Print Assumptions Kernel.UniversalSim.greg_ne_t2.
Print Assumptions Kernel.UniversalSim.greg_inj.
Print Assumptions Kernel.UniversalSim.greg_not_mp.
Print Assumptions Kernel.UniversalSim.gpc_not_mp.
Print Assumptions Kernel.UniversalSim.nc_ne_greg.
Print Assumptions Kernel.UniversalSim.nc_ne_gpc.
Print Assumptions Kernel.UniversalSim.nc_not_mp.
Print Assumptions Kernel.UniversalSim.nc_inj.
Print Assumptions Kernel.UniversalSim.slot_ne_greg.
Print Assumptions Kernel.UniversalSim.slot_ne_gpc.
Print Assumptions Kernel.UniversalSim.slot_ne_nc.
Print Assumptions Kernel.UniversalSim.slot_not_mp.
Print Assumptions Kernel.UniversalSim.slot_ge.
Print Assumptions Kernel.UniversalSim.slot_not_in.
Print Assumptions Kernel.UniversalSim.slot_inj.
Print Assumptions Kernel.UniversalSim.slot_ne_mp.
Print Assumptions Kernel.UniversalSim.slot_ne_dead.
Print Assumptions Kernel.UniversalSim.mp_ne_greg.
Print Assumptions Kernel.UniversalSim.mp_ne_gpc.
Print Assumptions Kernel.UniversalSim.mp_ne_nc.
Print Assumptions Kernel.UniversalSim.mp_not_in.
Print Assumptions Kernel.UniversalSim.mp_inj.
Print Assumptions Kernel.UniversalSim.mp_ne_dead.
Print Assumptions Kernel.UniversalSim.dead_ne_greg.
Print Assumptions Kernel.UniversalSim.dead_ne_gpc.
Print Assumptions Kernel.UniversalSim.dead_ne_nc.
Print Assumptions Kernel.UniversalSim.dead_ne_t2.
Print Assumptions Kernel.UniversalSim.dead_not_mp.
Print Assumptions Kernel.UniversalSim.dead_ge.
Print Assumptions Kernel.UniversalSim.dead_not_slots.
Print Assumptions Kernel.UniversalSim.ra_ne_t2.
Print Assumptions Kernel.UniversalSim.rb_ne_t2.
Print Assumptions Kernel.UniversalSim.ra_ne_slot.
Print Assumptions Kernel.UniversalSim.rb_ne_slot.
Print Assumptions Kernel.UniversalSim.ra_ne_t7.
Print Assumptions Kernel.UniversalSim.rb_ne_t7.
Print Assumptions Kernel.UniversalSim.ctr_dec.
Print Assumptions Kernel.UniversalSim.ctr_eqb_eq.
Print Assumptions Kernel.UniversalSim.ctr_eqb_neq.
Print Assumptions Kernel.UniversalSim.ctr_eqb_refl.
Print Assumptions Kernel.UniversalSim.gval_write.
Print Assumptions Kernel.UniversalSim.gpc_write.
Print Assumptions Kernel.UniversalSim.gkeep_record.
Print Assumptions Kernel.UniversalSim.gkeep_commit.
Print Assumptions Kernel.UniversalSim.gkeep_goto.
Print Assumptions Kernel.UniversalSim.gkeep_trap.
Print Assumptions Kernel.UniversalSim.gstep_exec.
Print Assumptions Kernel.UniversalSim.ghalted_iff.
Print Assumptions Kernel.UniversalSim.ghalted_trap.
Print Assumptions Kernel.UniversalSim.gexec_noerr.
Print Assumptions Kernel.UniversalSim.count_cons.
Print Assumptions Kernel.UniversalSim.count_le_length.
Print Assumptions Kernel.UniversalSim.fresh_slot.
Print Assumptions Kernel.UniversalSim.occ_dec.
Print Assumptions Kernel.UniversalSim.in_map_gfact.
Print Assumptions Kernel.UniversalSim.gfact_eq.
Print Assumptions Kernel.UniversalSim.rec_ok_frame.
Print Assumptions Kernel.UniversalSim.rec_ok_bump.
Print Assumptions Kernel.UniversalSim.hload_rel.
Print Assumptions Kernel.UniversalSim.hreach_step.
Print Assumptions Kernel.UniversalSim.host_at_head_not_halted.
Print Assumptions Kernel.UniversalSim.rel_halt_trap.
Print Assumptions Kernel.UniversalSim.R_fetch.
Print Assumptions Kernel.UniversalSim.R_ra.
Print Assumptions Kernel.UniversalSim.R_rb.
Print Assumptions Kernel.UniversalSim.R_corr.
Print Assumptions Kernel.UniversalSim.ustep_stop.
Print Assumptions Kernel.UniversalSim.ustep_inc.
Print Assumptions Kernel.UniversalSim.ustep_dec_taken.
Print Assumptions Kernel.UniversalSim.rel_keep.
Print Assumptions Kernel.UniversalSim.ustep_dec_zero.
Print Assumptions Kernel.UniversalSim.ustep_check.
Print Assumptions Kernel.UniversalSim.first_match.
Print Assumptions Kernel.UniversalSim.ustep_commit.
Print Assumptions Kernel.UniversalSim.ustep_certify.
Print Assumptions Kernel.UniversalSim.gnot_halted.
Print Assumptions Kernel.UniversalSim.U_step_with.
Print Assumptions Kernel.UniversalSim.U_step.
Print Assumptions Kernel.UniversalSim.rel_host_running.
(* === Kernel.UniversalThieleLinks : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalThieleLinks.host_cs_run.
Print Assumptions Kernel.UniversalThieleLinks.host_cs_cost.
Print Assumptions Kernel.UniversalThieleLinks.host_nfi.
(* === Kernel.EcosystemGame : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.EcosystemGame.toggle_game_positive.
Print Assumptions Kernel.EcosystemGame.toggle_game_consensus.
Print Assumptions Kernel.EcosystemGame.toggle_game_authentic.
Print Assumptions Kernel.EcosystemGame.toggle_game_coordinator_free.
Print Assumptions Kernel.EcosystemGame.toggle_game_revokes.
Print Assumptions Kernel.EcosystemGame.toggle_game_refutes_strong_pointer_necessity.
Print Assumptions Kernel.EcosystemGame.durable_consensus_implies_permanence.
(* === Kernel.ObservationPolicy : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ObservationPolicy.decoding_requires_fiber_constancy.
Print Assumptions Kernel.ObservationPolicy.selected_representatives_give_decoder.
Print Assumptions Kernel.ObservationPolicy.joint_floor_is_least.
Print Assumptions Kernel.ObservationPolicy.least_joint_floor_respects_all_events.
Print Assumptions Kernel.ObservationPolicy.independent_coordinates_joint_change_costs_one.
Print Assumptions Kernel.ObservationPolicy.calibrated_model_exists_iff_positive_cost.
Print Assumptions Kernel.ObservationPolicy.bit_erasure_classification.
Print Assumptions Kernel.ObservationPolicy.bit_model_has_satisfiable_calibration.
Print Assumptions Kernel.ObservationPolicy.retained_history_recovers_previous_state.
Print Assumptions Kernel.ObservationPolicy.retained_history_step_injective.
Print Assumptions Kernel.ObservationPolicy.history_simulates_observed_step.
Print Assumptions Kernel.ObservationPolicy.visible_reset_does_not_force_global_erasure.
(* === Kernel.PointerObservable : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PointerObservable.ReplicatedLedgerToy.toy_work_not_proliferating.
Print Assumptions Kernel.PointerObservable.ReplicatedLedgerToy.toy_cert_unique_pointer.
Print Assumptions Kernel.PointerObservable.pointer_on_unique.
Print Assumptions Kernel.PointerObservable.independent_copies_everywhere_are_constant.
Print Assumptions Kernel.PointerObservable.ReplicatedHeaderToy.synced_copy.
Print Assumptions Kernel.PointerObservable.ReplicatedHeaderToy.ledger_carriers_independent.
Print Assumptions Kernel.PointerObservable.ReplicatedHeaderToy.ledger_copying_alone_does_not_separate.
Print Assumptions Kernel.PointerObservable.ReplicatedHeaderToy.final_empty_synced.
Print Assumptions Kernel.PointerObservable.ReplicatedHeaderToy.ledger_finalized_is_pointer.
Print Assumptions Kernel.PointerObservable.ReplicatedHeaderToy.ledger_gas_not_relied_on.
(* === Kernel.PointerObservableCounterexamples : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PointerObservableCounterexamples.blind_observer_blocks_proliferation.
Print Assumptions Kernel.PointerObservableCounterexamples.DeniableAuthentication.deniable_model_observer_zero_records.
Print Assumptions Kernel.PointerObservableCounterexamples.DeniableAuthentication.deniable_authentication_model_not_proliferating.
Print Assumptions Kernel.PointerObservableCounterexamples.SymmetricMAC.mac_model_not_proliferating.
Print Assumptions Kernel.PointerObservableCounterexamples.ObjectCapability.capability_model_not_proliferating.
Print Assumptions Kernel.PointerObservableCounterexamples.PublicLog.public_log_model_proliferating.
Print Assumptions Kernel.PointerObservableCounterexamples.PublicLog.public_log_effort_not_proliferating.
Print Assumptions Kernel.PointerObservableCounterexamples.DigitalSignature.signature_model_proliferating.
Print Assumptions Kernel.PointerObservableCounterexamples.labeled_model_verdicts.
(* === Kernel.PointerObservableReductions : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PointerObservableReductions.mirror_rival_not_proliferating.
Print Assumptions Kernel.PointerObservableReductions.mirror_unique_pointer.
Print Assumptions Kernel.PointerObservableReductions.PoS_model_unique_pointer.
Print Assumptions Kernel.PointerObservableReductions.Gas_model_unique_pointer.
Print Assumptions Kernel.PointerObservableReductions.TEE_model_unique_pointer.
Print Assumptions Kernel.PointerObservableReductions.CT_model_unique_pointer.
Print Assumptions Kernel.PointerObservableReductions.PCC_model_unique_pointer.
Print Assumptions Kernel.PointerObservableReductions.five_labeled_models_have_selected_pointer.
(* === Kernel.RecordProliferationSurvey : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RecordProliferationSurvey.twelve_candidate_measurements_checked.
Print Assumptions Kernel.RecordProliferationSurvey.first_event_not_proliferating.
Print Assumptions Kernel.RecordProliferationSurvey.swapped_event_is_pointer_checked.
(* === Kernel.CommitmentPredicateAdequacy : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CommitmentPredicateAdequacy.cert_flip_is_least_covering_predicate.
Print Assumptions Kernel.CommitmentPredicateAdequacy.covers_cert_flips_sufficient_for_quantitative_floor.
Print Assumptions Kernel.CommitmentPredicateAdequacy.quantitative_floor_necessary_for_covers_cert_flips.
Print Assumptions Kernel.CommitmentPredicateAdequacy.quantitative_certification_floor_iff_covers_cert_flips.
Print Assumptions Kernel.CommitmentPredicateAdequacy.quantitative_floor_iff_a2_predicate_subsumed.
Print Assumptions Kernel.CommitmentPredicateAdequacy.certifying_trace_has_cert_flip.
Print Assumptions Kernel.CommitmentPredicateAdequacy.batch_certification_floor_iff_a2_predicate_subsumed.
Print Assumptions Kernel.CommitmentPredicateAdequacy.no_overcharge_forces_charge_only_on_cert_flips.
Print Assumptions Kernel.CommitmentPredicateAdequacy.exact_commitment_pricing_characterization.
Print Assumptions Kernel.CommitmentPredicateAdequacy.substitution_test_rejects_non_a2_exact_substitute.
Print Assumptions Kernel.CommitmentPredicateAdequacy.substitution_test_exact_substitute_is_a2.
Print Assumptions Kernel.CommitmentPredicateAdequacy.covers_cert_flips_sufficient_for_floor.
Print Assumptions Kernel.CommitmentPredicateAdequacy.floor_necessary_for_covers_cert_flips.
Print Assumptions Kernel.CommitmentPredicateAdequacy.local_predicate_certification_floor_iff_covers_cert_flips.
Print Assumptions Kernel.CommitmentPredicateAdequacy.universal_floor_forces_a2_predicate_subsumed.
Print Assumptions Kernel.CommitmentPredicateAdequacy.charged_branch_unreachable.
Print Assumptions Kernel.CommitmentPredicateAdequacy.uncharged_branch_unreachable.
Print Assumptions Kernel.CommitmentPredicateAdequacy.erasure_substitute_fails_commitment_floor.
Print Assumptions Kernel.CommitmentPredicateAdequacy.a2_predicate_has_commitment_floor.
Print Assumptions Kernel.CommitmentPredicateAdequacy.a2_predicate_has_quantitative_floor.
(* === Kernel.CommitmentVsErasure : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CommitmentVsErasure.erasure_branch_unreachable.
Print Assumptions Kernel.CommitmentVsErasure.trusted_erasure_system_certifies_without_erasure.
Print Assumptions Kernel.CommitmentVsErasure.trusted_a2_system_certification_cost_floor.
Print Assumptions Kernel.CommitmentVsErasure.commitment_cost_not_reducible_to_erasure_cost.
(* === Kernel.CostFrameworks : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CostFrameworks.run_graded_is_run.
Print Assumptions Kernel.CostFrameworks.a2_and_aara_iff_exact.
Print Assumptions Kernel.CostFrameworks.flips_le_cost.
(* === Kernel.CostSemanticsComparison : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CostSemanticsComparison.bind_ret_l.
Print Assumptions Kernel.CostSemanticsComparison.bind_ret_r.
Print Assumptions Kernel.CostSemanticsComparison.bind_assoc.
Print Assumptions Kernel.CostSemanticsComparison.run_writer_is_run_and_cost.
Print Assumptions Kernel.CostSemanticsComparison.a2_iff_nonnegative_amortized_cost.
Print Assumptions Kernel.CostSemanticsComparison.potential_telescoping.
Print Assumptions Kernel.CostSemanticsComparison.nfi_by_potential.
Print Assumptions Kernel.CostSemanticsComparison.certification_system_is_potential_method.
(* === Kernel.DecisionTreeBound : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.DecisionTreeBound.decision_tree_leaves_le_pow2_depth.
Print Assumptions Kernel.DecisionTreeBound.decision_tree_log2_leaf_bound.
Print Assumptions Kernel.DecisionTreeBound.decision_tree_leaf_count_positive.
Print Assumptions Kernel.DecisionTreeBound.decision_tree_log2_up_leaf_bound.
Print Assumptions Kernel.DecisionTreeBound.complete_tree_leaf_count.
Print Assumptions Kernel.DecisionTreeBound.complete_tree_depth.
(* === Kernel.FiniteCertMachine : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.FiniteCertMachine.filter_split_length.
Print Assumptions Kernel.FiniteCertMachine.fiber_bound_compression.
Print Assumptions Kernel.FiniteCertMachine.fin_finite.
Print Assumptions Kernel.FiniteCertMachine.fin_permanent.
Print Assumptions Kernel.FiniteCertMachine.next_slot_injective.
Print Assumptions Kernel.FiniteCertMachine.fnext_injective.
Print Assumptions Kernel.FiniteCertMachine.fcertify_merges.
Print Assumptions Kernel.FiniteCertMachine.fjump_merges.
Print Assumptions Kernel.FiniteCertMachine.fin_merging_priced.
Print Assumptions Kernel.FiniteCertMachine.fin_fiber_bound.
Print Assumptions Kernel.FiniteCertMachine.fin_compression_priced.
Print Assumptions Kernel.FiniteCertMachine.fin_a2_from_merging_price.
Print Assumptions Kernel.FiniteCertMachine.fin_a2_from_compression_price.
Print Assumptions Kernel.FiniteCertMachine.slot_of_nat_of_slot.
(* === Kernel.HonestCostTracking : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.HonestCostTracking.dishonest_free_certification.
Print Assumptions Kernel.HonestCostTracking.honest_cost_tracking_strict_restriction.
Print Assumptions Kernel.HonestCostTracking.free_forgery_violates_A2.
Print Assumptions Kernel.HonestCostTracking.dishonest_forge_system_violates_A2.
(* === Kernel.KnowledgeNarrowing : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.KnowledgeNarrowing.run_image_nodup.
Print Assumptions Kernel.KnowledgeNarrowing.run_image_spec.
Print Assumptions Kernel.KnowledgeNarrowing.run_image_step.
Print Assumptions Kernel.KnowledgeNarrowing.run_narrowing_priced.
Print Assumptions Kernel.KnowledgeNarrowing.run_narrowing_priced_log.
Print Assumptions Kernel.KnowledgeNarrowing.knowledge_contains_actual.
Print Assumptions Kernel.KnowledgeNarrowing.knowledge_sublist.
Print Assumptions Kernel.KnowledgeNarrowing.dstates_finite.
Print Assumptions Kernel.KnowledgeNarrowing.measure_forgets_nothing.
Print Assumptions Kernel.KnowledgeNarrowing.wipe_merges.
Print Assumptions Kernel.KnowledgeNarrowing.demon_fiber_bound.
Print Assumptions Kernel.KnowledgeNarrowing.demon_compression_priced.
Print Assumptions Kernel.KnowledgeNarrowing.wipe_costs_at_least_one.
Print Assumptions Kernel.KnowledgeNarrowing.demon_observer_learns.
Print Assumptions Kernel.KnowledgeNarrowing.demon_machine_spread_kept.
Print Assumptions Kernel.KnowledgeNarrowing.observer_narrowing_can_be_free.
(* === Kernel.KnowledgeNarrowingMinimal : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.KnowledgeNarrowingMinimal.demon_refutes_incremental.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.tri3_finite.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.tri3_step_injective.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.tri3_compression_priced.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.free_incremental_narrowing_with_three.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.states_along_length.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.map_constant.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.knowledge_constant_window.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.initial_knowledge_same_window.
Print Assumptions Kernel.KnowledgeNarrowingMinimal.no_free_incremental_narrowing_below_three.
(* === Kernel.PermanentCertification : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PermanentCertification.certified_states_spec.
Print Assumptions Kernel.PermanentCertification.certified_states_nodup.
Print Assumptions Kernel.PermanentCertification.permanent_image_incl.
Print Assumptions Kernel.PermanentCertification.permanent_flip_is_not_injective.
Print Assumptions Kernel.PermanentCertification.permanent_flips_collapse_at_least.
Print Assumptions Kernel.PermanentCertification.a2_from_merging_price_and_permanence.
Print Assumptions Kernel.PermanentCertification.permanent_certification_trace_floor.
Print Assumptions Kernel.PermanentCertification.honest_erasure_accounting_implies_a2.
Print Assumptions Kernel.PermanentCertification.commit_without_erasure_system_is_not_honest.
Print Assumptions Kernel.PermanentCertification.commit_without_erasure_system_finite_permanent.
Print Assumptions Kernel.PermanentCertification.unbounded_history_escapes.
Print Assumptions Kernel.PermanentCertification.revocable_certificate_escapes.
Print Assumptions Kernel.PermanentCertification.sheets_finite.
Print Assumptions Kernel.PermanentCertification.stamp_is_permanent.
Print Assumptions Kernel.PermanentCertification.priced_reset_satisfies_premises.
Print Assumptions Kernel.PermanentCertification.free_merge_escapes.
(* === Kernel.PermanentCertificationEntropy : 52 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_nil.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_cons.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_ext_in.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_le.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_nonneg.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_plus.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_minus.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_scal.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_zero.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_indicator.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_swap.
Print Assumptions Kernel.PermanentCertificationEntropy.ln2_pos.
Print Assumptions Kernel.PermanentCertificationEntropy.ln_le_minus_one.
Print Assumptions Kernel.PermanentCertificationEntropy.entropy_le_log_support.
Print Assumptions Kernel.PermanentCertificationEntropy.filter_in_b_length.
Print Assumptions Kernel.PermanentCertificationEntropy.uniform_on_distribution.
Print Assumptions Kernel.PermanentCertificationEntropy.uniform_on_entropy.
Print Assumptions Kernel.PermanentCertificationEntropy.filter_eq_length_one.
Print Assumptions Kernel.PermanentCertificationEntropy.push_distribution.
Print Assumptions Kernel.PermanentCertificationEntropy.push_support.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_permutation.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_map.
Print Assumptions Kernel.PermanentCertificationEntropy.push_injective_at.
Print Assumptions Kernel.PermanentCertificationEntropy.step_entropy_invariant_if_injective.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_select.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_nonneg_in.
Print Assumptions Kernel.PermanentCertificationEntropy.rsum_pos_witness.
Print Assumptions Kernel.PermanentCertificationEntropy.ln_le_mono.
Print Assumptions Kernel.PermanentCertificationEntropy.push_ge_point.
Print Assumptions Kernel.PermanentCertificationEntropy.push_ge_two.
Print Assumptions Kernel.PermanentCertificationEntropy.push_entropy_as_point_sum.
Print Assumptions Kernel.PermanentCertificationEntropy.entropy_drop_as_point_sum.
Print Assumptions Kernel.PermanentCertificationEntropy.entropy_drop_term_nonneg.
Print Assumptions Kernel.PermanentCertificationEntropy.entropy_drop_nonneg.
Print Assumptions Kernel.PermanentCertificationEntropy.entropy_drop_pos_of_support_merge.
Print Assumptions Kernel.PermanentCertificationEntropy.known_state_step_removes_no_entropy.
Print Assumptions Kernel.PermanentCertificationEntropy.not_nodup_map_witness.
Print Assumptions Kernel.PermanentCertificationEntropy.map_nodup_injective_on.
Print Assumptions Kernel.PermanentCertificationEntropy.merge_pair_removes_a_bit.
Print Assumptions Kernel.PermanentCertificationEntropy.certified_and_flips_nodup.
Print Assumptions Kernel.PermanentCertificationEntropy.certified_and_flips_land_certified.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_step_entropy_ceiling.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_step_entropy_drop.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_flip_uniform_entropy_drop.
Print Assumptions Kernel.PermanentCertificationEntropy.a2_from_entropy_price_and_permanence.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_flip_heat_floor.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_flip_heat_positive.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_flip_full_support_entropy_drop_positive.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_flip_full_support_heat_positive.
Print Assumptions Kernel.PermanentCertificationEntropy.known_state_flip_forces_no_heat.
Print Assumptions Kernel.PermanentCertificationEntropy.permanent_flip_spread_loses_a_bit.
Print Assumptions Kernel.PermanentCertificationEntropy.entropy_priced_trace_floor.
(* === Kernel.PermanentRecordPricing : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PermanentRecordPricing.nodup_app_disjoint.
Print Assumptions Kernel.PermanentRecordPricing.permanent_flips_compression_bound.
Print Assumptions Kernel.PermanentRecordPricing.flip_gives_certified_state.
Print Assumptions Kernel.PermanentRecordPricing.permanent_flips_log_bound.
Print Assumptions Kernel.PermanentRecordPricing.a2_from_compression_price_and_permanence.
Print Assumptions Kernel.PermanentRecordPricing.compression_priced_trace_floor.
Print Assumptions Kernel.PermanentRecordPricing.quads_finite.
Print Assumptions Kernel.PermanentRecordPricing.quad_stamp_permanent.
Print Assumptions Kernel.PermanentRecordPricing.quad_image_nonempty.
Print Assumptions Kernel.PermanentRecordPricing.quad_lists_short.
Print Assumptions Kernel.PermanentRecordPricing.quad_stamp_cost_two_is_priced.
Print Assumptions Kernel.PermanentRecordPricing.quad_stamp_needs_two.
Print Assumptions Kernel.PermanentRecordPricing.permanent_at_flip_is_not_injective.
Print Assumptions Kernel.PermanentRecordPricing.permanent_flip_merges_on_yes_side.
Print Assumptions Kernel.PermanentRecordPricing.flip_merges_or_revokes.
Print Assumptions Kernel.PermanentRecordPricing.injective_flip_revokes.
Print Assumptions Kernel.PermanentRecordPricing.forced_priced_iff_merges.
Print Assumptions Kernel.PermanentRecordPricing.permanent_record_write_is_forced_priced.
Print Assumptions Kernel.PermanentRecordPricing.forced_price_without_permanent_record.
(* === Kernel.PricingOnePremise : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PricingOnePremise.all_nodup.
Print Assumptions Kernel.PricingOnePremise.all_in.
Print Assumptions Kernel.PricingOnePremise.ln_INR_pos_le.
Print Assumptions Kernel.PricingOnePremise.log2_one.
Print Assumptions Kernel.PricingOnePremise.log2_pow2.
Print Assumptions Kernel.PricingOnePremise.log2_le_nat.
Print Assumptions Kernel.PricingOnePremise.prob_le_one.
Print Assumptions Kernel.PricingOnePremise.entropy_nonneg.
Print Assumptions Kernel.PricingOnePremise.entropy_drop_le_log_support_fibre.
Print Assumptions Kernel.PricingOnePremise.entropy_drop_le_log_fibre.
Print Assumptions Kernel.PricingOnePremise.step_no_pileup_entropy_invariant.
Print Assumptions Kernel.PricingOnePremise.entropy_drop_of_fibre.
Print Assumptions Kernel.PricingOnePremise.worst_case_entropy_drop.
Print Assumptions Kernel.PricingOnePremise.compression_iff_fibre.
Print Assumptions Kernel.PricingOnePremise.entropy_priced_iff_compression_priced.
Print Assumptions Kernel.PricingOnePremise.image_size_one.
Print Assumptions Kernel.PricingOnePremise.image_size_two.
Print Assumptions Kernel.PricingOnePremise.merging_priced_iff_pair_halving.
Print Assumptions Kernel.PricingOnePremise.merging_priced_iff_pair_entropy.
Print Assumptions Kernel.PricingOnePremise.one_premise_three_forms.
(* === Kernel.PricingPhysicsAudit : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PricingPhysicsAudit.no_forced_price_beyond_merges.
Print Assumptions Kernel.PricingPhysicsAudit.permanent_write_has_logical_payment.
Print Assumptions Kernel.PricingPhysicsAudit.mu_has_no_intrinsic_joule_value.
Print Assumptions Kernel.PricingPhysicsAudit.calibrated_mu_landauer_energy.
Print Assumptions Kernel.PricingPhysicsAudit.semantics_entropy_permutation_invariant.
Print Assumptions Kernel.PricingPhysicsAudit.permanence_heat_floor_uses_landauer.
(* === Kernel.QuantitativeNoFI : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.QuantitativeNoFI.qcs_telescoping.
Print Assumptions Kernel.QuantitativeNoFI.universal_nfi_quantitative.
Print Assumptions Kernel.QuantitativeNoFI.universal_nfi_quantitative_witness.
(* === Kernel.ShadowPricing : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ShadowPricing.shadow_floor_overcharges.
Print Assumptions Kernel.ShadowPricing.shadow_cannot_price_exactly.
Print Assumptions Kernel.ShadowPricing.step_price_is_exact.
Print Assumptions Kernel.ShadowPricing.window_showing_reading_prices_exactly.
Print Assumptions Kernel.ShadowPricing.window_showing_reading_has_no_collision.
(* === Kernel.StructuralUndecidability : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.StructuralUndecidability.structural_shortcut_undecidable.
Print Assumptions Kernel.StructuralUndecidability.admits_shortcut_not_decidable.
(* === Kernel.UniversalCertificationCost : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.UniversalCertificationCost.universal_nfi_any_substrate.
Print Assumptions Kernel.UniversalCertificationCost.every_toll_system_pays_the_floor.
Print Assumptions Kernel.UniversalCertificationCost.cert_trace_nonempty.
Print Assumptions Kernel.UniversalCertificationCost.cs_run_app.
Print Assumptions Kernel.UniversalCertificationCost.cs_total_cost_app.
Print Assumptions Kernel.UniversalCertificationCost.scs_run_embed.
Print Assumptions Kernel.UniversalCertificationCost.host_represents_simulating_cert_system.
(* === Kernel.ArcsineBoundary : 32 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ArcsineBoundary.am_cos_le.
Print Assumptions Kernel.ArcsineBoundary.am_acos_le.
Print Assumptions Kernel.ArcsineBoundary.am_cos_PI_minus.
Print Assumptions Kernel.ArcsineBoundary.am_acos_opp.
Print Assumptions Kernel.ArcsineBoundary.am_cos_abs.
Print Assumptions Kernel.ArcsineBoundary.am_sq_sin.
Print Assumptions Kernel.ArcsineBoundary.am_triangle_det.
Print Assumptions Kernel.ArcsineBoundary.am_inner_sym.
Print Assumptions Kernel.ArcsineBoundary.am_comb4.
Print Assumptions Kernel.ArcsineBoundary.am_inner_bound.
Print Assumptions Kernel.ArcsineBoundary.am_sphere_triangle.
Print Assumptions Kernel.ArcsineBoundary.am_path3.
Print Assumptions Kernel.ArcsineBoundary.am_neg_unit.
Print Assumptions Kernel.ArcsineBoundary.am_dist_neg_l.
Print Assumptions Kernel.ArcsineBoundary.am_dist_sym.
Print Assumptions Kernel.ArcsineBoundary.am_vectors.
Print Assumptions Kernel.ArcsineBoundary.am_necessary.
Print Assumptions Kernel.ArcsineBoundary.am_S_nonneg.
Print Assumptions Kernel.ArcsineBoundary.am_SC.
Print Assumptions Kernel.ArcsineBoundary.am_inner4.
Print Assumptions Kernel.ArcsineBoundary.am_b0_unit.
Print Assumptions Kernel.ArcsineBoundary.am_b1_unit.
Print Assumptions Kernel.ArcsineBoundary.am_a_ok.
Print Assumptions Kernel.ArcsineBoundary.am_dot_lift.
Print Assumptions Kernel.ArcsineBoundary.am_rabs_le.
Print Assumptions Kernel.ArcsineBoundary.am_sufficient.
Print Assumptions Kernel.ArcsineBoundary.am_cycle_arcsine.
Print Assumptions Kernel.ArcsineBoundary.am_arcsine.
Print Assumptions Kernel.ArcsineBoundary.am_quantum_arcsine.
Print Assumptions Kernel.ArcsineBoundary.am_345.
Print Assumptions Kernel.ArcsineBoundary.am_pythagorean_boundary.
Print Assumptions Kernel.ArcsineBoundary.am_tsirelson_boundary.
(* === Kernel.BoxCHSH : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.BoxCHSH.E_expand.
Print Assumptions Kernel.BoxCHSH.normalized_E_bound.
Print Assumptions Kernel.BoxCHSH.Qabs_triangle_4.
Print Assumptions Kernel.BoxCHSH.valid_box_S_le_4.
Print Assumptions Kernel.BoxCHSH.local_S_2_deterministic.
Print Assumptions Kernel.BoxCHSH.S_box_correlators.
Print Assumptions Kernel.BoxCHSH.box_chsh_bound_algebraic.
Print Assumptions Kernel.BoxCHSH.box_chsh_bound_algebraic_weak.
(* === Kernel.CHSHColumnCheck : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CHSHColumnCheck.psd2_quadratic_form_nonneg.
Print Assumptions Kernel.CHSHColumnCheck.zero_marginal_npa_column_contractive_implies_psd.
Print Assumptions Kernel.CHSHColumnCheck.npa_quad5_test_col0.
Print Assumptions Kernel.CHSHColumnCheck.npa_quad5_test_col1.
Print Assumptions Kernel.CHSHColumnCheck.npa_quad5_test_schur.
Print Assumptions Kernel.CHSHColumnCheck.npa_psd_implies_column_contractive.
Print Assumptions Kernel.CHSHColumnCheck.npa_psd_iff_column_contractive.
Print Assumptions Kernel.CHSHColumnCheck.column_contractive_iff_npa_psd.
Print Assumptions Kernel.CHSHColumnCheck.column_contractive_check_witness_sound.
Print Assumptions Kernel.CHSHColumnCheck.column_contractive_check_witness_npa_psd.
Print Assumptions Kernel.CHSHColumnCheck.npa_psd_zero_marginal_implies_row_bounds.
Print Assumptions Kernel.CHSHColumnCheck.semantics_invariant_chsh_party_swap.
Print Assumptions Kernel.CHSHColumnCheck.npa_psd_implies_tsirelson_bound.
Print Assumptions Kernel.CHSHColumnCheck.npa_psd_implies_tsirelson_bound_abs.
(* === Kernel.CHSHCouplingBridge : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_same_00.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_diff_00.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_same_01.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_diff_01.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_same_10.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_diff_10.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_same_11.
Print Assumptions Kernel.CHSHCouplingBridge.not_in_coupling_diff_11.
Print Assumptions Kernel.CHSHCouplingBridge.chsh_coupling_snd_bound.
Print Assumptions Kernel.CHSHCouplingBridge.chsh_coupling_fst_bound.
Print Assumptions Kernel.CHSHCouplingBridge.locally_consistent_gives_separable_coupling.
Print Assumptions Kernel.CHSHCouplingBridge.locally_consistent_classical_bound.
Print Assumptions Kernel.CHSHCouplingBridge.chsh_violation_rules_out_locally_factorizable_coupling.
Print Assumptions Kernel.CHSHCouplingBridge.chsh_violation_rules_out_locally_consistent_separable.
(* === Kernel.CHSHStatisticalBridge : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CHSHStatisticalBridge.Z_of_nat_pos.
Print Assumptions Kernel.CHSHStatisticalBridge.correlator_abs_le_1.
Print Assumptions Kernel.CHSHStatisticalBridge.chsh_stat_algebraic_bound.
Print Assumptions Kernel.CHSHStatisticalBridge.violation_wc_stat_eq_4.
Print Assumptions Kernel.CHSHStatisticalBridge.violation_wc_exceeds_bell.
Print Assumptions Kernel.CHSHStatisticalBridge.violation_wc_within_algebraic.
Print Assumptions Kernel.CHSHStatisticalBridge.correlator_pos_only.
Print Assumptions Kernel.CHSHStatisticalBridge.correlator_neg_only.
Print Assumptions Kernel.CHSHStatisticalBridge.bit_cases.
Print Assumptions Kernel.CHSHStatisticalBridge.local_bound_for_wc.
Print Assumptions Kernel.CHSHStatisticalBridge.chsh_stat_violation_not_local.
Print Assumptions Kernel.CHSHStatisticalBridge.violation_wc_not_local.
Print Assumptions Kernel.CHSHStatisticalBridge.violation_wc_total.
(* === Kernel.ConstructivePSD : 23 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ConstructivePSD.sum_fin5_unfold.
Print Assumptions Kernel.ConstructivePSD.quad5_unfold.
Print Assumptions Kernel.ConstructivePSD.Rabs_le_inv.
Print Assumptions Kernel.ConstructivePSD.Rabs_sq_le.
Print Assumptions Kernel.ConstructivePSD.sum_fin5_linear.
Print Assumptions Kernel.ConstructivePSD.sum_fin5_scal.
Print Assumptions Kernel.ConstructivePSD.bilinear5_sym.
Print Assumptions Kernel.ConstructivePSD.quad5_expansion_bilinear.
Print Assumptions Kernel.ConstructivePSD.sum_e_basis.
Print Assumptions Kernel.ConstructivePSD.sum_e_basis_r.
Print Assumptions Kernel.ConstructivePSD.quad5_e_basis.
Print Assumptions Kernel.ConstructivePSD.bilinear5_e_basis.
Print Assumptions Kernel.ConstructivePSD.quad5_scal.
Print Assumptions Kernel.ConstructivePSD.bilinear5_scal_r.
Print Assumptions Kernel.ConstructivePSD.bilinear5_linear_r.
Print Assumptions Kernel.ConstructivePSD.bilinear5_linear_l.
Print Assumptions Kernel.ConstructivePSD.bilinear5_scal_l.
Print Assumptions Kernel.ConstructivePSD.quad5_e_combo_3.
Print Assumptions Kernel.ConstructivePSD.quadratic_nonneg_discriminant.
Print Assumptions Kernel.ConstructivePSD.PSD5_off_diagonal_bound.
Print Assumptions Kernel.ConstructivePSD.PSD_perfect_corr_implies_equal_rows.
Print Assumptions Kernel.ConstructivePSD.psd_3x3_determinant_nonneg.
Print Assumptions Kernel.ConstructivePSD.PSD5_convex.
(* === Kernel.ElliptopeCompletion : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ElliptopeCompletion.completed_quad_expand.
Print Assumptions Kernel.ElliptopeCompletion.completed_matrix_symmetric.
Print Assumptions Kernel.ElliptopeCompletion.zero_marginal_implies_elliptope.
Print Assumptions Kernel.ElliptopeCompletion.psd_cauchy_schwarz.
Print Assumptions Kernel.ElliptopeCompletion.elliptope_tsirelson.
Print Assumptions Kernel.ElliptopeCompletion.pr_box_not_elliptope.
Print Assumptions Kernel.ElliptopeCompletion.deterministic_strategy_elliptope.
Print Assumptions Kernel.ElliptopeCompletion.classical_tightness_witness_elliptope.
Print Assumptions Kernel.ElliptopeCompletion.turing_point_elliptope.
Print Assumptions Kernel.ElliptopeCompletion.convex_ge0.
Print Assumptions Kernel.ElliptopeCompletion.elliptope_convex.
Print Assumptions Kernel.ElliptopeCompletion.beyond_classical_elliptope.
Print Assumptions Kernel.ElliptopeCompletion.sumf_nonneg.
Print Assumptions Kernel.ElliptopeCompletion.sumf_ext.
Print Assumptions Kernel.ElliptopeCompletion.sumf_scale.
Print Assumptions Kernel.ElliptopeCompletion.sumf_zero_all.
Print Assumptions Kernel.ElliptopeCompletion.elliptope_zero.
Print Assumptions Kernel.ElliptopeCompletion.elliptope_finite_mixture.
Print Assumptions Kernel.ElliptopeCompletion.lhv_mixture_elliptope.
(* === Kernel.ElliptopeGate : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ElliptopeGate.bden_pos.
Print Assumptions Kernel.ElliptopeGate.bden_IZR_pos.
Print Assumptions Kernel.ElliptopeGate.bden_IZR_neq0.
Print Assumptions Kernel.ElliptopeGate.bval_state_bucket_correlation.
Print Assumptions Kernel.ElliptopeGate.elliptope_pd_check_sound.
Print Assumptions Kernel.ElliptopeGate.state_bucket_correlation_1_0.
Print Assumptions Kernel.ElliptopeGate.state_bucket_correlation_0_1.
Print Assumptions Kernel.ElliptopeGate.mul2_neq0.
Print Assumptions Kernel.ElliptopeGate.mul3_neq0.
Print Assumptions Kernel.ElliptopeGate.div_eq_intro.
Print Assumptions Kernel.ElliptopeGate.one_eq_div.
Print Assumptions Kernel.ElliptopeGate.elliptope_ldl_check_sound.
Print Assumptions Kernel.ElliptopeGate.elliptope_check_full_sound.
Print Assumptions Kernel.ElliptopeGate.elliptope_full_gate_never_accepts_pr_box.
(* === Kernel.GenRealizability : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.GenRealizability.quad_n4_eq_quad5_ext.
Print Assumptions Kernel.GenRealizability.quad_n4_eq_quad5_restr.
Print Assumptions Kernel.GenRealizability.psd_n_unfold_5.
Print Assumptions Kernel.GenRealizability.symmetric_n_unfold_5.
Print Assumptions Kernel.GenRealizability.chsh_claim_is_zero_marginal_npa.
Print Assumptions Kernel.GenRealizability.column_contractive_iff_general_realizable.
Print Assumptions Kernel.GenRealizability.quad_n8_eq_quad9_ext.
Print Assumptions Kernel.GenRealizability.quad_n8_eq_quad9_restr.
Print Assumptions Kernel.GenRealizability.psd_n_unfold_9.
Print Assumptions Kernel.GenRealizability.q1ab_depends_only_on_index.
Print Assumptions Kernel.GenRealizability.fin9_index_roundtrip.
Print Assumptions Kernel.GenRealizability.q1ab_nat_to_fin9_eq.
Print Assumptions Kernel.GenRealizability.symmetric_n_unfold_9.
Print Assumptions Kernel.GenRealizability.q1ab_claim_is_npa_psd_q1ab.
Print Assumptions Kernel.GenRealizability.column_contractive_q1ab_iff_general_realizable.
Print Assumptions Kernel.GenRealizability.sum_n_affine.
Print Assumptions Kernel.GenRealizability.quad_n_convex_combo.
Print Assumptions Kernel.GenRealizability.psd_n_convex.
Print Assumptions Kernel.GenRealizability.deterministic_chsh_not_convex.
Print Assumptions Kernel.GenRealizability.genrealizable_captures_moment_presentable.
(* === Kernel.MinorConstraints : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.MinorConstraints.sum_n_le.
Print Assumptions Kernel.MinorConstraints.sum_n_scale.
Print Assumptions Kernel.MinorConstraints.sum_n_plus.
Print Assumptions Kernel.MinorConstraints.sum_n_minus.
Print Assumptions Kernel.MinorConstraints.sum_n_nonneg.
Print Assumptions Kernel.MinorConstraints.sum_n_cauchy_schwarz.
Print Assumptions Kernel.MinorConstraints.factorizable_cauchy_schwarz.
Print Assumptions Kernel.MinorConstraints.factorizable_satisfies_minors.
Print Assumptions Kernel.MinorConstraints.deterministic_strategy_chsh_bounded.
Print Assumptions Kernel.MinorConstraints.fine_theorem.
Print Assumptions Kernel.MinorConstraints.factorizable_CHSH_classical_bound.
Print Assumptions Kernel.MinorConstraints.local_box_CHSH_bound.
Print Assumptions Kernel.MinorConstraints.fine_theorem_holds.
(* === Kernel.NPAMomentMatrix : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NPAMomentMatrix.npa_diagonal_one.
Print Assumptions Kernel.NPAMomentMatrix.npa_E00_position.
Print Assumptions Kernel.NPAMomentMatrix.npa_E01_position.
Print Assumptions Kernel.NPAMomentMatrix.npa_E10_position.
Print Assumptions Kernel.NPAMomentMatrix.npa_E11_position.
Print Assumptions Kernel.NPAMomentMatrix.npa_rho_BB_position.
Print Assumptions Kernel.NPAMomentMatrix.npa_rho_AA_position.
Print Assumptions Kernel.NPAMomentMatrix.npa_psd_implies_normalized.
Print Assumptions Kernel.NPAMomentMatrix.npa_to_matrix_symmetric.
(* === Kernel.QuantumPartitionPSD_1AB : 134 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.QuantumPartitionPSD_1AB.fin9_destruct.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_moment_matrix_symmetric.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_to_matrix_symmetric.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.quad9_q1ab_sos_decomposition.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.vec9_destructure.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.column_contractive_q1ab_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.psd9_implies_column_contractive_q1ab.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_psd_iff_column_contractive.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.column_contractive_q1ab_iff_npa_psd.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_residual_g_zero_decomp.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_top_block_nonneg.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_bottom_block_nonneg.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.column_contractive_check_q1ab_sound_at_g_zero.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_check_at_gzero_forces_unit_ball.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_check_at_gzero_implies_classical_bound.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_caller_supplied_gamma_real_check_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_residual_g5_only_decomp.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.weighted_4d_CS_SOS_identity.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.weighted_4d_CS_nonneg.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_caller_witness_at_zero.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_bottom_block_g5_nonneg.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_caller_check_implies_column_contractive.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_caller_check_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_witness_strict_extension_exists.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.state_bucket_correlation_to_IZR.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_caller_witness_z_abs_sound.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_caller_witness_z_sound.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g5_full_integer_check_sound.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_residual_g345_decomp.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.augmented_2x2_qf_nonneg.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_caller_check_implies_column_contractive.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_caller_check_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_witness_g3g4_zero.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_LDLT_identity.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_qf_nonneg_from_pd.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q345_sym4_qf_equals_diff.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_minors_witness_implies_caller_witness.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_minors_witness_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.IZR_pos_neq_0.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_A_num_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_C_M_num_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_B_num_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_det_M_num_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H11_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H22_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H33_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H44_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H12_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H13_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H14_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H23_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H24_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_H34_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d1_Z_IZR.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d2_Z_IZR.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d3_Z_IZR.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d4_Z_IZR.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d2_scale.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d3_scale.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym4_d4_scale.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_d1_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_d2_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_d3_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_d4_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.COMMON_Z_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.COMMON_Z_pos_R.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_caller_witness_z_abs_sound.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g345_caller_witness_z_abs_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym5_Schur_identity.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym5_qf_nonneg_from_pd.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym6_Schur_identity.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.sym6_qf_nonneg_from_pd.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q12345_sym6_qf_equals_residual.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g12345_minors_witness_implies_column_contractive.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g12345_minors_witness_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q12345_witness_at_g12_zero_reduces_to_g345.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.g12345_COMMON_Z_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.g12345_COMMON_Z_pos_R.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H11_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H22_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H33_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H44_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H55_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H66_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H12_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H13_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H14_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H15_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H16_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H23_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H24_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H25_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H26_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H34_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H35_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H36_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H45_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H46_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_H56_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.schur_step_Z_IZR.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_22_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_23_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_24_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_25_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_26_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_33_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_34_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_35_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_36_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_44_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_45_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_46_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_55_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_56_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S6_66_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_22_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_23_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_24_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_25_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_33_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_34_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_35_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_44_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_45_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.cleared_g12345_S5_55_Z_bridge.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.KZ_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.KZ2_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.KZ4_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.KZ8_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.KZ12_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.KZ16_pos.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g12345_caller_witness_z_abs_sound.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_g12345_caller_witness_z_abs_implies_psd9.
Print Assumptions Kernel.QuantumPartitionPSD_1AB.q1ab_tie_is_a_constraint.
(* === Kernel.QuantumStrategies : 22 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.QuantumStrategies.qs_corr_dot.
Print Assumptions Kernel.QuantumStrategies.qs_uvec_unit.
Print Assumptions Kernel.QuantumStrategies.qs_vvec_unit.
Print Assumptions Kernel.QuantumStrategies.qs_dot_plus_r.
Print Assumptions Kernel.QuantumStrategies.qs_dot_minus_r.
Print Assumptions Kernel.QuantumStrategies.qs_dot_flat.
Print Assumptions Kernel.QuantumStrategies.qs_dot_cs.
Print Assumptions Kernel.QuantumStrategies.qs_dot_nonneg.
Print Assumptions Kernel.QuantumStrategies.qs_dot_sum_diff.
Print Assumptions Kernel.QuantumStrategies.qs_tsirelson.
Print Assumptions Kernel.QuantumStrategies.qs_bits_nodup.
Print Assumptions Kernel.QuantumStrategies.qs_r_sq.
Print Assumptions Kernel.QuantumStrategies.qs_bell_valid.
Print Assumptions Kernel.QuantumStrategies.qs_tsirelson_reached.
Print Assumptions Kernel.QuantumStrategies.qs_deterministic_plan.
Print Assumptions Kernel.QuantumStrategies.qs_dot_sym.
Print Assumptions Kernel.QuantumStrategies.qs_npa_correlators.
Print Assumptions Kernel.QuantumStrategies.qs_vec_unit.
Print Assumptions Kernel.QuantumStrategies.qs_npa_entries.
Print Assumptions Kernel.QuantumStrategies.qs_sum_fin5.
Print Assumptions Kernel.QuantumStrategies.qs_dot_combination.
Print Assumptions Kernel.QuantumStrategies.qs_npa_psd.
(* === Kernel.QuantumStrategiesComplex : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.QuantumStrategiesComplex.qc_four_vectors.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_gram_entries.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_gram_psd.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_corr_dot.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_uvec_unit.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_vvec_unit.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_dot_lift.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_tsirelson.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_npa_correlators.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_npa_psd.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_corr_real.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_obsI_real.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_obsJ_real.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_of_real_valid.
Print Assumptions Kernel.QuantumStrategiesComplex.qc_tsirelson_reached.
(* === Kernel.SchurComplement : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SchurComplement.sc_P_z.
Print Assumptions Kernel.SchurComplement.sc_cross_sym.
Print Assumptions Kernel.SchurComplement.sc_mvU_plus.
Print Assumptions Kernel.SchurComplement.sc_zQ.
Print Assumptions Kernel.SchurComplement.schur_identity.
Print Assumptions Kernel.SchurComplement.schur_complement_psd.
(* === Kernel.SmallChshCheck : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmallChshCheck.small_chsh_psd2_form_nonneg.
Print Assumptions Kernel.SmallChshCheck.small_chsh_contractive_implies_psd5.
Print Assumptions Kernel.SmallChshCheck.small_chsh_quad_col0.
Print Assumptions Kernel.SmallChshCheck.small_chsh_quad_col1.
Print Assumptions Kernel.SmallChshCheck.small_chsh_quad_schur.
Print Assumptions Kernel.SmallChshCheck.small_chsh_psd5_implies_contractive.
Print Assumptions Kernel.SmallChshCheck.small_chsh_psd_iff_contractive.
Print Assumptions Kernel.SmallChshCheck.small_chsh_scale_nonneg.
Print Assumptions Kernel.SmallChshCheck.small_chsh_Z_nonneg_iff.
Print Assumptions Kernel.SmallChshCheck.small_chsh_clear_denominators.
Print Assumptions Kernel.SmallChshCheck.small_chsh_n_pos_iff.
Print Assumptions Kernel.SmallChshCheck.small_chsh_corr_eq.
Print Assumptions Kernel.SmallChshCheck.small_chsh_check_unfold.
Print Assumptions Kernel.SmallChshCheck.small_chsh_check_iff.
Print Assumptions Kernel.SmallChshCheck.small_chsh_psd_row_bounds.
Print Assumptions Kernel.SmallChshCheck.small_chsh_psd_tsirelson.
Print Assumptions Kernel.SmallChshCheck.small_chsh_meaning_tsirelson.
Print Assumptions Kernel.SmallChshCheck.small_chsh_check_tsirelson.
(* === Kernel.SmallChshMachine : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.SmallChshMachine.small_chsh_prop_eqb_eq.
Print Assumptions Kernel.SmallChshMachine.small_chsh_tally_of_code.
Print Assumptions Kernel.SmallChshMachine.small_chsh_eval_iff.
Print Assumptions Kernel.SmallChshMachine.small_chsh_untouched_vals.
Print Assumptions Kernel.SmallChshMachine.small_chsh_flag_implies_tsirelson.
Print Assumptions Kernel.SmallChshMachine.small_chsh_program_flag_implies_tsirelson.
Print Assumptions Kernel.SmallChshMachine.small_chsh_chain_certifies_iff.
Print Assumptions Kernel.SmallChshMachine.small_chsh_tally_certifies_iff.
Print Assumptions Kernel.SmallChshMachine.small_chsh_tally_certifies.
Print Assumptions Kernel.SmallChshMachine.small_chsh_tally_refused_forever.
Print Assumptions Kernel.SmallChshMachine.small_chsh_score_12_5.
Print Assumptions Kernel.SmallChshMachine.small_chsh_score_14_5.
Print Assumptions Kernel.SmallChshMachine.small_chsh_score_16_5.
Print Assumptions Kernel.SmallChshMachine.small_chsh_score_pr_box.
Print Assumptions Kernel.SmallChshMachine.small_chsh_score_all_ones.
Print Assumptions Kernel.SmallChshMachine.small_chsh_demo_12_5_certifies.
Print Assumptions Kernel.SmallChshMachine.small_chsh_demo_14_5_certifies.
Print Assumptions Kernel.SmallChshMachine.small_chsh_demo_16_5_refused_forever.
Print Assumptions Kernel.SmallChshMachine.small_chsh_demo_pr_box_refused_forever.
Print Assumptions Kernel.SmallChshMachine.small_chsh_demo_all_ones_refused_forever.
(* === Kernel.TsirelsonAlgebraic : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TsirelsonAlgebraic.ta_Z_sa.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_quad_expand.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_quad_nonneg.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_tsirelson.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_realizable.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_arcsine.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_npa_quad.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_W_nonneg.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_npa_psd.
Print Assumptions Kernel.TsirelsonAlgebraic.ta_classical_instance.
(* === Kernel.TsirelsonFromAlgebra : 11 addressable theorems (unaddressable: 0) === *)
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
(* === Kernel.TsirelsonGeneral : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TsirelsonGeneral.sq_nonneg.
Print Assumptions Kernel.TsirelsonGeneral.cauchy_schwarz_chsh.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_from_row_bounds.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_bound_squared.
Print Assumptions Kernel.TsirelsonGeneral.semantics_invariant_party_swap.
Print Assumptions Kernel.TsirelsonGeneral.tsirelson_from_column_bounds.
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
(* === Kernel.TsirelsonRepresentation : 37 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TsirelsonRepresentation.tr_sum_S.
Print Assumptions Kernel.TsirelsonRepresentation.tr_in_idx.
Print Assumptions Kernel.TsirelsonRepresentation.tr_qf_S.
Print Assumptions Kernel.TsirelsonRepresentation.tr_sym_shift.
Print Assumptions Kernel.TsirelsonRepresentation.tr_qf_zero.
Print Assumptions Kernel.TsirelsonRepresentation.tr_pivot_nonneg.
Print Assumptions Kernel.TsirelsonRepresentation.tr_restrict.
Print Assumptions Kernel.TsirelsonRepresentation.tr_sum_e.
Print Assumptions Kernel.TsirelsonRepresentation.tr_qf_e.
Print Assumptions Kernel.TsirelsonRepresentation.tr_zero_pivot_row.
Print Assumptions Kernel.TsirelsonRepresentation.tr_schur_psd.
Print Assumptions Kernel.TsirelsonRepresentation.tr_gram.
Print Assumptions Kernel.TsirelsonRepresentation.tr_sumL_IZR.
Print Assumptions Kernel.TsirelsonRepresentation.tr_checks.
Print Assumptions Kernel.TsirelsonRepresentation.tr_forallb_idx.
Print Assumptions Kernel.TsirelsonRepresentation.tr_gammaZ_sym.
Print Assumptions Kernel.TsirelsonRepresentation.tr_gamma_sym.
Print Assumptions Kernel.TsirelsonRepresentation.tr_gamma_clifford.
Print Assumptions Kernel.TsirelsonRepresentation.tr_gamma_trace.
Print Assumptions Kernel.TsirelsonRepresentation.tr_r_sq.
Print Assumptions Kernel.TsirelsonRepresentation.tr_e_refl.
Print Assumptions Kernel.TsirelsonRepresentation.tr_obs_square.
Print Assumptions Kernel.TsirelsonRepresentation.tr_obs_valid.
Print Assumptions Kernel.TsirelsonRepresentation.tr_obs_validJ.
Print Assumptions Kernel.TsirelsonRepresentation.tr_psi_unit.
Print Assumptions Kernel.TsirelsonRepresentation.tr_dR_e.
Print Assumptions Kernel.TsirelsonRepresentation.tr_obs_pair.
Print Assumptions Kernel.TsirelsonRepresentation.tr_corr_inner.
Print Assumptions Kernel.TsirelsonRepresentation.tr_strategy_valid.
Print Assumptions Kernel.TsirelsonRepresentation.tr_G_sym.
Print Assumptions Kernel.TsirelsonRepresentation.tr_G_psd.
Print Assumptions Kernel.TsirelsonRepresentation.tr_elliptope_quantum.
Print Assumptions Kernel.TsirelsonRepresentation.tr_vectors_elliptope.
Print Assumptions Kernel.TsirelsonRepresentation.tr_quantum_elliptope.
Print Assumptions Kernel.TsirelsonRepresentation.tr_complex_elliptope.
Print Assumptions Kernel.TsirelsonRepresentation.tr_representation.
Print Assumptions Kernel.TsirelsonRepresentation.tr_representation_complex.
(* === Kernel.ValidCorrelation : 1 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ValidCorrelation.bell_math_deterministic.
(* === Kernel.CasperFFG : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CasperFFG.hash_ancestor_base.
Print Assumptions Kernel.CasperFFG.hash_ancestor_concat.
Print Assumptions Kernel.CasperFFG.hash_ancestor_other.
Print Assumptions Kernel.CasperFFG.nth_ancestor_ancestor.
Print Assumptions Kernel.CasperFFG.justified_means_ancestor.
Print Assumptions Kernel.CasperFFG.link_epochs.
Print Assumptions Kernel.CasperFFG.both_votes.
Print Assumptions Kernel.CasperFFG.dbl_vote_case.
Print Assumptions Kernel.CasperFFG.surround_case.
Print Assumptions Kernel.CasperFFG.crossing_link_slashes.
Print Assumptions Kernel.CasperFFG.same_epoch_distinct_slashes.
Print Assumptions Kernel.CasperFFG.distinct_justified_same_epoch_slashes.
Print Assumptions Kernel.CasperFFG.distinct_justified_epochs.
Print Assumptions Kernel.CasperFFG.finalized_epoch_distinct.
Print Assumptions Kernel.CasperFFG.non_equal_case_ind.
Print Assumptions Kernel.CasperFFG.non_equal_case.
Print Assumptions Kernel.CasperFFG.equal_case.
Print Assumptions Kernel.CasperFFG.safety'.
Print Assumptions Kernel.CasperFFG.accountable_safety.
(* === Kernel.CasperForkWitness : 20 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CasperForkWitness.all_validators_complete.
Print Assumptions Kernel.CasperForkWitness.weight_length.
Print Assumptions Kernel.CasperForkWitness.nodup_app_disjoint.
Print Assumptions Kernel.CasperForkWitness.two_thirds_lists_meet.
Print Assumptions Kernel.CasperForkWitness.fork_quorums_intersection.
Print Assumptions Kernel.CasperForkWitness.fork_at_most_one_parent.
Print Assumptions Kernel.CasperForkWitness.ancestors_parent_closed.
Print Assumptions Kernel.CasperForkWitness.hash_ancestor_in.
Print Assumptions Kernel.CasperForkWitness.q_branch_a_quorum.
Print Assumptions Kernel.CasperForkWitness.q_branch_b_quorum.
Print Assumptions Kernel.CasperForkWitness.one_step.
Print Assumptions Kernel.CasperForkWitness.finalized_a.
Print Assumptions Kernel.CasperForkWitness.finalized_b.
Print Assumptions Kernel.CasperForkWitness.b1_not_ancestor_a1.
Print Assumptions Kernel.CasperForkWitness.a1_not_ancestor_b1.
Print Assumptions Kernel.CasperForkWitness.casper_fork_exists.
Print Assumptions Kernel.CasperForkWitness.vote_va.
Print Assumptions Kernel.CasperForkWitness.vote_vc.
Print Assumptions Kernel.CasperForkWitness.two_link_voter_not_slashed.
Print Assumptions Kernel.CasperForkWitness.casper_fork_slashable.
(* === Kernel.CasperRecordReading : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CasperRecordReading.conflicting_records_are_priced.
Print Assumptions Kernel.CasperRecordReading.finalization_without_slashing.
(* === Kernel.ConcreteRAM : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ConcreteRAM.concrete_ram_write_reads_back.
Print Assumptions Kernel.ConcreteRAM.concrete_tied_ram_records_overwrite.
Print Assumptions Kernel.ConcreteRAM.concrete_untied_ram_record_unchanged.
Print Assumptions Kernel.ConcreteRAM.concrete_tied_and_untied_same_base.
(* === Kernel.ConcreteRecordMachines : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.ConcreteRecordMachines.ram_tied_overwrite_records_old_value.
Print Assumptions Kernel.ConcreteRecordMachines.ram_untied_overwrite_has_no_record.
Print Assumptions Kernel.ConcreteRecordMachines.janus_like_unbounded_inverse.
Print Assumptions Kernel.ConcreteRecordMachines.janus_like_bounded_inverse.
Print Assumptions Kernel.ConcreteRecordMachines.ram_untied_record_not_determined_by_base.
(* === Kernel.EVMStorageGas : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.EVMStorageGas.empty_slot_invariant.
Print Assumptions Kernel.EVMStorageGas.persistent_write_priced.
Print Assumptions Kernel.EVMStorageGas.revoked_write_nearly_free.
(* === Kernel.GasMetering : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.GasMetering.gas_schedule_exactness.
Print Assumptions Kernel.GasMetering.undercharged_opcode_admits_free_commitment.
Print Assumptions Kernel.GasMetering.undercharged_opcode_breaks_certification_floor.
Print Assumptions Kernel.GasMetering.overcharge_breaks_exactness.
Print Assumptions Kernel.GasMetering.toy_charged_costs.
Print Assumptions Kernel.GasMetering.toy_uncharged_free.
Print Assumptions Kernel.GasMetering.toy_charge_is_cert_flip.
Print Assumptions Kernel.GasMetering.toy_exact_unit_pricing.
Print Assumptions Kernel.GasMetering.toy_gas_schedule_is_exact.
(* === Kernel.NeculaPCC : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NeculaPCC.pcc_checker_accepts_iff_vc.
Print Assumptions Kernel.NeculaPCC.pcc_certificate_implies_vc.
Print Assumptions Kernel.NeculaPCC.pcc_unsafe_program_rejected.
(* === Kernel.PoSFinality : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PoSFinality.vote_preserves_finalized.
Print Assumptions Kernel.PoSFinality.nothing_at_stake_free_finalization.
Print Assumptions Kernel.PoSFinality.nothing_at_stake_is_free_forgery.
Print Assumptions Kernel.PoSFinality.slashing_cert_costs.
Print Assumptions Kernel.PoSFinality.slashing_finality_floor.
(* === Kernel.RFC9162Merkle : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RFC9162Merkle.rfc9162_inclusion_boundary_safe.
Print Assumptions Kernel.RFC9162Merkle.rfc9162_consistency_boundary_safe.
Print Assumptions Kernel.RFC9162Merkle.symbolic_digest_eqb_refl.
Print Assumptions Kernel.RFC9162Merkle.rfc9162_example_inclusion_d0.
Print Assumptions Kernel.RFC9162Merkle.rfc9162_example_inclusion_d3.
Print Assumptions Kernel.RFC9162Merkle.rfc9162_example_inclusion_d4.
Print Assumptions Kernel.RFC9162Merkle.rfc9162_example_inclusion_d6.
Print Assumptions Kernel.RFC9162Merkle.rfc9162_example_consistency_4_7.
Print Assumptions Kernel.RFC9162Merkle.ct_extension_preserves_entries.
Print Assumptions Kernel.RFC9162Merkle.ct_extension_size_monotone.
(* === Kernel.RealSystemConsequences : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RealSystemConsequences.ct_local_view_insufficient.
Print Assumptions Kernel.RealSystemConsequences.tpm_selection_binding_is_necessary.
Print Assumptions Kernel.RealSystemConsequences.weak_subjective_suffix_insufficient.
Print Assumptions Kernel.RealSystemConsequences.wal_ack_requires_durability.
Print Assumptions Kernel.RealSystemConsequences.audit_local_snapshot_insufficient.
(* === Kernel.TPMQuoteAuthenticity : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TPMQuoteAuthenticity.degenerate_accepts_forgery.
Print Assumptions Kernel.TPMQuoteAuthenticity.tpm_interface_authenticity_refuted.
(* === Kernel.TPMQuoteGap : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.TPMQuoteGap.quote_collision.
Print Assumptions Kernel.TPMQuoteGap.quote_cannot_attest_unmeasured_state.
Print Assumptions Kernel.TPMQuoteGap.quote_decides_measured_claims.
(* === Kernel.CalorimeterProtocol : 26 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.CalorimeterProtocol.canonical_reset_satisfies_master_equation.
Print Assumptions Kernel.CalorimeterProtocol.canonical_reset_heat_exact.
Print Assumptions Kernel.CalorimeterProtocol.selected_gap_gives_landauer_heat.
Print Assumptions Kernel.CalorimeterProtocol.ln_two_positive.
Print Assumptions Kernel.CalorimeterProtocol.canonical_reset_heat_below_landauer_at_small_gap.
Print Assumptions Kernel.CalorimeterProtocol.master_equation_does_not_fix_heat_scale.
Print Assumptions Kernel.CalorimeterProtocol.canonical_reset_is_one_mu.
Print Assumptions Kernel.CalorimeterProtocol.canonical_rates_break_detailed_balance.
Print Assumptions Kernel.CalorimeterProtocol.detailed_balance_settles_at_gibbs.
Print Assumptions Kernel.CalorimeterProtocol.detailed_balance_thermalizing_step.
Print Assumptions Kernel.CalorimeterProtocol.gibbs_pos.
Print Assumptions Kernel.CalorimeterProtocol.detailed_balance_never_empties.
Print Assumptions Kernel.CalorimeterProtocol.landauer_gap_settles_at_one_fifth.
Print Assumptions Kernel.CalorimeterProtocol.dpl_ext.
Print Assumptions Kernel.CalorimeterProtocol.dpl_val.
Print Assumptions Kernel.CalorimeterProtocol.free_energy_derivative.
Print Assumptions Kernel.CalorimeterProtocol.gibbs_le_half_at_nonneg.
Print Assumptions Kernel.CalorimeterProtocol.gibbs_antitone.
Print Assumptions Kernel.CalorimeterProtocol.free_energy_step_bounds.
Print Assumptions Kernel.CalorimeterProtocol.driven_first_law.
Print Assumptions Kernel.CalorimeterProtocol.driven_work_second_law.
Print Assumptions Kernel.CalorimeterProtocol.driven_work_near_free_energy.
Print Assumptions Kernel.CalorimeterProtocol.free_energy_at_zero.
Print Assumptions Kernel.CalorimeterProtocol.ln_le_loc.
Print Assumptions Kernel.CalorimeterProtocol.ln_one_plus_le.
Print Assumptions Kernel.CalorimeterProtocol.driven_reset_work_window.
(* === Kernel.RelaxationContinuous : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RelaxationContinuous.rcd_ln_mono.
Print Assumptions Kernel.RelaxationContinuous.rcd_sigma_nonneg.
Print Assumptions Kernel.RelaxationContinuous.rcd_lim_ext.
Print Assumptions Kernel.RelaxationContinuous.rcd_sum_deriv.
Print Assumptions Kernel.RelaxationContinuous.rcd_term_deriv.
Print Assumptions Kernel.RelaxationContinuous.rcd_flow_total.
Print Assumptions Kernel.RelaxationContinuous.rcd_flow_L.
Print Assumptions Kernel.RelaxationContinuous.rcd_D_derivative.
Print Assumptions Kernel.RelaxationContinuous.rcd_D_monotone.
Print Assumptions Kernel.RelaxationContinuous.rcd_neg_D_deriv.
Print Assumptions Kernel.RelaxationContinuous.rcd_produced_window.
Print Assumptions Kernel.RelaxationContinuous.rcd_produced_bounds.
(* === Kernel.RelaxationContinuousLimit : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_lin4.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_sum_le_gen.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_sum_le.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_sigma_ge.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_D_nonneg.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_mass.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_D_deriv.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_D_decay.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_exp_neg_le.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_D_limit.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_produced_limit.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_lim0_sum.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_cont_lim0.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_p_cont.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_vlnv.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_term_cont.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_D_at_zero.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_D_point.
Print Assumptions Kernel.RelaxationContinuousLimit.rcl_known_start_total.
(* === Kernel.RelaxationConvergence : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RelaxationConvergence.rc_sum_abs.
Print Assumptions Kernel.RelaxationConvergence.rc_sum_le.
Print Assumptions Kernel.RelaxationConvergence.rc_contract.
Print Assumptions Kernel.RelaxationConvergence.rc_delta_le_1.
Print Assumptions Kernel.RelaxationConvergence.rc_prob_run.
Print Assumptions Kernel.RelaxationConvergence.rc_l1_le_2.
Print Assumptions Kernel.RelaxationConvergence.rc_l1_pow.
Print Assumptions Kernel.RelaxationConvergence.rc_D_le_chi2.
Print Assumptions Kernel.RelaxationConvergence.rc_pi_min.
Print Assumptions Kernel.RelaxationConvergence.rc_sq_sum.
Print Assumptions Kernel.RelaxationConvergence.rc_chi2_le.
Print Assumptions Kernel.RelaxationConvergence.rc_converges.
Print Assumptions Kernel.RelaxationConvergence.rc_known_start_gap.
Print Assumptions Kernel.RelaxationConvergence.rc_known_start_limit.
(* === Kernel.RelaxationEntropy : 24 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RelaxationEntropy.re_exp_ge.
Print Assumptions Kernel.RelaxationEntropy.re_ln_le.
Print Assumptions Kernel.RelaxationEntropy.re_term_ge.
Print Assumptions Kernel.RelaxationEntropy.re_gibbs_list.
Print Assumptions Kernel.RelaxationEntropy.re_gibbs.
Print Assumptions Kernel.RelaxationEntropy.re_pi_stationary.
Print Assumptions Kernel.RelaxationEntropy.re_step_nonneg.
Print Assumptions Kernel.RelaxationEntropy.re_step_mass.
Print Assumptions Kernel.RelaxationEntropy.re_term_le_sum.
Print Assumptions Kernel.RelaxationEntropy.re_ln_div.
Print Assumptions Kernel.RelaxationEntropy.re_sigma_term.
Print Assumptions Kernel.RelaxationEntropy.re_sigma_is_drop.
Print Assumptions Kernel.RelaxationEntropy.re_sigma_nonneg.
Print Assumptions Kernel.RelaxationEntropy.re_relative_entropy_monotone.
Print Assumptions Kernel.RelaxationEntropy.re_run_nonneg.
Print Assumptions Kernel.RelaxationEntropy.re_run_mass.
Print Assumptions Kernel.RelaxationEntropy.re_point_prob.
Print Assumptions Kernel.RelaxationEntropy.re_point_entropy.
Print Assumptions Kernel.RelaxationEntropy.re_known_start_total.
Print Assumptions Kernel.RelaxationEntropy.re_known_start_bound.
Print Assumptions Kernel.RelaxationEntropy.re_known_start_vs_set.
Print Assumptions Kernel.RelaxationEntropy.re_flux_balance.
Print Assumptions Kernel.RelaxationEntropy.re_mass_split.
Print Assumptions Kernel.RelaxationEntropy.re_stretch_ratio.
(* === Kernel.RelaxationStretch : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RelaxationStretch.rs_UN.
Print Assumptions Kernel.RelaxationStretch.rs_keep_lin.
Print Assumptions Kernel.RelaxationStretch.rs_keep_ext.
Print Assumptions Kernel.RelaxationStretch.rs_split0.
Print Assumptions Kernel.RelaxationStretch.rs_split.
Print Assumptions Kernel.RelaxationStretch.rs_partial.
Print Assumptions Kernel.RelaxationStretch.rs_sum_le.
Print Assumptions Kernel.RelaxationStretch.rs_u_nonneg.
Print Assumptions Kernel.RelaxationStretch.rs_left_pow.
Print Assumptions Kernel.RelaxationStretch.rs_rate_nonneg.
Print Assumptions Kernel.RelaxationStretch.rs_mean_stretch.
(* === Kernel.RelaxationStretchContinuous : 39 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_UU.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_UN.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_U01.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_U_nonneg.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_N_nonneg.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_sum_le.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_le_sum.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_out_nonneg.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_out_split.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_into_N.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_massN_pos.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_mass_over_flow.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_Lam_pos.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_A_nonneg.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_M_pos.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_step_mono.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_step_bound.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_it_bound.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_it_grow.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_seq_ub.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_cv_ext.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_cv_const.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_h_lim.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_cv_sum.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_h_fix.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_leave_exists.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_mean_leave.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_G_deriv.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_F_deriv.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_S_deriv.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_S_start.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_S_nonneg.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_S_decay.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_negG_deriv.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_G_start.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_window_value.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_G_small.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_mean_stretch_time.
Print Assumptions Kernel.RelaxationStretchContinuous.rsc_stretch_identity.
(* === TestFixtures.VacuitySmoke : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions TestFixtures.VacuitySmoke.smoke_literal_true.
Print Assumptions TestFixtures.VacuitySmoke.smoke_unfolds_to_true.
Print Assumptions TestFixtures.VacuitySmoke.smoke_quantified_true.
Print Assumptions TestFixtures.VacuitySmoke.smoke_identity.
Print Assumptions TestFixtures.VacuitySmoke.smoke_two_hyps_pick_first.
Print Assumptions TestFixtures.VacuitySmoke.smoke_addnSm.
Print Assumptions TestFixtures.VacuitySmoke.smoke_succ_nonzero.
Print Assumptions TestFixtures.VacuitySmoke.smoke_genuine_equality.
Print Assumptions TestFixtures.VacuitySmoke.smoke_modus_ponens.
(* === Minimal.AxDgBlock : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.AxDgBlock.ax_dg_blind_shift.
Print Assumptions Minimal.AxDgBlock.ax_dg_shift_eqb.
Print Assumptions Minimal.AxDgBlock.ax_dg_existsb_shift.
Print Assumptions Minimal.AxDgBlock.ax_dg_block_cstep.
Print Assumptions Minimal.AxDgBlock.ax_dg_block_step.
Print Assumptions Minimal.AxDgBlock.ax_dg_block_stop.
Print Assumptions Minimal.AxDgBlock.ax_dg_block_go.
Print Assumptions Minimal.AxDgBlock.ax_dg_block_run.
Print Assumptions Minimal.AxDgBlock.ax_dg_blind_facts.
Print Assumptions Minimal.AxDgBlock.ax_dg_blind_chan.
(* === Minimal.BitSearch2 : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.BitSearch2.ent2_in_all_bits.
Print Assumptions Minimal.BitSearch2.ent2_agree_length.
Print Assumptions Minimal.BitSearch2.ent2_agree_app.
Print Assumptions Minimal.BitSearch2.ent2_agree_flip.
Print Assumptions Minimal.BitSearch2.ent2_agree_true_iff.
Print Assumptions Minimal.BitSearch2.ent2_eval_prop.
Print Assumptions Minimal.BitSearch2.ent2_skipn_cons.
Print Assumptions Minimal.BitSearch2.ent2_okb_world.
Print Assumptions Minimal.BitSearch2.ent2_trapped_run.
Print Assumptions Minimal.BitSearch2.ent2_checks_pass.
Print Assumptions Minimal.BitSearch2.ent2_checks_fail.
Print Assumptions Minimal.BitSearch2.ent2_qtrace_run.
Print Assumptions Minimal.BitSearch2.ent2_err_back.
Print Assumptions Minimal.BitSearch2.ent2_facts_le.
Print Assumptions Minimal.BitSearch2.ent2_facts_count.
Print Assumptions Minimal.BitSearch2.ent2_questions_cap.
(* === Minimal.BitSearchMember2 : 36 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.BitSearchMember2.ent2_checks_length.
Print Assumptions Minimal.BitSearchMember2.ent2_filter_checks.
Print Assumptions Minimal.BitSearchMember2.ent2_map_true.
Print Assumptions Minimal.BitSearchMember2.ent2_decode_qtrace.
Print Assumptions Minimal.BitSearchMember2.ent2_record_moves_checks.
Print Assumptions Minimal.BitSearchMember2.ent2_record_moves_qtrace.
Print Assumptions Minimal.BitSearchMember2.ent2_sum_const.
Print Assumptions Minimal.BitSearchMember2.ent2_prior_length.
Print Assumptions Minimal.BitSearchMember2.ent2_post_length.
Print Assumptions Minimal.BitSearchMember2.ent2_in_post.
Print Assumptions Minimal.BitSearchMember2.ent2_post_incl.
Print Assumptions Minimal.BitSearchMember2.ent2_skipn_app_len.
Print Assumptions Minimal.BitSearchMember2.ent2_reduction.
Print Assumptions Minimal.BitSearchMember2.ent2_forallb_false.
Print Assumptions Minimal.BitSearchMember2.ent2_witness.
Print Assumptions Minimal.BitSearchMember2.ent2_narrowing.
Print Assumptions Minimal.BitSearchMember2.ent2_okb_prefix.
Print Assumptions Minimal.BitSearchMember2.ent2_okb_iff.
Print Assumptions Minimal.BitSearchMember2.ent2_search_certifies_iff.
Print Assumptions Minimal.BitSearchMember2.ent2_search_posterior_is_certified.
Print Assumptions Minimal.BitSearchMember2.ent2_no_search_past_16.
Print Assumptions Minimal.BitSearchMember2.ent2_member_certified.
Print Assumptions Minimal.BitSearchMember2.ent2_bit_search.
Print Assumptions Minimal.BitSearchMember2.ent2_search_lands.
Print Assumptions Minimal.BitSearchMember2.ent2_checked_checks.
Print Assumptions Minimal.BitSearchMember2.ent2_checked_app.
Print Assumptions Minimal.BitSearchMember2.ent2_checked_qtrace.
Print Assumptions Minimal.BitSearchMember2.ent2_claims_length.
Print Assumptions Minimal.BitSearchMember2.ent2_answers_world.
Print Assumptions Minimal.BitSearchMember2.ent2_agree_prefix.
Print Assumptions Minimal.BitSearchMember2.ent2_nodup_join.
Print Assumptions Minimal.BitSearchMember2.ent2_nodup_all_bits.
Print Assumptions Minimal.BitSearchMember2.ent2_filter_mono.
Print Assumptions Minimal.BitSearchMember2.ent2_filter_map.
Print Assumptions Minimal.BitSearchMember2.ent2_prefix_class.
Print Assumptions Minimal.BitSearchMember2.ent2_search_questions_floor.
(* === Minimal.BitSearchObserved2 : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.BitSearchObserved2.ent2_suffix_class.
Print Assumptions Minimal.BitSearchObserved2.ent2_search_partition.
Print Assumptions Minimal.BitSearchObserved2.ent2_search_partition_bits.
Print Assumptions Minimal.BitSearchObserved2.ent2_search_observed.
(* === Minimal.CompressionSmall2 : 23 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CompressionSmall2.ent2_nodup_app_disjoint.
Print Assumptions Minimal.CompressionSmall2.ent2_flips_compression_bound.
Print Assumptions Minimal.CompressionSmall2.ent2_flip_gives_state.
Print Assumptions Minimal.CompressionSmall2.ent2_flips_log_bound.
Print Assumptions Minimal.CompressionSmall2.ent2_a2_from_compression.
Print Assumptions Minimal.CompressionSmall2.ent2_eqb_spec.
Print Assumptions Minimal.CompressionSmall2.ent2_filter_nodup_le.
Print Assumptions Minimal.CompressionSmall2.ent2_compression_priced_iff_fibres.
Print Assumptions Minimal.CompressionSmall2.ent2_compression_merges_priced.
Print Assumptions Minimal.CompressionSmall2.ent2_frag_eqb_agree.
Print Assumptions Minimal.CompressionSmall2.ent2_frag_fibre_agree.
Print Assumptions Minimal.CompressionSmall2.ent2_frag_compression_priced.
Print Assumptions Minimal.CompressionSmall2.ent2_frag_toll_by_compression.
Print Assumptions Minimal.CompressionSmall2.ent2_frag_cost_minimal.
Print Assumptions Minimal.CompressionSmall2.ent2_frag_bound_attained.
Print Assumptions Minimal.CompressionSmall2.ent2_small_not_compression_priced.
Print Assumptions Minimal.CompressionSmall2.ent2_compression_trace_floor.
Print Assumptions Minimal.CompressionSmall2.ent2_flip_merges_at.
Print Assumptions Minimal.CompressionSmall2.ent2_flip_merges_or_revokes.
Print Assumptions Minimal.CompressionSmall2.ent2_injective_flip_revokes.
Print Assumptions Minimal.CompressionSmall2.ent2_forced_priced_iff_merges.
Print Assumptions Minimal.CompressionSmall2.ent2_permanent_flip_forced.
Print Assumptions Minimal.CompressionSmall2.ent2_forced_without_permanent.
(* === Minimal.ConsensusSeparation : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.ConsensusSeparation.cs_copies_add.
Print Assumptions Minimal.ConsensusSeparation.cs_mono_r.
Print Assumptions Minimal.ConsensusSeparation.cs_no_consensus_monotonic.
Print Assumptions Minimal.ConsensusSeparation.cs_kind_eqb_eq.
Print Assumptions Minimal.ConsensusSeparation.cs_comp_assoc.
Print Assumptions Minimal.ConsensusSeparation.cs_comp_comm.
Print Assumptions Minimal.ConsensusSeparation.cs_copies_P.
Print Assumptions Minimal.ConsensusSeparation.cs_step_keeps_decided.
Print Assumptions Minimal.ConsensusSeparation.cs_steps_keep_decided.
Print Assumptions Minimal.ConsensusSeparation.cs_dec_mono.
Print Assumptions Minimal.ConsensusSeparation.cs_move_pos.
Print Assumptions Minimal.ConsensusSeparation.cs_step_inv.
Print Assumptions Minimal.ConsensusSeparation.cs_steps_inv.
Print Assumptions Minimal.ConsensusSeparation.cs_inv_copies.
Print Assumptions Minimal.ConsensusSeparation.cs_no_both.
Print Assumptions Minimal.ConsensusSeparation.cs_move_target_pos.
Print Assumptions Minimal.ConsensusSeparation.cs_can_choose.
Print Assumptions Minimal.ConsensusSeparation.cs_machine_consensus.
Print Assumptions Minimal.ConsensusSeparation.cs_machine_not_monotonic.
(* === Minimal.CoveringNeeded2 : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CoveringNeeded2.ent2_start_inj.
Print Assumptions Minimal.CoveringNeeded2.ent2_uncovered_posterior.
Print Assumptions Minimal.CoveringNeeded2.ent2_uncovered_claim_false.
Print Assumptions Minimal.CoveringNeeded2.ent2_no_cheap_covering.
(* === Minimal.CzLink : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CzLink.ds_run_add.
Print Assumptions Minimal.CzLink.cmpz_link_id.
Print Assumptions Minimal.CzLink.cmpz_link_compose.
Print Assumptions Minimal.CzLink.cmpz_link_weaken.
Print Assumptions Minimal.CzLink.cmpz_tower.
Print Assumptions Minimal.CzLink.cmpz_tower_uniform.
(* === Minimal.CzShared : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CzShared.cmpz_shared_base_toll.
Print Assumptions Minimal.CzShared.cmpz_shared_respect.
Print Assumptions Minimal.CzShared.cmpz_shared_raises.
Print Assumptions Minimal.CzShared.cmpz_shared_not_earned.
(* === Minimal.EarnedCore : 70 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EarnedCore.eval_iff.
Print Assumptions Minimal.EarnedCore.fact_eqb_eq.
Print Assumptions Minimal.EarnedCore.start_clean.
Print Assumptions Minimal.EarnedCore.run_app.
Print Assumptions Minimal.EarnedCore.run_snoc.
Print Assumptions Minimal.EarnedCore.total_cost_app.
Print Assumptions Minimal.EarnedCore.run_prog_halted.
Print Assumptions Minimal.EarnedCore.run_prog_trace.
Print Assumptions Minimal.EarnedCore.step_core.
Print Assumptions Minimal.EarnedCore.step_cert.
Print Assumptions Minimal.EarnedCore.step_mu.
Print Assumptions Minimal.EarnedCore.fetch_map.
Print Assumptions Minimal.EarnedCore.simulation_step.
Print Assumptions Minimal.EarnedCore.core_run_prog.
Print Assumptions Minimal.EarnedCore.core_run_halted.
Print Assumptions Minimal.EarnedCore.simulation_run.
Print Assumptions Minimal.EarnedCore.halting_correspondence.
Print Assumptions Minimal.EarnedCore.mu_conservation.
Print Assumptions Minimal.EarnedCore.mu_conservation_trace.
Print Assumptions Minimal.EarnedCore.mu_conservation_program.
Print Assumptions Minimal.EarnedCore.cert_latch.
Print Assumptions Minimal.EarnedCore.base_blind.
Print Assumptions Minimal.EarnedCore.cert_permanent.
Print Assumptions Minimal.EarnedCore.only_certify_certifies.
Print Assumptions Minimal.EarnedCore.a2.
Print Assumptions Minimal.EarnedCore.nfi_floor.
Print Assumptions Minimal.EarnedCore.ver_write.
Print Assumptions Minimal.EarnedCore.val_write.
Print Assumptions Minimal.EarnedCore.facts_write.
Print Assumptions Minimal.EarnedCore.chan_write.
Print Assumptions Minimal.EarnedCore.err_write.
Print Assumptions Minimal.EarnedCore.ver_mono.
Print Assumptions Minimal.EarnedCore.ver_same_val.
Print Assumptions Minimal.EarnedCore.ver_check.
Print Assumptions Minimal.EarnedCore.val_check.
Print Assumptions Minimal.EarnedCore.facts_step.
Print Assumptions Minimal.EarnedCore.facts_keep.
Print Assumptions Minimal.EarnedCore.full_table_traps.
Print Assumptions Minimal.EarnedCore.facts_bounded_step.
Print Assumptions Minimal.EarnedCore.chan_step.
Print Assumptions Minimal.EarnedCore.commit_ok_iff.
Print Assumptions Minimal.EarnedCore.unearned_commit_traps.
Print Assumptions Minimal.EarnedCore.uncommitted_certify_traps.
Print Assumptions Minimal.EarnedCore.ver_mono_run.
Print Assumptions Minimal.EarnedCore.untouched_of_ver.
Print Assumptions Minimal.EarnedCore.sound_step.
Print Assumptions Minimal.EarnedCore.sound_run.
Print Assumptions Minimal.EarnedCore.checker_soundness.
Print Assumptions Minimal.EarnedCore.committed_claim_holds.
Print Assumptions Minimal.EarnedCore.earned_intro.
Print Assumptions Minimal.EarnedCore.no_forging_step.
Print Assumptions Minimal.EarnedCore.no_forging.
Print Assumptions Minimal.EarnedCore.earned_commitment_provenance.
Print Assumptions Minimal.EarnedCore.cert_first.
Print Assumptions Minimal.EarnedCore.chan_origin.
Print Assumptions Minimal.EarnedCore.earned_certification_provenance.
Print Assumptions Minimal.EarnedCore.earned_certification_same_claim.
Print Assumptions Minimal.EarnedCore.certified_run_min_cost.
Print Assumptions Minimal.EarnedCore.program_certified_min_cost.
Print Assumptions Minimal.EarnedCore.min_cost_tight.
Print Assumptions Minimal.EarnedCore.receipt_separation.
Print Assumptions Minimal.EarnedCore.no_mu_oracle.
Print Assumptions Minimal.EarnedCore.no_cert_oracle.
Print Assumptions Minimal.EarnedCore.no_commit_oracle.
Print Assumptions Minimal.EarnedCore.run_prog_trapped.
Print Assumptions Minimal.EarnedCore.earned_run_check_can_fail.
Print Assumptions Minimal.EarnedCore.earned_run_refused_forever.
Print Assumptions Minimal.EarnedCore.chan_stays_some.
Print Assumptions Minimal.EarnedCore.certified_channel_earned.
Print Assumptions Minimal.EarnedCore.channel_names_last_commit.
(* === Minimal.EarnedGeneric : 79 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EarnedGeneric.prop_eqb_refl.
Print Assumptions Minimal.EarnedGeneric.generic_fact_eqb_eq.
Print Assumptions Minimal.EarnedGeneric.generic_start_clean.
Print Assumptions Minimal.EarnedGeneric.generic_run_app.
Print Assumptions Minimal.EarnedGeneric.generic_run_snoc.
Print Assumptions Minimal.EarnedGeneric.generic_total_cost_app.
Print Assumptions Minimal.EarnedGeneric.generic_run_prog_halted.
Print Assumptions Minimal.EarnedGeneric.generic_run_prog_trace.
Print Assumptions Minimal.EarnedGeneric.generic_run_prog_trapped.
Print Assumptions Minimal.EarnedGeneric.generic_mu_conservation_trace.
Print Assumptions Minimal.EarnedGeneric.generic_mu_conservation_program.
Print Assumptions Minimal.EarnedGeneric.generic_cert_latch.
Print Assumptions Minimal.EarnedGeneric.generic_cert_permanent.
Print Assumptions Minimal.EarnedGeneric.generic_only_certify_certifies.
Print Assumptions Minimal.EarnedGeneric.generic_a2.
Print Assumptions Minimal.EarnedGeneric.generic_nfi_floor.
Print Assumptions Minimal.EarnedGeneric.generic_ver_write.
Print Assumptions Minimal.EarnedGeneric.generic_val_write.
Print Assumptions Minimal.EarnedGeneric.generic_facts_write.
Print Assumptions Minimal.EarnedGeneric.generic_chan_write.
Print Assumptions Minimal.EarnedGeneric.generic_ver_mono.
Print Assumptions Minimal.EarnedGeneric.generic_ver_same_val.
Print Assumptions Minimal.EarnedGeneric.generic_ver_check.
Print Assumptions Minimal.EarnedGeneric.generic_val_check.
Print Assumptions Minimal.EarnedGeneric.generic_facts_step.
Print Assumptions Minimal.EarnedGeneric.generic_facts_keep.
Print Assumptions Minimal.EarnedGeneric.generic_full_table_traps.
Print Assumptions Minimal.EarnedGeneric.generic_facts_bounded_step.
Print Assumptions Minimal.EarnedGeneric.generic_chan_step.
Print Assumptions Minimal.EarnedGeneric.generic_commit_ok_iff.
Print Assumptions Minimal.EarnedGeneric.generic_unearned_commit_traps.
Print Assumptions Minimal.EarnedGeneric.generic_uncommitted_certify_traps.
Print Assumptions Minimal.EarnedGeneric.generic_ver_mono_run.
Print Assumptions Minimal.EarnedGeneric.generic_untouched_of_ver.
Print Assumptions Minimal.EarnedGeneric.generic_sound_step.
Print Assumptions Minimal.EarnedGeneric.generic_sound_run.
Print Assumptions Minimal.EarnedGeneric.generic_checker_soundness.
Print Assumptions Minimal.EarnedGeneric.generic_committed_claim_holds.
Print Assumptions Minimal.EarnedGeneric.generic_earned_intro.
Print Assumptions Minimal.EarnedGeneric.generic_no_forging_step.
Print Assumptions Minimal.EarnedGeneric.generic_no_forging.
Print Assumptions Minimal.EarnedGeneric.generic_earned_commitment_provenance.
Print Assumptions Minimal.EarnedGeneric.generic_cert_first.
Print Assumptions Minimal.EarnedGeneric.generic_chan_origin.
Print Assumptions Minimal.EarnedGeneric.generic_earned_certification_provenance.
Print Assumptions Minimal.EarnedGeneric.generic_certified_run_min_cost.
Print Assumptions Minimal.EarnedGeneric.generic_program_certified_min_cost.
Print Assumptions Minimal.EarnedGeneric.exec_check_pass.
Print Assumptions Minimal.EarnedGeneric.exec_check_fail.
Print Assumptions Minimal.EarnedGeneric.exec_commit_pass.
Print Assumptions Minimal.EarnedGeneric.chain_certifies.
Print Assumptions Minimal.EarnedGeneric.chain_refused_forever.
Print Assumptions Minimal.EarnedGeneric.chain_certifies_iff.
Print Assumptions Minimal.EarnedGeneric.ceval_iff.
Print Assumptions Minimal.EarnedGeneric.cprop_eqb_eq.
Print Assumptions Minimal.EarnedGeneric.core_earned_certification_provenance.
Print Assumptions Minimal.EarnedGeneric.core_checker_soundness.
Print Assumptions Minimal.EarnedGeneric.core_no_forging.
Print Assumptions Minimal.EarnedGeneric.core_certified_run_min_cost.
Print Assumptions Minimal.EarnedGeneric.core_zero_chain_iff.
Print Assumptions Minimal.EarnedGeneric.dec_fuel.
Print Assumptions Minimal.EarnedGeneric.dec_odd.
Print Assumptions Minimal.EarnedGeneric.dec_even.
Print Assumptions Minimal.EarnedGeneric.dec_pow.
Print Assumptions Minimal.EarnedGeneric.decode_encode.
Print Assumptions Minimal.EarnedGeneric.sortedb_iff.
Print Assumptions Minimal.EarnedGeneric.seval_iff.
Print Assumptions Minimal.EarnedGeneric.sprop_eqb_eq.
Print Assumptions Minimal.EarnedGeneric.sorted_earned_certification_provenance.
Print Assumptions Minimal.EarnedGeneric.sorted_checker_soundness.
Print Assumptions Minimal.EarnedGeneric.sorted_no_forging.
Print Assumptions Minimal.EarnedGeneric.sorted_certified_run_min_cost.
Print Assumptions Minimal.EarnedGeneric.sorted_committed_claim_holds.
Print Assumptions Minimal.EarnedGeneric.sorted_earned_provenance.
Print Assumptions Minimal.EarnedGeneric.sorted_run_certifies_iff.
Print Assumptions Minimal.EarnedGeneric.sorted_run_certifies.
Print Assumptions Minimal.EarnedGeneric.sorted_run_refused_forever.
Print Assumptions Minimal.EarnedGeneric.sorted_demo_certifies.
Print Assumptions Minimal.EarnedGeneric.sorted_demo_refused_forever.
(* === Minimal.EarnedMulti : 70 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EarnedMulti.multi_prop_eqb_refl.
Print Assumptions Minimal.EarnedMulti.multi_fact_eqb_eq.
Print Assumptions Minimal.EarnedMulti.multi_start_clean.
Print Assumptions Minimal.EarnedMulti.multi_run_app.
Print Assumptions Minimal.EarnedMulti.multi_run_snoc.
Print Assumptions Minimal.EarnedMulti.multi_total_cost_app.
Print Assumptions Minimal.EarnedMulti.multi_run_prog_halted.
Print Assumptions Minimal.EarnedMulti.multi_run_prog_trace.
Print Assumptions Minimal.EarnedMulti.multi_run_prog_add.
Print Assumptions Minimal.EarnedMulti.multi_run_prog_succ.
Print Assumptions Minimal.EarnedMulti.multi_cexec_trapped.
Print Assumptions Minimal.EarnedMulti.multi_trapped_halted.
Print Assumptions Minimal.EarnedMulti.multi_step_trapped.
Print Assumptions Minimal.EarnedMulti.multi_run_prog_trapped.
Print Assumptions Minimal.EarnedMulti.multi_err_permanent.
Print Assumptions Minimal.EarnedMulti.multi_mu_conservation_trace.
Print Assumptions Minimal.EarnedMulti.multi_mu_conservation_program.
Print Assumptions Minimal.EarnedMulti.multi_cert_latch.
Print Assumptions Minimal.EarnedMulti.multi_cert_permanent.
Print Assumptions Minimal.EarnedMulti.multi_only_certify_certifies.
Print Assumptions Minimal.EarnedMulti.multi_a2.
Print Assumptions Minimal.EarnedMulti.multi_nfi_floor.
Print Assumptions Minimal.EarnedMulti.multi_ver_write.
Print Assumptions Minimal.EarnedMulti.multi_val_write.
Print Assumptions Minimal.EarnedMulti.multi_facts_write.
Print Assumptions Minimal.EarnedMulti.multi_chan_write.
Print Assumptions Minimal.EarnedMulti.multi_err_write.
Print Assumptions Minimal.EarnedMulti.multi_pc_write.
Print Assumptions Minimal.EarnedMulti.multi_ver_mono.
Print Assumptions Minimal.EarnedMulti.multi_ver_same_val.
Print Assumptions Minimal.EarnedMulti.multi_ver_check.
Print Assumptions Minimal.EarnedMulti.multi_val_check.
Print Assumptions Minimal.EarnedMulti.multi_facts_step.
Print Assumptions Minimal.EarnedMulti.multi_facts_keep.
Print Assumptions Minimal.EarnedMulti.multi_full_table_traps.
Print Assumptions Minimal.EarnedMulti.multi_facts_bounded_step.
Print Assumptions Minimal.EarnedMulti.multi_chan_step.
Print Assumptions Minimal.EarnedMulti.multi_commit_ok_iff.
Print Assumptions Minimal.EarnedMulti.multi_unearned_commit_traps.
Print Assumptions Minimal.EarnedMulti.multi_uncommitted_certify_traps.
Print Assumptions Minimal.EarnedMulti.multi_frame_cexec.
Print Assumptions Minimal.EarnedMulti.multi_plain_cexec.
Print Assumptions Minimal.EarnedMulti.multi_plain_step.
Print Assumptions Minimal.EarnedMulti.multi_frame_step.
Print Assumptions Minimal.EarnedMulti.multi_frame_run.
Print Assumptions Minimal.EarnedMulti.multi_plain_run.
Print Assumptions Minimal.EarnedMulti.multi_ver_mono_run.
Print Assumptions Minimal.EarnedMulti.multi_untouched_of_ver.
Print Assumptions Minimal.EarnedMulti.multi_sound_step.
Print Assumptions Minimal.EarnedMulti.multi_sound_run.
Print Assumptions Minimal.EarnedMulti.multi_checker_soundness.
Print Assumptions Minimal.EarnedMulti.multi_committed_claim_holds.
Print Assumptions Minimal.EarnedMulti.multi_earned_intro.
Print Assumptions Minimal.EarnedMulti.multi_no_forging_step.
Print Assumptions Minimal.EarnedMulti.multi_no_forging.
Print Assumptions Minimal.EarnedMulti.multi_earned_commitment_provenance.
Print Assumptions Minimal.EarnedMulti.multi_cert_first.
Print Assumptions Minimal.EarnedMulti.multi_chan_origin.
Print Assumptions Minimal.EarnedMulti.multi_earned_certification_provenance.
Print Assumptions Minimal.EarnedMulti.multi_certified_run_min_cost.
Print Assumptions Minimal.EarnedMulti.multi_program_certified_min_cost.
Print Assumptions Minimal.EarnedMulti.multi_exec_check_pass.
Print Assumptions Minimal.EarnedMulti.multi_exec_check_fail.
Print Assumptions Minimal.EarnedMulti.multi_exec_commit_pass.
Print Assumptions Minimal.EarnedMulti.multi_exec_commit_fail.
Print Assumptions Minimal.EarnedMulti.multi_exec_certify_pass.
Print Assumptions Minimal.EarnedMulti.multi_exec_certify_fail.
Print Assumptions Minimal.EarnedMulti.multi_chain_certifies.
Print Assumptions Minimal.EarnedMulti.multi_chain_refused_forever.
Print Assumptions Minimal.EarnedMulti.multi_chain_certifies_iff.
(* === Minimal.EarnedMultiPriced : 73 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_prop_eqb_refl.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_fact_eqb_eq.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_start_clean.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_app.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_snoc.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_total_cost_app.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_prog_halted.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_prog_trace.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_prog_add.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_prog_succ.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_cexec_trapped.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_trapped_halted.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_step_trapped.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_run_prog_trapped.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_err_permanent.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_mu_conservation_trace.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_mu_conservation_program.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_cert_latch.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_cert_permanent.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_only_certify_certifies.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_a2.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_nfi_floor.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_ver_write.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_val_write.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_facts_write.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_chan_write.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_err_write.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_pc_write.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_ver_mono.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_ver_same_val.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_ver_check.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_val_check.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_facts_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_facts_keep.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_full_table_traps.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_facts_bounded_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_chan_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_commit_ok_iff.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_unearned_commit_traps.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_uncommitted_certify_traps.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_frame_cexec.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_plain_cexec.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_plain_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_frame_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_frame_run.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_plain_run.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_ver_mono_run.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_untouched_of_ver.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_sound_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_sound_run.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_checker_soundness.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_committed_claim_holds.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_earned_intro.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_no_forging_step.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_no_forging.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_earned_commitment_provenance.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_cert_first.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_chan_origin.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_earned_certification_provenance.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_certified_run_min_cost.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_program_certified_min_cost.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_check_pass.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_check_fail.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_commit_pass.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_commit_fail.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_certify_pass.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_certify_fail.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_exec_pay.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_pay_never_fires.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_pay_keeps.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_chain_certifies.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_chain_refused_forever.
Print Assumptions Minimal.EarnedMultiPriced.pu_multi_chain_certifies_iff.
(* === Minimal.EarnedPriced : 80 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EarnedPriced.pr_run_app.
Print Assumptions Minimal.EarnedPriced.pr_run_snoc.
Print Assumptions Minimal.EarnedPriced.pr_total_cost_app.
Print Assumptions Minimal.EarnedPriced.pr_base_blind.
Print Assumptions Minimal.EarnedPriced.pr_run_prog_halted.
Print Assumptions Minimal.EarnedPriced.pr_run_prog_trace.
Print Assumptions Minimal.EarnedPriced.pr_trapped_inert.
Print Assumptions Minimal.EarnedPriced.pr_run_prog_trapped.
Print Assumptions Minimal.EarnedPriced.pr_pay_neutral.
Print Assumptions Minimal.EarnedPriced.pr_pay_exec.
Print Assumptions Minimal.EarnedPriced.pr_pay_never_fires.
Print Assumptions Minimal.EarnedPriced.pr_cexec_embed.
Print Assumptions Minimal.EarnedPriced.pr_exec_embed.
Print Assumptions Minimal.EarnedPriced.pr_cost_embed.
Print Assumptions Minimal.EarnedPriced.pr_run_embed.
Print Assumptions Minimal.EarnedPriced.pr_fetch_map.
Print Assumptions Minimal.EarnedPriced.pr_next_instr_embed.
Print Assumptions Minimal.EarnedPriced.priced_extends_generic.
Print Assumptions Minimal.EarnedPriced.pr_pay_free_is_generic.
Print Assumptions Minimal.EarnedPriced.pr_mu_conservation.
Print Assumptions Minimal.EarnedPriced.pr_mu_conservation_trace.
Print Assumptions Minimal.EarnedPriced.pr_mu_conservation_program.
Print Assumptions Minimal.EarnedPriced.pr_cert_latch.
Print Assumptions Minimal.EarnedPriced.pr_cert_permanent.
Print Assumptions Minimal.EarnedPriced.pr_only_certify_certifies.
Print Assumptions Minimal.EarnedPriced.pr_a2.
Print Assumptions Minimal.EarnedPriced.pr_nfi_floor.
Print Assumptions Minimal.EarnedPriced.pr_ver_mono.
Print Assumptions Minimal.EarnedPriced.pr_ver_same_val.
Print Assumptions Minimal.EarnedPriced.pr_ver_check.
Print Assumptions Minimal.EarnedPriced.pr_val_check.
Print Assumptions Minimal.EarnedPriced.pr_facts_step.
Print Assumptions Minimal.EarnedPriced.pr_facts_keep.
Print Assumptions Minimal.EarnedPriced.pr_full_table_traps.
Print Assumptions Minimal.EarnedPriced.pr_facts_bounded_step.
Print Assumptions Minimal.EarnedPriced.pr_chan_step.
Print Assumptions Minimal.EarnedPriced.pr_unearned_commit_traps.
Print Assumptions Minimal.EarnedPriced.pr_uncommitted_certify_traps.
Print Assumptions Minimal.EarnedPriced.pr_facts_length_step.
Print Assumptions Minimal.EarnedPriced.pr_facts_count.
Print Assumptions Minimal.EarnedPriced.pr_facts_count_clean.
Print Assumptions Minimal.EarnedPriced.pr_facts_count_program.
Print Assumptions Minimal.EarnedPriced.pr_ver_mono_run.
Print Assumptions Minimal.EarnedPriced.pr_untouched_of_ver.
Print Assumptions Minimal.EarnedPriced.pr_untouched_prefix.
Print Assumptions Minimal.EarnedPriced.pr_sound_step.
Print Assumptions Minimal.EarnedPriced.pr_sound_run.
Print Assumptions Minimal.EarnedPriced.pr_checker_soundness.
Print Assumptions Minimal.EarnedPriced.pr_committed_claim_holds.
Print Assumptions Minimal.EarnedPriced.pr_earned_intro.
Print Assumptions Minimal.EarnedPriced.pr_no_forging_step.
Print Assumptions Minimal.EarnedPriced.pr_no_forging.
Print Assumptions Minimal.EarnedPriced.pr_earned_commitment_provenance.
Print Assumptions Minimal.EarnedPriced.pr_cert_first.
Print Assumptions Minimal.EarnedPriced.pr_chan_origin.
Print Assumptions Minimal.EarnedPriced.pr_earned_certification_provenance.
Print Assumptions Minimal.EarnedPriced.pr_certified_run_min_cost.
Print Assumptions Minimal.EarnedPriced.pr_program_certified_min_cost.
Print Assumptions Minimal.EarnedPriced.pr_exec_check_pass.
Print Assumptions Minimal.EarnedPriced.pr_exec_check_fail.
Print Assumptions Minimal.EarnedPriced.pr_exec_commit_pass.
Print Assumptions Minimal.EarnedPriced.pr_chain_certifies.
Print Assumptions Minimal.EarnedPriced.pr_chain_refused_forever.
Print Assumptions Minimal.EarnedPriced.pr_chain_certifies_iff.
Print Assumptions Minimal.EarnedPriced.pr_core_earned_certification_provenance.
Print Assumptions Minimal.EarnedPriced.pr_core_checker_soundness.
Print Assumptions Minimal.EarnedPriced.pr_core_no_forging.
Print Assumptions Minimal.EarnedPriced.pr_core_certified_run_min_cost.
Print Assumptions Minimal.EarnedPriced.pr_core_zero_chain_iff.
Print Assumptions Minimal.EarnedPriced.pr_sorted_earned_certification_provenance.
Print Assumptions Minimal.EarnedPriced.pr_sorted_checker_soundness.
Print Assumptions Minimal.EarnedPriced.pr_sorted_no_forging.
Print Assumptions Minimal.EarnedPriced.pr_sorted_certified_run_min_cost.
Print Assumptions Minimal.EarnedPriced.pr_sorted_committed_claim_holds.
Print Assumptions Minimal.EarnedPriced.pr_sorted_run_certifies_iff.
Print Assumptions Minimal.EarnedPriced.pr_sorted_run_certifies.
Print Assumptions Minimal.EarnedPriced.pr_sorted_run_refused_forever.
Print Assumptions Minimal.EarnedPriced.pr_sorted_demo_certifies.
Print Assumptions Minimal.EarnedPriced.pr_sorted_demo_refused_forever.
Print Assumptions Minimal.EarnedPriced.pr_sorted_paid_demo.
(* === Minimal.EntitlementMore2 : 24 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EntitlementMore2.ent2_sum_split.
Print Assumptions Minimal.EntitlementMore2.ent2_sum_pos.
Print Assumptions Minimal.EntitlementMore2.ent2_sum_le_mul.
Print Assumptions Minimal.EntitlementMore2.ent2_cover_sum_gen.
Print Assumptions Minimal.EntitlementMore2.ent2_cover_sum.
Print Assumptions Minimal.EntitlementMore2.ent2_partition_old_iff.
Print Assumptions Minimal.EntitlementMore2.ent2_partition_to_reduction.
Print Assumptions Minimal.EntitlementMore2.ent2_partition_bits.
Print Assumptions Minimal.EntitlementMore2.ent2_reduction_not_partition.
Print Assumptions Minimal.EntitlementMore2.ent2_mass_uniform.
Print Assumptions Minimal.EntitlementMore2.ent2_weighted_bits.
Print Assumptions Minimal.EntitlementMore2.ent2_wreduction_covers.
Print Assumptions Minimal.EntitlementMore2.ent2_weighted_cs.
Print Assumptions Minimal.EntitlementMore2.ent2_weighted_representation.
Print Assumptions Minimal.EntitlementMore2.ent2_rise_independent.
Print Assumptions Minimal.EntitlementMore2.ent2_expected_rise_exact.
Print Assumptions Minimal.EntitlementMore2.ent2_weighted_expected_bound.
Print Assumptions Minimal.EntitlementMore2.ent2_observed_representation.
Print Assumptions Minimal.EntitlementMore2.ent2_observed_partition_representation.
Print Assumptions Minimal.EntitlementMore2.ent2_record_adds.
Print Assumptions Minimal.EntitlementMore2.ent2_upgrade_iff.
Print Assumptions Minimal.EntitlementMore2.ent2_every_observed_shortcut_lands_here.
Print Assumptions Minimal.EntitlementMore2.ent2_obs_depth.
Print Assumptions Minimal.EntitlementMore2.ent2_observed_small_instance.
(* === Minimal.EntitlementSmall : 61 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EntitlementSmall.ent_complete_depth.
Print Assumptions Minimal.EntitlementSmall.ent_complete_leaves.
Print Assumptions Minimal.EntitlementSmall.ent_leaves_le_pow2.
Print Assumptions Minimal.EntitlementSmall.ent_leaves_pos.
Print Assumptions Minimal.EntitlementSmall.ent_log2_leaves_le_depth.
Print Assumptions Minimal.EntitlementSmall.ent_cover_bits.
Print Assumptions Minimal.EntitlementSmall.ent_narrowing_strengthens.
Print Assumptions Minimal.EntitlementSmall.ent_reduction_covers.
Print Assumptions Minimal.EntitlementSmall.ent_index_bits_le_depth.
Print Assumptions Minimal.EntitlementSmall.ent_two_observations.
Print Assumptions Minimal.EntitlementSmall.ent_exists_covering_tree.
Print Assumptions Minimal.EntitlementSmall.ent_cs_paid_le_bill.
Print Assumptions Minimal.EntitlementSmall.ent_cs_raising_step.
Print Assumptions Minimal.EntitlementSmall.ent_cs_count.
Print Assumptions Minimal.EntitlementSmall.ent_cs_entitlement.
Print Assumptions Minimal.EntitlementSmall.ent_ledger_rise.
Print Assumptions Minimal.EntitlementSmall.ent_complete_tree_bound.
Print Assumptions Minimal.EntitlementSmall.ent_representation.
Print Assumptions Minimal.EntitlementSmall.ent_every_shortcut_lands_here.
Print Assumptions Minimal.EntitlementSmall.ent_bools_eqb_eq.
Print Assumptions Minimal.EntitlementSmall.ent_all_bools_length.
Print Assumptions Minimal.EntitlementSmall.ent_all_bools_complete.
Print Assumptions Minimal.EntitlementSmall.ent_filter_split.
Print Assumptions Minimal.EntitlementSmall.ent_filter_filter_le.
Print Assumptions Minimal.EntitlementSmall.ent_fibres_count.
Print Assumptions Minimal.EntitlementSmall.ent_checked_le_record_moves.
Print Assumptions Minimal.EntitlementSmall.ent_questions_floor.
Print Assumptions Minimal.EntitlementSmall.ent_earned_complete_with.
Print Assumptions Minimal.EntitlementSmall.ent_small_certifies_iff.
Print Assumptions Minimal.EntitlementSmall.ent_small_posterior_is_certified.
Print Assumptions Minimal.EntitlementSmall.ent_small_ledger.
Print Assumptions Minimal.EntitlementSmall.ent_small_reduction.
Print Assumptions Minimal.EntitlementSmall.ent_small_witness.
Print Assumptions Minimal.EntitlementSmall.ent_small_narrowing.
Print Assumptions Minimal.EntitlementSmall.ent_small_certified.
Print Assumptions Minimal.EntitlementSmall.ent_small_realized.
Print Assumptions Minimal.EntitlementSmall.ent_small_instance.
Print Assumptions Minimal.EntitlementSmall.ent_small_lands.
Print Assumptions Minimal.EntitlementSmall.ent_small_questions.
Print Assumptions Minimal.EntitlementSmall.ent_narrow_filter.
Print Assumptions Minimal.EntitlementSmall.ent_narrow_le.
Print Assumptions Minimal.EntitlementSmall.ent_stages_product.
Print Assumptions Minimal.EntitlementSmall.ent_bits_of_cover.
Print Assumptions Minimal.EntitlementSmall.ent_stages_cover.
Print Assumptions Minimal.EntitlementSmall.ent_stages_bits.
Print Assumptions Minimal.EntitlementSmall.ent_stages_share_bits.
Print Assumptions Minimal.EntitlementSmall.ent_test_bits_cover.
Print Assumptions Minimal.EntitlementSmall.ent_stages_after_pos.
Print Assumptions Minimal.EntitlementSmall.ent_stages_round_bits.
Print Assumptions Minimal.EntitlementSmall.ent_passes_le_checked.
Print Assumptions Minimal.EntitlementSmall.ent_passes_sound.
Print Assumptions Minimal.EntitlementSmall.ent_forallb_false.
Print Assumptions Minimal.EntitlementSmall.ent_run_entitlement.
Print Assumptions Minimal.EntitlementSmall.ent_run_round_bits.
Print Assumptions Minimal.EntitlementSmall.ent_cs_run_app.
Print Assumptions Minimal.EntitlementSmall.ent_cs_passes_le.
Print Assumptions Minimal.EntitlementSmall.ent_cs_tested_le_paid.
Print Assumptions Minimal.EntitlementSmall.ent_cs_passes_sound.
Print Assumptions Minimal.EntitlementSmall.ent_cs_run_entitlement.
Print Assumptions Minimal.EntitlementSmall.ent_small_run_narrowing.
Print Assumptions Minimal.EntitlementSmall.ent_share_needed.
(* === Minimal.FragmentSmall : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.FragmentSmall.frag_up_spec.
Print Assumptions Minimal.FragmentSmall.frag_flip_merges.
Print Assumptions Minimal.FragmentSmall.frag_toll_from_merges.
Print Assumptions Minimal.FragmentSmall.frag_fin_finite.
Print Assumptions Minimal.FragmentSmall.frag_fin_permanent.
Print Assumptions Minimal.FragmentSmall.frag_next_injective.
Print Assumptions Minimal.FragmentSmall.frag_stamp_merges.
Print Assumptions Minimal.FragmentSmall.frag_jump_merges.
Print Assumptions Minimal.FragmentSmall.frag_fin_merges_priced.
Print Assumptions Minimal.FragmentSmall.frag_fin_toll.
Print Assumptions Minimal.FragmentSmall.frag_price_is_squeeze.
Print Assumptions Minimal.FragmentSmall.frag_frun_flip_paid.
Print Assumptions Minimal.FragmentSmall.frag_slot_of_nat.
Print Assumptions Minimal.FragmentSmall.frag_in_existsb.
Print Assumptions Minimal.FragmentSmall.frag_exec_commit.
Print Assumptions Minimal.FragmentSmall.frag_live_commit.
Print Assumptions Minimal.FragmentSmall.frag_runs_finite_machine.
Print Assumptions Minimal.FragmentSmall.frag_pays_finite_price.
Print Assumptions Minimal.FragmentSmall.frag_runs_finite_trace.
Print Assumptions Minimal.FragmentSmall.frag_certification_paid.
Print Assumptions Minimal.FragmentSmall.frag_setup_live.
Print Assumptions Minimal.FragmentSmall.frag_program_runs.
Print Assumptions Minimal.FragmentSmall.frag_program_earned.
Print Assumptions Minimal.FragmentSmall.frag_small_certify_merges.
Print Assumptions Minimal.FragmentSmall.frag_small_certifying_step_priced_merge.
Print Assumptions Minimal.FragmentSmall.frag_small_dec_free_merge.
Print Assumptions Minimal.FragmentSmall.frag_small_not_merge_priced.
(* === Minimal.LiftConverse : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.LiftConverse.lift_reduct_universal.
Print Assumptions Minimal.LiftConverse.lift_projection.
Print Assumptions Minimal.LiftConverse.lift_projection_run.
Print Assumptions Minimal.LiftConverse.lift_finite_branching_not_complete.
Print Assumptions Minimal.LiftConverse.lift_stateless_two_moves.
Print Assumptions Minimal.LiftConverse.lift_stateless_not_complete.
Print Assumptions Minimal.LiftConverse.lift_ub_not_finitely_branching.
Print Assumptions Minimal.LiftConverse.lift_finite_moves_not_a_base.
Print Assumptions Minimal.LiftConverse.lift_canonical_nonvac_iff.
(* === Minimal.LiftCore : 38 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.LiftCore.lift_lfact_eqb_eq.
Print Assumptions Minimal.LiftCore.lift_lrun_nil.
Print Assumptions Minimal.LiftCore.lift_lrun_cons.
Print Assumptions Minimal.LiftCore.lift_lrun_app.
Print Assumptions Minimal.LiftCore.lift_lrun_snoc.
Print Assumptions Minimal.LiftCore.lift_mu_step.
Print Assumptions Minimal.LiftCore.lift_cert_permanent.
Print Assumptions Minimal.LiftCore.lift_base_blind.
Print Assumptions Minimal.LiftCore.lift_cert_raise.
Print Assumptions Minimal.LiftCore.lift_ver_mono.
Print Assumptions Minimal.LiftCore.lift_ver_eq_base.
Print Assumptions Minimal.LiftCore.lift_ver_mono_run.
Print Assumptions Minimal.LiftCore.lift_ver_eq_base_run.
Print Assumptions Minimal.LiftCore.lift_facts_step.
Print Assumptions Minimal.LiftCore.lift_chan_step.
Print Assumptions Minimal.LiftCore.lift_facts_prov.
Print Assumptions Minimal.LiftCore.lift_chan_prov.
Print Assumptions Minimal.LiftCore.lift_cert_first.
Print Assumptions Minimal.LiftCore.lift_sim.
Print Assumptions Minimal.LiftCore.lift_step_err.
Print Assumptions Minimal.LiftCore.lift_step_check_ok.
Print Assumptions Minimal.LiftCore.lift_step_check_fail.
Print Assumptions Minimal.LiftCore.lift_step_commit_ok.
Print Assumptions Minimal.LiftCore.lift_step_certify_ok.
Print Assumptions Minimal.LiftCore.lift_base_clause.
Print Assumptions Minimal.LiftCore.lift_earned_chain.
Print Assumptions Minimal.LiftCore.lift_earned_clause.
Print Assumptions Minimal.LiftCore.lift_toll_clause.
Print Assumptions Minimal.LiftCore.lift_chain_true.
Print Assumptions Minimal.LiftCore.lift_run_err.
Print Assumptions Minimal.LiftCore.lift_chain_false.
Print Assumptions Minimal.LiftCore.lift_nonvac_clause.
Print Assumptions Minimal.LiftCore.lift_thiele_complete_with.
Print Assumptions Minimal.LiftCore.lift_thiele_complete.
Print Assumptions Minimal.LiftCore.lift_wc_eqb_eq.
Print Assumptions Minimal.LiftCore.lift_wc_eval_iff.
Print Assumptions Minimal.LiftCore.lift_window_nonvacuous.
Print Assumptions Minimal.LiftCore.lift_window_thiele_complete.
(* === Minimal.LiftMacro : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.LiftMacro.sim_macro_runs.
Print Assumptions Minimal.LiftMacro.ub_to_sim_inhabited.
Print Assumptions Minimal.LiftMacro.sim_to_macro_inhabited.
Print Assumptions Minimal.LiftMacro.sim_base_lifts.
Print Assumptions Minimal.LiftMacro.fl_run_tgt.
Print Assumptions Minimal.LiftMacro.fl_no_universal_base.
Print Assumptions Minimal.LiftMacro.fl_has_sim_base.
Print Assumptions Minimal.LiftMacro.fl_macro_lifts.
(* === Minimal.LiftOneCounter : 25 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.LiftOneCounter.lift_oc_f_some.
Print Assumptions Minimal.LiftOneCounter.lift_oc_f_none.
Print Assumptions Minimal.LiftOneCounter.lift_oc_iter_fixed.
Print Assumptions Minimal.LiftOneCounter.lift_oc_run_iter.
Print Assumptions Minimal.LiftOneCounter.lift_cf_succ.
Print Assumptions Minimal.LiftOneCounter.lift_cf_add.
Print Assumptions Minimal.LiftOneCounter.lift_stopped_stays.
Print Assumptions Minimal.LiftOneCounter.lift_alive_down.
Print Assumptions Minimal.LiftOneCounter.lift_alive_pc.
Print Assumptions Minimal.LiftOneCounter.lift_alive_iff_pc.
Print Assumptions Minimal.LiftOneCounter.lift_cnt_step.
Print Assumptions Minimal.LiftOneCounter.lift_rep_never.
Print Assumptions Minimal.LiftOneCounter.lift_bounded_never.
Print Assumptions Minimal.LiftOneCounter.lift_oc_pos_shift.
Print Assumptions Minimal.LiftOneCounter.lift_oc_posrun_shift.
Print Assumptions Minimal.LiftOneCounter.lift_oc_bounded_dec.
Print Assumptions Minimal.LiftOneCounter.lift_oc_greatest_below.
Print Assumptions Minimal.LiftOneCounter.lift_oc_first_spec.
Print Assumptions Minimal.LiftOneCounter.lift_oc_ivt.
Print Assumptions Minimal.LiftOneCounter.lift_oc_caseB.
Print Assumptions Minimal.LiftOneCounter.lift_oc_halts_bound.
Print Assumptions Minimal.LiftOneCounter.lift_oc_halts_dec.
Print Assumptions Minimal.LiftOneCounter.lift_oc_embed_step.
Print Assumptions Minimal.LiftOneCounter.lift_oc_embed_run.
Print Assumptions Minimal.LiftOneCounter.lift_oc_embed_halts.
(* === Minimal.LiftPigeon : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.LiftPigeon.lift_pigeon_dec.
Print Assumptions Minimal.LiftPigeon.lift_inj_le.
Print Assumptions Minimal.LiftPigeon.lift_pigeon.
(* === Minimal.MonotoneConsensus : 35 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.MonotoneConsensus.mc_run_app.
Print Assumptions Minimal.MonotoneConsensus.mc_loc_set_same.
Print Assumptions Minimal.MonotoneConsensus.mc_loc_set_other.
Print Assumptions Minimal.MonotoneConsensus.mc_obj_set.
Print Assumptions Minimal.MonotoneConsensus.mc_step_other.
Print Assumptions Minimal.MonotoneConsensus.mc_step_local.
Print Assumptions Minimal.MonotoneConsensus.mc_solo_local.
Print Assumptions Minimal.MonotoneConsensus.mc_decided_step_same.
Print Assumptions Minimal.MonotoneConsensus.mc_negb_neq.
Print Assumptions Minimal.MonotoneConsensus.mc_decided_keep_step.
Print Assumptions Minimal.MonotoneConsensus.mc_decided_keep.
Print Assumptions Minimal.MonotoneConsensus.mc_count_app.
Print Assumptions Minimal.MonotoneConsensus.mc_count_repeat.
Print Assumptions Minimal.MonotoneConsensus.mc_count_one.
Print Assumptions Minimal.MonotoneConsensus.mc_solo_decides.
Print Assumptions Minimal.MonotoneConsensus.mc_biv_undecided.
Print Assumptions Minimal.MonotoneConsensus.mc_undecided_count.
Print Assumptions Minimal.MonotoneConsensus.mc_vals_cases.
Print Assumptions Minimal.MonotoneConsensus.mc_find_crit.
Print Assumptions Minimal.MonotoneConsensus.mc_decided_loc.
Print Assumptions Minimal.MonotoneConsensus.mc_clash.
Print Assumptions Minimal.MonotoneConsensus.mc_step_upd.
Print Assumptions Minimal.MonotoneConsensus.mc_step_read.
Print Assumptions Minimal.MonotoneConsensus.mc_run_snoc.
Print Assumptions Minimal.MonotoneConsensus.mc_crit_false.
Print Assumptions Minimal.MonotoneConsensus.mc_init_biv.
Print Assumptions Minimal.MonotoneConsensus.mc_contradiction.
Print Assumptions Minimal.MonotoneConsensus.mc_no_consensus.
Print Assumptions Minimal.MonotoneConsensus.mc_upd2_comm.
Print Assumptions Minimal.MonotoneConsensus.mc_updr_comm.
Print Assumptions Minimal.MonotoneConsensus.mc_updr_over.
Print Assumptions Minimal.MonotoneConsensus.mc_guard_mono.
Print Assumptions Minimal.MonotoneConsensus.mc_eff_rel.
Print Assumptions Minimal.MonotoneConsensus.mc_mono_interfere.
Print Assumptions Minimal.MonotoneConsensus.mc_mono_no_consensus.
(* === Minimal.MultiThiele2 : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.MultiThiele2.ent2_run_mmachine.
Print Assumptions Minimal.MultiThiele2.ent2_msim.
Print Assumptions Minimal.MultiThiele2.ent2_untouched_prefix.
Print Assumptions Minimal.MultiThiele2.ent2_prop_eqb_eq.
Print Assumptions Minimal.MultiThiele2.ent2_chain_same.
Print Assumptions Minimal.MultiThiele2.ent2_chain_holds.
Print Assumptions Minimal.MultiThiele2.ent2_mmachine_complete.
(* === Minimal.NecEEnt : 47 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecEEnt.nec_e_cover_bits_any.
Print Assumptions Minimal.NecEEnt.nec_e_cs_count_any.
Print Assumptions Minimal.NecEEnt.nec_e_weighted_bits_any.
Print Assumptions Minimal.NecEEnt.nec_e_reduction_post_pos.
Print Assumptions Minimal.NecEEnt.nec_e_cs_entitlement_stronger.
Print Assumptions Minimal.NecEEnt.nec_e_cs_entitlement_from_stronger.
Print Assumptions Minimal.NecEEnt.nec_e_ecs_run.
Print Assumptions Minimal.NecEEnt.nec_e_bits16.
Print Assumptions Minimal.NecEEnt.nec_e_not_strict_if_equal.
Print Assumptions Minimal.NecEEnt.nec_e_red16.
Print Assumptions Minimal.NecEEnt.nec_e_red2.
Print Assumptions Minimal.NecEEnt.nec_e_w16.
Print Assumptions Minimal.NecEEnt.nec_e_w2.
Print Assumptions Minimal.NecEEnt.nec_e_sub16.
Print Assumptions Minimal.NecEEnt.nec_e_sub2.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_eqb_sound.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_eqb_refl.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_inclusion.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_distinguishing.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_covering.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_paid_depth.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_start_no.
Print Assumptions Minimal.NecEEnt.nec_e_cs_needs_end_yes.
Print Assumptions Minimal.NecEEnt.nec_e_commits.
Print Assumptions Minimal.NecEEnt.nec_e_runk_cert.
Print Assumptions Minimal.NecEEnt.nec_e_paid_runk.
Print Assumptions Minimal.NecEEnt.nec_e_bill_runk.
Print Assumptions Minimal.NecEEnt.nec_e_seq_bits.
Print Assumptions Minimal.NecEEnt.nec_e_pow_ge2.
Print Assumptions Minimal.NecEEnt.nec_e_cs_tight.
Print Assumptions Minimal.NecEEnt.nec_e_representation_stronger.
Print Assumptions Minimal.NecEEnt.nec_e_observed_stronger.
Print Assumptions Minimal.NecEEnt.nec_e_earned_complete.
Print Assumptions Minimal.NecEEnt.nec_e_chain_len.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_depth.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_covering.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_clean.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_record.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_distinguishing.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_eqb.
Print Assumptions Minimal.NecEEnt.nec_e_rep_needs_inclusion.
Print Assumptions Minimal.NecEEnt.nec_e_mrun_run.
Print Assumptions Minimal.NecEEnt.nec_e_record_moves_mrun.
Print Assumptions Minimal.NecEEnt.nec_e_rep_tight.
Print Assumptions Minimal.NecEEnt.nec_e_pay_without_narrowing.
Print Assumptions Minimal.NecEEnt.nec_e_questions_floor_stronger.
Print Assumptions Minimal.NecEEnt.nec_e_tree_full_iff.
(* === Minimal.NecESearch : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecESearch.nec_e_search_needs_a_question.
Print Assumptions Minimal.NecESearch.nec_e_questions_cap_tight.
Print Assumptions Minimal.NecESearch.nec_e_time_tax_one_paid_move.
Print Assumptions Minimal.NecESearch.nec_e_time_tax_free_needed.
(* === Minimal.NecSChain : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecSChain.nec_s_chain_costs_three.
Print Assumptions Minimal.NecSChain.nec_s_cert_provenance_needs_clean.
(* === Minimal.NecSClean : 31 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecSClean.nec_s_run_trapped.
Print Assumptions Minimal.NecSClean.nec_s_total_cost_incs.
Print Assumptions Minimal.NecSClean.nec_s_inc_step.
Print Assumptions Minimal.NecSClean.nec_s_dec_step.
Print Assumptions Minimal.NecSClean.nec_s_run_incs.
Print Assumptions Minimal.NecSClean.nec_s_run_decs.
Print Assumptions Minimal.NecSClean.nec_s_clean_conjuncts_each_buy_one.
Print Assumptions Minimal.NecSClean.nec_s_floor_two.
Print Assumptions Minimal.NecSClean.nec_s_min_cost_needs_flag_down.
Print Assumptions Minimal.NecSClean.nec_s_min_cost_needs_empty_channel.
Print Assumptions Minimal.NecSClean.nec_s_min_cost_needs_empty_table.
Print Assumptions Minimal.NecSClean.nec_s_old_or_earned.
Print Assumptions Minimal.NecSClean.nec_s_stale_commitment_provenance.
Print Assumptions Minimal.NecSClean.nec_s_stale_certification_provenance.
Print Assumptions Minimal.NecSClean.nec_s_stale_min_cost.
Print Assumptions Minimal.NecSClean.nec_s_clean_is_stale.
Print Assumptions Minimal.NecSClean.nec_s_nonstale_cheap.
Print Assumptions Minimal.NecSClean.nec_s_floor3_iff.
Print Assumptions Minimal.NecSClean.nec_s_witness_from_every_clean_start.
Print Assumptions Minimal.NecSClean.nec_s_clean_certifiable_iff_untrapped.
Print Assumptions Minimal.NecSClean.nec_s_soundness_from_sound.
Print Assumptions Minimal.NecSClean.nec_s_clean_is_sound.
Print Assumptions Minimal.NecSClean.nec_s_soundness_needs_live_half.
Print Assumptions Minimal.NecSClean.nec_s_soundness_needs_no_future_half.
Print Assumptions Minimal.NecSClean.nec_s_sound_or_trivial_step.
Print Assumptions Minimal.NecSClean.nec_s_sound_or_trivial_run.
Print Assumptions Minimal.NecSClean.nec_s_sound_not_necessary.
Print Assumptions Minimal.NecSClean.nec_s_stale_fact_false.
Print Assumptions Minimal.NecSClean.nec_s_soundness_needs_live_version.
Print Assumptions Minimal.NecSClean.nec_s_no_forging_iff.
Print Assumptions Minimal.NecSClean.nec_s_commitment_provenance_needs_table.
(* === Minimal.NecSHost : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecSHost.nec_s_universal_needs_untrapped.
Print Assumptions Minimal.NecSHost.nec_s_U_round_phase.
Print Assumptions Minimal.NecSHost.nec_s_U_any_phase.
Print Assumptions Minimal.NecSHost.nec_s_U_line_one.
Print Assumptions Minimal.NecSHost.nec_s_U_off_phase_stuck.
Print Assumptions Minimal.NecSHost.nec_s_phase_dec.
Print Assumptions Minimal.NecSHost.nec_s_U_phase_iff.
Print Assumptions Minimal.NecSHost.nec_s_hexec_guest_cert.
Print Assumptions Minimal.NecSHost.nec_s_disagreement_persists.
Print Assumptions Minimal.NecSHost.nec_s_mirror_needs_agreement.
Print Assumptions Minimal.NecSHost.nec_s_simulated_record_needs_untrapped.
Print Assumptions Minimal.NecSHost.nec_s_host_toll_needs_untrapped.
Print Assumptions Minimal.NecSHost.nec_s_host_cost_cover_tight.
Print Assumptions Minimal.NecSHost.nec_s_host_toll_attained.
Print Assumptions Minimal.NecSHost.nec_s_mirror_rise_iff.
Print Assumptions Minimal.NecSHost.nec_s_own_rise_iff.
Print Assumptions Minimal.NecSHost.nec_s_guestless_converse_false.
Print Assumptions Minimal.NecSHost.nec_s_mirror_earned_needs_load.
(* === Minimal.NecSNoCopy : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecSNoCopy.nec_s_prop_eqb_eq.
Print Assumptions Minimal.NecSNoCopy.nec_s_id_sound.
Print Assumptions Minimal.NecSNoCopy.nec_s_id_no_collision.
Print Assumptions Minimal.NecSNoCopy.nec_s_id_not_finite.
Print Assumptions Minimal.NecSNoCopy.nec_s_id_host_pair_traps.
Print Assumptions Minimal.NecSNoCopy.nec_s_nocopy_needs_finite_Q.
Print Assumptions Minimal.NecSNoCopy.nec_s_nocopy_needs_sound_translation.
Print Assumptions Minimal.NecSNoCopy.nec_s_guest_check_passes_iff.
(* === Minimal.NecSWindow : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecSWindow.nec_s_separation_any_clean_start.
Print Assumptions Minimal.NecSWindow.nec_s_same_ledger_different_flag.
Print Assumptions Minimal.NecSWindow.nec_s_no_flag_oracle_even_with_ledger.
Print Assumptions Minimal.NecSWindow.nec_s_no_mu_oracle_any_state.
Print Assumptions Minimal.NecSWindow.nec_s_total_cost_decs.
Print Assumptions Minimal.NecSWindow.nec_s_reach_window.
Print Assumptions Minimal.NecSWindow.nec_s_cert_oracle_iff.
Print Assumptions Minimal.NecSWindow.nec_s_clean_cert_oracle_iff_trapped.
Print Assumptions Minimal.NecSWindow.nec_s_clean_commit_oracle_iff_trapped.
Print Assumptions Minimal.NecSWindow.nec_s_only_order_certifies.
Print Assumptions Minimal.NecSWindow.nec_s_commit_refuses_true_stale.
Print Assumptions Minimal.NecSWindow.nec_s_versioned_refuses.
Print Assumptions Minimal.NecSWindow.nec_s_versionless_unsound.
Print Assumptions Minimal.NecSWindow.nec_s_simulation_needs_trap_down.
Print Assumptions Minimal.NecSWindow.nec_s_toll_without_permanence.
Print Assumptions Minimal.NecSWindow.nec_s_table_bound_attained.
Print Assumptions Minimal.NecSWindow.nec_s_refused_from_any_flag_down_state.
Print Assumptions Minimal.NecSWindow.nec_s_refused_any_continuation.
(* === Minimal.NecTEarned : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTEarned.zap_run_some.
Print Assumptions Minimal.NecTEarned.nec_t_zap_meets_all_but_chain.
Print Assumptions Minimal.NecTEarned.nec_t_zap_not_thiele_complete.
(* === Minimal.NecTGeneric : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTGeneric.nec_t_a1_iff_free_given_toll.
Print Assumptions Minimal.NecTGeneric.nec_t_clean_runs_need_three_moves.
Print Assumptions Minimal.NecTGeneric.nec_t_costs_zero_and_one_attained.
Print Assumptions Minimal.NecTGeneric.nec_t_generic_needs_varying_property.
Print Assumptions Minimal.NecTGeneric.nec_t_generic_needs_exact_eval.
Print Assumptions Minimal.NecTGeneric.nec_t_generic_needs_exact_eqb.
(* === Minimal.NecTLoop : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTLoop.strip_app.
Print Assumptions Minimal.NecTLoop.loop_run.
Print Assumptions Minimal.NecTLoop.strip_split.
Print Assumptions Minimal.NecTLoop.nec_t_loop_meets_all_but_ledger.
Print Assumptions Minimal.NecTLoop.nec_t_loop_not_thiele_complete.
(* === Minimal.NecTLoose : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTLoose.nec_t_certificate_three_attained.
Print Assumptions Minimal.NecTLoose.nec_t_complete_is_loose.
Print Assumptions Minimal.NecTLoose.nb_allnop.
Print Assumptions Minimal.NecTLoose.nb_nops.
Print Assumptions Minimal.NecTLoose.nb_dead.
Print Assumptions Minimal.NecTLoose.nb_N.
Print Assumptions Minimal.NecTLoose.nb_M.
Print Assumptions Minimal.NecTLoose.nb_K.
Print Assumptions Minimal.NecTLoose.nb_Z.
Print Assumptions Minimal.NecTLoose.nb_in_nbn.
Print Assumptions Minimal.NecTLoose.nb_chain_run.
Print Assumptions Minimal.NecTLoose.nec_t_nb_loose_complete.
Print Assumptions Minimal.NecTLoose.nec_t_nb_not_thiele_complete.
(* === Minimal.NecTPartition : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTPartition.nec_t_rel_of_partition_equiv.
Print Assumptions Minimal.NecTPartition.nec_t_blocks_of_equiv_partition.
Print Assumptions Minimal.NecTPartition.nec_t_rel_round_trip.
Print Assumptions Minimal.NecTPartition.nec_t_blocks_round_trip.
Print Assumptions Minimal.NecTPartition.nec_t_nonempty_needed.
Print Assumptions Minimal.NecTPartition.nec_t_cover_needed.
Print Assumptions Minimal.NecTPartition.nec_t_disjoint_needed.
(* === Minimal.NecTToll : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTToll.run_cm.
Print Assumptions Minimal.NecTToll.earned_chain_cm.
Print Assumptions Minimal.NecTToll.nec_t_doubled_cost_meets_all_but_toll.
Print Assumptions Minimal.NecTToll.nec_t_ledgerless_meets_all_but_ledger.
Print Assumptions Minimal.NecTToll.nec_t_unsound_check_meets_all_but_soundness.
Print Assumptions Minimal.NecTToll.nec_t_same_true_meets_all_but_respect.
(* === Minimal.NecTUnclean : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTUnclean.un_run_inl.
Print Assumptions Minimal.NecTUnclean.un_complete.
Print Assumptions Minimal.NecTUnclean.nec_t_unclean_start_breaks_only_certify.
(* === Minimal.NecTVerifier : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTVerifier.nec_t_ver_exists_implies_collision_free.
Print Assumptions Minimal.NecTVerifier.nec_t_ver_collision_free_implies_exists.
Print Assumptions Minimal.NecTVerifier.nec_t_ver_exists_iff_collision_free.
Print Assumptions Minimal.NecTVerifier.nec_t_clock_has_bare_verifier.
Print Assumptions Minimal.NecTVerifier.nec_t_weak_does_not_suffice.
(* === Minimal.PartitionReading : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.PartitionReading.pr_grouping_partition.
Print Assumptions Minimal.PartitionReading.same_part_sym.
Print Assumptions Minimal.PartitionReading.same_part_trans.
Print Assumptions Minimal.PartitionReading.sound_same_part.
Print Assumptions Minimal.PartitionReading.sound_refines.
Print Assumptions Minimal.PartitionReading.pr_entitled_iff_refines.
Print Assumptions Minimal.PartitionReading.pairs_ok_iff.
Print Assumptions Minimal.PartitionReading.sound_b_iff.
Print Assumptions Minimal.PartitionReading.same_part_b_iff.
Print Assumptions Minimal.PartitionReading.pr_reads_structural.
Print Assumptions Minimal.PartitionReading.p_inv_step.
Print Assumptions Minimal.PartitionReading.p_inv_run.
Print Assumptions Minimal.PartitionReading.p_inv_clean.
Print Assumptions Minimal.PartitionReading.pr_reading_entitles.
Print Assumptions Minimal.PartitionReading.pr_reading_entitles_only.
Print Assumptions Minimal.PartitionReading.pr_toll.
Print Assumptions Minimal.PartitionReading.p_cinv_step.
Print Assumptions Minimal.PartitionReading.pr_reading_costs_three.
(* === Minimal.PayFree : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.PayFree.pf_err_latch.
Print Assumptions Minimal.PayFree.pf_cert_latch.
Print Assumptions Minimal.PayFree.pf_existsb_in.
Print Assumptions Minimal.PayFree.pf_step.
Print Assumptions Minimal.PayFree.pf_err_before.
Print Assumptions Minimal.PayFree.pf_rep_same.
Print Assumptions Minimal.PayFree.pf_bound.
Print Assumptions Minimal.PayFree.pf_bound_start.
Print Assumptions Minimal.PayFree.pf_no_repeat_bound.
(* === Minimal.Presented : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Presented.presented_scode_inj.
Print Assumptions Minimal.Presented.presented_icode_inj.
Print Assumptions Minimal.Presented.presented_run_halted.
Print Assumptions Minimal.Presented.mledger_halted.
Print Assumptions Minimal.Presented.presented_run_add.
Print Assumptions Minimal.Presented.mledger_add.
Print Assumptions Minimal.Presented.presented_run_succ.
Print Assumptions Minimal.Presented.mledger_succ.
Print Assumptions Minimal.Presented.presented_halted_stable.
Print Assumptions Minimal.Presented.presented_mlatch_iff.
Print Assumptions Minimal.Presented.presented_mlatch_mono.
Print Assumptions Minimal.Presented.presented_mlatch_succ.
Print Assumptions Minimal.Presented.presented_first_raise_spec.
Print Assumptions Minimal.Presented.presented_first_raise_stable.
Print Assumptions Minimal.Presented.presented_raise_cost_le_ledger.
Print Assumptions Minimal.Presented.presented_surcharge_le_two.
Print Assumptions Minimal.Presented.presented_surcharge_zero_before_raise.
Print Assumptions Minimal.Presented.presented_surcharge_raised_at_start.
Print Assumptions Minimal.Presented.presented_surcharge_stable.
Print Assumptions Minimal.Presented.presented_surcharge_sufficient.
Print Assumptions Minimal.Presented.presented_no_exact_below_three.
Print Assumptions Minimal.Presented.presented_no_exact_below_three_program.
Print Assumptions Minimal.Presented.presented_extra_at_least.
Print Assumptions Minimal.Presented.presented_flip_sdec.
Print Assumptions Minimal.Presented.presented_flip_idec.
Print Assumptions Minimal.Presented.presented_flip_facts.
Print Assumptions Minimal.Presented.presented_flip_no_exact.
(* === Minimal.PricedComplete : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.PricedComplete.priced_run_eq.
Print Assumptions Minimal.PricedComplete.priced_toll.
Print Assumptions Minimal.PricedComplete.priced_sim.
Print Assumptions Minimal.PricedComplete.priced_pay_reads_as_failed_check.
Print Assumptions Minimal.PricedComplete.priced_chain_holds.
Print Assumptions Minimal.PricedComplete.priced_chain_iff.
Print Assumptions Minimal.PricedComplete.priced_thiele_complete_with.
Print Assumptions Minimal.PricedComplete.priced_thiele_complete.
Print Assumptions Minimal.PricedComplete.priced_sorted_thiele_complete.
Print Assumptions Minimal.PricedComplete.priced_core_thiele_complete.
(* === Minimal.RecordMerge : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.RecordMerge.rm_fact_eqb_refl.
Print Assumptions Minimal.RecordMerge.rm_commit_lands.
Print Assumptions Minimal.RecordMerge.rm_commit_merges.
Print Assumptions Minimal.RecordMerge.rm_merge_price_charges_record_moves.
Print Assumptions Minimal.RecordMerge.rm_toll_from_any_merge_price.
Print Assumptions Minimal.RecordMerge.rm_merge_price_gives_record_price.
Print Assumptions Minimal.RecordMerge.rm_certify_record_merge.
Print Assumptions Minimal.RecordMerge.rm_commit_record_merge.
Print Assumptions Minimal.RecordMerge.rm_base_core.
Print Assumptions Minimal.RecordMerge.rm_core_eq.
Print Assumptions Minimal.RecordMerge.rm_base_moves_no_record_merge.
Print Assumptions Minimal.RecordMerge.rm_small_record_priced.
Print Assumptions Minimal.RecordMerge.rm_toll_from_record_price.
Print Assumptions Minimal.RecordMerge.rm_record_price_and_exact_toll.
(* === Minimal.SmCodes : 23 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmCodes.sm_hb_correct.
Print Assumptions Minimal.SmCodes.sm_hb_unique.
Print Assumptions Minimal.SmCodes.sm_hb_spec.
Print Assumptions Minimal.SmCodes.sm_unp_eq.
Print Assumptions Minimal.SmCodes.sm_unpair_eq.
Print Assumptions Minimal.SmCodes.sm_unpair_pair.
Print Assumptions Minimal.SmCodes.sm_unpair_zero.
Print Assumptions Minimal.SmCodes.sm_pair_ge.
Print Assumptions Minimal.SmCodes.sm_lencode_ge.
Print Assumptions Minimal.SmCodes.sm_ldec_encode.
Print Assumptions Minimal.SmCodes.sm_ldecode_encode.
Print Assumptions Minimal.SmCodes.sm_kdec_kcode.
Print Assumptions Minimal.SmCodes.sm_kpdec_kpcode.
Print Assumptions Minimal.SmCodes.sm_of_to_ki.
Print Assumptions Minimal.SmCodes.sm_to_of_ki.
Print Assumptions Minimal.SmCodes.sm_map_of_to.
Print Assumptions Minimal.SmCodes.sm_map_to_of.
Print Assumptions Minimal.SmCodes.sm_hdecode_hcode.
Print Assumptions Minimal.SmCodes.sm_hcode_of.
Print Assumptions Minimal.SmCodes.sm_hcode_inj.
Print Assumptions Minimal.SmCodes.sm_kreloc_of.
Print Assumptions Minimal.SmCodes.sm_kspec_prog_of.
Print Assumptions Minimal.SmCodes.sm_kspec_code.
(* === Minimal.SmHostBlocks : 34 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmHostBlocks.sm_hagree_sym.
Print Assumptions Minimal.SmHostBlocks.sm_hequiv_sym.
Print Assumptions Minimal.SmHostBlocks.sm_hequiv_hfun.
Print Assumptions Minimal.SmHostBlocks.sm_step_core.
Print Assumptions Minimal.SmHostBlocks.sm_run_add.
Print Assumptions Minimal.SmHostBlocks.sm_run_succ.
Print Assumptions Minimal.SmHostBlocks.sm_halted_stay.
Print Assumptions Minimal.SmHostBlocks.sm_halted_after.
Print Assumptions Minimal.SmHostBlocks.sm_hends_unique.
Print Assumptions Minimal.SmHostBlocks.sm_hfun_det.
Print Assumptions Minimal.SmHostBlocks.sm_reloc_length.
Print Assumptions Minimal.SmHostBlocks.sm_embeds_app.
Print Assumptions Minimal.SmHostBlocks.sm_fetch_app_past.
Print Assumptions Minimal.SmHostBlocks.sm_fetch_app_left.
Print Assumptions Minimal.SmHostBlocks.sm_fetch_range.
Print Assumptions Minimal.SmHostBlocks.sm_fetch_out.
Print Assumptions Minimal.SmHostBlocks.sm_rj_in.
Print Assumptions Minimal.SmHostBlocks.sm_rj_out.
Print Assumptions Minimal.SmHostBlocks.sm_rj_S.
Print Assumptions Minimal.SmHostBlocks.sm_cost_ri.
Print Assumptions Minimal.SmHostBlocks.sm_ri_halt.
Print Assumptions Minimal.SmHostBlocks.sm_next_some.
Print Assumptions Minimal.SmHostBlocks.sm_next_intro.
Print Assumptions Minimal.SmHostBlocks.sm_block_cstep.
Print Assumptions Minimal.SmHostBlocks.sm_fires_ri.
Print Assumptions Minimal.SmHostBlocks.sm_block_step.
Print Assumptions Minimal.SmHostBlocks.sm_block_run_mid.
Print Assumptions Minimal.SmHostBlocks.sm_block_not_halted.
Print Assumptions Minimal.SmHostBlocks.sm_block_halted.
Print Assumptions Minimal.SmHostBlocks.sm_block_run_final.
Print Assumptions Minimal.SmHostBlocks.sm_plain_exec.
Print Assumptions Minimal.SmHostBlocks.sm_incs_length.
Print Assumptions Minimal.SmHostBlocks.sm_incs_run.
Print Assumptions Minimal.SmHostBlocks.sm_clear_run.
(* === Minimal.SmInterp : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmInterp.sm_lset_nth.
Print Assumptions Minimal.SmInterp.sm_kheval_eq.
Print Assumptions Minimal.SmInterp.sm_kmem_eq.
Print Assumptions Minimal.SmInterp.sm_fetch_of.
Print Assumptions Minimal.SmInterp.sm_krel_halted.
Print Assumptions Minimal.SmInterp.sm_write_rel.
Print Assumptions Minimal.SmInterp.sm_krel_step.
Print Assumptions Minimal.SmInterp.sm_core_run.
Print Assumptions Minimal.SmInterp.sm_krel_run.
Print Assumptions Minimal.SmInterp.sm_krel_start.
Print Assumptions Minimal.SmInterp.sm_kout_hfun.
Print Assumptions Minimal.SmInterp.sm_kstep_halted.
Print Assumptions Minimal.SmInterp.sm_krun_halted.
Print Assumptions Minimal.SmInterp.sm_krun_add.
Print Assumptions Minimal.SmInterp.sm_kout_mono.
Print Assumptions Minimal.SmInterp.sm_uev_spec.
Print Assumptions Minimal.SmInterp.sm_uev_mono.
Print Assumptions Minimal.SmInterp.sm_ev_mono.
Print Assumptions Minimal.SmInterp.sm_ev_spec.
(* === Minimal.SmLoops : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmLoops.sm2_RR_trans.
Print Assumptions Minimal.SmLoops.sm2_RR_one.
Print Assumptions Minimal.SmLoops.sm2_RR_run.
Print Assumptions Minimal.SmLoops.sm2_RR_steps.
Print Assumptions Minimal.SmLoops.sm2_RR_last.
Print Assumptions Minimal.SmLoops.sm2_pfe_refl.
Print Assumptions Minimal.SmLoops.sm2_pfe_trans.
Print Assumptions Minimal.SmLoops.sm2_pfe_sym.
Print Assumptions Minimal.SmLoops.sm2_fetch_next.
Print Assumptions Minimal.SmLoops.sm2_step_inc.
Print Assumptions Minimal.SmLoops.sm2_step_dec_pos.
Print Assumptions Minimal.SmLoops.sm2_step_dec_zero.
Print Assumptions Minimal.SmLoops.sm2_whilel_length.
Print Assumptions Minimal.SmLoops.sm2_inQ_app.
Print Assumptions Minimal.SmLoops.sm2_loose_trans.
Print Assumptions Minimal.SmLoops.sm2_while_exit.
Print Assumptions Minimal.SmLoops.sm2_while_trip.
Print Assumptions Minimal.SmLoops.sm2_while.
Print Assumptions Minimal.SmLoops.sm2_incs_chain.
(* === Minimal.SmLoops2 : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmLoops2.sm2_nth_tail.
Print Assumptions Minimal.SmLoops2.sm2_nth_mid.
Print Assumptions Minimal.SmLoops2.sm2_whilel_fetch.
Print Assumptions Minimal.SmLoops2.sm2_count_nil.
Print Assumptions Minimal.SmLoops2.sm2_fan_spec.
Print Assumptions Minimal.SmLoops2.sm2_step_check_ok.
Print Assumptions Minimal.SmLoops2.sm2_step_commit_ok.
Print Assumptions Minimal.SmLoops2.sm2_step_certify_ok.
Print Assumptions Minimal.SmLoops2.sm2_step_check_fail.
Print Assumptions Minimal.SmLoops2.sm2_check_loop.
(* === Minimal.SmLoops3 : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmLoops3.sm2_commit_loop.
Print Assumptions Minimal.SmLoops3.sm2_certify_loop.
Print Assumptions Minimal.SmLoops3.sm2_trapg_length.
Print Assumptions Minimal.SmLoops3.sm2_trap_zero.
Print Assumptions Minimal.SmLoops3.sm2_trap_pos.
(* === Minimal.SmTally : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmTally.sm2_cost_eq.
Print Assumptions Minimal.SmTally.sm2_rel_step.
Print Assumptions Minimal.SmTally.sm2_krun_rel.
Print Assumptions Minimal.SmTally.sm2_rel_start.
Print Assumptions Minimal.SmTally.sm2_comp_rel.
Print Assumptions Minimal.SmTally.sm2_krun_halted.
Print Assumptions Minimal.SmTally.sm2_krun_add.
Print Assumptions Minimal.SmTally.sm2_tal_mono.
Print Assumptions Minimal.SmTally.sm2_tal_real.
Print Assumptions Minimal.SmTally.sm2_inv_start.
Print Assumptions Minimal.SmTally.sm2_inv_exec.
Print Assumptions Minimal.SmTally.sm2_inv_step.
Print Assumptions Minimal.SmTally.sm2_reach_inv.
Print Assumptions Minimal.SmTally.sm2_final_numbers.
Print Assumptions Minimal.SmTally.sm2_ev_mono.
Print Assumptions Minimal.SmTally.sm2_ev_spec.
(* === Minimal.SmallConsensus : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SmallConsensus.sc_decode_code.
Print Assumptions Minimal.SmallConsensus.sc_init_inv.
Print Assumptions Minimal.SmallConsensus.sc_oldest_cons.
Print Assumptions Minimal.SmallConsensus.sc_check_effect.
Print Assumptions Minimal.SmallConsensus.sc_step_inv.
Print Assumptions Minimal.SmallConsensus.sc_run_inv.
Print Assumptions Minimal.SmallConsensus.sc_agreement.
Print Assumptions Minimal.SmallConsensus.sc_validity.
Print Assumptions Minimal.SmallConsensus.sc_step_other.
Print Assumptions Minimal.SmallConsensus.sc_step_progress.
Print Assumptions Minimal.SmallConsensus.sc_run_progress.
Print Assumptions Minimal.SmallConsensus.sc_wait_free.
(* === Minimal.Tc2Am : 22 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Am.am_run_add.
Print Assumptions Minimal.Tc2Am.am_run_S_l.
Print Assumptions Minimal.Tc2Am.am_run_S_r.
Print Assumptions Minimal.Tc2Am.am_hlt_stp.
Print Assumptions Minimal.Tc2Am.am_hlt_run.
Print Assumptions Minimal.Tc2Am.am_run_after.
Print Assumptions Minimal.Tc2Am.am_stp_q.
Print Assumptions Minimal.Tc2Am.am_run_q.
Print Assumptions Minimal.Tc2Am.am_stp_step1.
Print Assumptions Minimal.Tc2Am.am_stp_shB.
Print Assumptions Minimal.Tc2Am.am_stp_shA.
Print Assumptions Minimal.Tc2Am.am_run_shB.
Print Assumptions Minimal.Tc2Am.am_run_shA.
Print Assumptions Minimal.Tc2Am.am_sw_stp.
Print Assumptions Minimal.Tc2Am.am_sw_run.
Print Assumptions Minimal.Tc2Am.am_sw_hlt.
Print Assumptions Minimal.Tc2Am.tc2_dup_or_nodup.
Print Assumptions Minimal.Tc2Am.tc2_pigeon_b.
Print Assumptions Minimal.Tc2Am.tc2_bex_dec.
Print Assumptions Minimal.Tc2Am.tc2_ball_dec.
Print Assumptions Minimal.Tc2Am.tc2_least.
Print Assumptions Minimal.Tc2Am.tc2_pick_spec.
(* === Minimal.Tc2Chain : 29 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Chain.ch_outs_unique.
Print Assumptions Minimal.Tc2Chain.ch_outs_fwd.
Print Assumptions Minimal.Tc2Chain.ch_outs_bwd.
Print Assumptions Minimal.Tc2Chain.ch_stage_le.
Print Assumptions Minimal.Tc2Chain.sl_both.
Print Assumptions Minimal.Tc2Chain.st_next_iter.
Print Assumptions Minimal.Tc2Chain.iface_of_any.
Print Assumptions Minimal.Tc2Chain.am_usw_sw.
Print Assumptions Minimal.Tc2Chain.am_sw_usw.
Print Assumptions Minimal.Tc2Chain.am_b_sw.
Print Assumptions Minimal.Tc2Chain.am_a_sw.
Print Assumptions Minimal.Tc2Chain.am_swp_shA.
Print Assumptions Minimal.Tc2Chain.am_swp_shB.
Print Assumptions Minimal.Tc2Chain.am_shA_0.
Print Assumptions Minimal.Tc2Chain.am_shB_0.
Print Assumptions Minimal.Tc2Chain.am_run_usw.
Print Assumptions Minimal.Tc2Chain.am_sw_inj.
Print Assumptions Minimal.Tc2Chain.iface_A.
Print Assumptions Minimal.Tc2Chain.ifB_leaf_out.
Print Assumptions Minimal.Tc2Chain.ch_good_run.
Print Assumptions Minimal.Tc2Chain.chain.
Print Assumptions Minimal.Tc2Chain.ch_F_in.
Print Assumptions Minimal.Tc2Chain.ch_F_dec.
Print Assumptions Minimal.Tc2Chain.ch_outs_start.
Print Assumptions Minimal.Tc2Chain.ch_collision.
Print Assumptions Minimal.Tc2Chain.good_exists.
Print Assumptions Minimal.Tc2Chain.coprime_mul.
Print Assumptions Minimal.Tc2Chain.ch_prod_coprime.
Print Assumptions Minimal.Tc2Chain.am_no_multiplier.
(* === Minimal.Tc2Collision : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Collision.tc2_run_add.
Print Assumptions Minimal.Tc2Collision.tc2_after_halt.
Print Assumptions Minimal.Tc2Collision.tc2_out_from.
Print Assumptions Minimal.Tc2Collision.tc2_core_run_eq.
Print Assumptions Minimal.Tc2Collision.tc2_collision.
Print Assumptions Minimal.Tc2Collision.tc2_next_in.
Print Assumptions Minimal.Tc2Collision.tc2_pe_step.
Print Assumptions Minimal.Tc2Collision.tc2_pe_run.
Print Assumptions Minimal.Tc2Collision.tc2_collision_pure.
Print Assumptions Minimal.Tc2Collision.tc2_err_false.
Print Assumptions Minimal.Tc2Collision.tc2_shift_step.
Print Assumptions Minimal.Tc2Collision.tc2_shift_run.
Print Assumptions Minimal.Tc2Collision.tc2_start_shift.
Print Assumptions Minimal.Tc2Collision.tc2_safe_mono.
Print Assumptions Minimal.Tc2Collision.tc2_shifted_run.
Print Assumptions Minimal.Tc2Collision.tc2_slaving.
(* === Minimal.Tc2Embed : 44 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Embed.tc2_fa_eqb_true.
Print Assumptions Minimal.Tc2Embed.tc2_cl_in.
Print Assumptions Minimal.Tc2Embed.tc2_cl_range.
Print Assumptions Minimal.Tc2Embed.tc2_cl_out.
Print Assumptions Minimal.Tc2Embed.tc2_inv_start.
Print Assumptions Minimal.Tc2Embed.tc2_next_in.
Print Assumptions Minimal.Tc2Embed.tc2_fetch_cl.
Print Assumptions Minimal.Tc2Embed.tc2_abs_write.
Print Assumptions Minimal.Tc2Embed.tc2_abs_goto.
Print Assumptions Minimal.Tc2Embed.tc2_abs_trap.
Print Assumptions Minimal.Tc2Embed.tc2_abs_record.
Print Assumptions Minimal.Tc2Embed.tc2_abs_commit.
Print Assumptions Minimal.Tc2Embed.tc2_existsb_commit.
Print Assumptions Minimal.Tc2Embed.tc2_facts_write.
Print Assumptions Minimal.Tc2Embed.tc2_inv_cexec.
Print Assumptions Minimal.Tc2Embed.tc2_inv_step.
Print Assumptions Minimal.Tc2Embed.tc2_nx_none.
Print Assumptions Minimal.Tc2Embed.tc2_nx_some.
Print Assumptions Minimal.Tc2Embed.tc2_sim_step.
Print Assumptions Minimal.Tc2Embed.tc2_lu_in.
Print Assumptions Minimal.Tc2Embed.tc2_flat_len.
Print Assumptions Minimal.Tc2Embed.tc2_pw_pos.
Print Assumptions Minimal.Tc2Embed.tc2_lu_len.
Print Assumptions Minimal.Tc2Embed.tc2_thr_ge.
Print Assumptions Minimal.Tc2Embed.tc2_fal_in.
Print Assumptions Minimal.Tc2Embed.tc2_flat_len2.
Print Assumptions Minimal.Tc2Embed.tc2_fal_len.
Print Assumptions Minimal.Tc2Embed.tc2_lu_ok.
Print Assumptions Minimal.Tc2Embed.tc2_lq_in.
Print Assumptions Minimal.Tc2Embed.tc2_bump_ok.
Print Assumptions Minimal.Tc2Embed.tc2_fetch_in.
Print Assumptions Minimal.Tc2Embed.tc2_nx_okq.
Print Assumptions Minimal.Tc2Embed.tc2_nx_step1.
Print Assumptions Minimal.Tc2Embed.tc2_even_shift.
Print Assumptions Minimal.Tc2Embed.tc2_eval_shift.
Print Assumptions Minimal.Tc2Embed.tc2_nx_tameA.
Print Assumptions Minimal.Tc2Embed.tc2_nx_tameB.
Print Assumptions Minimal.Tc2Embed.tc2_am_stp.
Print Assumptions Minimal.Tc2Embed.tc2_sim_run.
Print Assumptions Minimal.Tc2Embed.tc2_inv_run.
Print Assumptions Minimal.Tc2Embed.tc2_nxi_some.
Print Assumptions Minimal.Tc2Embed.tc2_halted_iff.
Print Assumptions Minimal.Tc2Embed.tc2_abs_start.
Print Assumptions Minimal.Tc2Embed.tc2_pf_iff.
(* === Minimal.Tc2Forced : 42 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Forced.fs_par_lt.
Print Assumptions Minimal.Tc2Forced.fs_par_spec.
Print Assumptions Minimal.Tc2Forced.fs_par_add2.
Print Assumptions Minimal.Tc2Forced.fs_par_eq.
Print Assumptions Minimal.Tc2Forced.fs_yrep_ge.
Print Assumptions Minimal.Tc2Forced.fs_yrep_le.
Print Assumptions Minimal.Tc2Forced.fs_yrep_mod.
Print Assumptions Minimal.Tc2Forced.fo_s_0.
Print Assumptions Minimal.Tc2Forced.fo_d_0.
Print Assumptions Minimal.Tc2Forced.fo_S_some.
Print Assumptions Minimal.Tc2Forced.fo_S_none.
Print Assumptions Minimal.Tc2Forced.fs_corr.
Print Assumptions Minimal.Tc2Forced.fo_add.
Print Assumptions Minimal.Tc2Forced.fs_nx_bound.
Print Assumptions Minimal.Tc2Forced.fo_step.
Print Assumptions Minimal.Tc2Forced.fo_x_le.
Print Assumptions Minimal.Tc2Forced.fo_d_bound.
Print Assumptions Minimal.Tc2Forced.fo_p_lt.
Print Assumptions Minimal.Tc2Forced.fs_nx_q.
Print Assumptions Minimal.Tc2Forced.fo_q_in.
Print Assumptions Minimal.Tc2Forced.fo_par.
Print Assumptions Minimal.Tc2Forced.fs_nx_sh.
Print Assumptions Minimal.Tc2Forced.fo_sh.
Print Assumptions Minimal.Tc2Forced.fx_shA.
Print Assumptions Minimal.Tc2Forced.fq_shA.
Print Assumptions Minimal.Tc2Forced.fp_shA.
Print Assumptions Minimal.Tc2Forced.fs_nx_shs.
Print Assumptions Minimal.Tc2Forced.fs_cfg_eq.
Print Assumptions Minimal.Tc2Forced.orb_pump_asc.
Print Assumptions Minimal.Tc2Forced.fs_shA_of.
Print Assumptions Minimal.Tc2Forced.orb_x_from.
Print Assumptions Minimal.Tc2Forced.orb_pump_desc.
Print Assumptions Minimal.Tc2Forced.orb_no_desc.
Print Assumptions Minimal.Tc2Forced.orb_entry.
Print Assumptions Minimal.Tc2Forced.in01.
Print Assumptions Minimal.Tc2Forced.fs_Ax_in.
Print Assumptions Minimal.Tc2Forced.orb_win.
Print Assumptions Minimal.Tc2Forced.orb_stretch.
Print Assumptions Minimal.Tc2Forced.fs_shA_0.
Print Assumptions Minimal.Tc2Forced.fs_Sx_in_lS.
Print Assumptions Minimal.Tc2Forced.orb_periodic.
Print Assumptions Minimal.Tc2Forced.orb_class.
(* === Minimal.Tc2Mult : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Mult.tc2_fact_pos.
Print Assumptions Minimal.Tc2Mult.tc2_fact_div.
Print Assumptions Minimal.Tc2Mult.tc2_fact_coprime.
Print Assumptions Minimal.Tc2Mult.tc2_pw_mono.
Print Assumptions Minimal.Tc2Mult.tc2_lq_len.
Print Assumptions Minimal.Tc2Mult.tc2_q0_in.
Print Assumptions Minimal.Tc2Mult.tc2_no_mult.
(* === Minimal.Tc2Pow : 6 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Pow.ch_outs_start_f.
Print Assumptions Minimal.Tc2Pow.ch_collision_f.
Print Assumptions Minimal.Tc2Pow.good_exists_f.
Print Assumptions Minimal.Tc2Pow.ch_prod_pos.
Print Assumptions Minimal.Tc2Pow.am_no_power_of_two.
Print Assumptions Minimal.Tc2Pow.tc2_no_pow.
(* === Minimal.Tc2Stage : 26 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Tc2Stage.real_none.
Print Assumptions Minimal.Tc2Stage.real_some.
Print Assumptions Minimal.Tc2Stage.st_fp_unique.
Print Assumptions Minimal.Tc2Stage.st_any_mono.
Print Assumptions Minimal.Tc2Stage.fs_shA_add.
Print Assumptions Minimal.Tc2Stage.fo_d_diff.
Print Assumptions Minimal.Tc2Stage.pump_D.
Print Assumptions Minimal.Tc2Stage.pump_S.
Print Assumptions Minimal.Tc2Stage.pump_D_even.
Print Assumptions Minimal.Tc2Stage.fp_exist.
Print Assumptions Minimal.Tc2Stage.fp_T_ge.
Print Assumptions Minimal.Tc2Stage.fp_shift.
Print Assumptions Minimal.Tc2Stage.fs_start_eq.
Print Assumptions Minimal.Tc2Stage.st_fp_of_fpf.
Print Assumptions Minimal.Tc2Stage.fs_nx_none_inv.
Print Assumptions Minimal.Tc2Stage.fs_nx_some_inv.
Print Assumptions Minimal.Tc2Stage.st_leaf_of_halt.
Print Assumptions Minimal.Tc2Stage.st_nh_of_pump.
Print Assumptions Minimal.Tc2Stage.bounded_range.
Print Assumptions Minimal.Tc2Stage.pump0_bounded.
Print Assumptions Minimal.Tc2Stage.st_bdd_of_pump.
Print Assumptions Minimal.Tc2Stage.fo_x_from.
Print Assumptions Minimal.Tc2Stage.st_next_of_pump.
Print Assumptions Minimal.Tc2Stage.sl_type.
Print Assumptions Minimal.Tc2Stage.st_all_list.
Print Assumptions Minimal.Tc2Stage.sl_all.
(* === Minimal.TcBlocks : 30 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.TcBlocks.tc_rj_in.
Print Assumptions Minimal.TcBlocks.tc_rj_out.
Print Assumptions Minimal.TcBlocks.tc_rj_S.
Print Assumptions Minimal.TcBlocks.tc_grun_succ.
Print Assumptions Minimal.TcBlocks.tc_grun_add.
Print Assumptions Minimal.TcBlocks.tc_ghalted_after.
Print Assumptions Minimal.TcBlocks.tc_greloc_length.
Print Assumptions Minimal.TcBlocks.tc_gembeds_app.
Print Assumptions Minimal.TcBlocks.tc_gfetch_range.
Print Assumptions Minimal.TcBlocks.tc_gfetch_out.
Print Assumptions Minimal.TcBlocks.tc_eqb_add.
Print Assumptions Minimal.TcBlocks.tc_fsh_eqb.
Print Assumptions Minimal.TcBlocks.tc_existsb_fsh.
Print Assumptions Minimal.TcBlocks.tc_fsh_zero.
Print Assumptions Minimal.TcBlocks.tc_fsh_opt_zero.
Print Assumptions Minimal.TcBlocks.tc_gnext_some.
Print Assumptions Minimal.TcBlocks.tc_gnext_intro.
Print Assumptions Minimal.TcBlocks.tc_gri_halt.
Print Assumptions Minimal.TcBlocks.tc_gcrel_val.
Print Assumptions Minimal.TcBlocks.tc_gcrel_claim.
Print Assumptions Minimal.TcBlocks.tc_gblock_cstep.
Print Assumptions Minimal.TcBlocks.tc_gblock_step.
Print Assumptions Minimal.TcBlocks.tc_gblock_run_mid.
Print Assumptions Minimal.TcBlocks.tc_gblock_not_halted.
Print Assumptions Minimal.TcBlocks.tc_gblock_halted.
Print Assumptions Minimal.TcBlocks.tc_gblock_run_final.
Print Assumptions Minimal.TcBlocks.tc_gplain_exec.
Print Assumptions Minimal.TcBlocks.tc_compile_run.
Print Assumptions Minimal.TcBlocks.tc_gfetch_app_left.
Print Assumptions Minimal.TcBlocks.tc_gfetch_app_right.
(* === Minimal.ThieleComplete : 56 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.ThieleComplete.run_app.
Print Assumptions Minimal.ThieleComplete.base_runs_every_program.
Print Assumptions Minimal.ThieleComplete.base_halting_correspondence.
Print Assumptions Minimal.ThieleComplete.thiele_complete_over_complete.
Print Assumptions Minimal.ThieleComplete.thiele_complete_with_over.
Print Assumptions Minimal.ThieleComplete.over_certificate_means.
Print Assumptions Minimal.ThieleComplete.thiele_complete_is_weak.
Print Assumptions Minimal.ThieleComplete.record_moves_app.
Print Assumptions Minimal.ThieleComplete.ledger_counts_record_moves.
Print Assumptions Minimal.ThieleComplete.certificate_costs_three.
Print Assumptions Minimal.ThieleComplete.committed_claim_holds.
Print Assumptions Minimal.ThieleComplete.check_can_fail.
Print Assumptions Minimal.ThieleComplete.some_run_certifies.
Print Assumptions Minimal.ThieleComplete.only_certify_raises.
Print Assumptions Minimal.ThieleComplete.complete_costs_at_most_one.
Print Assumptions Minimal.ThieleComplete.complete_has_free_move.
Print Assumptions Minimal.ThieleComplete.one_move_record_excluded.
Print Assumptions Minimal.ThieleComplete.never_certifies_excluded.
Print Assumptions Minimal.ThieleComplete.clock_weakly_thiele_complete.
Print Assumptions Minimal.ThieleComplete.clock_not_thiele_complete.
Print Assumptions Minimal.ThieleComplete.latch_clock_weakly_thiele_complete.
Print Assumptions Minimal.ThieleComplete.latch_clock_not_thiele_complete.
Print Assumptions Minimal.ThieleComplete.paid_latch_weakly_thiele_complete.
Print Assumptions Minimal.ThieleComplete.paid_latch_meets_base_and_toll.
Print Assumptions Minimal.ThieleComplete.paid_latch_not_thiele_complete.
Print Assumptions Minimal.ThieleComplete.silent_weakly_thiele_complete.
Print Assumptions Minimal.ThieleComplete.silent_meets_base_record_toll.
Print Assumptions Minimal.ThieleComplete.silent_not_thiele_complete.
Print Assumptions Minimal.ThieleComplete.run_earned.
Print Assumptions Minimal.ThieleComplete.earned_sim.
Print Assumptions Minimal.ThieleComplete.untouched_prefix.
Print Assumptions Minimal.ThieleComplete.earned_chain_holds.
Print Assumptions Minimal.ThieleComplete.earned_core_complete_with.
Print Assumptions Minimal.ThieleComplete.earned_core_thiele_complete.
Print Assumptions Minimal.ThieleComplete.earned_claim_eqb_spec.
Print Assumptions Minimal.ThieleComplete.earned_same_keeps.
Print Assumptions Minimal.ThieleComplete.earned_check_sound.
Print Assumptions Minimal.ThieleComplete.earned_core_thiele_complete_over.
Print Assumptions Minimal.ThieleComplete.reference_step_agrees.
Print Assumptions Minimal.ThieleComplete.reference_agrees.
Print Assumptions Minimal.ThieleComplete.earned_core_runs_counter_programs.
Print Assumptions Minimal.ThieleComplete.check_ge_unit_cost.
Print Assumptions Minimal.ThieleComplete.run_generic.
Print Assumptions Minimal.ThieleComplete.generic_base_blind.
Print Assumptions Minimal.ThieleComplete.generic_sim.
Print Assumptions Minimal.ThieleComplete.generic_untouched_prefix.
Print Assumptions Minimal.ThieleComplete.generic_chain_holds.
Print Assumptions Minimal.ThieleComplete.generic_chain_iff.
Print Assumptions Minimal.ThieleComplete.generic_thiele_complete_with.
Print Assumptions Minimal.ThieleComplete.generic_claim_eqb_spec.
Print Assumptions Minimal.ThieleComplete.generic_same_keeps.
Print Assumptions Minimal.ThieleComplete.generic_check_sound.
Print Assumptions Minimal.ThieleComplete.earned_generic_thiele_complete.
Print Assumptions Minimal.ThieleComplete.sorted_machine_thiele_complete.
Print Assumptions Minimal.ThieleComplete.earned_generic_thiele_complete_over.
Print Assumptions Minimal.ThieleComplete.sorted_machine_thiele_complete_over.
(* === Minimal.ThieleCompleteIndependent : 29 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.ThieleCompleteIndependent.ext_run_map.
Print Assumptions Minimal.ThieleCompleteIndependent.ext_run_EM_app.
Print Assumptions Minimal.ThieleCompleteIndependent.ext_run_EM_cons.
Print Assumptions Minimal.ThieleCompleteIndependent.E_run_cons.
Print Assumptions Minimal.ThieleCompleteIndependent.ext_chain_transport.
Print Assumptions Minimal.ThieleCompleteIndependent.ext_record_parts.
Print Assumptions Minimal.ThieleCompleteIndependent.ext_non_vacuity.
Print Assumptions Minimal.ThieleCompleteIndependent.ext_exact_toll.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_trapped_stays.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_free_run.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_meets_b_c_d.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_not_permanent.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_fails_a.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_not_thiele_complete.
Print Assumptions Minimal.ThieleCompleteIndependent.drop_weakly_thiele_complete.
Print Assumptions Minimal.ThieleCompleteIndependent.free_meets_a_c_d.
Print Assumptions Minimal.ThieleCompleteIndependent.chain_needs_three.
Print Assumptions Minimal.ThieleCompleteIndependent.free_fails_b.
Print Assumptions Minimal.ThieleCompleteIndependent.free_trapped_stays.
Print Assumptions Minimal.ThieleCompleteIndependent.free_not_thiele_complete.
Print Assumptions Minimal.ThieleCompleteIndependent.free_weakly_thiele_complete.
Print Assumptions Minimal.ThieleCompleteIndependent.paid_run.
Print Assumptions Minimal.ThieleCompleteIndependent.earned_clauses.
Print Assumptions Minimal.ThieleCompleteIndependent.paid_chain.
Print Assumptions Minimal.ThieleCompleteIndependent.paid_meets_a_b_d.
Print Assumptions Minimal.ThieleCompleteIndependent.paid_fails_c.
Print Assumptions Minimal.ThieleCompleteIndependent.paid_not_thiele_complete.
Print Assumptions Minimal.ThieleCompleteIndependent.paid_weakly_thiele_complete.
Print Assumptions Minimal.ThieleCompleteIndependent.thiele_complete_clauses_independent.
(* === Minimal.ThieleCompleteScaled : 26 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.ThieleCompleteScaled.thiele_complete_at_one.
Print Assumptions Minimal.ThieleCompleteScaled.thiele_complete_has_a_unit.
Print Assumptions Minimal.ThieleCompleteScaled.run_scale.
Print Assumptions Minimal.ThieleCompleteScaled.run_unscale.
Print Assumptions Minimal.ThieleCompleteScaled.base_clause_scale.
Print Assumptions Minimal.ThieleCompleteScaled.base_clause_unscale.
Print Assumptions Minimal.ThieleCompleteScaled.earned_chain_scale.
Print Assumptions Minimal.ThieleCompleteScaled.earned_chain_unscale.
Print Assumptions Minimal.ThieleCompleteScaled.record_clause_scale.
Print Assumptions Minimal.ThieleCompleteScaled.record_clause_unscale.
Print Assumptions Minimal.ThieleCompleteScaled.nonvac_clause_scale.
Print Assumptions Minimal.ThieleCompleteScaled.nonvac_clause_unscale.
Print Assumptions Minimal.ThieleCompleteScaled.scale_complete_at.
Print Assumptions Minimal.ThieleCompleteScaled.unscale_complete.
Print Assumptions Minimal.ThieleCompleteScaled.unscale_same_step.
Print Assumptions Minimal.ThieleCompleteScaled.scaled_has_free_move.
Print Assumptions Minimal.ThieleCompleteScaled.paid_moves_not_thiele_complete_at_any_unit.
Print Assumptions Minimal.ThieleCompleteScaled.clock_not_thiele_complete_at_any_unit.
Print Assumptions Minimal.ThieleCompleteScaled.latch_clock_not_thiele_complete_at_any_unit.
Print Assumptions Minimal.ThieleCompleteScaled.scaled_ledger_counts.
Print Assumptions Minimal.ThieleCompleteScaled.scaled_certificate_costs_three_c.
Print Assumptions Minimal.ThieleCompleteScaled.unscale_with.
Print Assumptions Minimal.ThieleCompleteScaled.scaled_committed_claim_holds.
Print Assumptions Minimal.ThieleCompleteScaled.scaled_only_certify_raises.
Print Assumptions Minimal.ThieleCompleteScaled.doubled_earned_scaled.
Print Assumptions Minimal.ThieleCompleteScaled.doubled_earned_not_thiele_complete.
(* === Minimal.ThieleCompleteWindow : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.ThieleCompleteWindow.cm_dec_a_to_zero.
Print Assumptions Minimal.ThieleCompleteWindow.cm_dec_b_to_zero.
Print Assumptions Minimal.ThieleCompleteWindow.cm_inc_a.
Print Assumptions Minimal.ThieleCompleteWindow.cm_inc_b.
Print Assumptions Minimal.ThieleCompleteWindow.cm_reach.
Print Assumptions Minimal.ThieleCompleteWindow.base_run_window.
Print Assumptions Minimal.ThieleCompleteWindow.base_run_blind.
Print Assumptions Minimal.ThieleCompleteWindow.base_run_only_base.
Print Assumptions Minimal.ThieleCompleteWindow.complete_every_window_printed.
Print Assumptions Minimal.ThieleCompleteWindow.complete_two_runs.
Print Assumptions Minimal.ThieleCompleteWindow.complete_hides_ledger.
Print Assumptions Minimal.ThieleCompleteWindow.complete_hides_record.
Print Assumptions Minimal.ThieleCompleteWindow.complete_ledger_oracle_fails.
Print Assumptions Minimal.ThieleCompleteWindow.complete_record_oracle_fails.
Print Assumptions Minimal.ThieleCompleteWindow.complete_no_ledger_oracle.
Print Assumptions Minimal.ThieleCompleteWindow.complete_no_record_oracle.
Print Assumptions Minimal.ThieleCompleteWindow.thiele_complete_hides.
(* === Minimal.TimeTax2 : 30 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.TimeTax2.ent2_step_rel.
Print Assumptions Minimal.TimeTax2.ent2_free_run_shift.
Print Assumptions Minimal.TimeTax2.ent2_free_same_view.
Print Assumptions Minimal.TimeTax2.ent2_free_cannot_decide_fast.
Print Assumptions Minimal.TimeTax2.ent2_ladder_length.
Print Assumptions Minimal.TimeTax2.ent2_ladder_nth.
Print Assumptions Minimal.TimeTax2.ent2_ladder_fetch.
Print Assumptions Minimal.TimeTax2.ent2_ladder_fetch_some.
Print Assumptions Minimal.TimeTax2.ent2_mrun_stuck.
Print Assumptions Minimal.TimeTax2.ent2_mrun_add.
Print Assumptions Minimal.TimeTax2.ent2_ladder_climb.
Print Assumptions Minimal.TimeTax2.ent2_ladder_fail.
Print Assumptions Minimal.TimeTax2.ent2_ladder_decides.
Print Assumptions Minimal.TimeTax2.ent2_ladder_decides_in_m.
Print Assumptions Minimal.TimeTax2.ent2_machine_window.
Print Assumptions Minimal.TimeTax2.ent2_fetch_in.
Print Assumptions Minimal.TimeTax2.ent2_next_in.
Print Assumptions Minimal.TimeTax2.ent2_compile_free.
Print Assumptions Minimal.TimeTax2.ent2_machine_free_cannot_decide.
Print Assumptions Minimal.TimeTax2.ent2_machine_ladder_decides.
Print Assumptions Minimal.TimeTax2.ent2_ladder_free.
Print Assumptions Minimal.TimeTax2.ent2_chain_decides.
Print Assumptions Minimal.TimeTax2.ent2_time_tax.
Print Assumptions Minimal.TimeTax2.ent2_claim_strength_free.
Print Assumptions Minimal.TimeTax2.ent2_tax_pow_ge.
Print Assumptions Minimal.TimeTax2.ent2_tax_pow_gap.
Print Assumptions Minimal.TimeTax2.ent2_tax_ratio_grows.
Print Assumptions Minimal.TimeTax2.ent2_tax_last_saves_zero.
Print Assumptions Minimal.TimeTax2.ent2_tax_sighted_wins.
Print Assumptions Minimal.TimeTax2.ent2_tax_sighted_loses_at_zero.
(* === Minimal.UniversalCodes : 56 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.UniversalCodes.unpair_zero.
Print Assumptions Minimal.UniversalCodes.pow2_pos.
Print Assumptions Minimal.UniversalCodes.pair_pos.
Print Assumptions Minimal.UniversalCodes.pair_S.
Print Assumptions Minimal.UniversalCodes.pair_0.
Print Assumptions Minimal.UniversalCodes.unp_fuel.
Print Assumptions Minimal.UniversalCodes.unp_odd.
Print Assumptions Minimal.UniversalCodes.unp_even.
Print Assumptions Minimal.UniversalCodes.unp_pair.
Print Assumptions Minimal.UniversalCodes.unpair_pair.
Print Assumptions Minimal.UniversalCodes.pair_inj.
Print Assumptions Minimal.UniversalCodes.pair_onto.
Print Assumptions Minimal.UniversalCodes.unpair_some.
Print Assumptions Minimal.UniversalCodes.unpair_none.
Print Assumptions Minimal.UniversalCodes.unpair_sound.
Print Assumptions Minimal.UniversalCodes.pair_encode.
Print Assumptions Minimal.UniversalCodes.unpair_encode_nil.
Print Assumptions Minimal.UniversalCodes.unpair_encode_cons.
Print Assumptions Minimal.UniversalCodes.pdec_pcode.
Print Assumptions Minimal.UniversalCodes.pcode_pdec.
Print Assumptions Minimal.UniversalCodes.pcode_inj.
Print Assumptions Minimal.UniversalCodes.cdec_ccode.
Print Assumptions Minimal.UniversalCodes.cdec_sound.
Print Assumptions Minimal.UniversalCodes.ccode_inj.
Print Assumptions Minimal.UniversalCodes.ccode_lt.
Print Assumptions Minimal.UniversalCodes.hprop_eqb_eq.
Print Assumptions Minimal.UniversalCodes.heval_iff.
Print Assumptions Minimal.UniversalCodes.heval_pair.
Print Assumptions Minimal.UniversalCodes.hholds_pair.
Print Assumptions Minimal.UniversalCodes.heval_zero.
Print Assumptions Minimal.UniversalCodes.hholds_iff.
Print Assumptions Minimal.UniversalCodes.idecode_icode.
Print Assumptions Minimal.UniversalCodes.idecode_sound.
Print Assumptions Minimal.UniversalCodes.icode_inj.
Print Assumptions Minimal.UniversalCodes.icode_pos.
Print Assumptions Minimal.UniversalCodes.unpair_icode.
Print Assumptions Minimal.UniversalCodes.prog_code_decode.
Print Assumptions Minimal.UniversalCodes.prog_code_nil.
Print Assumptions Minimal.UniversalCodes.prog_code_cons.
Print Assumptions Minimal.UniversalCodes.prog_code_inj.
Print Assumptions Minimal.UniversalCodes.skip_code_S.
Print Assumptions Minimal.UniversalCodes.fetch_code_S.
Print Assumptions Minimal.UniversalCodes.fetch_code_skip.
Print Assumptions Minimal.UniversalCodes.skip_code_encode.
Print Assumptions Minimal.UniversalCodes.fetch_code_encode.
Print Assumptions Minimal.UniversalCodes.nth_error_map_opt.
Print Assumptions Minimal.UniversalCodes.skipn_map_comm.
Print Assumptions Minimal.UniversalCodes.fetch_code_prog.
Print Assumptions Minimal.UniversalCodes.skip_code_prog.
Print Assumptions Minimal.UniversalCodes.unpair_skip_prog.
Print Assumptions Minimal.UniversalCodes.skip_prog_past_end.
Print Assumptions Minimal.UniversalCodes.fetch_decode_prog.
Print Assumptions Minimal.UniversalCodes.guest_fetch_code.
Print Assumptions Minimal.UniversalCodes.host_earned_certification_provenance.
Print Assumptions Minimal.UniversalCodes.host_slot_soundness.
Print Assumptions Minimal.UniversalCodes.host_committed_slot_holds.
(* === Minimal.UniversalNoCopy : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.UniversalNoCopy.pigeonhole_not_injective.
Print Assumptions Minimal.UniversalNoCopy.collide.
Print Assumptions Minimal.UniversalNoCopy.pigeonhole_collision.
Print Assumptions Minimal.UniversalNoCopy.guest_check_passes.
Print Assumptions Minimal.UniversalNoCopy.guest_traps.
Print Assumptions Minimal.UniversalNoCopy.host_same_prop_succeeds.
Print Assumptions Minimal.UniversalNoCopy.no_exact_copy_host.
(* === Minimal.UniversalThiele : 47 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.UniversalThiele.hrun_app.
Print Assumptions Minimal.UniversalThiele.hrun_prog_halted.
Print Assumptions Minimal.UniversalThiele.hrun_prog_trace.
Print Assumptions Minimal.UniversalThiele.hrun_prog_add.
Print Assumptions Minimal.UniversalThiele.hexec_gprog.
Print Assumptions Minimal.UniversalThiele.hmu_conservation.
Print Assumptions Minimal.UniversalThiele.hmu_conservation_trace.
Print Assumptions Minimal.UniversalThiele.gmove_spec.
Print Assumptions Minimal.UniversalThiele.crossing_is_certify.
Print Assumptions Minimal.UniversalThiele.no_free_host_certification_step.
Print Assumptions Minimal.UniversalThiele.no_free_host_certification.
Print Assumptions Minimal.UniversalThiele.no_free_host_certification_program.
Print Assumptions Minimal.UniversalThiele.guestless_runs_leave_mirror.
Print Assumptions Minimal.UniversalThiele.own_record_only_by_certify.
Print Assumptions Minimal.UniversalThiele.host_own_toll.
Print Assumptions Minimal.UniversalThiele.host_mirror_toll.
Print Assumptions Minimal.UniversalThiele.host_toll.
Print Assumptions Minimal.UniversalThiele.hnext_own.
Print Assumptions Minimal.UniversalThiele.hcore_own_run.
Print Assumptions Minimal.UniversalThiele.host_thiele_complete.
Print Assumptions Minimal.UniversalThiele.gnext_one.
Print Assumptions Minimal.UniversalThiele.gstep_err.
Print Assumptions Minimal.UniversalThiele.gstep_gst.
Print Assumptions Minimal.UniversalThiele.universal_simulation.
Print Assumptions Minimal.UniversalThiele.U_round.
Print Assumptions Minimal.UniversalThiele.universal_program_simulation.
Print Assumptions Minimal.UniversalThiele.record_agreement_step.
Print Assumptions Minimal.UniversalThiele.record_agreement.
Print Assumptions Minimal.UniversalThiele.record_agreement_program.
Print Assumptions Minimal.UniversalThiele.hload_agrees.
Print Assumptions Minimal.UniversalThiele.simulated_record.
Print Assumptions Minimal.UniversalThiele.toll_enforced_by_host_step.
Print Assumptions Minimal.UniversalThiele.repeat_snoc.
Print Assumptions Minimal.UniversalThiele.run_prog_snoc.
Print Assumptions Minimal.UniversalThiele.every_guest_crossing_is_a_host_crossing.
Print Assumptions Minimal.UniversalThiele.host_pays_for_guest.
Print Assumptions Minimal.UniversalThiele.host_cost_covers_guest.
Print Assumptions Minimal.UniversalThiele.simulated_cost.
Print Assumptions Minimal.UniversalThiele.demo_certifies.
Print Assumptions Minimal.UniversalThiele.demo_program_certifies.
Print Assumptions Minimal.UniversalThiele.demo_forgery_fails.
Print Assumptions Minimal.UniversalThiele.guest_run_prog_add.
Print Assumptions Minimal.UniversalThiele.gnext_steps.
Print Assumptions Minimal.UniversalThiele.hexec_guest.
Print Assumptions Minimal.UniversalThiele.guest_runs_own_program.
Print Assumptions Minimal.UniversalThiele.guest_runs_own_steps.
Print Assumptions Minimal.UniversalThiele.host_mirror_earned.
(* === Minimal.VerifierSmall : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.VerifierSmall.ver_collision_blocks.
Print Assumptions Minimal.VerifierSmall.ver_sound_rejects.
Print Assumptions Minimal.VerifierSmall.ver_no_factor.
Print Assumptions Minimal.VerifierSmall.ver_full_state_escape.
Print Assumptions Minimal.VerifierSmall.ver_commitment_escape.
Print Assumptions Minimal.VerifierSmall.ver_honest_meets_contract.
Print Assumptions Minimal.VerifierSmall.ver_unchecked_breaks_contract.
Print Assumptions Minimal.VerifierSmall.ver_response_escape.
Print Assumptions Minimal.VerifierSmall.ver_complete_no_record_verifier.
Print Assumptions Minimal.VerifierSmall.ver_complete_no_ledger_verifier.
Print Assumptions Minimal.VerifierSmall.ver_complete_pair.
Print Assumptions Minimal.VerifierSmall.ver_complete_no_factor.
Print Assumptions Minimal.VerifierSmall.ver_record_claim.
Print Assumptions Minimal.VerifierSmall.ver_complete_escapes.
Print Assumptions Minimal.VerifierSmall.ver_complete_unchecked_fails.
Print Assumptions Minimal.VerifierSmall.ver_corollary.
Print Assumptions Minimal.VerifierSmall.ver_small_no_ledger_verifier.
