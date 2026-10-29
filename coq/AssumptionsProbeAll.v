(** Comprehensive Print Assumptions probe: every addressable proof-bearing
    declaration across every .v file in the repository (excluding vendor/,
    coq/archive/). Generated; do not edit. Functor and Module-Type interiors
    are skipped here and recorded separately in the inventory. *)

Require Audit.AdaptiveBlindness.
Require Audit.AxThieleLeast.
Require Audit.CanonicalObservation.
Require Audit.EnforcedRefinement.
Require Audit.IntrinsicBoundary.
Require Audit.LeastToll.
Require Audit.MacroBoundary.
Require Audit.ObservationContract.
Require Audit.PricingBoundary.
Require Audit.RepresentationCapacity.
Require Audit.TraceFactorization.
Require Audit.ValuationBoundary.
Require Kernel.AxCore.
Require Kernel.AxInfinite.
Require Kernel.AxLatch.
Require Kernel.AxLatch2.
Require Kernel.AxMerge.
Require Kernel.AxProb.
Require Kernel.AxShadow.
Require Kernel.AxThiele.
Require Kernel.AxWindow.
Require Kernel.CrossBaseGranularity.
Require Kernel.CrossBaseGranularityCore.
Require Kernel.CrossBaseGranularityL.
Require Kernel.CrossBaseGranularityRAM.
Require Kernel.CrossBaseGranularityTransCore.
Require Kernel.FiniteSums.
Require Kernel.GrowingRecord.
Require Kernel.GrowingRecordCore.
Require Kernel.Kernel.
Require Kernel.KernelTM.
Require Kernel.LRecursion.
Require Kernel.LatchConst.
Require Kernel.NatSubstrateInstance.
Require Kernel.NecFCalorimeter.
Require Kernel.NecFCounter.
Require Kernel.NecFCups.
Require Kernel.NecFEntropy.
Require Kernel.NecFEntropyTight.
Require Kernel.NecFFloor.
Require Kernel.NecFGibbs.
Require Kernel.NecFMerge.
Require Kernel.NecFNarrowing.
Require Kernel.NecFPaperToys.
Require Kernel.NecFQuant.
Require Kernel.NecFRepeat.
Require Kernel.NecFSqueeze.
Require Kernel.NecFSqueezeLog.
Require Kernel.NecFThreeState.
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
Require Kernel.ProbabilisticRecord.
Require Kernel.ProbabilisticRecordCore.
Require Kernel.ProperSubsumption.
Require Kernel.RecordAxisDiscrimination.
Require Kernel.StructuralClockSync.
Require Kernel.StructuralCore.
Require Kernel.StructuralCoreAnyBase.
Require Kernel.StructuralCoreCover.
Require Kernel.StructuralRecordAxis.
Require Kernel.Substrate.
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
Require Minimal.AccountingBridge.
Require Minimal.BrownianComputer.
Require Minimal.CommutationObstruction.
Require Minimal.CommutingGrid.
Require Minimal.CompleteHost.
Require Minimal.EditionCapacity.
Require Minimal.EditionHistory.
Require Minimal.Erasure.
Require Minimal.Fibre.
Require Minimal.GeometryLimits.
Require Minimal.GibbsGap.
Require Minimal.HaltingHole.
Require Minimal.HeatOrRoom.
Require Minimal.KeptDistinction.
Require Minimal.MeterRepresentation.
Require Minimal.Monitor.
Require Minimal.MuCore.
Require Minimal.MultiExecution.
Require Minimal.Multiplicity.
Require Minimal.Napkin.
Require Minimal.NecTPartition.
Require Minimal.NoisyChairs.
Require Minimal.NondetChairs.
Require Minimal.PartitionReading.
Require Minimal.PassiveGeometry.
Require Minimal.PeriodicIntersection.
Require Minimal.QuantumChairs.
Require Minimal.Recurrence.
Require Minimal.Representation.
Require Minimal.SharpHost.
Require Minimal.SliceCore.
Require Minimal.SlicedEstablishment.
Require Minimal.StepLaw.
Require Minimal.StructuralMeter.
Require Minimal.SynchronizedCapacity.
Require Minimal.Task.
Require Minimal.TwoArms.
Require Minimal.VerifierSmall.

(* === Audit.AdaptiveBlindness : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.AdaptiveBlindness.adaptive_observer_stays_blind.
Print Assumptions Audit.AdaptiveBlindness.adaptive_decision_stays_equal.
Print Assumptions Audit.AdaptiveBlindness.adaptive_probe_preserves_record.
Print Assumptions Audit.AdaptiveBlindness.adaptive_probe_keeps_hidden_distinction.
Print Assumptions Audit.AdaptiveBlindness.hidden_access_can_signal.
(* === Audit.AxThieleLeast : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.AxThieleLeast.ax_a2_two_point_iff.
Print Assumptions Audit.AxThieleLeast.lift_states_cover.
Print Assumptions Audit.AxThieleLeast.lift_can_raise_iff.
Print Assumptions Audit.AxThieleLeast.lift_toll_iff_least.
Print Assumptions Audit.AxThieleLeast.least_lift_is_thiele.
(* === Audit.CanonicalObservation : 16 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.CanonicalObservation.run_append.
Print Assumptions Audit.CanonicalObservation.future_equivalence_laws.
Print Assumptions Audit.CanonicalObservation.future_equivalence_preserves_observation.
Print Assumptions Audit.CanonicalObservation.future_equivalence_stable.
Print Assumptions Audit.CanonicalObservation.future_equivalence_coarsest.
Print Assumptions Audit.CanonicalObservation.coarsest_relation_unique.
Print Assumptions Audit.CanonicalObservation.canonical_preserves_future.
Print Assumptions Audit.CanonicalObservation.canonical_preserves_output.
Print Assumptions Audit.CanonicalObservation.canonical_preserves_start.
Print Assumptions Audit.CanonicalObservation.canonical_preserves_step.
Print Assumptions Audit.CanonicalObservation.canonical_preserves_run.
Print Assumptions Audit.CanonicalObservation.canonical_merges_exactly_equivalent_states.
Print Assumptions Audit.CanonicalObservation.canonical_unique.
Print Assumptions Audit.CanonicalObservation.canonical_surjective.
Print Assumptions Audit.CanonicalObservation.canonical_injective.
Print Assumptions Audit.CanonicalObservation.minimal_realizations_uniquely_isomorphic.
(* === Audit.EnforcedRefinement : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.EnforcedRefinement.guest_run_append.
Print Assumptions Audit.EnforcedRefinement.every_host_trace_refines.
Print Assumptions Audit.EnforcedRefinement.guest_trace_preserves.
Print Assumptions Audit.EnforcedRefinement.all_host_programs_preserve.
Print Assumptions Audit.EnforcedRefinement.accepted_host_run_has_guest_evidence.
(* === Audit.IntrinsicBoundary : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.IntrinsicBoundary.every_base_has_a_slice_without_hidden_distinctions.
Print Assumptions Audit.IntrinsicBoundary.identity_slice_never_raises.
Print Assumptions Audit.IntrinsicBoundary.identity_slice_has_zero_vertical_price.
Print Assumptions Audit.IntrinsicBoundary.identity_slice_preserves_every_base_step.
Print Assumptions Audit.IntrinsicBoundary.identical_dynamics_do_not_determine_price.
Print Assumptions Audit.IntrinsicBoundary.both_slices_have_a_raise.
Print Assumptions Audit.IntrinsicBoundary.three_states_reachable.
Print Assumptions Audit.IntrinsicBoundary.collapse_preserves_slice_operations.
Print Assumptions Audit.IntrinsicBoundary.no_injection_from_three_to_two.
Print Assumptions Audit.IntrinsicBoundary.toggle_symmetry_forces_constant_reading.
Print Assumptions Audit.IntrinsicBoundary.no_nonconstant_renaming_invariant_toggle_reading.
Print Assumptions Audit.IntrinsicBoundary.finite_observations_do_not_establish_permanence.
(* === Audit.LeastToll : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.LeastToll.free_reading_invariance.
Print Assumptions Audit.LeastToll.can_raise_exact.
Print Assumptions Audit.LeastToll.least_price_satisfies_toll.
Print Assumptions Audit.LeastToll.toll_exactly_dominates_least_price.
Print Assumptions Audit.LeastToll.trace_floor_exactly_dominates_least_price.
Print Assumptions Audit.LeastToll.unique_least_valid_price.
Print Assumptions Audit.LeastToll.every_reading_toll_prices_every_change.
Print Assumptions Audit.LeastToll.every_reading_toll_iff_free_moves_are_identity.
(* === Audit.MacroBoundary : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.MacroBoundary.every_macro_boundary_matches.
Print Assumptions Audit.MacroBoundary.macro_prefix_exposes_unmatched_acceptance.
Print Assumptions Audit.MacroBoundary.this_host_is_not_permanent.
Print Assumptions Audit.MacroBoundary.permanent_trace.
Print Assumptions Audit.MacroBoundary.false_endpoint_excludes_accepting_prefix.
(* === Audit.ObservationContract : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.ObservationContract.output_factorization_iff.
Print Assumptions Audit.ObservationContract.transition_factorization_iff.
Print Assumptions Audit.ObservationContract.base_only_implementation_iff.
Print Assumptions Audit.ObservationContract.encoding_preserves_runs.
Print Assumptions Audit.ObservationContract.encoding_cannot_merge_distinguishable_states.
Print Assumptions Audit.ObservationContract.hidden_pair_survives_view_preserving_encoding.
Print Assumptions Audit.ObservationContract.operational_adequacy_iff.
Print Assumptions Audit.ObservationContract.branching_answers_exclude_exact_deterministic_encoding.
Print Assumptions Audit.ObservationContract.hidden_bit_blocks_visible_only_dynamics.
(* === Audit.PricingBoundary : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.PricingBoundary.permanence.
Print Assumptions Audit.PricingBoundary.exact_accounting.
Print Assumptions Audit.PricingBoundary.every_collision_has_paid_source.
Print Assumptions Audit.PricingBoundary.entry_is_free.
Print Assumptions Audit.PricingBoundary.entry_has_no_competing_source.
(* === Audit.RepresentationCapacity : 3 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.RepresentationCapacity.faithful_encoding_preserves_fibre_bound.
Print Assumptions Audit.RepresentationCapacity.ordinary_bits_attain_the_bound.
Print Assumptions Audit.RepresentationCapacity.one_latch_does_not_require_history_recovery.
(* === Audit.TraceFactorization : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.TraceFactorization.morphism_runs.
Print Assumptions Audit.TraceFactorization.morphism_requires_kernel_inclusion.
Print Assumptions Audit.TraceFactorization.factor_on_words.
Print Assumptions Audit.TraceFactorization.factor_is_morphism.
Print Assumptions Audit.TraceFactorization.reachable_morphism_unique.
Print Assumptions Audit.TraceFactorization.morphism_exists_iff_kernel_inclusion.
Print Assumptions Audit.TraceFactorization.unique_factorization_iff_kernel_inclusion.
Print Assumptions Audit.TraceFactorization.factor_surjective_on_target_reachable.
Print Assumptions Audit.TraceFactorization.trace_evaluation_uniquely_preserves_steps.
(* === Audit.ValuationBoundary : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Audit.ValuationBoundary.toll_and_permanence.
Print Assumptions Audit.ValuationBoundary.no_boolean_shadow_rule.
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
(* === Kernel.AxShadow : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxShadow.ax_nodup_map_collision.
Print Assumptions Kernel.AxShadow.ax_filter_split.
Print Assumptions Kernel.AxShadow.ax_filter_filter_le.
Print Assumptions Kernel.AxShadow.ax_fibres_count.
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
(* === Kernel.AxThiele : 21 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.AxThiele.flat_obeys_toll.
Print Assumptions Kernel.AxThiele.ax_flat_run.
Print Assumptions Kernel.AxThiele.flat_has_no_distinction.
Print Assumptions Kernel.AxThiele.flat_is_not_thiele.
Print Assumptions Kernel.AxThiele.ax_total_pos_has_priced.
Print Assumptions Kernel.AxThiele.thiele_has_a_priced_move.
Print Assumptions Kernel.AxThiele.thiele_floor.
Print Assumptions Kernel.AxThiele.two_not_le.
Print Assumptions Kernel.AxThiele.two_point_run_crosses.
Print Assumptions Kernel.AxThiele.two_point_member_raising_move.
Print Assumptions Kernel.AxThiele.latch_is_thiele.
Print Assumptions Kernel.AxThiele.latch_merges.
Print Assumptions Kernel.AxThiele.no_one_state_member.
Print Assumptions Kernel.AxThiele.two_state_member_has_latch_move.
Print Assumptions Kernel.AxThiele.toggle_is_not_thiele.
Print Assumptions Kernel.AxThiele.history_lift_shadow.
Print Assumptions Kernel.AxThiele.history_lift_bit_stays.
Print Assumptions Kernel.AxThiele.history_lift_bit_up.
Print Assumptions Kernel.AxThiele.history_lift_is_thiele.
Print Assumptions Kernel.AxThiele.shadow_hides_history.
Print Assumptions Kernel.AxThiele.moving_machine_is_a_shadow.
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
(* === Kernel.LatchConst : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.LatchConst.const_latch_honest.
Print Assumptions Kernel.LatchConst.const_latch_no_distinction.
(* === Kernel.NatSubstrateInstance : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.NatSubstrateInstance.nat_mu_monotone.
Print Assumptions Kernel.NatSubstrateInstance.nat_encode_decode.
Print Assumptions Kernel.NatSubstrateInstance.nat_recursion_theorem.
Print Assumptions Kernel.NatSubstrateInstance.nat_no_refuses.
Print Assumptions Kernel.NatSubstrateInstance.nat_admits_extensional.
Print Assumptions Kernel.NatSubstrateInstance.nat_structural_shortcut_undecidable.
Print Assumptions Kernel.NatSubstrateInstance.nat_self_undecidable.
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
(* === Kernel.RecordAxisDiscrimination : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.RecordAxisDiscrimination.latch_core_honest.
Print Assumptions Kernel.RecordAxisDiscrimination.latch_run_shape.
Print Assumptions Kernel.RecordAxisDiscrimination.latch_constant_up.
Print Assumptions Kernel.RecordAxisDiscrimination.latch_distinguishes.
Print Assumptions Kernel.RecordAxisDiscrimination.history_latch_injective.
Print Assumptions Kernel.RecordAxisDiscrimination.history_latch_honest.
Print Assumptions Kernel.RecordAxisDiscrimination.finite_reversible_cannot_write.
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
(* === Kernel.PricingOnePremise : 25 addressable theorems (unaddressable: 0) === *)
Print Assumptions Kernel.PricingOnePremise.po_filter_split.
Print Assumptions Kernel.PricingOnePremise.po_filter_filter_le.
Print Assumptions Kernel.PricingOnePremise.po_fibres_count.
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
Print Assumptions Kernel.PricingOnePremise.eqb_s_spec.
Print Assumptions Kernel.PricingOnePremise.filter_nodup_le.
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
(* === Minimal.AccountingBridge : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.AccountingBridge.positive_filter_count.
Print Assumptions Minimal.AccountingBridge.merge_count_bounded_by_charge.
Print Assumptions Minimal.AccountingBridge.list_charge_app.
Print Assumptions Minimal.AccountingBridge.run_charge_succ.
Print Assumptions Minimal.AccountingBridge.cumulative_ledger_correspondence.
Print Assumptions Minimal.AccountingBridge.ledger_bounds_observed_merges.
Print Assumptions Minimal.AccountingBridge.finite_holding_forces_paid_run.
Print Assumptions Minimal.AccountingBridge.aggregate_bound_does_not_imply_local_coverage.
Print Assumptions Minimal.AccountingBridge.paid_entry_free_idle.
Print Assumptions Minimal.AccountingBridge.each_opcode_injective.
Print Assumptions Minimal.AccountingBridge.scheduling_can_merge.
Print Assumptions Minimal.AccountingBridge.opcode_injectivity_does_not_price_dispatch.
(* === Minimal.BrownianComputer : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.BrownianComputer.ratio_gt_1.
Print Assumptions Minimal.BrownianComputer.ratio_lt_1.
Print Assumptions Minimal.BrownianComputer.heat_at_any_speed.
Print Assumptions Minimal.BrownianComputer.no_heat_at_rest.
Print Assumptions Minimal.BrownianComputer.ln_le_minus1.
Print Assumptions Minimal.BrownianComputer.ln_ratio_ge_v.
Print Assumptions Minimal.BrownianComputer.heat_time_floor.
(* === Minimal.CommutationObstruction : 9 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CommutationObstruction.initial_early.
Print Assumptions Minimal.CommutationObstruction.F_early.
Print Assumptions Minimal.CommutationObstruction.G_early.
Print Assumptions Minimal.CommutationObstruction.three_zero_states.
Print Assumptions Minimal.CommutationObstruction.four_zero_if_singletons.
Print Assumptions Minimal.CommutationObstruction.add_sides.
Print Assumptions Minimal.CommutationObstruction.capacity_of_distinct.
Print Assumptions Minimal.CommutationObstruction.unrestricted_exclusive_resets_need_five.
Print Assumptions Minimal.CommutationObstruction.commuting_exclusive_resets_need_six.
(* === Minimal.CommutingGrid : 18 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CommutingGrid.steps_commute.
Print Assumptions Minimal.CommutingGrid.left_injective.
Print Assumptions Minimal.CommutingGrid.right_injective.
Print Assumptions Minimal.CommutingGrid.left_projects.
Print Assumptions Minimal.CommutingGrid.right_projects.
Print Assumptions Minimal.CommutingGrid.initial_grid.
Print Assumptions Minimal.CommutingGrid.reachable_exact.
Print Assumptions Minimal.CommutingGrid.diagonal_exact.
Print Assumptions Minimal.CommutingGrid.triangle_exact.
Print Assumptions Minimal.CommutingGrid.prefix_exact.
Print Assumptions Minimal.CommutingGrid.map_injective_nodup.
Print Assumptions Minimal.CommutingGrid.diagonal_nodup.
Print Assumptions Minimal.CommutingGrid.append_disjoint_nodup.
Print Assumptions Minimal.CommutingGrid.triangle_nodup.
Print Assumptions Minimal.CommutingGrid.prefix_nodup.
Print Assumptions Minimal.CommutingGrid.diagonal_length.
Print Assumptions Minimal.CommutingGrid.triangle_length.
Print Assumptions Minimal.CommutingGrid.exact_reachable_capacity.
(* === Minimal.CompleteHost : 32 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.CompleteHost.iter_add.
Print Assumptions Minimal.CompleteHost.iter_succ_from.
Print Assumptions Minimal.CompleteHost.nodup_map_on.
Print Assumptions Minimal.CompleteHost.positive_iter_held.
Print Assumptions Minimal.CompleteHost.held_prefix_distinct.
Print Assumptions Minimal.CompleteHost.held_prefix_capacity.
Print Assumptions Minimal.CompleteHost.injective_host_fresh_forever.
Print Assumptions Minimal.CompleteHost.finite_held_region_not_injective.
Print Assumptions Minimal.CompleteHost.finite_hold_collision.
Print Assumptions Minimal.CompleteHost.finite_hold_run_collision.
Print Assumptions Minimal.CompleteHost.preparation_capacity.
Print Assumptions Minimal.CompleteHost.projected_guest_trace.
Print Assumptions Minimal.CompleteHost.guest_not_halted_early.
Print Assumptions Minimal.CompleteHost.last_running_outside.
Print Assumptions Minimal.CompleteHost.last_running_enters.
Print Assumptions Minimal.CompleteHost.held_closed.
Print Assumptions Minimal.CompleteHost.completed_trace_stays_visible.
Print Assumptions Minimal.CompleteHost.all_time_projection.
Print Assumptions Minimal.CompleteHost.prepared_execution_prefix.
Print Assumptions Minimal.CompleteHost.cropped_frame_finite_hold.
Print Assumptions Minimal.CompleteHost.cropped_frame_injective_hold.
Print Assumptions Minimal.CompleteHost.cropped_frame_holding_capacity.
Print Assumptions Minimal.CompleteHost.complete_host_finite.
Print Assumptions Minimal.CompleteHost.completed_view_cannot_decode_time.
Print Assumptions Minimal.CompleteHost.preparation_has_unique_preimage.
Print Assumptions Minimal.CompleteHost.first_halt_has_unique_preimage.
Print Assumptions Minimal.CompleteHost.delayed_collision_in_held_region.
Print Assumptions Minimal.CompleteHost.start_membership_not_permanent.
Print Assumptions Minimal.CompleteHost.retaining_program_preserves_injectivity.
Print Assumptions Minimal.CompleteHost.reusable_toggle_is_injective.
Print Assumptions Minimal.CompleteHost.reusable_toggle_returns.
Print Assumptions Minimal.CompleteHost.constant_view_cannot_recover_full_state.
(* === Minimal.EditionCapacity : 13 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EditionCapacity.run_append.
Print Assumptions Minimal.EditionCapacity.block_effect.
Print Assumptions Minimal.EditionCapacity.realize_every_history.
Print Assumptions Minimal.EditionCapacity.trailing_false_irrelevant.
Print Assumptions Minimal.EditionCapacity.exact_edition_queries.
Print Assumptions Minimal.EditionCapacity.common_workspace.
Print Assumptions Minimal.EditionCapacity.distinct_histories_same_workspace.
Print Assumptions Minimal.EditionCapacity.edition_history_capacity.
Print Assumptions Minimal.EditionCapacity.no_finite_history_cover.
Print Assumptions Minimal.EditionCapacity.model_attains_exact_profile_count.
Print Assumptions Minimal.EditionCapacity.workspace_write_preserves_historical_queries.
Print Assumptions Minimal.EditionCapacity.workspace_step_independent_of_history.
Print Assumptions Minimal.EditionCapacity.current_certification_is_not_the_permanent_boolean.
(* === Minimal.EditionHistory : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.EditionHistory.journal_step_consistent.
Print Assumptions Minimal.EditionHistory.abstraction_step.
Print Assumptions Minimal.EditionHistory.all_program_history_refinement.
Print Assumptions Minimal.EditionHistory.abstraction_query.
Print Assumptions Minimal.EditionHistory.exact_records_every_program.
(* === Minimal.Erasure : 10 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Erasure.mixed_fibre_excludes_final_verifier.
Print Assumptions Minimal.Erasure.verifier_requires_fibre_constancy.
Print Assumptions Minimal.Erasure.fibre_constancy_suffices_with_representatives.
Print Assumptions Minimal.Erasure.searching_a_valid_preimage_is_not_actual_history.
Print Assumptions Minimal.Erasure.inline_reading_is_exact.
Print Assumptions Minimal.Erasure.mixed_fibre_forces_distinct_enriched_states.
Print Assumptions Minimal.Erasure.collision_does_not_always_prevent_verification.
Print Assumptions Minimal.Erasure.fixed_length_injective_history.
Print Assumptions Minimal.Erasure.unknown_duration_can_hide_history_under_injective_steps.
Print Assumptions Minimal.Erasure.different_injective_programs_can_hide_history.
(* === Minimal.Fibre : 1 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Fibre.permanent_check_in_finite_fibre_merges.
(* === Minimal.GeometryLimits : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.GeometryLimits.idempotent_changed_state_collides.
Print Assumptions Minimal.GeometryLimits.preserving_record_does_not_force_shadow_independence.
Print Assumptions Minimal.GeometryLimits.ordinary_record_variable_is_protected.
Print Assumptions Minimal.GeometryLimits.including_protected_record_in_view_need_not_be_noninjective.
(* === Minimal.GibbsGap : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.GibbsGap.Rsum_map_plus.
Print Assumptions Minimal.GibbsGap.Rsum_map_scale.
Print Assumptions Minimal.GibbsGap.Rsum_le.
Print Assumptions Minimal.GibbsGap.Rsum_lt.
Print Assumptions Minimal.GibbsGap.Rsum_map_const.
Print Assumptions Minimal.GibbsGap.ln_le_minus1.
Print Assumptions Minimal.GibbsGap.ln_lt_minus1.
Print Assumptions Minimal.GibbsGap.N_pos.
Print Assumptions Minimal.GibbsGap.term_ge.
Print Assumptions Minimal.GibbsGap.term_gt.
Print Assumptions Minimal.GibbsGap.map_id_list.
Print Assumptions Minimal.GibbsGap.base_sum.
Print Assumptions Minimal.GibbsGap.gibbs_nonneg.
Print Assumptions Minimal.GibbsGap.gibbs_strict.
Print Assumptions Minimal.GibbsGap.relent_is_entropy_gap.
(* === Minimal.HaltingHole : 2 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.HaltingHole.partial_raises_without_merge.
Print Assumptions Minimal.HaltingHole.totalised_halt_is_merge.
(* === Minimal.HeatOrRoom : 44 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.HeatOrRoom.nodup_app_disjoint.
Print Assumptions Minimal.HeatOrRoom.nodup_flat_map.
Print Assumptions Minimal.HeatOrRoom.nodup_map_inj_on.
Print Assumptions Minimal.HeatOrRoom.nodup_map_of_inj_on.
Print Assumptions Minimal.HeatOrRoom.length_flat_map_const.
Print Assumptions Minimal.HeatOrRoom.iterF_add.
Print Assumptions Minimal.HeatOrRoom.iter_pos_yes.
Print Assumptions Minimal.HeatOrRoom.cancel_iter.
Print Assumptions Minimal.HeatOrRoom.permanent_flip_iterates_distinct.
Print Assumptions Minimal.HeatOrRoom.permanent_flip_no_finite_list.
Print Assumptions Minimal.HeatOrRoom.run_yes_after.
Print Assumptions Minimal.HeatOrRoom.run_no_before.
Print Assumptions Minimal.HeatOrRoom.run_cancel.
Print Assumptions Minimal.HeatOrRoom.run_merges_or_fresh.
Print Assumptions Minimal.HeatOrRoom.run_bounded_by_room.
Print Assumptions Minimal.HeatOrRoom.iter_pos_q0.
Print Assumptions Minimal.HeatOrRoom.cancel.
Print Assumptions Minimal.HeatOrRoom.nodes_separate.
Print Assumptions Minimal.HeatOrRoom.in_traj.
Print Assumptions Minimal.HeatOrRoom.traj_length.
Print Assumptions Minimal.HeatOrRoom.traj_nodup.
Print Assumptions Minimal.HeatOrRoom.traj_disjoint.
Print Assumptions Minimal.HeatOrRoom.others_nodup.
Print Assumptions Minimal.HeatOrRoom.nodes_nodup.
Print Assumptions Minimal.HeatOrRoom.nodes_length.
Print Assumptions Minimal.HeatOrRoom.extra_not_node.
Print Assumptions Minimal.HeatOrRoom.retention_bound.
Print Assumptions Minimal.HeatOrRoom.retention_horizon.
Print Assumptions Minimal.HeatOrRoom.tight_reset.
Print Assumptions Minimal.HeatOrRoom.tight_x0_q0.
Print Assumptions Minimal.HeatOrRoom.tight_others_not_q0.
Print Assumptions Minimal.HeatOrRoom.tight_others_distinct.
Print Assumptions Minimal.HeatOrRoom.tight_length.
Print Assumptions Minimal.HeatOrRoom.tight_length_others.
Print Assumptions Minimal.HeatOrRoom.in_path.
Print Assumptions Minimal.HeatOrRoom.tight_nodup.
Print Assumptions Minimal.HeatOrRoom.tight_closed.
Print Assumptions Minimal.HeatOrRoom.tight_reps_in.
Print Assumptions Minimal.HeatOrRoom.iter_node.
Print Assumptions Minimal.HeatOrRoom.iter_Z.
Print Assumptions Minimal.HeatOrRoom.reached_shape.
Print Assumptions Minimal.HeatOrRoom.tight_retain.
Print Assumptions Minimal.HeatOrRoom.tight_merges_next.
Print Assumptions Minimal.HeatOrRoom.tight_exact.
(* === Minimal.KeptDistinction : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.KeptDistinction.write_is_permanent.
Print Assumptions Minimal.KeptDistinction.write_raises.
Print Assumptions Minimal.KeptDistinction.write_is_a_merge.
Print Assumptions Minimal.KeptDistinction.four_state_escape_fails.
Print Assumptions Minimal.KeptDistinction.tape_write_injective.
Print Assumptions Minimal.KeptDistinction.tape_write_never_returns.
Print Assumptions Minimal.KeptDistinction.no_space_holds_its_own_readings.
Print Assumptions Minimal.KeptDistinction.regress_price_unbounded.
Print Assumptions Minimal.KeptDistinction.shift_bijective.
Print Assumptions Minimal.KeptDistinction.shift_raises_and_keeps.
Print Assumptions Minimal.KeptDistinction.iter_shift_val.
Print Assumptions Minimal.KeptDistinction.shift_never_returns.
(* === Minimal.MeterRepresentation : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.MeterRepresentation.reset_prefix_meter_not_a_state_function.
Print Assumptions Minimal.MeterRepresentation.reset_prefix_merge_not_a_state_function.
Print Assumptions Minimal.MeterRepresentation.clock_projects.
Print Assumptions Minimal.MeterRepresentation.clock_orbit.
Print Assumptions Minimal.MeterRepresentation.clock_orbit_distinct.
Print Assumptions Minimal.MeterRepresentation.clock_run_retains.
Print Assumptions Minimal.MeterRepresentation.clock_run_no_observed_merges.
Print Assumptions Minimal.MeterRepresentation.clock_run_room.
Print Assumptions Minimal.MeterRepresentation.clock_full_meter.
Print Assumptions Minimal.MeterRepresentation.clock_can_represent_original_meter.
Print Assumptions Minimal.MeterRepresentation.instrumentation_changes_full_graph_meter.
(* === Minimal.Monitor : 14 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Monitor.step_matches_history.
Print Assumptions Minimal.Monitor.every_program_matches_history.
Print Assumptions Minimal.Monitor.exact_historical_verdict.
Print Assumptions Minimal.Monitor.truth_soundness.
Print Assumptions Minimal.Monitor.every_full_state_is_reachable.
Print Assumptions Minimal.Monitor.unchecked_steps_keep_verdict_false.
Print Assumptions Minimal.Monitor.no_unchecked_forgery.
Print Assumptions Minimal.Monitor.reachability_does_not_supply_unchecked_reachability.
Print Assumptions Minimal.Monitor.two_histories_one_data_two_states.
Print Assumptions Minimal.Monitor.writes_invalidate_without_versions.
Print Assumptions Minimal.Monitor.current_verdict_is_not_permanent.
Print Assumptions Minimal.Monitor.repeated_check_merges_inside_one_fibre.
Print Assumptions Minimal.Monitor.single_fixed_map_contains_arbitrary_programs.
Print Assumptions Minimal.Monitor.sound_use_does_not_force_saved_record_mutation.
(* === Minimal.MuCore : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.MuCore.mu_conservation.
Print Assumptions Minimal.MuCore.mu_conservation_trace.
Print Assumptions Minimal.MuCore.a2.
Print Assumptions Minimal.MuCore.nfi_floor.
Print Assumptions Minimal.MuCore.only_certify_certifies.
Print Assumptions Minimal.MuCore.receipt_separation.
Print Assumptions Minimal.MuCore.no_mu_oracle.
Print Assumptions Minimal.MuCore.no_cert_oracle.
Print Assumptions Minimal.MuCore.run_cons.
Print Assumptions Minimal.MuCore.crun_cons.
Print Assumptions Minimal.MuCore.classical_conservativity.
Print Assumptions Minimal.MuCore.classical_embedding.
(* === Minimal.MultiExecution : 12 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.MultiExecution.layer_distinct.
Print Assumptions Minimal.MultiExecution.layer_image.
Print Assumptions Minimal.MultiExecution.size_nonincreasing.
Print Assumptions Minimal.MultiExecution.exact_loss_telescopes.
Print Assumptions Minimal.MultiExecution.final_capacity.
Print Assumptions Minimal.MultiExecution.ensemble_loss_bound.
Print Assumptions Minimal.MultiExecution.drop_witness.
Print Assumptions Minimal.MultiExecution.decrease_time.
Print Assumptions Minimal.MultiExecution.execution_collision_before_deadline.
Print Assumptions Minimal.MultiExecution.canonical_output_loss.
Print Assumptions Minimal.MultiExecution.halving_edge.
Print Assumptions Minimal.MultiExecution.execution_halving_bound.
(* === Minimal.Multiplicity : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Multiplicity.mass_empty.
Print Assumptions Minimal.Multiplicity.mass_cons.
Print Assumptions Minimal.Multiplicity.count_partition.
Print Assumptions Minimal.Multiplicity.mass_bound.
Print Assumptions Minimal.Multiplicity.bounded_multiplicity_capacity.
Print Assumptions Minimal.Multiplicity.overcapacity_forces_large_pile.
Print Assumptions Minimal.Multiplicity.preparation_overcapacity.
(* === Minimal.Napkin : 11 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Napkin.run2_raise.
Print Assumptions Minimal.Napkin.smallest_machine_merges.
Print Assumptions Minimal.Napkin.latch_meets_definition.
Print Assumptions Minimal.Napkin.cost_blind_admits_free_cert.
Print Assumptions Minimal.Napkin.gate_step_is_substrate.
Print Assumptions Minimal.Napkin.forge_step_not_substrate.
Print Assumptions Minimal.Napkin.shadows_agree.
Print Assumptions Minimal.Napkin.no_mu_oracle.
Print Assumptions Minimal.Napkin.no_cert_oracle.
Print Assumptions Minimal.Napkin.free_run_forges.
Print Assumptions Minimal.Napkin.substrate_forbids_free_flip.
(* === Minimal.NecTPartition : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NecTPartition.nec_t_rel_of_partition_equiv.
Print Assumptions Minimal.NecTPartition.nec_t_blocks_of_equiv_partition.
Print Assumptions Minimal.NecTPartition.nec_t_rel_round_trip.
Print Assumptions Minimal.NecTPartition.nec_t_blocks_round_trip.
Print Assumptions Minimal.NecTPartition.nec_t_nonempty_needed.
Print Assumptions Minimal.NecTPartition.nec_t_cover_needed.
Print Assumptions Minimal.NecTPartition.nec_t_disjoint_needed.
(* === Minimal.NoisyChairs : 27 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NoisyChairs.Qsum_map_plus.
Print Assumptions Minimal.NoisyChairs.Qsum_map_ext.
Print Assumptions Minimal.NoisyChairs.Qsum_swap.
Print Assumptions Minimal.NoisyChairs.Qsum_nonneg.
Print Assumptions Minimal.NoisyChairs.Qsum_zero_each.
Print Assumptions Minimal.NoisyChairs.Qsum_map_zero.
Print Assumptions Minimal.NoisyChairs.Qsum_map_scale.
Print Assumptions Minimal.NoisyChairs.len_cons.
Print Assumptions Minimal.NoisyChairs.Qsum_pos_of_member.
Print Assumptions Minimal.NoisyChairs.Qsq_nonneg.
Print Assumptions Minimal.NoisyChairs.Qsq_pos.
Print Assumptions Minimal.NoisyChairs.Qsum_le.
Print Assumptions Minimal.NoisyChairs.total_into.
Print Assumptions Minimal.NoisyChairs.split_rows.
Print Assumptions Minimal.NoisyChairs.inside_rows.
Print Assumptions Minimal.NoisyChairs.into_nonneg.
Print Assumptions Minimal.NoisyChairs.no_entry_from_outside.
Print Assumptions Minimal.NoisyChairs.noisy_chairs.
Print Assumptions Minimal.NoisyChairs.colsums_total.
Print Assumptions Minimal.NoisyChairs.raise_breaks_uniform.
Print Assumptions Minimal.NoisyChairs.expand.
Print Assumptions Minimal.NoisyChairs.raise_concentrates.
Print Assumptions Minimal.NoisyChairs.uniform_floor.
Print Assumptions Minimal.NoisyChairs.variance_identity.
Print Assumptions Minimal.NoisyChairs.column_jensen.
Print Assumptions Minimal.NoisyChairs.no_merge_no_concentration.
Print Assumptions Minimal.NoisyChairs.raise_concentrates_uniform.
(* === Minimal.NondetChairs : 4 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.NondetChairs.g_in.
Print Assumptions Minimal.NondetChairs.g_R.
Print Assumptions Minimal.NondetChairs.map_collision.
Print Assumptions Minimal.NondetChairs.nondet_merge.
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
(* === Minimal.PassiveGeometry : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.PassiveGeometry.horizontal_projection.
Print Assumptions Minimal.PassiveGeometry.horizontal_preserves_record.
Print Assumptions Minimal.PassiveGeometry.permanent_trajectory_blindness.
Print Assumptions Minimal.PassiveGeometry.no_in_view_decoder.
Print Assumptions Minimal.PassiveGeometry.vertical_change_forces_nontrivial_fibre.
(* === Minimal.PeriodicIntersection : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.PeriodicIntersection.F_G_power.
Print Assumptions Minimal.PeriodicIntersection.powers_commute.
Print Assumptions Minimal.PeriodicIntersection.crossing_periodicity.
Print Assumptions Minimal.PeriodicIntersection.crossing_only_in_tails.
Print Assumptions Minimal.PeriodicIntersection.unit_period_crossing_is_joint_end.
Print Assumptions Minimal.PeriodicIntersection.iterate_injective.
Print Assumptions Minimal.PeriodicIntersection.global_crossing_forces_periodic_seed.
Print Assumptions Minimal.PeriodicIntersection.population_arithmetic.
(* === Minimal.QuantumChairs : 22 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.QuantumChairs.adjM.
Print Assumptions Minimal.QuantumChairs.adjD.
Print Assumptions Minimal.QuantumChairs.adjN.
Print Assumptions Minimal.QuantumChairs.adj1.
Print Assumptions Minimal.QuantumChairs.adjB.
Print Assumptions Minimal.QuantumChairs.PQ.
Print Assumptions Minimal.QuantumChairs.QP.
Print Assumptions Minimal.QuantumChairs.QQ.
Print Assumptions Minimal.QuantumChairs.adjQ.
Print Assumptions Minimal.QuantumChairs.PQ1.
Print Assumptions Minimal.QuantumChairs.UP_eq.
Print Assumptions Minimal.QuantumChairs.adjV_direct.
Print Assumptions Minimal.QuantumChairs.adjV.
Print Assumptions Minimal.QuantumChairs.adjV_V.
Print Assumptions Minimal.QuantumChairs.adjV_Q.
Print Assumptions Minimal.QuantumChairs.Q_V.
Print Assumptions Minimal.QuantumChairs.V_Q.
Print Assumptions Minimal.QuantumChairs.Q_adjV.
Print Assumptions Minimal.QuantumChairs.left_inv.
Print Assumptions Minimal.QuantumChairs.right_inv.
Print Assumptions Minimal.QuantumChairs.V_adjV.
Print Assumptions Minimal.QuantumChairs.quantum_chairs.
(* === Minimal.Recurrence : 5 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Recurrence.NoDup_snoc.
Print Assumptions Minimal.Recurrence.nodup_or_collision.
Print Assumptions Minimal.Recurrence.some_revisit.
Print Assumptions Minimal.Recurrence.returns_to_start.
Print Assumptions Minimal.Recurrence.reversible_keeps_nothing.
(* === Minimal.Representation : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Representation.unchecked_reachability_excludes_positive_verdict.
Print Assumptions Minimal.Representation.same_workspace_different_history_forces_distinct_states.
Print Assumptions Minimal.Representation.workspace_verdict_impossible.
Print Assumptions Minimal.Representation.map_injective_nodup.
Print Assumptions Minimal.Representation.nodup_append_separate.
Print Assumptions Minimal.Representation.profiles_length.
Print Assumptions Minimal.Representation.profiles_complete.
Print Assumptions Minimal.Representation.profiles_nodup.
Print Assumptions Minimal.Representation.independent_profiles_capacity.
Print Assumptions Minimal.Representation.bitmask_capacity_attained.
Print Assumptions Minimal.Representation.legal_profiles_count.
Print Assumptions Minimal.Representation.legal_profiles_distinct.
Print Assumptions Minimal.Representation.descriptions_count.
Print Assumptions Minimal.Representation.descriptions_distinct.
Print Assumptions Minimal.Representation.exact_profile_representation_lower_bound.
(* === Minimal.SharpHost : 32 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SharpHost.index_bound.
Print Assumptions Minimal.SharpHost.index_injective.
Print Assumptions Minimal.SharpHost.index_node.
Print Assumptions Minimal.SharpHost.index_node_small.
Print Assumptions Minimal.SharpHost.node_index.
Print Assumptions Minimal.SharpHost.step_index.
Print Assumptions Minimal.SharpHost.step_node.
Print Assumptions Minimal.SharpHost.iter_node.
Print Assumptions Minimal.SharpHost.all_states_exact.
Print Assumptions Minimal.SharpHost.all_states_nodup.
Print Assumptions Minimal.SharpHost.all_states_count.
Print Assumptions Minimal.SharpHost.held_states_exact.
Print Assumptions Minimal.SharpHost.held_states_nodup.
Print Assumptions Minimal.SharpHost.held_states_count.
Print Assumptions Minimal.SharpHost.entry_outside.
Print Assumptions Minimal.SharpHost.entry_enters.
Print Assumptions Minimal.SharpHost.held_closed.
Print Assumptions Minimal.SharpHost.retains_capacity.
Print Assumptions Minimal.SharpHost.first_collision.
Print Assumptions Minimal.SharpHost.fails_next_capacity.
Print Assumptions Minimal.SharpHost.capacity_exact.
Print Assumptions Minimal.SharpHost.early_not_terminal.
Print Assumptions Minimal.SharpHost.view_prep.
Print Assumptions Minimal.SharpHost.prepares_start.
Print Assumptions Minimal.SharpHost.view_node_positive.
Print Assumptions Minimal.SharpHost.view_start.
Print Assumptions Minimal.SharpHost.view_held_exact.
Print Assumptions Minimal.SharpHost.view_holds.
Print Assumptions Minimal.SharpHost.view_simulates.
Print Assumptions Minimal.SharpHost.guest_all_time.
Print Assumptions Minimal.SharpHost.entry_is_last_running.
Print Assumptions Minimal.SharpHost.sharp_finite_host_exists.
(* === Minimal.SliceCore : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SliceCore.observation_reflexive.
Print Assumptions Minimal.SliceCore.observation_symmetric.
Print Assumptions Minimal.SliceCore.observation_transitive.
Print Assumptions Minimal.SliceCore.observation_step.
Print Assumptions Minimal.SliceCore.observation_now.
Print Assumptions Minimal.SliceCore.observation_greatest.
Print Assumptions Minimal.SliceCore.erasure_least.
Print Assumptions Minimal.SliceCore.erasure_preserves_iff_marks_invisible.
Print Assumptions Minimal.SliceCore.invisible_marks_allow_purge.
Print Assumptions Minimal.SliceCore.zero_cost_preserves_ledger.
Print Assumptions Minimal.SliceCore.zero_cost_preserves_record.
Print Assumptions Minimal.SliceCore.mark_immediately_silent.
Print Assumptions Minimal.SliceCore.steering_exposes_mark.
Print Assumptions Minimal.SliceCore.no_autonomous_working_projection.
Print Assumptions Minimal.SliceCore.factorization_obstruction.
(* === Minimal.SlicedEstablishment : 15 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SlicedEstablishment.horizontal_trace_projects.
Print Assumptions Minimal.SlicedEstablishment.horizontal_trace_preserves_verdict.
Print Assumptions Minimal.SlicedEstablishment.universal_window_blindness.
Print Assumptions Minimal.SlicedEstablishment.mixed_trace_projects_after_erasure.
Print Assumptions Minimal.SlicedEstablishment.vertical_raise_forces_hidden_pair.
Print Assumptions Minimal.SlicedEstablishment.vertical_raise_fibre_capacity.
Print Assumptions Minimal.SlicedEstablishment.finite_vertical_establishment_collision.
Print Assumptions Minimal.SlicedEstablishment.abstract_establishment_necessity.
Print Assumptions Minimal.SlicedEstablishment.supplied_toll.
Print Assumptions Minimal.SlicedEstablishment.supplied_toll_run_floor.
Print Assumptions Minimal.SlicedEstablishment.horizontal_ledger_preserved.
Print Assumptions Minimal.SlicedEstablishment.independent_current_profiles_capacity.
Print Assumptions Minimal.SlicedEstablishment.Witness.exact_ever_checked_meaning.
Print Assumptions Minimal.SlicedEstablishment.Witness.clean_start_exact_history.
Print Assumptions Minimal.SlicedEstablishment.Witness.passing_check_realizes_hidden_pair.
(* === Minimal.StepLaw : 7 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.StepLaw.run_add.
Print Assumptions Minimal.StepLaw.revisit_periodic.
Print Assumptions Minimal.StepLaw.step_law.
Print Assumptions Minimal.StepLaw.merge_is_collision.
Print Assumptions Minimal.StepLaw.revisit_means_loop.
Print Assumptions Minimal.StepLaw.first_revisit_start_or_merge.
Print Assumptions Minimal.StepLaw.later_steps_repeat.
(* === Minimal.StructuralMeter : 17 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.StructuralMeter.bad_pair_exact.
Print Assumptions Minimal.StructuralMeter.merge_target_exact.
Print Assumptions Minimal.StructuralMeter.merges_zero_iff.
Print Assumptions Minimal.StructuralMeter.source_member.
Print Assumptions Minimal.StructuralMeter.no_collision_retains.
Print Assumptions Minimal.StructuralMeter.retains_no_collision.
Print Assumptions Minimal.StructuralMeter.zero_merges_iff_retains.
Print Assumptions Minimal.StructuralMeter.nonempty_run_has_room.
Print Assumptions Minimal.StructuralMeter.any_nonempty_run_has_positive_structural_mu.
Print Assumptions Minimal.StructuralMeter.zero_merges_exact_room.
Print Assumptions Minimal.StructuralMeter.merge_or_room.
Print Assumptions Minimal.StructuralMeter.room_shortfall_forces_merge.
Print Assumptions Minimal.StructuralMeter.room_bounded_by_held_capacity.
Print Assumptions Minimal.StructuralMeter.finite_room_forces_merge.
Print Assumptions Minimal.StructuralMeter.structural_mu_positive.
Print Assumptions Minimal.StructuralMeter.fixed_point_blocks_positive_internal_ledger.
Print Assumptions Minimal.StructuralMeter.structural_meter_can_plateau.
(* === Minimal.SynchronizedCapacity : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.SynchronizedCapacity.nodup_append_disjoint.
Print Assumptions Minimal.SynchronizedCapacity.nodup_product.
Print Assumptions Minimal.SynchronizedCapacity.same_time_separated.
Print Assumptions Minimal.SynchronizedCapacity.different_times_separated.
Print Assumptions Minimal.SynchronizedCapacity.spacetime_embedding_injective.
Print Assumptions Minimal.SynchronizedCapacity.synchronized_population_distinct.
Print Assumptions Minimal.SynchronizedCapacity.synchronized_population_count.
Print Assumptions Minimal.SynchronizedCapacity.synchronized_capacity_bound.
(* === Minimal.Task : 19 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.Task.permanent_current_truth_impossible.
Print Assumptions Minimal.Task.run_app.
Print Assumptions Minimal.Task.step_legal.
Print Assumptions Minimal.Task.run_legal.
Print Assumptions Minimal.Task.step_projects.
Print Assumptions Minimal.Task.autonomous_workspace.
Print Assumptions Minimal.Task.writes_invalidate_before_publication.
Print Assumptions Minimal.Task.historical_certificate_survives.
Print Assumptions Minimal.Task.current_certificate_requires_truth.
Print Assumptions Minimal.Task.only_certify_publishes.
Print Assumptions Minimal.Task.journal_consistent.
Print Assumptions Minimal.Task.compression_step.
Print Assumptions Minimal.Task.journal_refinement.
Print Assumptions Minimal.Task.exact_history_all_programs.
Print Assumptions Minimal.Task.witness_reaches.
Print Assumptions Minimal.Task.phases_legal.
Print Assumptions Minimal.Task.phases_distinct.
Print Assumptions Minimal.Task.carrier_size.
Print Assumptions Minimal.Task.signature_separates.
(* === Minimal.TwoArms : 21 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.TwoArms.commute.
Print Assumptions Minimal.TwoArms.F_projects.
Print Assumptions Minimal.TwoArms.G_projects.
Print Assumptions Minimal.TwoArms.F_closed.
Print Assumptions Minimal.TwoArms.G_closed.
Print Assumptions Minimal.TwoArms.carrier_exact.
Print Assumptions Minimal.TwoArms.append_nodup.
Print Assumptions Minimal.TwoArms.carrier_nodup.
Print Assumptions Minimal.TwoArms.carrier_size.
Print Assumptions Minimal.TwoArms.F_rank.
Print Assumptions Minimal.TwoArms.G_rank.
Print Assumptions Minimal.TwoArms.initial_valid_rank.
Print Assumptions Minimal.TwoArms.reach_valid_rank.
Print Assumptions Minimal.TwoArms.F_injective_before_end.
Print Assumptions Minimal.TwoArms.G_injective_before_end.
Print Assumptions Minimal.TwoArms.retains_through_horizon.
Print Assumptions Minimal.TwoArms.infinite_commute.
Print Assumptions Minimal.TwoArms.infinite_F_injective.
Print Assumptions Minimal.TwoArms.infinite_G_injective.
Print Assumptions Minimal.TwoArms.infinite_F_projects.
Print Assumptions Minimal.TwoArms.infinite_G_projects.
(* === Minimal.VerifierSmall : 8 addressable theorems (unaddressable: 0) === *)
Print Assumptions Minimal.VerifierSmall.ver_collision_blocks.
Print Assumptions Minimal.VerifierSmall.ver_sound_rejects.
Print Assumptions Minimal.VerifierSmall.ver_no_factor.
Print Assumptions Minimal.VerifierSmall.ver_full_state_escape.
Print Assumptions Minimal.VerifierSmall.ver_commitment_escape.
Print Assumptions Minimal.VerifierSmall.ver_honest_meets_contract.
Print Assumptions Minimal.VerifierSmall.ver_unchecked_breaks_contract.
Print Assumptions Minimal.VerifierSmall.ver_response_escape.
