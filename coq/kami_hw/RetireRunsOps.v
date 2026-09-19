(** RetireRunsOps.v: from a live boundary, the concrete scheduler runs every
    multi-cycle instruction to the boundary its retirement theorem observes.

    The step firing is selected at a live boundary ([live_step_runs]); each
    theorem below is the busy part after it. [compose_ext_runs],
    [morph_ext_runs]: the coupling FSM run. [chsh_lassert_runs]: 23 CHSH FSM
    firings. [lassert_sat_runs]: the header firing and the scan loop, with the
    scan count of [lassert_sat_refines]. Single-cycle instructions have an
    empty busy part. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval
  StepWordFacts StepFields StepRefineCommon StepRefine StepFieldsMorph StepRefineMorph
  ImplementationContract Abstraction NormalizationSteps NormalizationLoop NormalizationRetirement MorphLoading
  MorphCopy MorphJoin RuleEnabled FsmDecoded ChshDecoded ChshRun ChshStepFields ChshRetire
  LassertSpec LassertWord LassertStepFields LassertRetire CouplingFsmEnds CouplingFsmLoad CouplingFsmNorm
  CouplingFsmRun CouplingFsmCopy CouplingFsmJoin CouplingMorphRich CouplingMorphKami CouplingMorphRetire
  CouplingComposeRun CouplingComposeKami CouplingComposeRetire BoundaryRun RetireRuns RetireRunsFsm.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma live_step_runs : forall b, hw_live b -> Runs b (step_next b) 1.
Proof. intros b H. exact (runs_one b _ _ (live_step_selected b H)). Qed.

Theorem chsh_lassert_runs : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  step_fetched b = chsh_lassert_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 -> hwb_bianchi b = false -> hw_live b ->
  Busy_runs (step_next b) (chsh_iter 23 (step_next b)) 23.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb Hlive.
  destruct (chsh_run_result (step_next b) (step_chsh_lassert_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)) as [Hph _].
  exact (chsh_runs 23 (step_next b) (step_chsh_lassert_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)
    (step_chsh_lassert_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)
    (fun m Hm => eq_ind_r (fun x => x <> natToWord 5 0) (natToWord5_succ_ne0 m ltac:(lia)) (Hph m ltac:(lia)))).
Qed.

Theorem lassert_sat_runs : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen,
  step_fetched b = lassert_sat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_trap_vector b) = LASSERT_TRAP_PC ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) = flen ->
  wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 3 + flen < pow2 32 ->
  1 <= mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) <= count_zeros (lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)))) ->
  wordToNat (hw_mu b) + flen * 8 + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) + 1 < pow2 32 ->
  exists n, 1 <= n <= flen /\
    Busy_runs (step_next b) (lscan_iter n (lhdr_next (step_next b))) (1 + n) /\
    hw_idle (lscan_iter n (lhdr_next (step_next b))) /\
    hwb_snapshot (lscan_iter n (lhdr_next (step_next b))) =
    kami_step (hwb_snapshot b) (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) true flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb Hlive Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu.
  pose proof Hlive as [Hh [He _]].
  destruct (lassert_sat_refines a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb He Hh Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu)
    as [n [Hn [Hph [Hfin Hsnap]]]].
  pose proof (step_lassert_sat_lassert_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as L1.
  pose proof (step_lassert_sat_chsh_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as C1.
  pose proof (step_lassert_sat_mc_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as M1.
  exists n. split; [exact Hn|]. split; [|split; [|exact Hsnap]].
  2: { split; [exact Hfin|split].
       - rewrite lscan_iter_keeps_chsh_phase, lhdr_keeps_chsh_phase. exact C1.
       - rewrite lscan_iter_keeps_mc_phase, lhdr_keeps_mc_phase. exact M1. }
  apply (busy_runs_trans _ _ 1 (busy_one _ _ _ ltac:(apply (busy_lassert _ 1 L1); word_neq)
    (lhdr_phase_selected (step_next b) L1 C1 M1)) _ n).
  apply lscan_runs; [rewrite lhdr_keeps_chsh_phase; exact C1|rewrite lhdr_keeps_mc_phase; exact M1|exact Hph].
Qed.

Theorem compose_ext_runs : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  step_fetched b = compose_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_mu b) + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) < pow2 WordSz ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_coupling_pair_next_id b) < 16 ->
  hwb_morph_valid_below_next b -> hwb_morph_coupling_refs_ok b -> hwb_coupling_desc_zero_invalid b ->
  hwb_desc_zero_empty b -> hwb_desc_pairs_below_next b -> hwb_pairs_valid_below_next b ->
  hwb_identity_desc_zero b -> hwb_labels_represented b ->
  hw_morph_valid_table b (bits4 b0 b1 b2 b3) = true -> hw_morph_valid_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) = true ->
  hw_morph_dst_table b (bits4 b0 b1 b2 b3) = hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) ->
  wordToNat (hw_label_len b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))) + wordToNat (hw_label_len b (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) <= 32 ->
  wordToNat (hw_coupling_pair_next_id b) + List.length (compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 16 ->
  exists k, Busy_runs (step_next b) (compose_fsm_final (step_next b)) k.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 Imv Iref Iz Iz0 Idp Ipv Iid Ilab V1 V2 Hmatch Hlab Hcap.
  pose proof (step_compose_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_compose_ext_mc_i a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_i.
  pose proof (step_compose_ext_mc_j a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_j.
  pose proof (step_compose_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_compose_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  pose proof (step_compose_ext_mc_src1_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src1_count.
  pose proof (step_compose_ext_mc_src2_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src2_count.
  pose proof (step_compose_ext_mc_src1_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src1_base.
  pose proof (step_compose_ext_mc_src2_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src2_base.
  pose proof (step_compose_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_compose_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), (morph_live_valid b (bits4 b0 b1 b2 b3) Imv),
    (morph_live_valid b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Imv), V1, V2, Hmatch in *.
  destruct (weq (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) as [_|NE]; [|contradiction].
  cbv beta iota in F_mc_phase, F_mc_i, F_mc_j, F_mc_write_base, F_mc_write_ptr, F_mc_src1_count, F_mc_src2_count, F_mc_src1_base, F_mc_src2_base, F_lassert_phase, F_chsh_phase.
  set (P := wordToNat (hw_coupling_pair_next_id b)) in *.
  assert (HPb : hw_coupling_pair_next_id b = natToWord 5 P) by (unfold P; symmetry; apply natToWord_wordToNat).
  pose proof (desc_fits b (bits4 b0 b1 b2 b3) Iref Iz0 Idp V1) as Fit1. pose proof (desc_fits b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Iref Iz0 Idp V2) as Fit2.
  fold P in Fit1, Fit2.
  assert (Raw : compose_raw (step_next b) = compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
    by exact (compose_raw_step b (step_next b) (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Iid Iz0 V2
      (step_keeps_coupling_pair_src_table b) (step_keeps_coupling_pair_dst_table b)
      F_mc_phase F_mc_src1_count F_mc_src2_count F_mc_src1_base F_mc_src2_base).
  assert (W0 : wordToNat (natToWord CouplingPairCountSz 0) = 0) by reflexivity.
  destruct (compose_fsm_runs (step_next b) P
    ltac:(rewrite F_mc_phase; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)), (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); auto)
    F_mc_i F_mc_j ltac:(rewrite F_mc_write_base; exact HPb) ltac:(rewrite F_mc_write_ptr; exact HPb)
    ltac:(rewrite F_mc_src1_count; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); lia)
    ltac:(rewrite F_mc_src2_count; destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); lia)
    ltac:(rewrite F_mc_src1_count, F_mc_src1_base; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); lia)
    ltac:(rewrite F_mc_src2_count, F_mc_src2_base; destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); lia)
    ltac:(rewrite Raw; exact Hcap) F_lassert_phase F_chsh_phase)
    as [k Rk].
  exists k. exact Rk.
Qed.

Theorem morph_ext_runs : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) count,
  step_fetched b = morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_ptTable b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) <> 0 -> wordToNat (hw_ptTable b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <> 0 ->
  hw_mem b (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) = natToWord 32 count ->
  count + wordToNat (hw_coupling_pair_next_id b) <= 16 -> 2 * count + wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 127 ->
  exists k, Busy_runs (step_next b) (morph_fsm_final count (step_next b)) k.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hroom Hdesc Hsrc Hdst Hcount Hfit Hbase.
  pose proof (step_morph_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_morph_ext_mc_mem_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_mem_base.
  pose proof (step_morph_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_morph_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  pose proof (step_morph_ext_mem a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mem.
  pose proof (step_morph_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_morph_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), !module_present_eqb,
    (proj2 (Nat.eqb_neq _ _) Hsrc), (proj2 (Nat.eqb_neq _ _) Hdst) in *.
  cbv beta iota delta [negb] in F_mc_phase, F_mc_mem_base, F_mc_write_base, F_mc_write_ptr, F_mem, F_lassert_phase, F_chsh_phase.
  set (P := wordToNat (hw_coupling_pair_next_id b)).
  assert (HP : hw_coupling_pair_next_id (step_next b) = natToWord 5 P)
    by (rewrite step_keeps_coupling_pair_next_id; unfold P; symmetry; apply natToWord_wordToNat).
  destruct (morph_fsm_runs (step_next b) (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) P count
    ltac:(rewrite F_mc_phase; reflexivity) F_mc_mem_base HP
    ltac:(rewrite F_mc_write_base; exact HP) ltac:(rewrite F_mc_write_ptr; exact HP)
    ltac:(rewrite F_mem, split1_zext7; exact Hcount) ltac:(unfold P in *; lia) Hbase
    F_lassert_phase F_chsh_phase)
    as [k Rk].
  exists k. exact Rk.
Qed.
