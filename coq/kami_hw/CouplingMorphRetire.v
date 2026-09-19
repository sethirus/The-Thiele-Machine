(** CouplingMorphRetire.v: retirement of MORPH at its extended encoding.
    [morph_ext_run]: from a live boundary, the step firing and the coupling FSM
    run (header, loading, normalization, commit) are an actual Kami execution.
    [morph_ext_retire]: its final snapshot equals [kami_step] of the MORPH
    instruction. Admission premises: morph and descriptor room; source and
    target modules present; the serialized pair count fits the pair table
    (count plus pair pointer at most 16, pair pointer below 16) and memory
    (pairs and the label word below address 128); an empty label; and every
    declared pair within the source and target regions. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval
  StepWordFacts StepFields StepRefineCommon StepRefine StepFieldsMorph StepRefineMorph
  ImplementationContract Abstraction NormalizationSteps NormalizationLoop NormalizationRetirement MorphLoading
  RuleEnabled FsmDecoded ChshRetire CouplingFsmEnds CouplingFsmLoad CouplingFsmNorm CouplingFsmRun
  CouplingMorphRich CouplingMorphKami.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma desc_room_of_lt : forall b, wordToNat (hw_coupling_desc_next_id b) < 16 -> hw_desc_room b = true.
Proof.
  intros b H. unfold hw_desc_room. destruct (wlt_dec _ _) as [_|N]; [reflexivity|].
  exfalso. apply N. apply lt_wlt. rewrite wordToNat_natToWord_2 by (cbn; lia). exact H.
Qed.

Lemma split1_zext7 : forall w : word 7, split1 7 25 (zext w 25) = w.
Proof. intro w. unfold zext. apply split1_combine. Qed.

Theorem morph_ext_run : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) count,
  step_fetched b = morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_ptTable b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) <> 0 -> wordToNat (hw_ptTable b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <> 0 ->
  hw_mem b (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) = natToWord 32 count ->
  count + wordToNat (hw_coupling_pair_next_id b) <= 16 -> 2 * count + wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 127 ->
  exists labels, Multistep thieleCore (hwb_regs b) (hwb_regs (morph_fsm_final count (step_next b))) labels.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hroom Hdesc Hsrc Hdst Hcount Hfit Hbase.
  pose proof Hlive as [Hh [He _]].
  pose proof (step_morph_ext_pc a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pc.
  pose proof (step_morph_ext_mu a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu.
  pose proof (step_morph_ext_err a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_err.
  pose proof (step_morph_ext_halted a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_halted.
  pose proof (step_morph_ext_regs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_regs.
  pose proof (step_morph_ext_mem a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mem.
  pose proof (step_morph_ext_error_code a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_error_code.
  pose proof (step_morph_ext_cert_addr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_cert_addr.
  pose proof (step_morph_ext_partition_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_partition_ops.
  pose proof (step_morph_ext_mdl_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mdl_ops.
  pose proof (step_morph_ext_info_gain a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_info_gain.
  pose proof (step_morph_ext_mu_tensor a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu_tensor.
  pose proof (step_morph_ext_module_tensors a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_module_tensors.
  pose proof (step_morph_ext_ptTable a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ptTable.
  pose proof (step_morph_ext_pt_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pt_next_id.
  pose proof (step_morph_ext_certified a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_certified.
  pose proof (step_morph_ext_wc_same_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_00.
  pose proof (step_morph_ext_wc_diff_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_00.
  pose proof (step_morph_ext_wc_same_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_01.
  pose proof (step_morph_ext_wc_diff_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_01.
  pose proof (step_morph_ext_wc_same_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_10.
  pose proof (step_morph_ext_wc_diff_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_10.
  pose proof (step_morph_ext_wc_same_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_11.
  pose proof (step_morph_ext_wc_diff_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_11.
  pose proof (step_morph_ext_morph_src_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_src_table.
  pose proof (step_morph_ext_morph_dst_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_dst_table.
  pose proof (step_morph_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_coupling_desc_table.
  pose proof (step_morph_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_identity_table.
  pose proof (step_morph_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_valid_table.
  pose proof (step_morph_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_next_id.
  pose proof (step_morph_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_table.
  pose proof (step_morph_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_len_table.
  pose proof (step_morph_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_morph_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  pose proof (step_morph_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_morph_ext_mc_mem_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_mem_base.
  pose proof (step_morph_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_morph_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), !module_present_eqb,
    (proj2 (Nat.eqb_neq _ _) Hsrc), (proj2 (Nat.eqb_neq _ _) Hdst) in *.
  cbv beta iota delta [negb] in F_pc, F_mu, F_err, F_halted, F_regs, F_mem, F_error_code, F_cert_addr, F_partition_ops, F_mdl_ops, F_info_gain, F_mu_tensor, F_module_tensors, F_ptTable, F_pt_next_id, F_certified, F_wc_same_00, F_wc_diff_00, F_wc_same_01, F_wc_diff_01, F_wc_same_10, F_wc_diff_10, F_wc_same_11, F_wc_diff_11, F_morph_src_table, F_morph_dst_table, F_morph_coupling_desc_table, F_morph_identity_table, F_morph_valid_table, F_morph_next_id, F_coupling_desc_label_table, F_coupling_desc_label_len_table, F_lassert_phase, F_chsh_phase, F_mc_phase, F_mc_mem_base, F_mc_write_base, F_mc_write_ptr.
  set (P := wordToNat (hw_coupling_pair_next_id b)).
  assert (HP : hw_coupling_pair_next_id (step_next b) = natToWord 5 P)
    by (rewrite step_keeps_coupling_pair_next_id; unfold P; symmetry; apply natToWord_wordToNat).
  destruct (morph_fsm_run (step_next b) (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) P count
    ltac:(rewrite F_mc_phase; reflexivity) F_mc_mem_base HP
    ltac:(rewrite F_mc_write_base; exact HP) ltac:(rewrite F_mc_write_ptr; exact HP)
    ltac:(rewrite F_mem, split1_zext7; exact Hcount) ltac:(unfold P in *; lia) Hbase)
    as [l [out [src' [dst' [Hrun _]]]]].
  eexists. eapply normalization_multistep_trans; [exact (live_step_multistep b Hlive)|exact Hrun].
Qed.

Theorem morph_ext_retire : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) count,
  step_fetched b = morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_mu b) + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) < pow2 WordSz ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_ptTable b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) <> 0 -> wordToNat (hw_ptTable b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <> 0 ->
  hw_mem b (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) = natToWord 32 count ->
  count + wordToNat (hw_coupling_pair_next_id b) <= 16 -> wordToNat (hw_coupling_pair_next_id b) < 16 ->
  2 * count + wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 127 ->
  wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) + 1 + 2 * count < 128 ->
  hw_mem b (natToWord 7 (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) + 1 + 2 * count)) = natToWord 32 0 ->
  forallb (pair_respects_regions (snap_region (hwb_snapshot b) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7)))) (snap_region (hwb_snapshot b) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))))
    (load_coupling_pairs_from_mem (snapshot_mem_to_list (snap_mem (hwb_snapshot b))) (S (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))))) count) = true ->
  hwb_snapshot (morph_fsm_final count (step_next b)) =
  kami_step (hwb_snapshot b) (instr_morph (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hpc Hmu Hroom Hdesc Hsrc Hdst Hcount Hfit HP16 Hbase Hlab128 Hlabel Hreg.
  pose proof Hlive as [Hh [He _]].
  pose proof (step_morph_ext_pc a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pc.
  pose proof (step_morph_ext_mu a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu.
  pose proof (step_morph_ext_err a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_err.
  pose proof (step_morph_ext_halted a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_halted.
  pose proof (step_morph_ext_regs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_regs.
  pose proof (step_morph_ext_mem a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mem.
  pose proof (step_morph_ext_error_code a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_error_code.
  pose proof (step_morph_ext_cert_addr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_cert_addr.
  pose proof (step_morph_ext_partition_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_partition_ops.
  pose proof (step_morph_ext_mdl_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mdl_ops.
  pose proof (step_morph_ext_info_gain a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_info_gain.
  pose proof (step_morph_ext_mu_tensor a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu_tensor.
  pose proof (step_morph_ext_module_tensors a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_module_tensors.
  pose proof (step_morph_ext_ptTable a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ptTable.
  pose proof (step_morph_ext_pt_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pt_next_id.
  pose proof (step_morph_ext_certified a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_certified.
  pose proof (step_morph_ext_wc_same_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_00.
  pose proof (step_morph_ext_wc_diff_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_00.
  pose proof (step_morph_ext_wc_same_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_01.
  pose proof (step_morph_ext_wc_diff_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_01.
  pose proof (step_morph_ext_wc_same_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_10.
  pose proof (step_morph_ext_wc_diff_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_10.
  pose proof (step_morph_ext_wc_same_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_11.
  pose proof (step_morph_ext_wc_diff_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_11.
  pose proof (step_morph_ext_morph_src_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_src_table.
  pose proof (step_morph_ext_morph_dst_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_dst_table.
  pose proof (step_morph_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_coupling_desc_table.
  pose proof (step_morph_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_identity_table.
  pose proof (step_morph_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_valid_table.
  pose proof (step_morph_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_next_id.
  pose proof (step_morph_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_table.
  pose proof (step_morph_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_len_table.
  pose proof (step_morph_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_morph_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  pose proof (step_morph_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_morph_ext_mc_mem_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_mem_base.
  pose proof (step_morph_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_morph_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), !module_present_eqb,
    (proj2 (Nat.eqb_neq _ _) Hsrc), (proj2 (Nat.eqb_neq _ _) Hdst) in *.
  cbv beta iota delta [negb] in F_pc, F_mu, F_err, F_halted, F_regs, F_mem, F_error_code, F_cert_addr, F_partition_ops, F_mdl_ops, F_info_gain, F_mu_tensor, F_module_tensors, F_ptTable, F_pt_next_id, F_certified, F_wc_same_00, F_wc_diff_00, F_wc_same_01, F_wc_diff_01, F_wc_same_10, F_wc_diff_10, F_wc_same_11, F_wc_diff_11, F_morph_src_table, F_morph_dst_table, F_morph_coupling_desc_table, F_morph_identity_table, F_morph_valid_table, F_morph_next_id, F_coupling_desc_label_table, F_coupling_desc_label_len_table, F_lassert_phase, F_chsh_phase, F_mc_phase, F_mc_mem_base, F_mc_write_base, F_mc_write_ptr.
  set (P := wordToNat (hw_coupling_pair_next_id b)) in *.
  assert (HPb : hw_coupling_pair_next_id b = natToWord 5 P) by (unfold P; symmetry; apply natToWord_wordToNat).
  assert (HP : hw_coupling_pair_next_id (step_next b) = natToWord 5 P)
    by (rewrite step_keeps_coupling_pair_next_id; exact HPb).
  destruct (morph_fsm_run (step_next b) (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) P count
    ltac:(rewrite F_mc_phase; reflexivity) F_mc_mem_base HP
    ltac:(rewrite F_mc_write_base; exact HP) ltac:(rewrite F_mc_write_ptr; exact HP)
    ltac:(rewrite F_mem, split1_zext7; exact Hcount) ltac:(lia) Hbase)
    as [l [out [src' [dst' [_ [Hout [Hslice [Hpre [Rs [Rd [Rv [Rn [Rph [Rwb [RdB [RdC [RdV [RdN [Rerr Rec]]]]]]]]]]]]]]]]]]].
  rewrite F_mem, step_keeps_coupling_pair_src_table, step_keeps_coupling_pair_dst_table in Hslice.
  rewrite step_keeps_coupling_pair_src_table, step_keeps_coupling_pair_dst_table in Hpre.
  rewrite step_keeps_coupling_pair_valid_table in Rv.
  rewrite step_keeps_coupling_desc_base_table, step_keeps_coupling_desc_next_id in RdB.
  rewrite step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id in RdC.
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_next_id in RdV.
  rewrite step_keeps_coupling_desc_next_id in RdN.
  set (Fin := morph_fsm_final count (step_next b)) in *.
  set (memlist := snapshot_mem_to_list (snap_mem (hwb_snapshot b))) in *.
  assert (Hb128 : wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) < 128) by lia.
  assert (Cnt : serialized_coupling_pair_count memlist (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) = count).
  { unfold serialized_coupling_pair_count. unfold memlist. rewrite memory_word_at_hw by exact Hb128.
    rewrite natToWord_wordToNat, Hcount, wordToNat_natToWord_2 by (apply lt128_pow2_32; lia).
    change (MEM_SIZE / 2) with 64. apply Nat.min_l. lia. }
  assert (Load : load_coupling_pairs_from_mem memlist (S (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))))) count =
    map natpair (table_slice (loaded_table (hw_mem b) (wplus (zext (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) 25) (natToWord 32 1)) P count (hw_coupling_pair_src_table b) 0)
                              (loaded_table (hw_mem b) (wplus (zext (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) 25) (natToWord 32 1)) P count (hw_coupling_pair_dst_table b) 1) P count)).
  { rewrite morph_loaded_raw_pairs by lia. unfold memlist. rewrite <- (raw_pairs_nat b (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) count Hbase). reflexivity. }
  pose proof (kami_step_morph_success (hwb_snapshot b) (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
    (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) as K.
  cbv zeta in K. fold memlist in K. rewrite Cnt in K.
  rewrite K; [| (cbn [snap_pt_sizes hwb_snapshot]; rewrite hwb_vector_nat_at; exact Hsrc ) | (cbn [snap_pt_sizes hwb_snapshot]; rewrite hwb_vector_nat_at; exact Hdst ) | exact Hreg | (change (memory_word_at memlist (S (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) + 2 * count) = 0); unfold memlist;
        rewrite memory_word_at_hw by lia; replace (S (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) + 2 * count) with (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) + 1 + 2 * count) by lia;
        rewrite Hlabel; reflexivity ) ].
  clear K.
  rewrite Load, nodup_map_natpair, <- Hslice.
  assert (Rich : rich_state_add_morph_with_coupling (hwb_rich b) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
      (map natpair (table_slice src' dst' P (out - P))) ""%string false = (hwb_rich Fin, wordToNat (hw_morph_next_id b))).
  { apply (rich_after_morph_commit b Fin _ _ P out _ (natToWord WordSz 0) (natToWord 6 1)); try lia.
    - exact HPb.
    - unfold Fin; rewrite morph_fsm_keeps_morph_valid_table; exact F_morph_valid_table.
    - unfold Fin; rewrite morph_fsm_keeps_morph_src_table; exact F_morph_src_table.
    - unfold Fin; rewrite morph_fsm_keeps_morph_dst_table; exact F_morph_dst_table.
    - unfold Fin; rewrite morph_fsm_keeps_morph_coupling_desc_table; exact F_morph_coupling_desc_table.
    - unfold Fin; rewrite morph_fsm_keeps_morph_identity_table; exact F_morph_identity_table.
    - unfold Fin; rewrite morph_fsm_keeps_morph_next_id; exact F_morph_next_id.
    - exact RdV.
    - exact RdB.
    - exact RdC.
    - unfold Fin; rewrite morph_fsm_keeps_coupling_desc_label_table; exact F_coupling_desc_label_table.
    - unfold Fin; rewrite morph_fsm_keeps_coupling_desc_label_len_table; exact F_coupling_desc_label_len_table.
    - reflexivity.
    - exact RdN.
    - exact Rn.
    - intros k Hk. rewrite Rv. unfold hwb_valid. rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia).
      rewrite loaded_valid_at by lia.
      destruct (Nat.ltb_spec k P); destruct (Nat.leb_spec P k); destruct (Nat.ltb_spec k (P + count)); cbn [andb]; try reflexivity; lia.
    - intros k Hk. pose proof (Hpre k Hk) as E. unfold table_pair in E.
      rewrite !(pair_index_small k) in E by lia. injection E as E1 E2.
      rewrite Rs, Rd. unfold hwb_vector_nat. rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia).
      exact (conj (f_equal (@wordToNat _) E1) (f_equal (@wordToNat _) E2)).
    - intros k Hk. unfold table_slice. rewrite map_map.
      set (f := fun x : nat => natpair (table_pair src' dst' x)).
      rewrite (nth_indep (map f (seq P (out - P))) (0, 0) (f 0)) by (rewrite map_length, seq_length; lia).
      rewrite map_nth, seq_nth by lia. unfold f. replace (P + (k - P)) with k by lia.
      rewrite Rs, Rd. unfold natpair, table_pair. cbn [fst snd]. unfold hwb_vector_nat.
      rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia). rewrite (pair_index_small k) by lia. reflexivity.
    - unfold table_slice. rewrite !map_length, seq_length. reflexivity.
    - split; [unfold Fin; rewrite morph_fsm_keeps_formula_desc_valid_table; apply step_keeps_formula_desc_valid_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_formula_desc_base_table; apply step_keeps_formula_desc_base_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_formula_desc_count_table; apply step_keeps_formula_desc_count_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_formula_desc_next_id; apply step_keeps_formula_desc_next_id|]. split; [unfold Fin; rewrite morph_fsm_keeps_cert_desc_valid_table; apply step_keeps_cert_desc_valid_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_cert_desc_base_table; apply step_keeps_cert_desc_base_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_cert_desc_count_table; apply step_keeps_cert_desc_count_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_cert_desc_next_id; apply step_keeps_cert_desc_next_id|]. split; [unfold Fin; rewrite morph_fsm_keeps_desc_meta_valid_table; apply step_keeps_desc_meta_valid_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_desc_meta_subtype_table; apply step_keeps_desc_meta_subtype_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_desc_meta_kind_table; apply step_keeps_desc_meta_kind_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_desc_meta_inline_len_table; apply step_keeps_desc_meta_inline_len_table|]. split; [unfold Fin; rewrite morph_fsm_keeps_desc_meta_aux_table; apply step_keeps_desc_meta_aux_table|]. unfold Fin; rewrite morph_fsm_keeps_desc_meta_next_id; apply step_keeps_desc_meta_next_id. }
  change (snap_rich_state (hwb_snapshot b)) with (hwb_rich b). rewrite Rich. cbn [fst snd].
  unfold hwb_snapshot at 1. rewrite Rerr, Rec. unfold Fin.
  rewrite morph_fsm_keeps_pc, morph_fsm_keeps_mu, morph_fsm_keeps_halted, morph_fsm_keeps_regs, morph_fsm_keeps_mem, morph_fsm_keeps_cert_addr, morph_fsm_keeps_partition_ops, morph_fsm_keeps_mdl_ops, morph_fsm_keeps_info_gain, morph_fsm_keeps_mu_tensor, morph_fsm_keeps_module_tensors, morph_fsm_keeps_ptTable, morph_fsm_keeps_pt_next_id, morph_fsm_keeps_certified, morph_fsm_keeps_wc_same_00, morph_fsm_keeps_wc_diff_00, morph_fsm_keeps_wc_same_01, morph_fsm_keeps_wc_diff_01, morph_fsm_keeps_wc_same_10, morph_fsm_keeps_wc_diff_10, morph_fsm_keeps_wc_same_11, morph_fsm_keeps_wc_diff_11, morph_fsm_keeps_csr_status, morph_fsm_keeps_csr_heap_base, morph_fsm_keeps_logic_acc, morph_fsm_keeps_mstatus.
  rewrite F_pc, F_mu, F_halted, F_regs, F_mem, F_cert_addr, F_partition_ops, F_mdl_ops, F_info_gain, F_mu_tensor, F_module_tensors, F_ptTable, F_pt_next_id, F_certified, F_wc_same_00, F_wc_diff_00, F_wc_same_01, F_wc_diff_01, F_wc_same_10, F_wc_diff_10, F_wc_same_11, F_wc_diff_11, F_err, F_error_code.
  rewrite step_keeps_csr_status, step_keeps_csr_heap_base, step_keeps_logic_acc, step_keeps_mstatus.
  unfold kami_advance_rich_morph. snap_projections. rewrite ?He, ?Hh.
  apply kami_snapshot_ext; snap_projections.
  all: first [ syntactic | close_pc | close_mu_cost
    | close_vector_update ltac:(etransitivity; [apply wordToNat_zext4_32|]; rewrite (wordToNat_trunc4_5_small _ Hroom);
        rewrite word64_below_pow2_32 by exact (lt16_pow2_32 _ Hroom); reflexivity) ].
Qed.

Corollary morph_ext_execution : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) count,
  step_fetched b = morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_mu b) + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) < pow2 WordSz ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_ptTable b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) <> 0 -> wordToNat (hw_ptTable b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <> 0 ->
  hw_mem b (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) = natToWord 32 count ->
  count + wordToNat (hw_coupling_pair_next_id b) <= 16 -> wordToNat (hw_coupling_pair_next_id b) < 16 ->
  2 * count + wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 127 ->
  wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) + 1 + 2 * count < 128 ->
  hw_mem b (natToWord 7 (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) + 1 + 2 * count)) = natToWord 32 0 ->
  forallb (pair_respects_regions (snap_region (hwb_snapshot b) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7)))) (snap_region (hwb_snapshot b) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))))
    (load_coupling_pairs_from_mem (snapshot_mem_to_list (snap_mem (hwb_snapshot b))) (S (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))))) count) = true ->
  exists labels,
    Multistep thieleCore (hwb_regs b) (hwb_regs (morph_fsm_final count (step_next b))) labels /\
    hwb_snapshot (morph_fsm_final count (step_next b)) =
    kami_step (hwb_snapshot b) (instr_morph (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hpc Hmu Hroom Hdesc Hsrc Hdst Hcount Hfit HP16 Hbase Hlab128 Hlabel Hreg.
  destruct (morph_ext_run a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hroom Hdesc Hsrc Hdst Hcount Hfit Hbase) as [l Hl].
  exists l. split; [exact Hl|].
  exact (morph_ext_retire a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hpc Hmu Hroom Hdesc Hsrc Hdst Hcount Hfit HP16 Hbase Hlab128 Hlabel Hreg).
Qed.
