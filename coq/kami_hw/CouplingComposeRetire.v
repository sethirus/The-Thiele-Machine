(** CouplingComposeRetire.v: retirement of COMPOSE at its extended encoding.

    [compose_fsm_run]: from the phase the step firing leaves (4, the copy
    loop, when either side is an identity; 7, the join loop, otherwise), the
    coupling FSM is an actual Kami execution to the commit.
    [compose_ext_retire]: from a live boundary, the final snapshot of the step
    firing and that run equals [kami_step] of the COMPOSE instruction.
    Admission premises: morph and descriptor room; the pair pointer below 16;
    the raw composed pairs fit the pair table; at most 32 label atoms in the
    composed label; and the table invariants of [CouplingComposeKami]. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval
  StepWordFacts StepFields StepRefineCommon StepRefine StepFieldsMorph StepRefineMorph
  ImplementationContract Abstraction NormalizationSteps NormalizationLoop NormalizationRetirement MorphLoading
  MorphCopy MorphJoin RuleEnabled FsmDecoded ChshRetire CouplingFsmEnds CouplingFsmLoad CouplingFsmNorm
  CouplingFsmRun CouplingFsmCopy CouplingFsmJoin CouplingMorphRich CouplingMorphKami CouplingMorphRetire
  CouplingComposeRun CouplingComposeKami.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** * The FSM run from the step's phase *)

Definition compose_raw (s : HWB) : list coupling_pair :=
  let c1 := wordToNat (hw_mc_src1_count s) in
  let c2 := wordToNat (hw_mc_src2_count s) in
  let a1 := wordToNat (hw_mc_src1_base s) in
  let a2 := wordToNat (hw_mc_src2_base s) in
  if weq (hw_mc_phase s) (natToWord 4 4)
  then table_slice (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s) a1 c1 ++
       table_slice (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s) a2 c2
  else raw_join (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s) a1 c1 a2 c2.

Definition compose_fsm_final (s : HWB) : HWB :=
  let c1 := wordToNat (hw_mc_src1_count s) in
  let c2 := wordToNat (hw_mc_src2_count s) in
  if weq (hw_mc_phase s) (natToWord 4 4)
  then compose_copy_final (c1 + c2) s
  else compose_join_final c1 c2 (List.length (compose_raw s)) s.

Lemma phase4_ne7 : natToWord 4 7 <> natToWord 4 4.
Proof. intro E. apply (f_equal (@wordToNat 4)) in E. vm_compute in E. discriminate. Qed.

Theorem compose_fsm_run : forall s P,
  (hw_mc_phase s = natToWord 4 4 \/ hw_mc_phase s = natToWord 4 7) ->
  hw_mc_i s = natToWord 5 0 -> hw_mc_j s = natToWord 5 0 ->
  hw_mc_write_base s = natToWord 5 P -> hw_mc_write_ptr s = natToWord 5 P ->
  wordToNat (hw_mc_src1_count s) <= 16 -> wordToNat (hw_mc_src2_count s) <= 16 ->
  wordToNat (hw_mc_src1_base s) + wordToNat (hw_mc_src1_count s) <= P ->
  wordToNat (hw_mc_src2_base s) + wordToNat (hw_mc_src2_count s) <= P ->
  P + List.length (compose_raw s) <= 16 ->
  exists labels out src' dst',
    Multistep thieleCore (hwb_regs s) (hwb_regs (compose_fsm_final s)) labels /\
    P <= out <= P + List.length (compose_raw s) /\
    table_slice src' dst' P (out - P) = nodup coupling_pair_eq_dec (compose_raw s) /\
    (forall k, k < P -> table_pair src' dst' k =
       table_pair (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s) k) /\
    hw_coupling_pair_src_table (compose_fsm_final s) = src' /\
    hw_coupling_pair_dst_table (compose_fsm_final s) = dst' /\
    hw_coupling_pair_valid_table (compose_fsm_final s) =
      loaded_valid P (List.length (compose_raw s)) (hw_coupling_pair_valid_table s) /\
    hw_coupling_pair_next_id (compose_fsm_final s) = natToWord 5 out /\
    hw_mc_phase (compose_fsm_final s) = natToWord 4 0 /\
    hw_coupling_desc_base_table (compose_fsm_final s) =
      put_vector (hw_coupling_desc_base_table s) (split1 4 1 (hw_coupling_desc_next_id s)) (split1 4 1 (natToWord 5 P)) /\
    hw_coupling_desc_count_table (compose_fsm_final s) =
      put_vector (hw_coupling_desc_count_table s) (split1 4 1 (hw_coupling_desc_next_id s))
        (wminus (natToWord 5 out) (natToWord 5 P)) /\
    hw_coupling_desc_valid_table (compose_fsm_final s) =
      put_vector (hw_coupling_desc_valid_table s) (split1 4 1 (hw_coupling_desc_next_id s)) true /\
    hw_coupling_desc_next_id (compose_fsm_final s) =
      wplus (hw_coupling_desc_next_id s) (natToWord 5 1) /\
    hw_err (compose_fsm_final s) = hw_err s /\
    hw_error_code (compose_fsm_final s) = hw_error_code s.
Proof.
  intros s P Hph Hi Hj Hwb Hwp Hc1 Hc2 Hr1 Hr2 Hcap.
  unfold compose_fsm_final, compose_raw in *. cbv zeta in *.
  destruct Hph as [Hph|Hph]; rewrite Hph in *.
  - destruct (weq (natToWord 4 4) (natToWord 4 4)) as [_|NE]; [|contradiction].
    assert (Hlen : List.length (table_slice (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s)
        (wordToNat (hw_mc_src1_base s)) (wordToNat (hw_mc_src1_count s)) ++
      table_slice (hw_coupling_pair_src_table s) (hw_coupling_pair_dst_table s)
        (wordToNat (hw_mc_src2_base s)) (wordToNat (hw_mc_src2_count s))) =
      wordToNat (hw_mc_src1_count s) + wordToNat (hw_mc_src2_count s))
      by (unfold table_slice; rewrite app_length, !map_length, !seq_length; reflexivity).
    rewrite Hlen in *.
    exact (compose_copy_run s P _ _ _ _ Hph Hi Hj (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _))
      (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _)) Hwb Hwp Hc1 Hc2 Hr1 Hr2 Hcap).
  - destruct (weq (natToWord 4 7) (natToWord 4 4)) as [E|_]; [exact (False_ind _ (phase4_ne7 E))|].
    exact (compose_join_run s P _ _ _ _ Hph Hi Hj (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _))
      (eq_sym (natToWord_wordToNat _)) (eq_sym (natToWord_wordToNat _)) Hwb Hwp Hc1 Hc2 Hr1 Hr2 Hcap).
Qed.

(** * Registers the COMPOSE run leaves unchanged *)
Lemma compose_fsm_keeps_active_module : forall s, hw_active_module (compose_fsm_final s) = hw_active_module s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_active_module|apply compose_join_keeps_active_module]. Qed.
Lemma compose_fsm_keeps_bus_load_instr_addr : forall s, hw_bus_load_instr_addr (compose_fsm_final s) = hw_bus_load_instr_addr s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_bus_load_instr_addr|apply compose_join_keeps_bus_load_instr_addr]. Qed.
Lemma compose_fsm_keeps_bus_load_instr_data : forall s, hw_bus_load_instr_data (compose_fsm_final s) = hw_bus_load_instr_data s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_bus_load_instr_data|apply compose_join_keeps_bus_load_instr_data]. Qed.
Lemma compose_fsm_keeps_bus_load_instr_kick : forall s, hw_bus_load_instr_kick (compose_fsm_final s) = hw_bus_load_instr_kick s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_bus_load_instr_kick|apply compose_join_keeps_bus_load_instr_kick]. Qed.
Lemma compose_fsm_keeps_cert_addr : forall s, hw_cert_addr (compose_fsm_final s) = hw_cert_addr s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_cert_addr|apply compose_join_keeps_cert_addr]. Qed.
Lemma compose_fsm_keeps_cert_desc_base_table : forall s, hw_cert_desc_base_table (compose_fsm_final s) = hw_cert_desc_base_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_cert_desc_base_table|apply compose_join_keeps_cert_desc_base_table]. Qed.
Lemma compose_fsm_keeps_cert_desc_count_table : forall s, hw_cert_desc_count_table (compose_fsm_final s) = hw_cert_desc_count_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_cert_desc_count_table|apply compose_join_keeps_cert_desc_count_table]. Qed.
Lemma compose_fsm_keeps_cert_desc_next_id : forall s, hw_cert_desc_next_id (compose_fsm_final s) = hw_cert_desc_next_id s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_cert_desc_next_id|apply compose_join_keeps_cert_desc_next_id]. Qed.
Lemma compose_fsm_keeps_cert_desc_valid_table : forall s, hw_cert_desc_valid_table (compose_fsm_final s) = hw_cert_desc_valid_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_cert_desc_valid_table|apply compose_join_keeps_cert_desc_valid_table]. Qed.
Lemma compose_fsm_keeps_certified : forall s, hw_certified (compose_fsm_final s) = hw_certified s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_certified|apply compose_join_keeps_certified]. Qed.
Lemma compose_fsm_keeps_chsh_A_neg_a : forall s, hw_chsh_A_neg_a (compose_fsm_final s) = hw_chsh_A_neg_a s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_A_neg_a|apply compose_join_keeps_chsh_A_neg_a]. Qed.
Lemma compose_fsm_keeps_chsh_A_neg_b : forall s, hw_chsh_A_neg_b (compose_fsm_final s) = hw_chsh_A_neg_b s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_A_neg_b|apply compose_join_keeps_chsh_A_neg_b]. Qed.
Lemma compose_fsm_keeps_chsh_A_pos : forall s, hw_chsh_A_pos (compose_fsm_final s) = hw_chsh_A_pos s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_A_pos|apply compose_join_keeps_chsh_A_pos]. Qed.
Lemma compose_fsm_keeps_chsh_A_times_B : forall s, hw_chsh_A_times_B (compose_fsm_final s) = hw_chsh_A_times_B s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_A_times_B|apply compose_join_keeps_chsh_A_times_B]. Qed.
Lemma compose_fsm_keeps_chsh_B_neg_a : forall s, hw_chsh_B_neg_a (compose_fsm_final s) = hw_chsh_B_neg_a s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_B_neg_a|apply compose_join_keeps_chsh_B_neg_a]. Qed.
Lemma compose_fsm_keeps_chsh_B_neg_b : forall s, hw_chsh_B_neg_b (compose_fsm_final s) = hw_chsh_B_neg_b s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_B_neg_b|apply compose_join_keeps_chsh_B_neg_b]. Qed.
Lemma compose_fsm_keeps_chsh_B_pos : forall s, hw_chsh_B_pos (compose_fsm_final s) = hw_chsh_B_pos s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_B_pos|apply compose_join_keeps_chsh_B_pos]. Qed.
Lemma compose_fsm_keeps_chsh_C_sq : forall s, hw_chsh_C_sq (compose_fsm_final s) = hw_chsh_C_sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_C_sq|apply compose_join_keeps_chsh_C_sq]. Qed.
Lemma compose_fsm_keeps_chsh_abs_C1 : forall s, hw_chsh_abs_C1 (compose_fsm_final s) = hw_chsh_abs_C1 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_abs_C1|apply compose_join_keeps_chsh_abs_C1]. Qed.
Lemma compose_fsm_keeps_chsh_abs_C2 : forall s, hw_chsh_abs_C2 (compose_fsm_final s) = hw_chsh_abs_C2 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_abs_C2|apply compose_join_keeps_chsh_abs_C2]. Qed.
Lemma compose_fsm_keeps_chsh_check_result : forall s, hw_chsh_check_result (compose_fsm_final s) = hw_chsh_check_result s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_check_result|apply compose_join_keeps_chsh_check_result]. Qed.
Lemma compose_fsm_keeps_chsh_d00 : forall s, hw_chsh_d00 (compose_fsm_final s) = hw_chsh_d00 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d00|apply compose_join_keeps_chsh_d00]. Qed.
Lemma compose_fsm_keeps_chsh_d00d01 : forall s, hw_chsh_d00d01 (compose_fsm_final s) = hw_chsh_d00d01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d00d01|apply compose_join_keeps_chsh_d00d01]. Qed.
Lemma compose_fsm_keeps_chsh_d00sq : forall s, hw_chsh_d00sq (compose_fsm_final s) = hw_chsh_d00sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d00sq|apply compose_join_keeps_chsh_d00sq]. Qed.
Lemma compose_fsm_keeps_chsh_d01 : forall s, hw_chsh_d01 (compose_fsm_final s) = hw_chsh_d01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d01|apply compose_join_keeps_chsh_d01]. Qed.
Lemma compose_fsm_keeps_chsh_d01sq : forall s, hw_chsh_d01sq (compose_fsm_final s) = hw_chsh_d01sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d01sq|apply compose_join_keeps_chsh_d01sq]. Qed.
Lemma compose_fsm_keeps_chsh_d10 : forall s, hw_chsh_d10 (compose_fsm_final s) = hw_chsh_d10 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d10|apply compose_join_keeps_chsh_d10]. Qed.
Lemma compose_fsm_keeps_chsh_d10d11 : forall s, hw_chsh_d10d11 (compose_fsm_final s) = hw_chsh_d10d11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d10d11|apply compose_join_keeps_chsh_d10d11]. Qed.
Lemma compose_fsm_keeps_chsh_d10sq : forall s, hw_chsh_d10sq (compose_fsm_final s) = hw_chsh_d10sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d10sq|apply compose_join_keeps_chsh_d10sq]. Qed.
Lemma compose_fsm_keeps_chsh_d11 : forall s, hw_chsh_d11 (compose_fsm_final s) = hw_chsh_d11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d11|apply compose_join_keeps_chsh_d11]. Qed.
Lemma compose_fsm_keeps_chsh_d11sq : forall s, hw_chsh_d11sq (compose_fsm_final s) = hw_chsh_d11sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_d11sq|apply compose_join_keeps_chsh_d11sq]. Qed.
Lemma compose_fsm_keeps_chsh_n00 : forall s, hw_chsh_n00 (compose_fsm_final s) = hw_chsh_n00 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n00|apply compose_join_keeps_chsh_n00]. Qed.
Lemma compose_fsm_keeps_chsh_n00n01 : forall s, hw_chsh_n00n01 (compose_fsm_final s) = hw_chsh_n00n01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n00n01|apply compose_join_keeps_chsh_n00n01]. Qed.
Lemma compose_fsm_keeps_chsh_n00sq : forall s, hw_chsh_n00sq (compose_fsm_final s) = hw_chsh_n00sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n00sq|apply compose_join_keeps_chsh_n00sq]. Qed.
Lemma compose_fsm_keeps_chsh_n01 : forall s, hw_chsh_n01 (compose_fsm_final s) = hw_chsh_n01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n01|apply compose_join_keeps_chsh_n01]. Qed.
Lemma compose_fsm_keeps_chsh_n01sq : forall s, hw_chsh_n01sq (compose_fsm_final s) = hw_chsh_n01sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n01sq|apply compose_join_keeps_chsh_n01sq]. Qed.
Lemma compose_fsm_keeps_chsh_n10 : forall s, hw_chsh_n10 (compose_fsm_final s) = hw_chsh_n10 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n10|apply compose_join_keeps_chsh_n10]. Qed.
Lemma compose_fsm_keeps_chsh_n10n11 : forall s, hw_chsh_n10n11 (compose_fsm_final s) = hw_chsh_n10n11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n10n11|apply compose_join_keeps_chsh_n10n11]. Qed.
Lemma compose_fsm_keeps_chsh_n10sq : forall s, hw_chsh_n10sq (compose_fsm_final s) = hw_chsh_n10sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n10sq|apply compose_join_keeps_chsh_n10sq]. Qed.
Lemma compose_fsm_keeps_chsh_n11 : forall s, hw_chsh_n11 (compose_fsm_final s) = hw_chsh_n11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n11|apply compose_join_keeps_chsh_n11]. Qed.
Lemma compose_fsm_keeps_chsh_n11sq : forall s, hw_chsh_n11sq (compose_fsm_final s) = hw_chsh_n11sq s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_n11sq|apply compose_join_keeps_chsh_n11sq]. Qed.
Lemma compose_fsm_keeps_chsh_phase : forall s, hw_chsh_phase (compose_fsm_final s) = hw_chsh_phase s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_phase|apply compose_join_keeps_chsh_phase]. Qed.
Lemma compose_fsm_keeps_chsh_sign00 : forall s, hw_chsh_sign00 (compose_fsm_final s) = hw_chsh_sign00 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_sign00|apply compose_join_keeps_chsh_sign00]. Qed.
Lemma compose_fsm_keeps_chsh_sign01 : forall s, hw_chsh_sign01 (compose_fsm_final s) = hw_chsh_sign01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_sign01|apply compose_join_keeps_chsh_sign01]. Qed.
Lemma compose_fsm_keeps_chsh_sign10 : forall s, hw_chsh_sign10 (compose_fsm_final s) = hw_chsh_sign10 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_sign10|apply compose_join_keeps_chsh_sign10]. Qed.
Lemma compose_fsm_keeps_chsh_sign11 : forall s, hw_chsh_sign11 (compose_fsm_final s) = hw_chsh_sign11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_chsh_sign11|apply compose_join_keeps_chsh_sign11]. Qed.
Lemma compose_fsm_keeps_coupling_desc_label_len_table : forall s, hw_coupling_desc_label_len_table (compose_fsm_final s) = hw_coupling_desc_label_len_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_coupling_desc_label_len_table|apply compose_join_keeps_coupling_desc_label_len_table]. Qed.
Lemma compose_fsm_keeps_coupling_desc_label_table : forall s, hw_coupling_desc_label_table (compose_fsm_final s) = hw_coupling_desc_label_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_coupling_desc_label_table|apply compose_join_keeps_coupling_desc_label_table]. Qed.
Lemma compose_fsm_keeps_csr_heap_base : forall s, hw_csr_heap_base (compose_fsm_final s) = hw_csr_heap_base s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_csr_heap_base|apply compose_join_keeps_csr_heap_base]. Qed.
Lemma compose_fsm_keeps_csr_status : forall s, hw_csr_status (compose_fsm_final s) = hw_csr_status s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_csr_status|apply compose_join_keeps_csr_status]. Qed.
Lemma compose_fsm_keeps_desc_meta_aux_table : forall s, hw_desc_meta_aux_table (compose_fsm_final s) = hw_desc_meta_aux_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_desc_meta_aux_table|apply compose_join_keeps_desc_meta_aux_table]. Qed.
Lemma compose_fsm_keeps_desc_meta_inline_len_table : forall s, hw_desc_meta_inline_len_table (compose_fsm_final s) = hw_desc_meta_inline_len_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_desc_meta_inline_len_table|apply compose_join_keeps_desc_meta_inline_len_table]. Qed.
Lemma compose_fsm_keeps_desc_meta_kind_table : forall s, hw_desc_meta_kind_table (compose_fsm_final s) = hw_desc_meta_kind_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_desc_meta_kind_table|apply compose_join_keeps_desc_meta_kind_table]. Qed.
Lemma compose_fsm_keeps_desc_meta_next_id : forall s, hw_desc_meta_next_id (compose_fsm_final s) = hw_desc_meta_next_id s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_desc_meta_next_id|apply compose_join_keeps_desc_meta_next_id]. Qed.
Lemma compose_fsm_keeps_desc_meta_subtype_table : forall s, hw_desc_meta_subtype_table (compose_fsm_final s) = hw_desc_meta_subtype_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_desc_meta_subtype_table|apply compose_join_keeps_desc_meta_subtype_table]. Qed.
Lemma compose_fsm_keeps_desc_meta_valid_table : forall s, hw_desc_meta_valid_table (compose_fsm_final s) = hw_desc_meta_valid_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_desc_meta_valid_table|apply compose_join_keeps_desc_meta_valid_table]. Qed.
Lemma compose_fsm_keeps_formula_desc_base_table : forall s, hw_formula_desc_base_table (compose_fsm_final s) = hw_formula_desc_base_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_formula_desc_base_table|apply compose_join_keeps_formula_desc_base_table]. Qed.
Lemma compose_fsm_keeps_formula_desc_count_table : forall s, hw_formula_desc_count_table (compose_fsm_final s) = hw_formula_desc_count_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_formula_desc_count_table|apply compose_join_keeps_formula_desc_count_table]. Qed.
Lemma compose_fsm_keeps_formula_desc_next_id : forall s, hw_formula_desc_next_id (compose_fsm_final s) = hw_formula_desc_next_id s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_formula_desc_next_id|apply compose_join_keeps_formula_desc_next_id]. Qed.
Lemma compose_fsm_keeps_formula_desc_valid_table : forall s, hw_formula_desc_valid_table (compose_fsm_final s) = hw_formula_desc_valid_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_formula_desc_valid_table|apply compose_join_keeps_formula_desc_valid_table]. Qed.
Lemma compose_fsm_keeps_halted : forall s, hw_halted (compose_fsm_final s) = hw_halted s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_halted|apply compose_join_keeps_halted]. Qed.
Lemma compose_fsm_keeps_imem : forall s, hw_imem (compose_fsm_final s) = hw_imem s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_imem|apply compose_join_keeps_imem]. Qed.
Lemma compose_fsm_keeps_info_gain : forall s, hw_info_gain (compose_fsm_final s) = hw_info_gain s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_info_gain|apply compose_join_keeps_info_gain]. Qed.
Lemma compose_fsm_keeps_lassert_cbase : forall s, hw_lassert_cbase (compose_fsm_final s) = hw_lassert_cbase s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_cbase|apply compose_join_keeps_lassert_cbase]. Qed.
Lemma compose_fsm_keeps_lassert_cbuf : forall s, hw_lassert_cbuf (compose_fsm_final s) = hw_lassert_cbuf s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_cbuf|apply compose_join_keeps_lassert_cbuf]. Qed.
Lemma compose_fsm_keeps_lassert_clause_sat : forall s, hw_lassert_clause_sat (compose_fsm_final s) = hw_lassert_clause_sat s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_clause_sat|apply compose_join_keeps_lassert_clause_sat]. Qed.
Lemma compose_fsm_keeps_lassert_clen : forall s, hw_lassert_clen (compose_fsm_final s) = hw_lassert_clen s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_clen|apply compose_join_keeps_lassert_clen]. Qed.
Lemma compose_fsm_keeps_lassert_counter_clause_sat : forall s, hw_lassert_counter_clause_sat (compose_fsm_final s) = hw_lassert_counter_clause_sat s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_counter_clause_sat|apply compose_join_keeps_lassert_counter_clause_sat]. Qed.
Lemma compose_fsm_keeps_lassert_counter_seen_fail : forall s, hw_lassert_counter_seen_fail (compose_fsm_final s) = hw_lassert_counter_seen_fail s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_counter_seen_fail|apply compose_join_keeps_lassert_counter_seen_fail]. Qed.
Lemma compose_fsm_keeps_lassert_cptr : forall s, hw_lassert_cptr (compose_fsm_final s) = hw_lassert_cptr s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_cptr|apply compose_join_keeps_lassert_cptr]. Qed.
Lemma compose_fsm_keeps_lassert_fbase : forall s, hw_lassert_fbase (compose_fsm_final s) = hw_lassert_fbase s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_fbase|apply compose_join_keeps_lassert_fbase]. Qed.
Lemma compose_fsm_keeps_lassert_fbuf : forall s, hw_lassert_fbuf (compose_fsm_final s) = hw_lassert_fbuf s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_fbuf|apply compose_join_keeps_lassert_fbuf]. Qed.
Lemma compose_fsm_keeps_lassert_flen : forall s, hw_lassert_flen (compose_fsm_final s) = hw_lassert_flen s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_flen|apply compose_join_keeps_lassert_flen]. Qed.
Lemma compose_fsm_keeps_lassert_fptr : forall s, hw_lassert_fptr (compose_fsm_final s) = hw_lassert_fptr s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_fptr|apply compose_join_keeps_lassert_fptr]. Qed.
Lemma compose_fsm_keeps_lassert_kind : forall s, hw_lassert_kind (compose_fsm_final s) = hw_lassert_kind s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_kind|apply compose_join_keeps_lassert_kind]. Qed.
Lemma compose_fsm_keeps_lassert_nvars : forall s, hw_lassert_nvars (compose_fsm_final s) = hw_lassert_nvars s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_nvars|apply compose_join_keeps_lassert_nvars]. Qed.
Lemma compose_fsm_keeps_lassert_phase : forall s, hw_lassert_phase (compose_fsm_final s) = hw_lassert_phase s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_lassert_phase|apply compose_join_keeps_lassert_phase]. Qed.
Lemma compose_fsm_keeps_logic_acc : forall s, hw_logic_acc (compose_fsm_final s) = hw_logic_acc s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_logic_acc|apply compose_join_keeps_logic_acc]. Qed.
Lemma compose_fsm_keeps_mc_cost : forall s, hw_mc_cost (compose_fsm_final s) = hw_mc_cost s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_cost|apply compose_join_keeps_mc_cost]. Qed.
Lemma compose_fsm_keeps_mc_dst_reg : forall s, hw_mc_dst_reg (compose_fsm_final s) = hw_mc_dst_reg s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_dst_reg|apply compose_join_keeps_mc_dst_reg]. Qed.
Lemma compose_fsm_keeps_mc_is_id1 : forall s, hw_mc_is_id1 (compose_fsm_final s) = hw_mc_is_id1 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_is_id1|apply compose_join_keeps_mc_is_id1]. Qed.
Lemma compose_fsm_keeps_mc_is_id2 : forall s, hw_mc_is_id2 (compose_fsm_final s) = hw_mc_is_id2 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_is_id2|apply compose_join_keeps_mc_is_id2]. Qed.
Lemma compose_fsm_keeps_mc_mem_base : forall s, hw_mc_mem_base (compose_fsm_final s) = hw_mc_mem_base s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_mem_base|apply compose_join_keeps_mc_mem_base]. Qed.
Lemma compose_fsm_keeps_mc_morph_slot : forall s, hw_mc_morph_slot (compose_fsm_final s) = hw_mc_morph_slot s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_morph_slot|apply compose_join_keeps_mc_morph_slot]. Qed.
Lemma compose_fsm_keeps_mc_new_dst_mod : forall s, hw_mc_new_dst_mod (compose_fsm_final s) = hw_mc_new_dst_mod s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_new_dst_mod|apply compose_join_keeps_mc_new_dst_mod]. Qed.
Lemma compose_fsm_keeps_mc_new_src_mod : forall s, hw_mc_new_src_mod (compose_fsm_final s) = hw_mc_new_src_mod s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_new_src_mod|apply compose_join_keeps_mc_new_src_mod]. Qed.
Lemma compose_fsm_keeps_mc_op : forall s, hw_mc_op (compose_fsm_final s) = hw_mc_op s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_op|apply compose_join_keeps_mc_op]. Qed.
Lemma compose_fsm_keeps_mc_pair_count : forall s, hw_mc_pair_count (compose_fsm_final s) = hw_mc_pair_count s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_pair_count|apply compose_join_keeps_mc_pair_count]. Qed.
Lemma compose_fsm_keeps_mc_read_ptr : forall s, hw_mc_read_ptr (compose_fsm_final s) = hw_mc_read_ptr s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_read_ptr|apply compose_join_keeps_mc_read_ptr]. Qed.
Lemma compose_fsm_keeps_mc_src1_base : forall s, hw_mc_src1_base (compose_fsm_final s) = hw_mc_src1_base s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_src1_base|apply compose_join_keeps_mc_src1_base]. Qed.
Lemma compose_fsm_keeps_mc_src1_count : forall s, hw_mc_src1_count (compose_fsm_final s) = hw_mc_src1_count s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_src1_count|apply compose_join_keeps_mc_src1_count]. Qed.
Lemma compose_fsm_keeps_mc_src2_base : forall s, hw_mc_src2_base (compose_fsm_final s) = hw_mc_src2_base s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_src2_base|apply compose_join_keeps_mc_src2_base]. Qed.
Lemma compose_fsm_keeps_mc_src2_count : forall s, hw_mc_src2_count (compose_fsm_final s) = hw_mc_src2_count s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_src2_count|apply compose_join_keeps_mc_src2_count]. Qed.
Lemma compose_fsm_keeps_mc_write_base : forall s, hw_mc_write_base (compose_fsm_final s) = hw_mc_write_base s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mc_write_base|apply compose_join_keeps_mc_write_base]. Qed.
Lemma compose_fsm_keeps_mcycle_hi : forall s, hw_mcycle_hi (compose_fsm_final s) = hw_mcycle_hi s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mcycle_hi|apply compose_join_keeps_mcycle_hi]. Qed.
Lemma compose_fsm_keeps_mcycle_lo : forall s, hw_mcycle_lo (compose_fsm_final s) = hw_mcycle_lo s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mcycle_lo|apply compose_join_keeps_mcycle_lo]. Qed.
Lemma compose_fsm_keeps_mdl_ops : forall s, hw_mdl_ops (compose_fsm_final s) = hw_mdl_ops s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mdl_ops|apply compose_join_keeps_mdl_ops]. Qed.
Lemma compose_fsm_keeps_mem : forall s, hw_mem (compose_fsm_final s) = hw_mem s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mem|apply compose_join_keeps_mem]. Qed.
Lemma compose_fsm_keeps_minstret_hi : forall s, hw_minstret_hi (compose_fsm_final s) = hw_minstret_hi s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_minstret_hi|apply compose_join_keeps_minstret_hi]. Qed.
Lemma compose_fsm_keeps_minstret_lo : forall s, hw_minstret_lo (compose_fsm_final s) = hw_minstret_lo s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_minstret_lo|apply compose_join_keeps_minstret_lo]. Qed.
Lemma compose_fsm_keeps_module_tensors : forall s, hw_module_tensors (compose_fsm_final s) = hw_module_tensors s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_module_tensors|apply compose_join_keeps_module_tensors]. Qed.
Lemma compose_fsm_keeps_morph_coupling_desc_table : forall s, hw_morph_coupling_desc_table (compose_fsm_final s) = hw_morph_coupling_desc_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_morph_coupling_desc_table|apply compose_join_keeps_morph_coupling_desc_table]. Qed.
Lemma compose_fsm_keeps_morph_dst_table : forall s, hw_morph_dst_table (compose_fsm_final s) = hw_morph_dst_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_morph_dst_table|apply compose_join_keeps_morph_dst_table]. Qed.
Lemma compose_fsm_keeps_morph_identity_table : forall s, hw_morph_identity_table (compose_fsm_final s) = hw_morph_identity_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_morph_identity_table|apply compose_join_keeps_morph_identity_table]. Qed.
Lemma compose_fsm_keeps_morph_next_id : forall s, hw_morph_next_id (compose_fsm_final s) = hw_morph_next_id s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_morph_next_id|apply compose_join_keeps_morph_next_id]. Qed.
Lemma compose_fsm_keeps_morph_src_table : forall s, hw_morph_src_table (compose_fsm_final s) = hw_morph_src_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_morph_src_table|apply compose_join_keeps_morph_src_table]. Qed.
Lemma compose_fsm_keeps_morph_valid_table : forall s, hw_morph_valid_table (compose_fsm_final s) = hw_morph_valid_table s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_morph_valid_table|apply compose_join_keeps_morph_valid_table]. Qed.
Lemma compose_fsm_keeps_mstatus : forall s, hw_mstatus (compose_fsm_final s) = hw_mstatus s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mstatus|apply compose_join_keeps_mstatus]. Qed.
Lemma compose_fsm_keeps_mu : forall s, hw_mu (compose_fsm_final s) = hw_mu s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mu|apply compose_join_keeps_mu]. Qed.
Lemma compose_fsm_keeps_mu_tensor : forall s, hw_mu_tensor (compose_fsm_final s) = hw_mu_tensor s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_mu_tensor|apply compose_join_keeps_mu_tensor]. Qed.
Lemma compose_fsm_keeps_partition_ops : forall s, hw_partition_ops (compose_fsm_final s) = hw_partition_ops s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_partition_ops|apply compose_join_keeps_partition_ops]. Qed.
Lemma compose_fsm_keeps_pc : forall s, hw_pc (compose_fsm_final s) = hw_pc s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_pc|apply compose_join_keeps_pc]. Qed.
Lemma compose_fsm_keeps_ptTable : forall s, hw_ptTable (compose_fsm_final s) = hw_ptTable s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_ptTable|apply compose_join_keeps_ptTable]. Qed.
Lemma compose_fsm_keeps_pt_next_id : forall s, hw_pt_next_id (compose_fsm_final s) = hw_pt_next_id s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_pt_next_id|apply compose_join_keeps_pt_next_id]. Qed.
Lemma compose_fsm_keeps_regs : forall s, hw_regs (compose_fsm_final s) = hw_regs s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_regs|apply compose_join_keeps_regs]. Qed.
Lemma compose_fsm_keeps_trap_vector : forall s, hw_trap_vector (compose_fsm_final s) = hw_trap_vector s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_trap_vector|apply compose_join_keeps_trap_vector]. Qed.
Lemma compose_fsm_keeps_wc_diff_00 : forall s, hw_wc_diff_00 (compose_fsm_final s) = hw_wc_diff_00 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_diff_00|apply compose_join_keeps_wc_diff_00]. Qed.
Lemma compose_fsm_keeps_wc_diff_01 : forall s, hw_wc_diff_01 (compose_fsm_final s) = hw_wc_diff_01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_diff_01|apply compose_join_keeps_wc_diff_01]. Qed.
Lemma compose_fsm_keeps_wc_diff_10 : forall s, hw_wc_diff_10 (compose_fsm_final s) = hw_wc_diff_10 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_diff_10|apply compose_join_keeps_wc_diff_10]. Qed.
Lemma compose_fsm_keeps_wc_diff_11 : forall s, hw_wc_diff_11 (compose_fsm_final s) = hw_wc_diff_11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_diff_11|apply compose_join_keeps_wc_diff_11]. Qed.
Lemma compose_fsm_keeps_wc_same_00 : forall s, hw_wc_same_00 (compose_fsm_final s) = hw_wc_same_00 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_same_00|apply compose_join_keeps_wc_same_00]. Qed.
Lemma compose_fsm_keeps_wc_same_01 : forall s, hw_wc_same_01 (compose_fsm_final s) = hw_wc_same_01 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_same_01|apply compose_join_keeps_wc_same_01]. Qed.
Lemma compose_fsm_keeps_wc_same_10 : forall s, hw_wc_same_10 (compose_fsm_final s) = hw_wc_same_10 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_same_10|apply compose_join_keeps_wc_same_10]. Qed.
Lemma compose_fsm_keeps_wc_same_11 : forall s, hw_wc_same_11 (compose_fsm_final s) = hw_wc_same_11 s.
Proof. intro s. unfold compose_fsm_final. cbv zeta. destruct (weq _ _); [apply compose_copy_keeps_wc_same_11|apply compose_join_keeps_wc_same_11]. Qed.
(** * Part B *)

Lemma desc_fits : forall b m,
  hwb_morph_coupling_refs_ok b -> hwb_desc_zero_empty b -> hwb_desc_pairs_below_next b ->
  hw_morph_valid_table b m = true ->
  wordToNat (hw_coupling_desc_base_table b (hw_morph_coupling_desc_table b m)) +
  wordToNat (hw_coupling_desc_count_table b (hw_morph_coupling_desc_table b m)) <=
  wordToNat (hw_coupling_pair_next_id b).
Proof.
  intros b m Hr [Hz0 Hc0] Hd Hm. pose proof (Hr m Hm) as R. unfold hw_coupling_ref_ok in R.
  destruct (hw_coupling_desc_valid_table b (hw_morph_coupling_desc_table b m)) eqn:V.
  - exact (Hd _ V).
  - destruct (weq (hw_morph_coupling_desc_table b m) (natToWord DescIdxSz 0)) as [E|E].
    + rewrite E. change (natToWord DescIdxSz 0) with (natToWord CouplingDescIdxSz 0).
      rewrite Hz0, Hc0. change (wordToNat (natToWord CouplingPairIdxSz 0)) with 0.
      change (wordToNat (natToWord CouplingPairCountSz 0)) with 0. lia.
    + exfalso. revert R. destruct (wlt_dec _ _); discriminate.
Qed.

Lemma compose_raw_step : forall b s (M1 M2 : word MorphTableIdxSz),
  hwb_identity_desc_zero b -> hwb_desc_zero_empty b ->
  hw_morph_valid_table b M2 = true ->
  hw_coupling_pair_src_table s = hw_coupling_pair_src_table b ->
  hw_coupling_pair_dst_table s = hw_coupling_pair_dst_table b ->
  hw_mc_phase s = (if hw_morph_identity_table b M1 then natToWord 4 4
                   else if hw_morph_identity_table b M2 then natToWord 4 4 else natToWord 4 7) ->
  hw_mc_src1_count s = (if hw_morph_identity_table b M1 then natToWord CouplingPairCountSz 0
                        else hw_coupling_desc_count_table b (hw_morph_coupling_desc_table b M1)) ->
  hw_mc_src2_count s = (if hw_morph_identity_table b M2 then natToWord CouplingPairCountSz 0
                        else hw_coupling_desc_count_table b (hw_morph_coupling_desc_table b M2)) ->
  hw_mc_src1_base s = hw_coupling_desc_base_table b (hw_morph_coupling_desc_table b M1) ->
  hw_mc_src2_base s = hw_coupling_desc_base_table b (hw_morph_coupling_desc_table b M2) ->
  compose_raw s = compose_pairs b M1 M2.
Proof.
  intros b s M1 M2 Hid [Hz0 Hc0] V2 Hs Hd Hph H1 H2 B1 B2.
  unfold compose_raw, compose_pairs, hw_desc_slice. cbv zeta.
  rewrite Hs, Hd, Hph, H1, H2, B1, B2.
  change (wordToNat (natToWord CouplingPairCountSz 0)) with 0.
  destruct (hw_morph_identity_table b M1) eqn:I1; destruct (hw_morph_identity_table b M2) eqn:I2.
  - destruct (weq (natToWord 4 4) (natToWord 4 4)) as [_|NE]; [|contradiction].
    rewrite (Hid M2 V2 I2). change (natToWord DescIdxSz 0) with (natToWord CouplingDescIdxSz 0).
    rewrite Hc0. reflexivity.
  - destruct (weq (natToWord 4 4) (natToWord 4 4)) as [_|NE]; [reflexivity|contradiction].
  - destruct (weq (natToWord 4 4) (natToWord 4 4)) as [_|NE]; [|contradiction].
    apply app_nil_r.
  - destruct (weq (natToWord 4 7) (natToWord 4 4)) as [Ew|_]; [exact (False_ind _ (phase4_ne7 Ew))|].
    apply raw_join_relational.
Qed.

Theorem compose_ext_run : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
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
  exists labels, Multistep thieleCore (hwb_regs b) (hwb_regs (compose_fsm_final (step_next b))) labels.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 Imv Iref Iz Iz0 Idp Ipv Iid Ilab V1 V2 Hmatch Hlab Hcap.
  pose proof Hlive as [Hh [He _]].
  pose proof (step_compose_ext_pc a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pc.
  pose proof (step_compose_ext_mu a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu.
  pose proof (step_compose_ext_err a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_err.
  pose proof (step_compose_ext_halted a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_halted.
  pose proof (step_compose_ext_regs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_regs.
  pose proof (step_compose_ext_mem a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mem.
  pose proof (step_compose_ext_error_code a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_error_code.
  pose proof (step_compose_ext_cert_addr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_cert_addr.
  pose proof (step_compose_ext_partition_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_partition_ops.
  pose proof (step_compose_ext_mdl_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mdl_ops.
  pose proof (step_compose_ext_info_gain a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_info_gain.
  pose proof (step_compose_ext_mu_tensor a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu_tensor.
  pose proof (step_compose_ext_module_tensors a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_module_tensors.
  pose proof (step_compose_ext_ptTable a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ptTable.
  pose proof (step_compose_ext_pt_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pt_next_id.
  pose proof (step_compose_ext_certified a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_certified.
  pose proof (step_compose_ext_wc_same_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_00.
  pose proof (step_compose_ext_wc_diff_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_00.
  pose proof (step_compose_ext_wc_same_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_01.
  pose proof (step_compose_ext_wc_diff_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_01.
  pose proof (step_compose_ext_wc_same_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_10.
  pose proof (step_compose_ext_wc_diff_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_10.
  pose proof (step_compose_ext_wc_same_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_11.
  pose proof (step_compose_ext_wc_diff_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_11.
  pose proof (step_compose_ext_morph_src_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_src_table.
  pose proof (step_compose_ext_morph_dst_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_dst_table.
  pose proof (step_compose_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_coupling_desc_table.
  pose proof (step_compose_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_identity_table.
  pose proof (step_compose_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_valid_table.
  pose proof (step_compose_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_next_id.
  pose proof (step_compose_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_table.
  pose proof (step_compose_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_len_table.
  pose proof (step_compose_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_compose_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  pose proof (step_compose_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_compose_ext_mc_src1_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src1_count.
  pose proof (step_compose_ext_mc_src2_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src2_count.
  pose proof (step_compose_ext_mc_src1_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src1_base.
  pose proof (step_compose_ext_mc_src2_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src2_base.
  pose proof (step_compose_ext_mc_i a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_i.
  pose proof (step_compose_ext_mc_j a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_j.
  pose proof (step_compose_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_compose_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), (morph_live_valid b (bits4 b0 b1 b2 b3) Imv),
    (morph_live_valid b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Imv), V1, V2, Hmatch in *.
  destruct (weq (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) as [_|NE]; [|contradiction].
  cbv beta iota in F_pc, F_mu, F_err, F_halted, F_regs, F_mem, F_error_code, F_cert_addr, F_partition_ops, F_mdl_ops, F_info_gain, F_mu_tensor, F_module_tensors, F_ptTable, F_pt_next_id, F_certified, F_wc_same_00, F_wc_diff_00, F_wc_same_01, F_wc_diff_01, F_wc_same_10, F_wc_diff_10, F_wc_same_11, F_wc_diff_11, F_morph_src_table, F_morph_dst_table, F_morph_coupling_desc_table, F_morph_identity_table, F_morph_valid_table, F_morph_next_id, F_coupling_desc_label_table, F_coupling_desc_label_len_table, F_lassert_phase, F_chsh_phase, F_mc_phase, F_mc_src1_count, F_mc_src2_count, F_mc_src1_base, F_mc_src2_base, F_mc_i, F_mc_j, F_mc_write_base, F_mc_write_ptr.
  set (P := wordToNat (hw_coupling_pair_next_id b)) in *.
  assert (HPb : hw_coupling_pair_next_id b = natToWord 5 P) by (unfold P; symmetry; apply natToWord_wordToNat).
  pose proof (desc_fits b (bits4 b0 b1 b2 b3) Iref Iz0 Idp V1) as Fit1. pose proof (desc_fits b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Iref Iz0 Idp V2) as Fit2.
  fold P in Fit1, Fit2.
  assert (Raw : compose_raw (step_next b) = compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
    by exact (compose_raw_step b (step_next b) (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Iid Iz0 V2
      (step_keeps_coupling_pair_src_table b) (step_keeps_coupling_pair_dst_table b)
      F_mc_phase F_mc_src1_count F_mc_src2_count F_mc_src1_base F_mc_src2_base).
  assert (W0 : wordToNat (natToWord CouplingPairCountSz 0) = 0) by reflexivity.
  destruct (compose_fsm_run (step_next b) P
    ltac:(rewrite F_mc_phase; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)), (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); auto)
    F_mc_i F_mc_j ltac:(rewrite F_mc_write_base; exact HPb) ltac:(rewrite F_mc_write_ptr; exact HPb)
    ltac:(rewrite F_mc_src1_count; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); lia)
    ltac:(rewrite F_mc_src2_count; destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); lia)
    ltac:(rewrite F_mc_src1_count, F_mc_src1_base; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); lia)
    ltac:(rewrite F_mc_src2_count, F_mc_src2_base; destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); lia)
    ltac:(rewrite Raw; exact Hcap))
    as [l [_ [_ [_ [Hrun _]]]]].
  eexists. eapply normalization_multistep_trans; [exact (live_step_multistep b Hlive)|exact Hrun].
Qed.

Theorem compose_ext_retire : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
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
  hwb_snapshot (compose_fsm_final (step_next b)) = kami_step (hwb_snapshot b) (instr_compose (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 Imv Iref Iz Iz0 Idp Ipv Iid Ilab V1 V2 Hmatch Hlab Hcap.
  pose proof Hlive as [Hh [He _]].
  pose proof (step_compose_ext_pc a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pc.
  pose proof (step_compose_ext_mu a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu.
  pose proof (step_compose_ext_err a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_err.
  pose proof (step_compose_ext_halted a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_halted.
  pose proof (step_compose_ext_regs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_regs.
  pose proof (step_compose_ext_mem a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mem.
  pose proof (step_compose_ext_error_code a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_error_code.
  pose proof (step_compose_ext_cert_addr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_cert_addr.
  pose proof (step_compose_ext_partition_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_partition_ops.
  pose proof (step_compose_ext_mdl_ops a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mdl_ops.
  pose proof (step_compose_ext_info_gain a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_info_gain.
  pose proof (step_compose_ext_mu_tensor a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mu_tensor.
  pose proof (step_compose_ext_module_tensors a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_module_tensors.
  pose proof (step_compose_ext_ptTable a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ptTable.
  pose proof (step_compose_ext_pt_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_pt_next_id.
  pose proof (step_compose_ext_certified a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_certified.
  pose proof (step_compose_ext_wc_same_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_00.
  pose proof (step_compose_ext_wc_diff_00 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_00.
  pose proof (step_compose_ext_wc_same_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_01.
  pose proof (step_compose_ext_wc_diff_01 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_01.
  pose proof (step_compose_ext_wc_same_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_10.
  pose proof (step_compose_ext_wc_diff_10 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_10.
  pose proof (step_compose_ext_wc_same_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_same_11.
  pose proof (step_compose_ext_wc_diff_11 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wc_diff_11.
  pose proof (step_compose_ext_morph_src_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_src_table.
  pose proof (step_compose_ext_morph_dst_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_dst_table.
  pose proof (step_compose_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_coupling_desc_table.
  pose proof (step_compose_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_identity_table.
  pose proof (step_compose_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_valid_table.
  pose proof (step_compose_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_next_id.
  pose proof (step_compose_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_table.
  pose proof (step_compose_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_len_table.
  pose proof (step_compose_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_compose_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  pose proof (step_compose_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_compose_ext_mc_src1_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src1_count.
  pose proof (step_compose_ext_mc_src2_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src2_count.
  pose proof (step_compose_ext_mc_src1_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src1_base.
  pose proof (step_compose_ext_mc_src2_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_src2_base.
  pose proof (step_compose_ext_mc_i a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_i.
  pose proof (step_compose_ext_mc_j a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_j.
  pose proof (step_compose_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_compose_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), (morph_live_valid b (bits4 b0 b1 b2 b3) Imv),
    (morph_live_valid b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Imv), V1, V2, Hmatch in *.
  destruct (weq (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) as [_|NE]; [|contradiction].
  cbv beta iota in F_pc, F_mu, F_err, F_halted, F_regs, F_mem, F_error_code, F_cert_addr, F_partition_ops, F_mdl_ops, F_info_gain, F_mu_tensor, F_module_tensors, F_ptTable, F_pt_next_id, F_certified, F_wc_same_00, F_wc_diff_00, F_wc_same_01, F_wc_diff_01, F_wc_same_10, F_wc_diff_10, F_wc_same_11, F_wc_diff_11, F_morph_src_table, F_morph_dst_table, F_morph_coupling_desc_table, F_morph_identity_table, F_morph_valid_table, F_morph_next_id, F_coupling_desc_label_table, F_coupling_desc_label_len_table, F_lassert_phase, F_chsh_phase, F_mc_phase, F_mc_src1_count, F_mc_src2_count, F_mc_src1_base, F_mc_src2_base, F_mc_i, F_mc_j, F_mc_write_base, F_mc_write_ptr.
  set (P := wordToNat (hw_coupling_pair_next_id b)) in *.
  assert (HPb : hw_coupling_pair_next_id b = natToWord 5 P) by (unfold P; symmetry; apply natToWord_wordToNat).
  pose proof (desc_fits b (bits4 b0 b1 b2 b3) Iref Iz0 Idp V1) as Fit1. pose proof (desc_fits b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Iref Iz0 Idp V2) as Fit2.
  fold P in Fit1, Fit2.
  assert (Raw : compose_raw (step_next b) = compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
    by exact (compose_raw_step b (step_next b) (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) Iid Iz0 V2
      (step_keeps_coupling_pair_src_table b) (step_keeps_coupling_pair_dst_table b)
      F_mc_phase F_mc_src1_count F_mc_src2_count F_mc_src1_base F_mc_src2_base).
  assert (W0 : wordToNat (natToWord CouplingPairCountSz 0) = 0) by reflexivity.
  destruct (compose_fsm_run (step_next b) P
    ltac:(rewrite F_mc_phase; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)), (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); auto)
    F_mc_i F_mc_j ltac:(rewrite F_mc_write_base; exact HPb) ltac:(rewrite F_mc_write_ptr; exact HPb)
    ltac:(rewrite F_mc_src1_count; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); lia)
    ltac:(rewrite F_mc_src2_count; destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); lia)
    ltac:(rewrite F_mc_src1_count, F_mc_src1_base; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); lia)
    ltac:(rewrite F_mc_src2_count, F_mc_src2_base; destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); lia)
    ltac:(rewrite Raw; exact Hcap))
    as [l [out [src' [dst' [_ [Hout [Hslice [Hpre [Rs [Rd [Rv [Rn [Rph [RdB [RdC [RdV [RdN [Rerr Rec]]]]]]]]]]]]]]]]]].
  rewrite Raw in Hout, Hslice, Rv.
  rewrite step_keeps_coupling_pair_src_table, step_keeps_coupling_pair_dst_table in Hpre.
  rewrite step_keeps_coupling_pair_valid_table in Rv.
  rewrite step_keeps_coupling_desc_base_table, step_keeps_coupling_desc_next_id in RdB.
  rewrite step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id in RdC.
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_next_id in RdV.
  rewrite step_keeps_coupling_desc_next_id in RdN.
  set (Fin := compose_fsm_final (step_next b)) in *.
  refine (eq_trans _ (eq_sym (kami_step_compose_hw b (wordToNat (bits4 a0 a1 a2 a3)) (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7)) Iref Iz Iz0 Idp Ipv ltac:(lia) V1 V2 Hmatch))).
  cbv zeta. rewrite (compose_label_hw b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3)) (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) Ilab Hlab).
  rewrite <- Hslice.
  assert (Rich : rich_state_add_morph_with_coupling (hwb_rich b) (wordToNat (hw_morph_src_table b (bits4 b0 b1 b2 b3)))
      (wordToNat (hw_morph_dst_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))))
      (map natpair (table_slice src' dst' P (out - P)))
      (atom_label (wordToNat (wplus (hw_label_len b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))) (hw_label_len b (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))))))
         (wordToNat (wplus (hw_label_word b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))) (wlshift (hw_label_word b (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (hw_label_len b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))))))))
      false = (hwb_rich Fin, wordToNat (hw_morph_next_id b))).
  { apply (rich_after_morph_commit b Fin _ _ P out _
      (wplus (hw_label_word b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))) (wlshift (hw_label_word b (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (hw_label_len b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))))))
      (wplus (hw_label_len b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))) (hw_label_len b (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))))); try lia.
    - exact HPb.
    - unfold Fin; rewrite compose_fsm_keeps_morph_valid_table; exact F_morph_valid_table.
    - unfold Fin; rewrite compose_fsm_keeps_morph_src_table; exact F_morph_src_table.
    - unfold Fin; rewrite compose_fsm_keeps_morph_dst_table; exact F_morph_dst_table.
    - unfold Fin; rewrite compose_fsm_keeps_morph_coupling_desc_table; exact F_morph_coupling_desc_table.
    - unfold Fin; rewrite compose_fsm_keeps_morph_identity_table; exact F_morph_identity_table.
    - unfold Fin; rewrite compose_fsm_keeps_morph_next_id; exact F_morph_next_id.
    - exact RdV.
    - exact RdB.
    - exact RdC.
    - unfold Fin; rewrite compose_fsm_keeps_coupling_desc_label_table; exact F_coupling_desc_label_table.
    - unfold Fin; rewrite compose_fsm_keeps_coupling_desc_label_len_table; exact F_coupling_desc_label_len_table.
    - reflexivity.
    - exact RdN.
    - exact Rn.
    - intros k Hk. rewrite Rv. unfold hwb_valid. rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia).
      rewrite loaded_valid_at by lia.
      destruct (Nat.ltb_spec k P); destruct (Nat.leb_spec P k);
        destruct (Nat.ltb_spec k (P + List.length (compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))))); cbn [andb]; try reflexivity; lia.
    - intros k Hk. pose proof (Hpre k Hk) as Ek. unfold table_pair in Ek.
      rewrite !(pair_index_small k) in Ek by lia. injection Ek as E1 E2.
      rewrite Rs, Rd. unfold hwb_vector_nat. rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia).
      exact (conj (f_equal (@wordToNat _) E1) (f_equal (@wordToNat _) E2)).
    - intros k Hk. unfold table_slice. rewrite map_map.
      set (f := fun x : nat => natpair (table_pair src' dst' x)).
      rewrite (nth_indep (map f (seq P (out - P))) (0, 0) (f 0)) by (rewrite map_length, seq_length; lia).
      rewrite map_nth, seq_nth by lia. unfold f. replace (P + (k - P)) with k by lia.
      rewrite Rs, Rd. unfold natpair, table_pair. cbn [fst snd]. unfold hwb_vector_nat.
      rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia). rewrite (pair_index_small k) by lia. reflexivity.
    - unfold table_slice. rewrite !map_length, seq_length. reflexivity.
    - split; [unfold Fin; rewrite compose_fsm_keeps_formula_desc_valid_table; apply step_keeps_formula_desc_valid_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_formula_desc_base_table; apply step_keeps_formula_desc_base_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_formula_desc_count_table; apply step_keeps_formula_desc_count_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_formula_desc_next_id; apply step_keeps_formula_desc_next_id|]. split; [unfold Fin; rewrite compose_fsm_keeps_cert_desc_valid_table; apply step_keeps_cert_desc_valid_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_cert_desc_base_table; apply step_keeps_cert_desc_base_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_cert_desc_count_table; apply step_keeps_cert_desc_count_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_cert_desc_next_id; apply step_keeps_cert_desc_next_id|]. split; [unfold Fin; rewrite compose_fsm_keeps_desc_meta_valid_table; apply step_keeps_desc_meta_valid_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_desc_meta_subtype_table; apply step_keeps_desc_meta_subtype_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_desc_meta_kind_table; apply step_keeps_desc_meta_kind_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_desc_meta_inline_len_table; apply step_keeps_desc_meta_inline_len_table|]. split; [unfold Fin; rewrite compose_fsm_keeps_desc_meta_aux_table; apply step_keeps_desc_meta_aux_table|]. unfold Fin; rewrite compose_fsm_keeps_desc_meta_next_id; apply step_keeps_desc_meta_next_id. }
  change (snap_rich_state (hwb_snapshot b)) with (hwb_rich b).
  rewrite Rich. cbn [fst snd].
  unfold hwb_snapshot at 1. rewrite Rerr, Rec. unfold Fin.
  rewrite compose_fsm_keeps_pc, compose_fsm_keeps_mu, compose_fsm_keeps_halted, compose_fsm_keeps_regs, compose_fsm_keeps_mem, compose_fsm_keeps_cert_addr, compose_fsm_keeps_partition_ops, compose_fsm_keeps_mdl_ops, compose_fsm_keeps_info_gain, compose_fsm_keeps_mu_tensor, compose_fsm_keeps_module_tensors, compose_fsm_keeps_ptTable, compose_fsm_keeps_pt_next_id, compose_fsm_keeps_certified, compose_fsm_keeps_wc_same_00, compose_fsm_keeps_wc_diff_00, compose_fsm_keeps_wc_same_01, compose_fsm_keeps_wc_diff_01, compose_fsm_keeps_wc_same_10, compose_fsm_keeps_wc_diff_10, compose_fsm_keeps_wc_same_11, compose_fsm_keeps_wc_diff_11, compose_fsm_keeps_csr_status, compose_fsm_keeps_csr_heap_base, compose_fsm_keeps_logic_acc, compose_fsm_keeps_mstatus.
  rewrite F_pc, F_mu, F_halted, F_regs, F_mem, F_cert_addr, F_partition_ops, F_mdl_ops, F_info_gain, F_mu_tensor, F_module_tensors, F_ptTable, F_pt_next_id, F_certified, F_wc_same_00, F_wc_diff_00, F_wc_same_01, F_wc_diff_01, F_wc_same_10, F_wc_diff_10, F_wc_same_11, F_wc_diff_11, F_err, F_error_code.
  rewrite step_keeps_csr_status, step_keeps_csr_heap_base, step_keeps_logic_acc, step_keeps_mstatus.
  unfold kami_advance_rich_morph. snap_projections. rewrite ?He, ?Hh.
  apply kami_snapshot_ext; snap_projections.
  all: first [ syntactic | close_pc | close_mu_cost
    | close_vector_update ltac:(etransitivity; [apply wordToNat_zext4_32|]; rewrite (wordToNat_trunc4_5_small _ Hroom);
        rewrite word64_below_pow2_32 by exact (lt16_pow2_32 _ Hroom); reflexivity) ].
Qed.

Corollary compose_ext_execution : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
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
  exists labels,
    Multistep thieleCore (hwb_regs b) (hwb_regs (compose_fsm_final (step_next b))) labels /\
    hwb_snapshot (compose_fsm_final (step_next b)) = kami_step (hwb_snapshot b) (instr_compose (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 Imv Iref Iz Iz0 Idp Ipv Iid Ilab V1 V2 Hmatch Hlab Hcap.
  destruct (compose_ext_run a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 Imv Iref Iz Iz0 Idp Ipv Iid Ilab V1 V2 Hmatch Hlab Hcap) as [l Hl].
  exists l. split; [exact Hl|].
  exact (compose_ext_retire a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 Imv Iref Iz Iz0 Idp Ipv Iid Ilab V1 V2 Hmatch Hlab Hcap).
Qed.
