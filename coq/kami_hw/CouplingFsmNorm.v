(** CouplingFsmNorm.v: the coupling normalization loop at the typed boundary.
    [nscan_run] is the suffix scan, [nouter_step_facts] one scan-and-emit
    iteration, and [nouter_run] the whole loop, which preserves
    [normalization_prefix_invariant] and is an actual Kami execution. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop NormalizationPrefix NormalizationScanExecution RuleEnabled FsmDecoded ChshRetire.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma rule_in_index : forall n, n <= 11 -> In (normalization_rule n) (getRules thieleCore).
Proof.
  intros n Hn. rewrite cpu_rules_listed. apply in_map. cbn [In].
  assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11) by lia.
  intuition.
Qed.

Lemma wlt_nat5 : forall a b, a < 32 -> b < 32 ->
  (if wlt_dec (natToWord 5 a) (natToWord 5 b) then true else false) = Nat.ltb a b.
Proof.
  intros a b Ha Hb. destruct (wlt_dec _ _) as [H|H].
  - apply wlt_lt in H. rewrite !wordToNat_natToWord_2 in H by assumption.
    symmetry. apply Nat.ltb_lt. exact H.
  - symmetry. apply Nat.ltb_ge. destruct (Nat.lt_ge_cases a b) as [L|L]; [|exact L].
    exfalso. apply H. apply lt_wlt. rewrite !wordToNat_natToWord_2 by assumption. exact L.
Qed.

Lemma weq_nat5 : forall a b, a < 32 -> b < 32 ->
  (if weq (natToWord 5 a) (natToWord 5 b) then true else false) = Nat.eqb a b.
Proof. intros a b Ha Hb. exact (bounded_word_eqb a b Ha Hb). Qed.

Lemma succ_word5 : forall a, wplus (natToWord 5 a) (natToWord 5 1) = natToWord 5 (S a).
Proof. intro a. rewrite <- natToWord_plus, Nat.add_1_r. reflexivity. Qed.

(** * Scan rule *)

Lemma mcnscan_keeps_pc : forall c, hw_pc (mcnscan_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mu : forall c, hw_mu (mcnscan_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_err : forall c, hw_err (mcnscan_next c) = hw_err c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_halted : forall c, hw_halted (mcnscan_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_regs : forall c, hw_regs (mcnscan_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mem : forall c, hw_mem (mcnscan_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_imem : forall c, hw_imem (mcnscan_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_partition_ops : forall c, hw_partition_ops (mcnscan_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mdl_ops : forall c, hw_mdl_ops (mcnscan_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_info_gain : forall c, hw_info_gain (mcnscan_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_error_code : forall c, hw_error_code (mcnscan_next c) = hw_error_code c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_logic_acc : forall c, hw_logic_acc (mcnscan_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_cert_addr : forall c, hw_cert_addr (mcnscan_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_active_module : forall c, hw_active_module (mcnscan_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mstatus : forall c, hw_mstatus (mcnscan_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mcycle_lo : forall c, hw_mcycle_lo (mcnscan_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mcycle_hi : forall c, hw_mcycle_hi (mcnscan_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_minstret_lo : forall c, hw_minstret_lo (mcnscan_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_minstret_hi : forall c, hw_minstret_hi (mcnscan_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_trap_vector : forall c, hw_trap_vector (mcnscan_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_certified : forall c, hw_certified (mcnscan_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_phase : forall c, hw_lassert_phase (mcnscan_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_kind : forall c, hw_lassert_kind (mcnscan_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_fbase : forall c, hw_lassert_fbase (mcnscan_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_cbase : forall c, hw_lassert_cbase (mcnscan_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_flen : forall c, hw_lassert_flen (mcnscan_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_clen : forall c, hw_lassert_clen (mcnscan_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_nvars : forall c, hw_lassert_nvars (mcnscan_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_fptr : forall c, hw_lassert_fptr (mcnscan_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_cptr : forall c, hw_lassert_cptr (mcnscan_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mcnscan_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mcnscan_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mcnscan_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mcnscan_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mcnscan_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_phase : forall c, hw_chsh_phase (mcnscan_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n00 : forall c, hw_chsh_n00 (mcnscan_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n01 : forall c, hw_chsh_n01 (mcnscan_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n10 : forall c, hw_chsh_n10 (mcnscan_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n11 : forall c, hw_chsh_n11 (mcnscan_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d00 : forall c, hw_chsh_d00 (mcnscan_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d01 : forall c, hw_chsh_d01 (mcnscan_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d10 : forall c, hw_chsh_d10 (mcnscan_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d11 : forall c, hw_chsh_d11 (mcnscan_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mcnscan_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mcnscan_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mcnscan_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mcnscan_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mcnscan_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mcnscan_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mcnscan_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mcnscan_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mcnscan_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mcnscan_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mcnscan_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mcnscan_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mcnscan_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mcnscan_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mcnscan_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mcnscan_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mcnscan_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mcnscan_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mcnscan_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mcnscan_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mcnscan_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mcnscan_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mcnscan_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mcnscan_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mcnscan_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mcnscan_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_chsh_check_result : forall c, hw_chsh_check_result (mcnscan_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mcnscan_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mcnscan_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mcnscan_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mu_tensor : forall c, hw_mu_tensor (mcnscan_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_module_tensors : forall c, hw_module_tensors (mcnscan_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_csr_status : forall c, hw_csr_status (mcnscan_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_csr_heap_base : forall c, hw_csr_heap_base (mcnscan_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_ptTable : forall c, hw_ptTable (mcnscan_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_pt_next_id : forall c, hw_pt_next_id (mcnscan_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_morph_src_table : forall c, hw_morph_src_table (mcnscan_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_morph_dst_table : forall c, hw_morph_dst_table (mcnscan_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mcnscan_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_morph_valid_table : forall c, hw_morph_valid_table (mcnscan_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_morph_identity_table : forall c, hw_morph_identity_table (mcnscan_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_morph_next_id : forall c, hw_morph_next_id (mcnscan_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mcnscan_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mcnscan_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mcnscan_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mcnscan_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mcnscan_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mcnscan_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_pair_src_table : forall c, hw_coupling_pair_src_table (mcnscan_next c) = hw_coupling_pair_src_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_pair_dst_table : forall c, hw_coupling_pair_dst_table (mcnscan_next c) = hw_coupling_pair_dst_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (mcnscan_next c) = hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mcnscan_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_op : forall c, hw_mc_op (mcnscan_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_mem_base : forall c, hw_mc_mem_base (mcnscan_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_pair_count : forall c, hw_mc_pair_count (mcnscan_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (mcnscan_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_src1_base : forall c, hw_mc_src1_base (mcnscan_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_src1_count : forall c, hw_mc_src1_count (mcnscan_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_src2_base : forall c, hw_mc_src2_base (mcnscan_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_src2_count : forall c, hw_mc_src2_count (mcnscan_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_i : forall c, hw_mc_i (mcnscan_next c) = hw_mc_i c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mcnscan_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mcnscan_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_write_base : forall c, hw_mc_write_base (mcnscan_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_write_ptr : forall c, hw_mc_write_ptr (mcnscan_next c) = hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (mcnscan_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mcnscan_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mcnscan_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mcnscan_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mcnscan_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_mc_cost : forall c, hw_mc_cost (mcnscan_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mcnscan_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mcnscan_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mcnscan_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mcnscan_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mcnscan_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mcnscan_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mcnscan_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mcnscan_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mcnscan_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mcnscan_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mcnscan_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mcnscan_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mcnscan_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mcnscan_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_same_00 : forall c, hw_wc_same_00 (mcnscan_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mcnscan_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_same_01 : forall c, hw_wc_same_01 (mcnscan_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mcnscan_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_same_10 : forall c, hw_wc_same_10 (mcnscan_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mcnscan_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_same_11 : forall c, hw_wc_same_11 (mcnscan_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mcnscan_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mcnscan_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma mcnscan_j : forall c, hw_mc_j (mcnscan_next c) = wplus (hw_mc_j c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcnscan_phase : forall c, hw_mc_phase (mcnscan_next c) =
  if (if wlt_dec (hw_mc_j c) (hw_mc_write_ptr c) then true else false) then natToWord 4 8 else natToWord 4 9.
Proof. reflexivity. Qed.
Lemma mcnscan_dup : forall c, hw_mc_duplicate (mcnscan_next c) =
  orb (hw_mc_duplicate c) (andb (if wlt_dec (hw_mc_j c) (hw_mc_write_ptr c) then true else false)
    (scan_match (hw_mc_i c) (hw_mc_j c) (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c))).
Proof. reflexivity. Qed.

(** * Emit rule *)

Lemma mcnemit_keeps_pc : forall c, hw_pc (mcnemit_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mu : forall c, hw_mu (mcnemit_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_err : forall c, hw_err (mcnemit_next c) = hw_err c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_halted : forall c, hw_halted (mcnemit_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_regs : forall c, hw_regs (mcnemit_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mem : forall c, hw_mem (mcnemit_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_imem : forall c, hw_imem (mcnemit_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_partition_ops : forall c, hw_partition_ops (mcnemit_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mdl_ops : forall c, hw_mdl_ops (mcnemit_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_info_gain : forall c, hw_info_gain (mcnemit_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_error_code : forall c, hw_error_code (mcnemit_next c) = hw_error_code c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_logic_acc : forall c, hw_logic_acc (mcnemit_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_cert_addr : forall c, hw_cert_addr (mcnemit_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_active_module : forall c, hw_active_module (mcnemit_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mstatus : forall c, hw_mstatus (mcnemit_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mcycle_lo : forall c, hw_mcycle_lo (mcnemit_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mcycle_hi : forall c, hw_mcycle_hi (mcnemit_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_minstret_lo : forall c, hw_minstret_lo (mcnemit_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_minstret_hi : forall c, hw_minstret_hi (mcnemit_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_trap_vector : forall c, hw_trap_vector (mcnemit_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_certified : forall c, hw_certified (mcnemit_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_phase : forall c, hw_lassert_phase (mcnemit_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_kind : forall c, hw_lassert_kind (mcnemit_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_fbase : forall c, hw_lassert_fbase (mcnemit_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_cbase : forall c, hw_lassert_cbase (mcnemit_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_flen : forall c, hw_lassert_flen (mcnemit_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_clen : forall c, hw_lassert_clen (mcnemit_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_nvars : forall c, hw_lassert_nvars (mcnemit_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_fptr : forall c, hw_lassert_fptr (mcnemit_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_cptr : forall c, hw_lassert_cptr (mcnemit_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mcnemit_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mcnemit_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mcnemit_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mcnemit_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mcnemit_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_phase : forall c, hw_chsh_phase (mcnemit_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n00 : forall c, hw_chsh_n00 (mcnemit_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n01 : forall c, hw_chsh_n01 (mcnemit_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n10 : forall c, hw_chsh_n10 (mcnemit_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n11 : forall c, hw_chsh_n11 (mcnemit_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d00 : forall c, hw_chsh_d00 (mcnemit_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d01 : forall c, hw_chsh_d01 (mcnemit_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d10 : forall c, hw_chsh_d10 (mcnemit_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d11 : forall c, hw_chsh_d11 (mcnemit_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mcnemit_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mcnemit_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mcnemit_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mcnemit_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mcnemit_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mcnemit_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mcnemit_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mcnemit_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mcnemit_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mcnemit_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mcnemit_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mcnemit_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mcnemit_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mcnemit_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mcnemit_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mcnemit_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mcnemit_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mcnemit_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mcnemit_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mcnemit_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mcnemit_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mcnemit_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mcnemit_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mcnemit_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mcnemit_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mcnemit_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_chsh_check_result : forall c, hw_chsh_check_result (mcnemit_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mcnemit_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mcnemit_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mcnemit_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mu_tensor : forall c, hw_mu_tensor (mcnemit_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_module_tensors : forall c, hw_module_tensors (mcnemit_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_csr_status : forall c, hw_csr_status (mcnemit_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_csr_heap_base : forall c, hw_csr_heap_base (mcnemit_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_ptTable : forall c, hw_ptTable (mcnemit_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_pt_next_id : forall c, hw_pt_next_id (mcnemit_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_morph_src_table : forall c, hw_morph_src_table (mcnemit_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_morph_dst_table : forall c, hw_morph_dst_table (mcnemit_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mcnemit_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_morph_valid_table : forall c, hw_morph_valid_table (mcnemit_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_morph_identity_table : forall c, hw_morph_identity_table (mcnemit_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_morph_next_id : forall c, hw_morph_next_id (mcnemit_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mcnemit_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mcnemit_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mcnemit_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mcnemit_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mcnemit_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mcnemit_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (mcnemit_next c) = hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mcnemit_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_op : forall c, hw_mc_op (mcnemit_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_mem_base : forall c, hw_mc_mem_base (mcnemit_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_pair_count : forall c, hw_mc_pair_count (mcnemit_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (mcnemit_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_src1_base : forall c, hw_mc_src1_base (mcnemit_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_src1_count : forall c, hw_mc_src1_count (mcnemit_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_src2_base : forall c, hw_mc_src2_base (mcnemit_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_src2_count : forall c, hw_mc_src2_count (mcnemit_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mcnemit_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mcnemit_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_write_base : forall c, hw_mc_write_base (mcnemit_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mcnemit_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mcnemit_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mcnemit_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mcnemit_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_mc_cost : forall c, hw_mc_cost (mcnemit_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mcnemit_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mcnemit_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mcnemit_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mcnemit_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mcnemit_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mcnemit_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mcnemit_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mcnemit_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mcnemit_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mcnemit_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mcnemit_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mcnemit_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mcnemit_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mcnemit_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_same_00 : forall c, hw_wc_same_00 (mcnemit_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mcnemit_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_same_01 : forall c, hw_wc_same_01 (mcnemit_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mcnemit_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_same_10 : forall c, hw_wc_same_10 (mcnemit_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mcnemit_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_same_11 : forall c, hw_wc_same_11 (mcnemit_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mcnemit_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mcnemit_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma mcnemit_src : forall c, hw_coupling_pair_src_table (mcnemit_next c) =
  if hw_mc_duplicate c then hw_coupling_pair_src_table c
  else put_vector (hw_coupling_pair_src_table c) (pair_index (hw_mc_norm_ptr c))
         (hw_coupling_pair_src_table c (pair_index (hw_mc_i c))).
Proof. reflexivity. Qed.
Lemma mcnemit_dst : forall c, hw_coupling_pair_dst_table (mcnemit_next c) =
  if hw_mc_duplicate c then hw_coupling_pair_dst_table c
  else put_vector (hw_coupling_pair_dst_table c) (pair_index (hw_mc_norm_ptr c))
         (hw_coupling_pair_dst_table c (pair_index (hw_mc_i c))).
Proof. reflexivity. Qed.
Lemma mcnemit_norm : forall c, hw_mc_norm_ptr (mcnemit_next c) = emit_next (hw_mc_norm_ptr c) (hw_mc_duplicate c).
Proof. reflexivity. Qed.
Lemma mcnemit_i : forall c, hw_mc_i (mcnemit_next c) = wplus (hw_mc_i c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcnemit_j : forall c, hw_mc_j (mcnemit_next c) = wplus (wplus (hw_mc_i c) (natToWord 5 1)) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcnemit_dup : forall c, hw_mc_duplicate (mcnemit_next c) = false.
Proof. reflexivity. Qed.
Lemma mcnemit_phase : forall c, hw_mc_phase (mcnemit_next c) =
  if (if weq (wplus (hw_mc_i c) (natToWord 5 1)) (hw_mc_write_ptr c) then true else false)
  then natToWord 4 11 else natToWord 4 8.
Proof. reflexivity. Qed.
Lemma mcnemit_write_ptr : forall c, hw_mc_write_ptr (mcnemit_next c) =
  if (if weq (wplus (hw_mc_i c) (natToWord 5 1)) (hw_mc_write_ptr c) then true else false)
  then emit_next (hw_mc_norm_ptr c) (hw_mc_duplicate c) else hw_mc_write_ptr c.
Proof. reflexivity. Qed.

(** * Scan loop *)

Fixpoint nscan_iter (n : nat) (c : HWB) : HWB :=
  match n with
  | O => c
  | S m => nscan_iter m (mcnscan_next c)
  end.

Lemma nscan_iter_keeps_pc : forall n c, hw_pc (nscan_iter n c) = hw_pc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_pc]. Qed.
Lemma nscan_iter_keeps_mu : forall n c, hw_mu (nscan_iter n c) = hw_mu c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mu]. Qed.
Lemma nscan_iter_keeps_err : forall n c, hw_err (nscan_iter n c) = hw_err c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_err]. Qed.
Lemma nscan_iter_keeps_halted : forall n c, hw_halted (nscan_iter n c) = hw_halted c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_halted]. Qed.
Lemma nscan_iter_keeps_regs : forall n c, hw_regs (nscan_iter n c) = hw_regs c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_regs]. Qed.
Lemma nscan_iter_keeps_mem : forall n c, hw_mem (nscan_iter n c) = hw_mem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mem]. Qed.
Lemma nscan_iter_keeps_imem : forall n c, hw_imem (nscan_iter n c) = hw_imem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_imem]. Qed.
Lemma nscan_iter_keeps_partition_ops : forall n c, hw_partition_ops (nscan_iter n c) = hw_partition_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_partition_ops]. Qed.
Lemma nscan_iter_keeps_mdl_ops : forall n c, hw_mdl_ops (nscan_iter n c) = hw_mdl_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mdl_ops]. Qed.
Lemma nscan_iter_keeps_info_gain : forall n c, hw_info_gain (nscan_iter n c) = hw_info_gain c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_info_gain]. Qed.
Lemma nscan_iter_keeps_error_code : forall n c, hw_error_code (nscan_iter n c) = hw_error_code c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_error_code]. Qed.
Lemma nscan_iter_keeps_logic_acc : forall n c, hw_logic_acc (nscan_iter n c) = hw_logic_acc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_logic_acc]. Qed.
Lemma nscan_iter_keeps_cert_addr : forall n c, hw_cert_addr (nscan_iter n c) = hw_cert_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_cert_addr]. Qed.
Lemma nscan_iter_keeps_active_module : forall n c, hw_active_module (nscan_iter n c) = hw_active_module c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_active_module]. Qed.
Lemma nscan_iter_keeps_mstatus : forall n c, hw_mstatus (nscan_iter n c) = hw_mstatus c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mstatus]. Qed.
Lemma nscan_iter_keeps_mcycle_lo : forall n c, hw_mcycle_lo (nscan_iter n c) = hw_mcycle_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mcycle_lo]. Qed.
Lemma nscan_iter_keeps_mcycle_hi : forall n c, hw_mcycle_hi (nscan_iter n c) = hw_mcycle_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mcycle_hi]. Qed.
Lemma nscan_iter_keeps_minstret_lo : forall n c, hw_minstret_lo (nscan_iter n c) = hw_minstret_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_minstret_lo]. Qed.
Lemma nscan_iter_keeps_minstret_hi : forall n c, hw_minstret_hi (nscan_iter n c) = hw_minstret_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_minstret_hi]. Qed.
Lemma nscan_iter_keeps_trap_vector : forall n c, hw_trap_vector (nscan_iter n c) = hw_trap_vector c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_trap_vector]. Qed.
Lemma nscan_iter_keeps_certified : forall n c, hw_certified (nscan_iter n c) = hw_certified c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_certified]. Qed.
Lemma nscan_iter_keeps_lassert_phase : forall n c, hw_lassert_phase (nscan_iter n c) = hw_lassert_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_phase]. Qed.
Lemma nscan_iter_keeps_lassert_kind : forall n c, hw_lassert_kind (nscan_iter n c) = hw_lassert_kind c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_kind]. Qed.
Lemma nscan_iter_keeps_lassert_fbase : forall n c, hw_lassert_fbase (nscan_iter n c) = hw_lassert_fbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_fbase]. Qed.
Lemma nscan_iter_keeps_lassert_cbase : forall n c, hw_lassert_cbase (nscan_iter n c) = hw_lassert_cbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_cbase]. Qed.
Lemma nscan_iter_keeps_lassert_flen : forall n c, hw_lassert_flen (nscan_iter n c) = hw_lassert_flen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_flen]. Qed.
Lemma nscan_iter_keeps_lassert_clen : forall n c, hw_lassert_clen (nscan_iter n c) = hw_lassert_clen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_clen]. Qed.
Lemma nscan_iter_keeps_lassert_nvars : forall n c, hw_lassert_nvars (nscan_iter n c) = hw_lassert_nvars c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_nvars]. Qed.
Lemma nscan_iter_keeps_lassert_fptr : forall n c, hw_lassert_fptr (nscan_iter n c) = hw_lassert_fptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_fptr]. Qed.
Lemma nscan_iter_keeps_lassert_cptr : forall n c, hw_lassert_cptr (nscan_iter n c) = hw_lassert_cptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_cptr]. Qed.
Lemma nscan_iter_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (nscan_iter n c) = hw_lassert_fbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_fbuf]. Qed.
Lemma nscan_iter_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (nscan_iter n c) = hw_lassert_cbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_cbuf]. Qed.
Lemma nscan_iter_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (nscan_iter n c) = hw_lassert_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_clause_sat]. Qed.
Lemma nscan_iter_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (nscan_iter n c) = hw_lassert_counter_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_counter_clause_sat]. Qed.
Lemma nscan_iter_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (nscan_iter n c) = hw_lassert_counter_seen_fail c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_lassert_counter_seen_fail]. Qed.
Lemma nscan_iter_keeps_chsh_phase : forall n c, hw_chsh_phase (nscan_iter n c) = hw_chsh_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_phase]. Qed.
Lemma nscan_iter_keeps_chsh_n00 : forall n c, hw_chsh_n00 (nscan_iter n c) = hw_chsh_n00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n00]. Qed.
Lemma nscan_iter_keeps_chsh_n01 : forall n c, hw_chsh_n01 (nscan_iter n c) = hw_chsh_n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n01]. Qed.
Lemma nscan_iter_keeps_chsh_n10 : forall n c, hw_chsh_n10 (nscan_iter n c) = hw_chsh_n10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n10]. Qed.
Lemma nscan_iter_keeps_chsh_n11 : forall n c, hw_chsh_n11 (nscan_iter n c) = hw_chsh_n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n11]. Qed.
Lemma nscan_iter_keeps_chsh_d00 : forall n c, hw_chsh_d00 (nscan_iter n c) = hw_chsh_d00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d00]. Qed.
Lemma nscan_iter_keeps_chsh_d01 : forall n c, hw_chsh_d01 (nscan_iter n c) = hw_chsh_d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d01]. Qed.
Lemma nscan_iter_keeps_chsh_d10 : forall n c, hw_chsh_d10 (nscan_iter n c) = hw_chsh_d10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d10]. Qed.
Lemma nscan_iter_keeps_chsh_d11 : forall n c, hw_chsh_d11 (nscan_iter n c) = hw_chsh_d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d11]. Qed.
Lemma nscan_iter_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (nscan_iter n c) = hw_chsh_sign00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_sign00]. Qed.
Lemma nscan_iter_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (nscan_iter n c) = hw_chsh_sign01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_sign01]. Qed.
Lemma nscan_iter_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (nscan_iter n c) = hw_chsh_sign10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_sign10]. Qed.
Lemma nscan_iter_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (nscan_iter n c) = hw_chsh_sign11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_sign11]. Qed.
Lemma nscan_iter_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (nscan_iter n c) = hw_chsh_n00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n00sq]. Qed.
Lemma nscan_iter_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (nscan_iter n c) = hw_chsh_n01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n01sq]. Qed.
Lemma nscan_iter_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (nscan_iter n c) = hw_chsh_n10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n10sq]. Qed.
Lemma nscan_iter_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (nscan_iter n c) = hw_chsh_n11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n11sq]. Qed.
Lemma nscan_iter_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (nscan_iter n c) = hw_chsh_d00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d00sq]. Qed.
Lemma nscan_iter_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (nscan_iter n c) = hw_chsh_d01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d01sq]. Qed.
Lemma nscan_iter_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (nscan_iter n c) = hw_chsh_d10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d10sq]. Qed.
Lemma nscan_iter_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (nscan_iter n c) = hw_chsh_d11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d11sq]. Qed.
Lemma nscan_iter_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (nscan_iter n c) = hw_chsh_A_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_A_pos]. Qed.
Lemma nscan_iter_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (nscan_iter n c) = hw_chsh_A_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_A_neg_a]. Qed.
Lemma nscan_iter_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (nscan_iter n c) = hw_chsh_A_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_A_neg_b]. Qed.
Lemma nscan_iter_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (nscan_iter n c) = hw_chsh_B_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_B_pos]. Qed.
Lemma nscan_iter_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (nscan_iter n c) = hw_chsh_B_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_B_neg_a]. Qed.
Lemma nscan_iter_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (nscan_iter n c) = hw_chsh_B_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_B_neg_b]. Qed.
Lemma nscan_iter_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (nscan_iter n c) = hw_chsh_d00d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d00d01]. Qed.
Lemma nscan_iter_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (nscan_iter n c) = hw_chsh_n10n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n10n11]. Qed.
Lemma nscan_iter_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (nscan_iter n c) = hw_chsh_d10d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_d10d11]. Qed.
Lemma nscan_iter_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (nscan_iter n c) = hw_chsh_n00n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_n00n01]. Qed.
Lemma nscan_iter_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (nscan_iter n c) = hw_chsh_abs_C1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_abs_C1]. Qed.
Lemma nscan_iter_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (nscan_iter n c) = hw_chsh_abs_C2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_abs_C2]. Qed.
Lemma nscan_iter_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (nscan_iter n c) = hw_chsh_C_sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_C_sq]. Qed.
Lemma nscan_iter_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (nscan_iter n c) = hw_chsh_A_times_B c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_A_times_B]. Qed.
Lemma nscan_iter_keeps_chsh_check_result : forall n c, hw_chsh_check_result (nscan_iter n c) = hw_chsh_check_result c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_chsh_check_result]. Qed.
Lemma nscan_iter_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (nscan_iter n c) = hw_bus_load_instr_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_bus_load_instr_addr]. Qed.
Lemma nscan_iter_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (nscan_iter n c) = hw_bus_load_instr_data c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_bus_load_instr_data]. Qed.
Lemma nscan_iter_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (nscan_iter n c) = hw_bus_load_instr_kick c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_bus_load_instr_kick]. Qed.
Lemma nscan_iter_keeps_mu_tensor : forall n c, hw_mu_tensor (nscan_iter n c) = hw_mu_tensor c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mu_tensor]. Qed.
Lemma nscan_iter_keeps_module_tensors : forall n c, hw_module_tensors (nscan_iter n c) = hw_module_tensors c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_module_tensors]. Qed.
Lemma nscan_iter_keeps_csr_status : forall n c, hw_csr_status (nscan_iter n c) = hw_csr_status c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_csr_status]. Qed.
Lemma nscan_iter_keeps_csr_heap_base : forall n c, hw_csr_heap_base (nscan_iter n c) = hw_csr_heap_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_csr_heap_base]. Qed.
Lemma nscan_iter_keeps_ptTable : forall n c, hw_ptTable (nscan_iter n c) = hw_ptTable c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_ptTable]. Qed.
Lemma nscan_iter_keeps_pt_next_id : forall n c, hw_pt_next_id (nscan_iter n c) = hw_pt_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_pt_next_id]. Qed.
Lemma nscan_iter_keeps_morph_src_table : forall n c, hw_morph_src_table (nscan_iter n c) = hw_morph_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_morph_src_table]. Qed.
Lemma nscan_iter_keeps_morph_dst_table : forall n c, hw_morph_dst_table (nscan_iter n c) = hw_morph_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_morph_dst_table]. Qed.
Lemma nscan_iter_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (nscan_iter n c) = hw_morph_coupling_desc_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_morph_coupling_desc_table]. Qed.
Lemma nscan_iter_keeps_morph_valid_table : forall n c, hw_morph_valid_table (nscan_iter n c) = hw_morph_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_morph_valid_table]. Qed.
Lemma nscan_iter_keeps_morph_identity_table : forall n c, hw_morph_identity_table (nscan_iter n c) = hw_morph_identity_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_morph_identity_table]. Qed.
Lemma nscan_iter_keeps_morph_next_id : forall n c, hw_morph_next_id (nscan_iter n c) = hw_morph_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_morph_next_id]. Qed.
Lemma nscan_iter_keeps_coupling_desc_base_table : forall n c, hw_coupling_desc_base_table (nscan_iter n c) = hw_coupling_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_desc_base_table]. Qed.
Lemma nscan_iter_keeps_coupling_desc_count_table : forall n c, hw_coupling_desc_count_table (nscan_iter n c) = hw_coupling_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_desc_count_table]. Qed.
Lemma nscan_iter_keeps_coupling_desc_valid_table : forall n c, hw_coupling_desc_valid_table (nscan_iter n c) = hw_coupling_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_desc_valid_table]. Qed.
Lemma nscan_iter_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (nscan_iter n c) = hw_coupling_desc_label_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_desc_label_table]. Qed.
Lemma nscan_iter_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (nscan_iter n c) = hw_coupling_desc_label_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_desc_label_len_table]. Qed.
Lemma nscan_iter_keeps_coupling_desc_next_id : forall n c, hw_coupling_desc_next_id (nscan_iter n c) = hw_coupling_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_desc_next_id]. Qed.
Lemma nscan_iter_keeps_coupling_pair_src_table : forall n c, hw_coupling_pair_src_table (nscan_iter n c) = hw_coupling_pair_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_pair_src_table]. Qed.
Lemma nscan_iter_keeps_coupling_pair_dst_table : forall n c, hw_coupling_pair_dst_table (nscan_iter n c) = hw_coupling_pair_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_pair_dst_table]. Qed.
Lemma nscan_iter_keeps_coupling_pair_valid_table : forall n c, hw_coupling_pair_valid_table (nscan_iter n c) = hw_coupling_pair_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_pair_valid_table]. Qed.
Lemma nscan_iter_keeps_coupling_pair_next_id : forall n c, hw_coupling_pair_next_id (nscan_iter n c) = hw_coupling_pair_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_coupling_pair_next_id]. Qed.
Lemma nscan_iter_keeps_mc_op : forall n c, hw_mc_op (nscan_iter n c) = hw_mc_op c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_op]. Qed.
Lemma nscan_iter_keeps_mc_mem_base : forall n c, hw_mc_mem_base (nscan_iter n c) = hw_mc_mem_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_mem_base]. Qed.
Lemma nscan_iter_keeps_mc_pair_count : forall n c, hw_mc_pair_count (nscan_iter n c) = hw_mc_pair_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_pair_count]. Qed.
Lemma nscan_iter_keeps_mc_read_ptr : forall n c, hw_mc_read_ptr (nscan_iter n c) = hw_mc_read_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_read_ptr]. Qed.
Lemma nscan_iter_keeps_mc_src1_base : forall n c, hw_mc_src1_base (nscan_iter n c) = hw_mc_src1_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_src1_base]. Qed.
Lemma nscan_iter_keeps_mc_src1_count : forall n c, hw_mc_src1_count (nscan_iter n c) = hw_mc_src1_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_src1_count]. Qed.
Lemma nscan_iter_keeps_mc_src2_base : forall n c, hw_mc_src2_base (nscan_iter n c) = hw_mc_src2_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_src2_base]. Qed.
Lemma nscan_iter_keeps_mc_src2_count : forall n c, hw_mc_src2_count (nscan_iter n c) = hw_mc_src2_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_src2_count]. Qed.
Lemma nscan_iter_keeps_mc_i : forall n c, hw_mc_i (nscan_iter n c) = hw_mc_i c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_i]. Qed.
Lemma nscan_iter_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (nscan_iter n c) = hw_mc_is_id1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_is_id1]. Qed.
Lemma nscan_iter_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (nscan_iter n c) = hw_mc_is_id2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_is_id2]. Qed.
Lemma nscan_iter_keeps_mc_write_base : forall n c, hw_mc_write_base (nscan_iter n c) = hw_mc_write_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_write_base]. Qed.
Lemma nscan_iter_keeps_mc_write_ptr : forall n c, hw_mc_write_ptr (nscan_iter n c) = hw_mc_write_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_write_ptr]. Qed.
Lemma nscan_iter_keeps_mc_norm_ptr : forall n c, hw_mc_norm_ptr (nscan_iter n c) = hw_mc_norm_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_norm_ptr]. Qed.
Lemma nscan_iter_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (nscan_iter n c) = hw_mc_dst_reg c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_dst_reg]. Qed.
Lemma nscan_iter_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (nscan_iter n c) = hw_mc_morph_slot c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_morph_slot]. Qed.
Lemma nscan_iter_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (nscan_iter n c) = hw_mc_new_src_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_new_src_mod]. Qed.
Lemma nscan_iter_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (nscan_iter n c) = hw_mc_new_dst_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_new_dst_mod]. Qed.
Lemma nscan_iter_keeps_mc_cost : forall n c, hw_mc_cost (nscan_iter n c) = hw_mc_cost c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_mc_cost]. Qed.
Lemma nscan_iter_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (nscan_iter n c) = hw_formula_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_formula_desc_base_table]. Qed.
Lemma nscan_iter_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (nscan_iter n c) = hw_formula_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_formula_desc_count_table]. Qed.
Lemma nscan_iter_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (nscan_iter n c) = hw_formula_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_formula_desc_valid_table]. Qed.
Lemma nscan_iter_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (nscan_iter n c) = hw_formula_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_formula_desc_next_id]. Qed.
Lemma nscan_iter_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (nscan_iter n c) = hw_cert_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_cert_desc_base_table]. Qed.
Lemma nscan_iter_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (nscan_iter n c) = hw_cert_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_cert_desc_count_table]. Qed.
Lemma nscan_iter_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (nscan_iter n c) = hw_cert_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_cert_desc_valid_table]. Qed.
Lemma nscan_iter_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (nscan_iter n c) = hw_cert_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_cert_desc_next_id]. Qed.
Lemma nscan_iter_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (nscan_iter n c) = hw_desc_meta_subtype_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_desc_meta_subtype_table]. Qed.
Lemma nscan_iter_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (nscan_iter n c) = hw_desc_meta_kind_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_desc_meta_kind_table]. Qed.
Lemma nscan_iter_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (nscan_iter n c) = hw_desc_meta_inline_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_desc_meta_inline_len_table]. Qed.
Lemma nscan_iter_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (nscan_iter n c) = hw_desc_meta_aux_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_desc_meta_aux_table]. Qed.
Lemma nscan_iter_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (nscan_iter n c) = hw_desc_meta_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_desc_meta_valid_table]. Qed.
Lemma nscan_iter_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (nscan_iter n c) = hw_desc_meta_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_desc_meta_next_id]. Qed.
Lemma nscan_iter_keeps_wc_same_00 : forall n c, hw_wc_same_00 (nscan_iter n c) = hw_wc_same_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_same_00]. Qed.
Lemma nscan_iter_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (nscan_iter n c) = hw_wc_diff_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_diff_00]. Qed.
Lemma nscan_iter_keeps_wc_same_01 : forall n c, hw_wc_same_01 (nscan_iter n c) = hw_wc_same_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_same_01]. Qed.
Lemma nscan_iter_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (nscan_iter n c) = hw_wc_diff_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_diff_01]. Qed.
Lemma nscan_iter_keeps_wc_same_10 : forall n c, hw_wc_same_10 (nscan_iter n c) = hw_wc_same_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_same_10]. Qed.
Lemma nscan_iter_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (nscan_iter n c) = hw_wc_diff_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_diff_10]. Qed.
Lemma nscan_iter_keeps_wc_same_11 : forall n c, hw_wc_same_11 (nscan_iter n c) = hw_wc_same_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_same_11]. Qed.
Lemma nscan_iter_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (nscan_iter n c) = hw_wc_diff_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nscan_iter]; rewrite IH; apply mcnscan_keeps_wc_diff_11]. Qed.

Theorem nscan_run : forall n c i lo e dup src dst,
  lo + n = e -> e <= 16 -> i < 16 ->
  hw_mc_phase c = natToWord 4 8 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 lo ->
  hw_mc_write_ptr c = natToWord 5 e -> hw_mc_duplicate c = dup ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  (forall m, m <= n -> hw_mc_phase (nscan_iter m c) = natToWord 4 8) /\
  hw_mc_phase (nscan_iter (S n) c) = natToWord 4 9 /\
  hw_mc_duplicate (nscan_iter (S n) c) = scan_accumulated src dst i lo n dup.
Proof.
  induction n as [|n IH]; intros c i lo e dup src dst Hn He Hi Hp Hic Hj Hw Hd Hs Ht.
  - rewrite Nat.add_0_r in Hn. subst lo. cbn [nscan_iter].
    split; [intros m Hm; assert (m = 0) by lia; subst m; exact Hp|].
    rewrite mcnscan_phase, mcnscan_dup, Hj, Hw, Hd, wlt_nat5, Nat.ltb_irrefl by lia.
    split; [reflexivity|]. unfold scan_accumulated. rewrite scan_seen_empty. reflexivity.
  - assert (L : lo < e) by lia.
    assert (P1 : hw_mc_phase (mcnscan_next c) = natToWord 4 8).
    { rewrite mcnscan_phase, Hj, Hw, wlt_nat5 by lia. rewrite (proj2 (Nat.ltb_lt _ _) L). reflexivity. }
    destruct (IH (mcnscan_next c) i (S lo) e
      (orb dup (scan_match (natToWord 5 i) (natToWord 5 lo) src dst)) src dst
      ltac:(lia) He Hi P1 ltac:(rewrite mcnscan_keeps_mc_i; exact Hic)
      ltac:(rewrite mcnscan_j, Hj; apply succ_word5)
      ltac:(rewrite mcnscan_keeps_mc_write_ptr; exact Hw)
      ltac:(rewrite mcnscan_dup, Hj, Hw, wlt_nat5, (proj2 (Nat.ltb_lt _ _) L), Hic, Hs, Ht, Hd by lia; reflexivity)
      ltac:(rewrite mcnscan_keeps_coupling_pair_src_table; exact Hs)
      ltac:(rewrite mcnscan_keeps_coupling_pair_dst_table; exact Ht)) as [IHp [IHf IHd]].
    split; [intros m Hm; destruct m as [|m]; [exact Hp|cbn [nscan_iter]; apply IHp; lia]|].
    cbn [nscan_iter] in IHf, IHd |- *. split; [exact IHf|].
    rewrite IHd. unfold scan_accumulated, scan_seen. cbn [seq existsb]. rewrite orb_assoc. reflexivity.
Qed.

Lemma nscan_multistep : forall n c,
  (forall m, m < n -> hw_mc_phase (nscan_iter m c) = natToWord 4 8) ->
  Multistep thieleCore (hwb_regs c) (hwb_regs (nscan_iter n c))
    (repeat (normalization_label "mc_normalize_scan") n).
Proof.
  induction n as [|n IH]; intros c H.
  - constructor. reflexivity.
  - assert (G : evalExpr (((Var type (SyntaxKind (Bit 4)) (hw_mc_phase c)) == $$(natToWord 4 8)))%kami_expr = true).
    { cbn [evalExpr evalConstT]. change (hw_mc_phase c) with (hw_mc_phase (nscan_iter 0 c)). rewrite (H 0 ltac:(lia)). reflexivity. }
    destruct (mcnscan_enabled c G) as [u [Hu Eu]].
    cbn [nscan_iter]. replace (repeat (normalization_label "mc_normalize_scan") (S n))
      with (repeat (normalization_label "mc_normalize_scan") n ++ [normalization_label "mc_normalize_scan"])
      by (change [normalization_label "mc_normalize_scan"] with (repeat (normalization_label "mc_normalize_scan") 1); rewrite <- repeat_app, Nat.add_1_r; reflexivity).
    apply (normalization_multistep_trans _ (hwb_regs (mcnscan_next c))).
    + rewrite <- Eu. apply normalization_substep_execution.
      exact (cpu_rule_substep _ _ _ (rule_in_index 8 ltac:(lia)) Hu).
    + apply IH. intros m Hm. exact (H (S m) ltac:(lia)).
Qed.

(** * One outer iteration: the suffix scan and the emit *)

Definition nouter_step (c : HWB) : HWB :=
  mcnemit_next (nscan_iter (wordToNat (hw_mc_write_ptr c) - wordToNat (hw_mc_i c)) c).

Lemma nouter_step_facts : forall c src dst i out e,
  i < e -> e <= 16 ->
  hw_mc_phase c = natToWord 4 8 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 (S i) ->
  hw_mc_write_ptr c = natToWord 5 e -> hw_mc_duplicate c = false -> hw_mc_norm_ptr c = natToWord 5 out ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  let dup := scan_seen src dst i (S i) (e - S i) in
  Multistep thieleCore (hwb_regs c) (hwb_regs (nouter_step c))
    ([normalization_label "mc_normalize_emit"] ++ repeat (normalization_label "mc_normalize_scan") (e - i)) /\
  hw_mc_phase (nouter_step c) = natToWord 4 (if Nat.eqb (S i) e then 11 else 8) /\
  hw_mc_i (nouter_step c) = natToWord 5 (S i) /\
  hw_mc_j (nouter_step c) = natToWord 5 (S (S i)) /\
  hw_mc_write_ptr (nouter_step c) = natToWord 5 (if Nat.eqb (S i) e then next_output out dup else e) /\
  hw_mc_duplicate (nouter_step c) = false /\
  hw_mc_norm_ptr (nouter_step c) = natToWord 5 (next_output out dup) /\
  hw_coupling_pair_src_table (nouter_step c) = emitted_table src i out dup /\
  hw_coupling_pair_dst_table (nouter_step c) = emitted_table dst i out dup.
Proof.
  intros c src dst i out e Hi He Hp Hic Hj Hw Hd Ho Hs Ht dup.
  assert (Hn : wordToNat (hw_mc_write_ptr c) - wordToNat (hw_mc_i c) = S (e - S i)).
  { rewrite Hw, Hic, !wordToNat_natToWord_2 by (cbn; lia). lia. }
  unfold nouter_step. rewrite Hn.
  destruct (nscan_run (e - S i) c i (S i) e false src dst ltac:(lia) He ltac:(lia) Hp Hic Hj Hw Hd Hs Ht)
    as [Pm [Pf Df]].
  set (s := nscan_iter (S (e - S i)) c) in *.
  assert (Si : hw_mc_i s = natToWord 5 i) by (unfold s; rewrite nscan_iter_keeps_mc_i; exact Hic).
  assert (Sw : hw_mc_write_ptr s = natToWord 5 e) by (unfold s; rewrite nscan_iter_keeps_mc_write_ptr; exact Hw).
  assert (So : hw_mc_norm_ptr s = natToWord 5 out) by (unfold s; rewrite nscan_iter_keeps_mc_norm_ptr; exact Ho).
  assert (Ss : hw_coupling_pair_src_table s = src) by (unfold s; rewrite nscan_iter_keeps_coupling_pair_src_table; exact Hs).
  assert (St : hw_coupling_pair_dst_table s = dst) by (unfold s; rewrite nscan_iter_keeps_coupling_pair_dst_table; exact Ht).
  assert (Sd : hw_mc_duplicate s = dup) by (rewrite Df; reflexivity).
  assert (Done : (if weq (wplus (hw_mc_i s) (natToWord 5 1)) (hw_mc_write_ptr s) then true else false) = Nat.eqb (S i) e).
  { rewrite Si, Sw, succ_word5. apply weq_nat5; lia. }
  split.
  - apply (normalization_multistep_trans _ (hwb_regs s)).
    + unfold s. replace (e - i) with (S (e - S i)) by lia. apply nscan_multistep.
      intros m Hm. apply Pm. lia.
    + assert (G : evalExpr (((Var type (SyntaxKind (Bit 4)) (hw_mc_phase s)) == $$(natToWord 4 9)))%kami_expr = true).
      { cbn [evalExpr evalConstT]. rewrite Pf. reflexivity. }
      destruct (mcnemit_enabled s G) as [u [Hu Eu]].
      rewrite <- Eu. change [normalization_label "mc_normalize_emit"] with ([normalization_label "mc_normalize_emit"] ++ nil).
      apply (normalization_multistep_trans _ (hwb_regs s)); [constructor; reflexivity|].
      apply normalization_substep_execution.
      exact (cpu_rule_substep _ _ _ (rule_in_index 9 ltac:(lia)) Hu).
  - rewrite mcnemit_phase, Done. split; [destruct (Nat.eqb (S i) e); reflexivity|].
    rewrite mcnemit_i, Si, succ_word5. split; [reflexivity|].
    rewrite mcnemit_j, Si, !succ_word5. split; [reflexivity|].
    rewrite mcnemit_write_ptr, Done, So, Sd, normalization_emit_output_nat, Sw.
    split; [destruct (Nat.eqb (S i) e); reflexivity|].
    split; [apply mcnemit_dup|].
    rewrite mcnemit_norm, So, Sd, normalization_emit_output_nat. split; [reflexivity|].
    rewrite mcnemit_src, mcnemit_dst, Sd, So, Si, Ss, St. unfold emitted_table.
    split; reflexivity.
Qed.

Lemma nouter_step_keeps_pc : forall c, hw_pc (nouter_step c) = hw_pc c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_pc. apply nscan_iter_keeps_pc. Qed.
Lemma nouter_step_keeps_mu : forall c, hw_mu (nouter_step c) = hw_mu c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mu. apply nscan_iter_keeps_mu. Qed.
Lemma nouter_step_keeps_err : forall c, hw_err (nouter_step c) = hw_err c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_err. apply nscan_iter_keeps_err. Qed.
Lemma nouter_step_keeps_halted : forall c, hw_halted (nouter_step c) = hw_halted c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_halted. apply nscan_iter_keeps_halted. Qed.
Lemma nouter_step_keeps_regs : forall c, hw_regs (nouter_step c) = hw_regs c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_regs. apply nscan_iter_keeps_regs. Qed.
Lemma nouter_step_keeps_mem : forall c, hw_mem (nouter_step c) = hw_mem c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mem. apply nscan_iter_keeps_mem. Qed.
Lemma nouter_step_keeps_imem : forall c, hw_imem (nouter_step c) = hw_imem c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_imem. apply nscan_iter_keeps_imem. Qed.
Lemma nouter_step_keeps_partition_ops : forall c, hw_partition_ops (nouter_step c) = hw_partition_ops c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_partition_ops. apply nscan_iter_keeps_partition_ops. Qed.
Lemma nouter_step_keeps_mdl_ops : forall c, hw_mdl_ops (nouter_step c) = hw_mdl_ops c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mdl_ops. apply nscan_iter_keeps_mdl_ops. Qed.
Lemma nouter_step_keeps_info_gain : forall c, hw_info_gain (nouter_step c) = hw_info_gain c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_info_gain. apply nscan_iter_keeps_info_gain. Qed.
Lemma nouter_step_keeps_error_code : forall c, hw_error_code (nouter_step c) = hw_error_code c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_error_code. apply nscan_iter_keeps_error_code. Qed.
Lemma nouter_step_keeps_logic_acc : forall c, hw_logic_acc (nouter_step c) = hw_logic_acc c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_logic_acc. apply nscan_iter_keeps_logic_acc. Qed.
Lemma nouter_step_keeps_cert_addr : forall c, hw_cert_addr (nouter_step c) = hw_cert_addr c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_cert_addr. apply nscan_iter_keeps_cert_addr. Qed.
Lemma nouter_step_keeps_active_module : forall c, hw_active_module (nouter_step c) = hw_active_module c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_active_module. apply nscan_iter_keeps_active_module. Qed.
Lemma nouter_step_keeps_mstatus : forall c, hw_mstatus (nouter_step c) = hw_mstatus c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mstatus. apply nscan_iter_keeps_mstatus. Qed.
Lemma nouter_step_keeps_mcycle_lo : forall c, hw_mcycle_lo (nouter_step c) = hw_mcycle_lo c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mcycle_lo. apply nscan_iter_keeps_mcycle_lo. Qed.
Lemma nouter_step_keeps_mcycle_hi : forall c, hw_mcycle_hi (nouter_step c) = hw_mcycle_hi c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mcycle_hi. apply nscan_iter_keeps_mcycle_hi. Qed.
Lemma nouter_step_keeps_minstret_lo : forall c, hw_minstret_lo (nouter_step c) = hw_minstret_lo c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_minstret_lo. apply nscan_iter_keeps_minstret_lo. Qed.
Lemma nouter_step_keeps_minstret_hi : forall c, hw_minstret_hi (nouter_step c) = hw_minstret_hi c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_minstret_hi. apply nscan_iter_keeps_minstret_hi. Qed.
Lemma nouter_step_keeps_trap_vector : forall c, hw_trap_vector (nouter_step c) = hw_trap_vector c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_trap_vector. apply nscan_iter_keeps_trap_vector. Qed.
Lemma nouter_step_keeps_certified : forall c, hw_certified (nouter_step c) = hw_certified c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_certified. apply nscan_iter_keeps_certified. Qed.
Lemma nouter_step_keeps_lassert_phase : forall c, hw_lassert_phase (nouter_step c) = hw_lassert_phase c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_phase. apply nscan_iter_keeps_lassert_phase. Qed.
Lemma nouter_step_keeps_lassert_kind : forall c, hw_lassert_kind (nouter_step c) = hw_lassert_kind c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_kind. apply nscan_iter_keeps_lassert_kind. Qed.
Lemma nouter_step_keeps_lassert_fbase : forall c, hw_lassert_fbase (nouter_step c) = hw_lassert_fbase c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_fbase. apply nscan_iter_keeps_lassert_fbase. Qed.
Lemma nouter_step_keeps_lassert_cbase : forall c, hw_lassert_cbase (nouter_step c) = hw_lassert_cbase c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_cbase. apply nscan_iter_keeps_lassert_cbase. Qed.
Lemma nouter_step_keeps_lassert_flen : forall c, hw_lassert_flen (nouter_step c) = hw_lassert_flen c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_flen. apply nscan_iter_keeps_lassert_flen. Qed.
Lemma nouter_step_keeps_lassert_clen : forall c, hw_lassert_clen (nouter_step c) = hw_lassert_clen c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_clen. apply nscan_iter_keeps_lassert_clen. Qed.
Lemma nouter_step_keeps_lassert_nvars : forall c, hw_lassert_nvars (nouter_step c) = hw_lassert_nvars c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_nvars. apply nscan_iter_keeps_lassert_nvars. Qed.
Lemma nouter_step_keeps_lassert_fptr : forall c, hw_lassert_fptr (nouter_step c) = hw_lassert_fptr c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_fptr. apply nscan_iter_keeps_lassert_fptr. Qed.
Lemma nouter_step_keeps_lassert_cptr : forall c, hw_lassert_cptr (nouter_step c) = hw_lassert_cptr c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_cptr. apply nscan_iter_keeps_lassert_cptr. Qed.
Lemma nouter_step_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (nouter_step c) = hw_lassert_fbuf c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_fbuf. apply nscan_iter_keeps_lassert_fbuf. Qed.
Lemma nouter_step_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (nouter_step c) = hw_lassert_cbuf c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_cbuf. apply nscan_iter_keeps_lassert_cbuf. Qed.
Lemma nouter_step_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (nouter_step c) = hw_lassert_clause_sat c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_clause_sat. apply nscan_iter_keeps_lassert_clause_sat. Qed.
Lemma nouter_step_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (nouter_step c) = hw_lassert_counter_clause_sat c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_counter_clause_sat. apply nscan_iter_keeps_lassert_counter_clause_sat. Qed.
Lemma nouter_step_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (nouter_step c) = hw_lassert_counter_seen_fail c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_lassert_counter_seen_fail. apply nscan_iter_keeps_lassert_counter_seen_fail. Qed.
Lemma nouter_step_keeps_chsh_phase : forall c, hw_chsh_phase (nouter_step c) = hw_chsh_phase c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_phase. apply nscan_iter_keeps_chsh_phase. Qed.
Lemma nouter_step_keeps_chsh_n00 : forall c, hw_chsh_n00 (nouter_step c) = hw_chsh_n00 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n00. apply nscan_iter_keeps_chsh_n00. Qed.
Lemma nouter_step_keeps_chsh_n01 : forall c, hw_chsh_n01 (nouter_step c) = hw_chsh_n01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n01. apply nscan_iter_keeps_chsh_n01. Qed.
Lemma nouter_step_keeps_chsh_n10 : forall c, hw_chsh_n10 (nouter_step c) = hw_chsh_n10 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n10. apply nscan_iter_keeps_chsh_n10. Qed.
Lemma nouter_step_keeps_chsh_n11 : forall c, hw_chsh_n11 (nouter_step c) = hw_chsh_n11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n11. apply nscan_iter_keeps_chsh_n11. Qed.
Lemma nouter_step_keeps_chsh_d00 : forall c, hw_chsh_d00 (nouter_step c) = hw_chsh_d00 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d00. apply nscan_iter_keeps_chsh_d00. Qed.
Lemma nouter_step_keeps_chsh_d01 : forall c, hw_chsh_d01 (nouter_step c) = hw_chsh_d01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d01. apply nscan_iter_keeps_chsh_d01. Qed.
Lemma nouter_step_keeps_chsh_d10 : forall c, hw_chsh_d10 (nouter_step c) = hw_chsh_d10 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d10. apply nscan_iter_keeps_chsh_d10. Qed.
Lemma nouter_step_keeps_chsh_d11 : forall c, hw_chsh_d11 (nouter_step c) = hw_chsh_d11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d11. apply nscan_iter_keeps_chsh_d11. Qed.
Lemma nouter_step_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (nouter_step c) = hw_chsh_sign00 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_sign00. apply nscan_iter_keeps_chsh_sign00. Qed.
Lemma nouter_step_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (nouter_step c) = hw_chsh_sign01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_sign01. apply nscan_iter_keeps_chsh_sign01. Qed.
Lemma nouter_step_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (nouter_step c) = hw_chsh_sign10 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_sign10. apply nscan_iter_keeps_chsh_sign10. Qed.
Lemma nouter_step_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (nouter_step c) = hw_chsh_sign11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_sign11. apply nscan_iter_keeps_chsh_sign11. Qed.
Lemma nouter_step_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (nouter_step c) = hw_chsh_n00sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n00sq. apply nscan_iter_keeps_chsh_n00sq. Qed.
Lemma nouter_step_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (nouter_step c) = hw_chsh_n01sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n01sq. apply nscan_iter_keeps_chsh_n01sq. Qed.
Lemma nouter_step_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (nouter_step c) = hw_chsh_n10sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n10sq. apply nscan_iter_keeps_chsh_n10sq. Qed.
Lemma nouter_step_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (nouter_step c) = hw_chsh_n11sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n11sq. apply nscan_iter_keeps_chsh_n11sq. Qed.
Lemma nouter_step_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (nouter_step c) = hw_chsh_d00sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d00sq. apply nscan_iter_keeps_chsh_d00sq. Qed.
Lemma nouter_step_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (nouter_step c) = hw_chsh_d01sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d01sq. apply nscan_iter_keeps_chsh_d01sq. Qed.
Lemma nouter_step_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (nouter_step c) = hw_chsh_d10sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d10sq. apply nscan_iter_keeps_chsh_d10sq. Qed.
Lemma nouter_step_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (nouter_step c) = hw_chsh_d11sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d11sq. apply nscan_iter_keeps_chsh_d11sq. Qed.
Lemma nouter_step_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (nouter_step c) = hw_chsh_A_pos c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_A_pos. apply nscan_iter_keeps_chsh_A_pos. Qed.
Lemma nouter_step_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (nouter_step c) = hw_chsh_A_neg_a c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_A_neg_a. apply nscan_iter_keeps_chsh_A_neg_a. Qed.
Lemma nouter_step_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (nouter_step c) = hw_chsh_A_neg_b c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_A_neg_b. apply nscan_iter_keeps_chsh_A_neg_b. Qed.
Lemma nouter_step_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (nouter_step c) = hw_chsh_B_pos c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_B_pos. apply nscan_iter_keeps_chsh_B_pos. Qed.
Lemma nouter_step_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (nouter_step c) = hw_chsh_B_neg_a c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_B_neg_a. apply nscan_iter_keeps_chsh_B_neg_a. Qed.
Lemma nouter_step_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (nouter_step c) = hw_chsh_B_neg_b c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_B_neg_b. apply nscan_iter_keeps_chsh_B_neg_b. Qed.
Lemma nouter_step_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (nouter_step c) = hw_chsh_d00d01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d00d01. apply nscan_iter_keeps_chsh_d00d01. Qed.
Lemma nouter_step_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (nouter_step c) = hw_chsh_n10n11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n10n11. apply nscan_iter_keeps_chsh_n10n11. Qed.
Lemma nouter_step_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (nouter_step c) = hw_chsh_d10d11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_d10d11. apply nscan_iter_keeps_chsh_d10d11. Qed.
Lemma nouter_step_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (nouter_step c) = hw_chsh_n00n01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_n00n01. apply nscan_iter_keeps_chsh_n00n01. Qed.
Lemma nouter_step_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (nouter_step c) = hw_chsh_abs_C1 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_abs_C1. apply nscan_iter_keeps_chsh_abs_C1. Qed.
Lemma nouter_step_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (nouter_step c) = hw_chsh_abs_C2 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_abs_C2. apply nscan_iter_keeps_chsh_abs_C2. Qed.
Lemma nouter_step_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (nouter_step c) = hw_chsh_C_sq c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_C_sq. apply nscan_iter_keeps_chsh_C_sq. Qed.
Lemma nouter_step_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (nouter_step c) = hw_chsh_A_times_B c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_A_times_B. apply nscan_iter_keeps_chsh_A_times_B. Qed.
Lemma nouter_step_keeps_chsh_check_result : forall c, hw_chsh_check_result (nouter_step c) = hw_chsh_check_result c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_chsh_check_result. apply nscan_iter_keeps_chsh_check_result. Qed.
Lemma nouter_step_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (nouter_step c) = hw_bus_load_instr_addr c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_bus_load_instr_addr. apply nscan_iter_keeps_bus_load_instr_addr. Qed.
Lemma nouter_step_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (nouter_step c) = hw_bus_load_instr_data c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_bus_load_instr_data. apply nscan_iter_keeps_bus_load_instr_data. Qed.
Lemma nouter_step_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (nouter_step c) = hw_bus_load_instr_kick c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_bus_load_instr_kick. apply nscan_iter_keeps_bus_load_instr_kick. Qed.
Lemma nouter_step_keeps_mu_tensor : forall c, hw_mu_tensor (nouter_step c) = hw_mu_tensor c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mu_tensor. apply nscan_iter_keeps_mu_tensor. Qed.
Lemma nouter_step_keeps_module_tensors : forall c, hw_module_tensors (nouter_step c) = hw_module_tensors c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_module_tensors. apply nscan_iter_keeps_module_tensors. Qed.
Lemma nouter_step_keeps_csr_status : forall c, hw_csr_status (nouter_step c) = hw_csr_status c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_csr_status. apply nscan_iter_keeps_csr_status. Qed.
Lemma nouter_step_keeps_csr_heap_base : forall c, hw_csr_heap_base (nouter_step c) = hw_csr_heap_base c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_csr_heap_base. apply nscan_iter_keeps_csr_heap_base. Qed.
Lemma nouter_step_keeps_ptTable : forall c, hw_ptTable (nouter_step c) = hw_ptTable c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_ptTable. apply nscan_iter_keeps_ptTable. Qed.
Lemma nouter_step_keeps_pt_next_id : forall c, hw_pt_next_id (nouter_step c) = hw_pt_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_pt_next_id. apply nscan_iter_keeps_pt_next_id. Qed.
Lemma nouter_step_keeps_morph_src_table : forall c, hw_morph_src_table (nouter_step c) = hw_morph_src_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_morph_src_table. apply nscan_iter_keeps_morph_src_table. Qed.
Lemma nouter_step_keeps_morph_dst_table : forall c, hw_morph_dst_table (nouter_step c) = hw_morph_dst_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_morph_dst_table. apply nscan_iter_keeps_morph_dst_table. Qed.
Lemma nouter_step_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (nouter_step c) = hw_morph_coupling_desc_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_morph_coupling_desc_table. apply nscan_iter_keeps_morph_coupling_desc_table. Qed.
Lemma nouter_step_keeps_morph_valid_table : forall c, hw_morph_valid_table (nouter_step c) = hw_morph_valid_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_morph_valid_table. apply nscan_iter_keeps_morph_valid_table. Qed.
Lemma nouter_step_keeps_morph_identity_table : forall c, hw_morph_identity_table (nouter_step c) = hw_morph_identity_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_morph_identity_table. apply nscan_iter_keeps_morph_identity_table. Qed.
Lemma nouter_step_keeps_morph_next_id : forall c, hw_morph_next_id (nouter_step c) = hw_morph_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_morph_next_id. apply nscan_iter_keeps_morph_next_id. Qed.
Lemma nouter_step_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (nouter_step c) = hw_coupling_desc_base_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_desc_base_table. apply nscan_iter_keeps_coupling_desc_base_table. Qed.
Lemma nouter_step_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (nouter_step c) = hw_coupling_desc_count_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_desc_count_table. apply nscan_iter_keeps_coupling_desc_count_table. Qed.
Lemma nouter_step_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (nouter_step c) = hw_coupling_desc_valid_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_desc_valid_table. apply nscan_iter_keeps_coupling_desc_valid_table. Qed.
Lemma nouter_step_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (nouter_step c) = hw_coupling_desc_label_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_desc_label_table. apply nscan_iter_keeps_coupling_desc_label_table. Qed.
Lemma nouter_step_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (nouter_step c) = hw_coupling_desc_label_len_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_desc_label_len_table. apply nscan_iter_keeps_coupling_desc_label_len_table. Qed.
Lemma nouter_step_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (nouter_step c) = hw_coupling_desc_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_desc_next_id. apply nscan_iter_keeps_coupling_desc_next_id. Qed.
Lemma nouter_step_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (nouter_step c) = hw_coupling_pair_valid_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_pair_valid_table. apply nscan_iter_keeps_coupling_pair_valid_table. Qed.
Lemma nouter_step_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (nouter_step c) = hw_coupling_pair_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_coupling_pair_next_id. apply nscan_iter_keeps_coupling_pair_next_id. Qed.
Lemma nouter_step_keeps_mc_op : forall c, hw_mc_op (nouter_step c) = hw_mc_op c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_op. apply nscan_iter_keeps_mc_op. Qed.
Lemma nouter_step_keeps_mc_mem_base : forall c, hw_mc_mem_base (nouter_step c) = hw_mc_mem_base c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_mem_base. apply nscan_iter_keeps_mc_mem_base. Qed.
Lemma nouter_step_keeps_mc_pair_count : forall c, hw_mc_pair_count (nouter_step c) = hw_mc_pair_count c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_pair_count. apply nscan_iter_keeps_mc_pair_count. Qed.
Lemma nouter_step_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (nouter_step c) = hw_mc_read_ptr c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_read_ptr. apply nscan_iter_keeps_mc_read_ptr. Qed.
Lemma nouter_step_keeps_mc_src1_base : forall c, hw_mc_src1_base (nouter_step c) = hw_mc_src1_base c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_src1_base. apply nscan_iter_keeps_mc_src1_base. Qed.
Lemma nouter_step_keeps_mc_src1_count : forall c, hw_mc_src1_count (nouter_step c) = hw_mc_src1_count c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_src1_count. apply nscan_iter_keeps_mc_src1_count. Qed.
Lemma nouter_step_keeps_mc_src2_base : forall c, hw_mc_src2_base (nouter_step c) = hw_mc_src2_base c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_src2_base. apply nscan_iter_keeps_mc_src2_base. Qed.
Lemma nouter_step_keeps_mc_src2_count : forall c, hw_mc_src2_count (nouter_step c) = hw_mc_src2_count c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_src2_count. apply nscan_iter_keeps_mc_src2_count. Qed.
Lemma nouter_step_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (nouter_step c) = hw_mc_is_id1 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_is_id1. apply nscan_iter_keeps_mc_is_id1. Qed.
Lemma nouter_step_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (nouter_step c) = hw_mc_is_id2 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_is_id2. apply nscan_iter_keeps_mc_is_id2. Qed.
Lemma nouter_step_keeps_mc_write_base : forall c, hw_mc_write_base (nouter_step c) = hw_mc_write_base c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_write_base. apply nscan_iter_keeps_mc_write_base. Qed.
Lemma nouter_step_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (nouter_step c) = hw_mc_dst_reg c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_dst_reg. apply nscan_iter_keeps_mc_dst_reg. Qed.
Lemma nouter_step_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (nouter_step c) = hw_mc_morph_slot c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_morph_slot. apply nscan_iter_keeps_mc_morph_slot. Qed.
Lemma nouter_step_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (nouter_step c) = hw_mc_new_src_mod c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_new_src_mod. apply nscan_iter_keeps_mc_new_src_mod. Qed.
Lemma nouter_step_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (nouter_step c) = hw_mc_new_dst_mod c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_new_dst_mod. apply nscan_iter_keeps_mc_new_dst_mod. Qed.
Lemma nouter_step_keeps_mc_cost : forall c, hw_mc_cost (nouter_step c) = hw_mc_cost c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_mc_cost. apply nscan_iter_keeps_mc_cost. Qed.
Lemma nouter_step_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (nouter_step c) = hw_formula_desc_base_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_formula_desc_base_table. apply nscan_iter_keeps_formula_desc_base_table. Qed.
Lemma nouter_step_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (nouter_step c) = hw_formula_desc_count_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_formula_desc_count_table. apply nscan_iter_keeps_formula_desc_count_table. Qed.
Lemma nouter_step_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (nouter_step c) = hw_formula_desc_valid_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_formula_desc_valid_table. apply nscan_iter_keeps_formula_desc_valid_table. Qed.
Lemma nouter_step_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (nouter_step c) = hw_formula_desc_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_formula_desc_next_id. apply nscan_iter_keeps_formula_desc_next_id. Qed.
Lemma nouter_step_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (nouter_step c) = hw_cert_desc_base_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_cert_desc_base_table. apply nscan_iter_keeps_cert_desc_base_table. Qed.
Lemma nouter_step_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (nouter_step c) = hw_cert_desc_count_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_cert_desc_count_table. apply nscan_iter_keeps_cert_desc_count_table. Qed.
Lemma nouter_step_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (nouter_step c) = hw_cert_desc_valid_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_cert_desc_valid_table. apply nscan_iter_keeps_cert_desc_valid_table. Qed.
Lemma nouter_step_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (nouter_step c) = hw_cert_desc_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_cert_desc_next_id. apply nscan_iter_keeps_cert_desc_next_id. Qed.
Lemma nouter_step_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (nouter_step c) = hw_desc_meta_subtype_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_desc_meta_subtype_table. apply nscan_iter_keeps_desc_meta_subtype_table. Qed.
Lemma nouter_step_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (nouter_step c) = hw_desc_meta_kind_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_desc_meta_kind_table. apply nscan_iter_keeps_desc_meta_kind_table. Qed.
Lemma nouter_step_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (nouter_step c) = hw_desc_meta_inline_len_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_desc_meta_inline_len_table. apply nscan_iter_keeps_desc_meta_inline_len_table. Qed.
Lemma nouter_step_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (nouter_step c) = hw_desc_meta_aux_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_desc_meta_aux_table. apply nscan_iter_keeps_desc_meta_aux_table. Qed.
Lemma nouter_step_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (nouter_step c) = hw_desc_meta_valid_table c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_desc_meta_valid_table. apply nscan_iter_keeps_desc_meta_valid_table. Qed.
Lemma nouter_step_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (nouter_step c) = hw_desc_meta_next_id c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_desc_meta_next_id. apply nscan_iter_keeps_desc_meta_next_id. Qed.
Lemma nouter_step_keeps_wc_same_00 : forall c, hw_wc_same_00 (nouter_step c) = hw_wc_same_00 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_same_00. apply nscan_iter_keeps_wc_same_00. Qed.
Lemma nouter_step_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (nouter_step c) = hw_wc_diff_00 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_diff_00. apply nscan_iter_keeps_wc_diff_00. Qed.
Lemma nouter_step_keeps_wc_same_01 : forall c, hw_wc_same_01 (nouter_step c) = hw_wc_same_01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_same_01. apply nscan_iter_keeps_wc_same_01. Qed.
Lemma nouter_step_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (nouter_step c) = hw_wc_diff_01 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_diff_01. apply nscan_iter_keeps_wc_diff_01. Qed.
Lemma nouter_step_keeps_wc_same_10 : forall c, hw_wc_same_10 (nouter_step c) = hw_wc_same_10 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_same_10. apply nscan_iter_keeps_wc_same_10. Qed.
Lemma nouter_step_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (nouter_step c) = hw_wc_diff_10 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_diff_10. apply nscan_iter_keeps_wc_diff_10. Qed.
Lemma nouter_step_keeps_wc_same_11 : forall c, hw_wc_same_11 (nouter_step c) = hw_wc_same_11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_same_11. apply nscan_iter_keeps_wc_same_11. Qed.
Lemma nouter_step_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (nouter_step c) = hw_wc_diff_11 c.
Proof. intro c. unfold nouter_step. rewrite mcnemit_keeps_wc_diff_11. apply nscan_iter_keeps_wc_diff_11. Qed.

Fixpoint nouter_iter (n : nat) (c : HWB) : HWB :=
  match n with
  | O => c
  | S m => nouter_iter m (nouter_step c)
  end.

Lemma nouter_iter_keeps_pc : forall n c, hw_pc (nouter_iter n c) = hw_pc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_pc]. Qed.
Lemma nouter_iter_keeps_mu : forall n c, hw_mu (nouter_iter n c) = hw_mu c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mu]. Qed.
Lemma nouter_iter_keeps_err : forall n c, hw_err (nouter_iter n c) = hw_err c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_err]. Qed.
Lemma nouter_iter_keeps_halted : forall n c, hw_halted (nouter_iter n c) = hw_halted c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_halted]. Qed.
Lemma nouter_iter_keeps_regs : forall n c, hw_regs (nouter_iter n c) = hw_regs c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_regs]. Qed.
Lemma nouter_iter_keeps_mem : forall n c, hw_mem (nouter_iter n c) = hw_mem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mem]. Qed.
Lemma nouter_iter_keeps_imem : forall n c, hw_imem (nouter_iter n c) = hw_imem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_imem]. Qed.
Lemma nouter_iter_keeps_partition_ops : forall n c, hw_partition_ops (nouter_iter n c) = hw_partition_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_partition_ops]. Qed.
Lemma nouter_iter_keeps_mdl_ops : forall n c, hw_mdl_ops (nouter_iter n c) = hw_mdl_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mdl_ops]. Qed.
Lemma nouter_iter_keeps_info_gain : forall n c, hw_info_gain (nouter_iter n c) = hw_info_gain c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_info_gain]. Qed.
Lemma nouter_iter_keeps_error_code : forall n c, hw_error_code (nouter_iter n c) = hw_error_code c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_error_code]. Qed.
Lemma nouter_iter_keeps_logic_acc : forall n c, hw_logic_acc (nouter_iter n c) = hw_logic_acc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_logic_acc]. Qed.
Lemma nouter_iter_keeps_cert_addr : forall n c, hw_cert_addr (nouter_iter n c) = hw_cert_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_cert_addr]. Qed.
Lemma nouter_iter_keeps_active_module : forall n c, hw_active_module (nouter_iter n c) = hw_active_module c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_active_module]. Qed.
Lemma nouter_iter_keeps_mstatus : forall n c, hw_mstatus (nouter_iter n c) = hw_mstatus c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mstatus]. Qed.
Lemma nouter_iter_keeps_mcycle_lo : forall n c, hw_mcycle_lo (nouter_iter n c) = hw_mcycle_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mcycle_lo]. Qed.
Lemma nouter_iter_keeps_mcycle_hi : forall n c, hw_mcycle_hi (nouter_iter n c) = hw_mcycle_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mcycle_hi]. Qed.
Lemma nouter_iter_keeps_minstret_lo : forall n c, hw_minstret_lo (nouter_iter n c) = hw_minstret_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_minstret_lo]. Qed.
Lemma nouter_iter_keeps_minstret_hi : forall n c, hw_minstret_hi (nouter_iter n c) = hw_minstret_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_minstret_hi]. Qed.
Lemma nouter_iter_keeps_trap_vector : forall n c, hw_trap_vector (nouter_iter n c) = hw_trap_vector c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_trap_vector]. Qed.
Lemma nouter_iter_keeps_certified : forall n c, hw_certified (nouter_iter n c) = hw_certified c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_certified]. Qed.
Lemma nouter_iter_keeps_lassert_phase : forall n c, hw_lassert_phase (nouter_iter n c) = hw_lassert_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_phase]. Qed.
Lemma nouter_iter_keeps_lassert_kind : forall n c, hw_lassert_kind (nouter_iter n c) = hw_lassert_kind c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_kind]. Qed.
Lemma nouter_iter_keeps_lassert_fbase : forall n c, hw_lassert_fbase (nouter_iter n c) = hw_lassert_fbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_fbase]. Qed.
Lemma nouter_iter_keeps_lassert_cbase : forall n c, hw_lassert_cbase (nouter_iter n c) = hw_lassert_cbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_cbase]. Qed.
Lemma nouter_iter_keeps_lassert_flen : forall n c, hw_lassert_flen (nouter_iter n c) = hw_lassert_flen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_flen]. Qed.
Lemma nouter_iter_keeps_lassert_clen : forall n c, hw_lassert_clen (nouter_iter n c) = hw_lassert_clen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_clen]. Qed.
Lemma nouter_iter_keeps_lassert_nvars : forall n c, hw_lassert_nvars (nouter_iter n c) = hw_lassert_nvars c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_nvars]. Qed.
Lemma nouter_iter_keeps_lassert_fptr : forall n c, hw_lassert_fptr (nouter_iter n c) = hw_lassert_fptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_fptr]. Qed.
Lemma nouter_iter_keeps_lassert_cptr : forall n c, hw_lassert_cptr (nouter_iter n c) = hw_lassert_cptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_cptr]. Qed.
Lemma nouter_iter_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (nouter_iter n c) = hw_lassert_fbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_fbuf]. Qed.
Lemma nouter_iter_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (nouter_iter n c) = hw_lassert_cbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_cbuf]. Qed.
Lemma nouter_iter_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (nouter_iter n c) = hw_lassert_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_clause_sat]. Qed.
Lemma nouter_iter_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (nouter_iter n c) = hw_lassert_counter_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_counter_clause_sat]. Qed.
Lemma nouter_iter_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (nouter_iter n c) = hw_lassert_counter_seen_fail c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_lassert_counter_seen_fail]. Qed.
Lemma nouter_iter_keeps_chsh_phase : forall n c, hw_chsh_phase (nouter_iter n c) = hw_chsh_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_phase]. Qed.
Lemma nouter_iter_keeps_chsh_n00 : forall n c, hw_chsh_n00 (nouter_iter n c) = hw_chsh_n00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n00]. Qed.
Lemma nouter_iter_keeps_chsh_n01 : forall n c, hw_chsh_n01 (nouter_iter n c) = hw_chsh_n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n01]. Qed.
Lemma nouter_iter_keeps_chsh_n10 : forall n c, hw_chsh_n10 (nouter_iter n c) = hw_chsh_n10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n10]. Qed.
Lemma nouter_iter_keeps_chsh_n11 : forall n c, hw_chsh_n11 (nouter_iter n c) = hw_chsh_n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n11]. Qed.
Lemma nouter_iter_keeps_chsh_d00 : forall n c, hw_chsh_d00 (nouter_iter n c) = hw_chsh_d00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d00]. Qed.
Lemma nouter_iter_keeps_chsh_d01 : forall n c, hw_chsh_d01 (nouter_iter n c) = hw_chsh_d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d01]. Qed.
Lemma nouter_iter_keeps_chsh_d10 : forall n c, hw_chsh_d10 (nouter_iter n c) = hw_chsh_d10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d10]. Qed.
Lemma nouter_iter_keeps_chsh_d11 : forall n c, hw_chsh_d11 (nouter_iter n c) = hw_chsh_d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d11]. Qed.
Lemma nouter_iter_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (nouter_iter n c) = hw_chsh_sign00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_sign00]. Qed.
Lemma nouter_iter_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (nouter_iter n c) = hw_chsh_sign01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_sign01]. Qed.
Lemma nouter_iter_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (nouter_iter n c) = hw_chsh_sign10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_sign10]. Qed.
Lemma nouter_iter_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (nouter_iter n c) = hw_chsh_sign11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_sign11]. Qed.
Lemma nouter_iter_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (nouter_iter n c) = hw_chsh_n00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n00sq]. Qed.
Lemma nouter_iter_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (nouter_iter n c) = hw_chsh_n01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n01sq]. Qed.
Lemma nouter_iter_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (nouter_iter n c) = hw_chsh_n10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n10sq]. Qed.
Lemma nouter_iter_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (nouter_iter n c) = hw_chsh_n11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n11sq]. Qed.
Lemma nouter_iter_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (nouter_iter n c) = hw_chsh_d00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d00sq]. Qed.
Lemma nouter_iter_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (nouter_iter n c) = hw_chsh_d01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d01sq]. Qed.
Lemma nouter_iter_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (nouter_iter n c) = hw_chsh_d10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d10sq]. Qed.
Lemma nouter_iter_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (nouter_iter n c) = hw_chsh_d11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d11sq]. Qed.
Lemma nouter_iter_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (nouter_iter n c) = hw_chsh_A_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_A_pos]. Qed.
Lemma nouter_iter_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (nouter_iter n c) = hw_chsh_A_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_A_neg_a]. Qed.
Lemma nouter_iter_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (nouter_iter n c) = hw_chsh_A_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_A_neg_b]. Qed.
Lemma nouter_iter_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (nouter_iter n c) = hw_chsh_B_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_B_pos]. Qed.
Lemma nouter_iter_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (nouter_iter n c) = hw_chsh_B_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_B_neg_a]. Qed.
Lemma nouter_iter_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (nouter_iter n c) = hw_chsh_B_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_B_neg_b]. Qed.
Lemma nouter_iter_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (nouter_iter n c) = hw_chsh_d00d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d00d01]. Qed.
Lemma nouter_iter_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (nouter_iter n c) = hw_chsh_n10n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n10n11]. Qed.
Lemma nouter_iter_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (nouter_iter n c) = hw_chsh_d10d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_d10d11]. Qed.
Lemma nouter_iter_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (nouter_iter n c) = hw_chsh_n00n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_n00n01]. Qed.
Lemma nouter_iter_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (nouter_iter n c) = hw_chsh_abs_C1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_abs_C1]. Qed.
Lemma nouter_iter_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (nouter_iter n c) = hw_chsh_abs_C2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_abs_C2]. Qed.
Lemma nouter_iter_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (nouter_iter n c) = hw_chsh_C_sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_C_sq]. Qed.
Lemma nouter_iter_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (nouter_iter n c) = hw_chsh_A_times_B c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_A_times_B]. Qed.
Lemma nouter_iter_keeps_chsh_check_result : forall n c, hw_chsh_check_result (nouter_iter n c) = hw_chsh_check_result c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_chsh_check_result]. Qed.
Lemma nouter_iter_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (nouter_iter n c) = hw_bus_load_instr_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_bus_load_instr_addr]. Qed.
Lemma nouter_iter_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (nouter_iter n c) = hw_bus_load_instr_data c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_bus_load_instr_data]. Qed.
Lemma nouter_iter_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (nouter_iter n c) = hw_bus_load_instr_kick c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_bus_load_instr_kick]. Qed.
Lemma nouter_iter_keeps_mu_tensor : forall n c, hw_mu_tensor (nouter_iter n c) = hw_mu_tensor c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mu_tensor]. Qed.
Lemma nouter_iter_keeps_module_tensors : forall n c, hw_module_tensors (nouter_iter n c) = hw_module_tensors c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_module_tensors]. Qed.
Lemma nouter_iter_keeps_csr_status : forall n c, hw_csr_status (nouter_iter n c) = hw_csr_status c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_csr_status]. Qed.
Lemma nouter_iter_keeps_csr_heap_base : forall n c, hw_csr_heap_base (nouter_iter n c) = hw_csr_heap_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_csr_heap_base]. Qed.
Lemma nouter_iter_keeps_ptTable : forall n c, hw_ptTable (nouter_iter n c) = hw_ptTable c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_ptTable]. Qed.
Lemma nouter_iter_keeps_pt_next_id : forall n c, hw_pt_next_id (nouter_iter n c) = hw_pt_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_pt_next_id]. Qed.
Lemma nouter_iter_keeps_morph_src_table : forall n c, hw_morph_src_table (nouter_iter n c) = hw_morph_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_morph_src_table]. Qed.
Lemma nouter_iter_keeps_morph_dst_table : forall n c, hw_morph_dst_table (nouter_iter n c) = hw_morph_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_morph_dst_table]. Qed.
Lemma nouter_iter_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (nouter_iter n c) = hw_morph_coupling_desc_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_morph_coupling_desc_table]. Qed.
Lemma nouter_iter_keeps_morph_valid_table : forall n c, hw_morph_valid_table (nouter_iter n c) = hw_morph_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_morph_valid_table]. Qed.
Lemma nouter_iter_keeps_morph_identity_table : forall n c, hw_morph_identity_table (nouter_iter n c) = hw_morph_identity_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_morph_identity_table]. Qed.
Lemma nouter_iter_keeps_morph_next_id : forall n c, hw_morph_next_id (nouter_iter n c) = hw_morph_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_morph_next_id]. Qed.
Lemma nouter_iter_keeps_coupling_desc_base_table : forall n c, hw_coupling_desc_base_table (nouter_iter n c) = hw_coupling_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_desc_base_table]. Qed.
Lemma nouter_iter_keeps_coupling_desc_count_table : forall n c, hw_coupling_desc_count_table (nouter_iter n c) = hw_coupling_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_desc_count_table]. Qed.
Lemma nouter_iter_keeps_coupling_desc_valid_table : forall n c, hw_coupling_desc_valid_table (nouter_iter n c) = hw_coupling_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_desc_valid_table]. Qed.
Lemma nouter_iter_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (nouter_iter n c) = hw_coupling_desc_label_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_desc_label_table]. Qed.
Lemma nouter_iter_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (nouter_iter n c) = hw_coupling_desc_label_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_desc_label_len_table]. Qed.
Lemma nouter_iter_keeps_coupling_desc_next_id : forall n c, hw_coupling_desc_next_id (nouter_iter n c) = hw_coupling_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_desc_next_id]. Qed.
Lemma nouter_iter_keeps_coupling_pair_valid_table : forall n c, hw_coupling_pair_valid_table (nouter_iter n c) = hw_coupling_pair_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_pair_valid_table]. Qed.
Lemma nouter_iter_keeps_coupling_pair_next_id : forall n c, hw_coupling_pair_next_id (nouter_iter n c) = hw_coupling_pair_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_coupling_pair_next_id]. Qed.
Lemma nouter_iter_keeps_mc_op : forall n c, hw_mc_op (nouter_iter n c) = hw_mc_op c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_op]. Qed.
Lemma nouter_iter_keeps_mc_mem_base : forall n c, hw_mc_mem_base (nouter_iter n c) = hw_mc_mem_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_mem_base]. Qed.
Lemma nouter_iter_keeps_mc_pair_count : forall n c, hw_mc_pair_count (nouter_iter n c) = hw_mc_pair_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_pair_count]. Qed.
Lemma nouter_iter_keeps_mc_read_ptr : forall n c, hw_mc_read_ptr (nouter_iter n c) = hw_mc_read_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_read_ptr]. Qed.
Lemma nouter_iter_keeps_mc_src1_base : forall n c, hw_mc_src1_base (nouter_iter n c) = hw_mc_src1_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_src1_base]. Qed.
Lemma nouter_iter_keeps_mc_src1_count : forall n c, hw_mc_src1_count (nouter_iter n c) = hw_mc_src1_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_src1_count]. Qed.
Lemma nouter_iter_keeps_mc_src2_base : forall n c, hw_mc_src2_base (nouter_iter n c) = hw_mc_src2_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_src2_base]. Qed.
Lemma nouter_iter_keeps_mc_src2_count : forall n c, hw_mc_src2_count (nouter_iter n c) = hw_mc_src2_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_src2_count]. Qed.
Lemma nouter_iter_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (nouter_iter n c) = hw_mc_is_id1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_is_id1]. Qed.
Lemma nouter_iter_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (nouter_iter n c) = hw_mc_is_id2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_is_id2]. Qed.
Lemma nouter_iter_keeps_mc_write_base : forall n c, hw_mc_write_base (nouter_iter n c) = hw_mc_write_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_write_base]. Qed.
Lemma nouter_iter_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (nouter_iter n c) = hw_mc_dst_reg c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_dst_reg]. Qed.
Lemma nouter_iter_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (nouter_iter n c) = hw_mc_morph_slot c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_morph_slot]. Qed.
Lemma nouter_iter_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (nouter_iter n c) = hw_mc_new_src_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_new_src_mod]. Qed.
Lemma nouter_iter_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (nouter_iter n c) = hw_mc_new_dst_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_new_dst_mod]. Qed.
Lemma nouter_iter_keeps_mc_cost : forall n c, hw_mc_cost (nouter_iter n c) = hw_mc_cost c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_mc_cost]. Qed.
Lemma nouter_iter_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (nouter_iter n c) = hw_formula_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_formula_desc_base_table]. Qed.
Lemma nouter_iter_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (nouter_iter n c) = hw_formula_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_formula_desc_count_table]. Qed.
Lemma nouter_iter_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (nouter_iter n c) = hw_formula_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_formula_desc_valid_table]. Qed.
Lemma nouter_iter_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (nouter_iter n c) = hw_formula_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_formula_desc_next_id]. Qed.
Lemma nouter_iter_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (nouter_iter n c) = hw_cert_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_cert_desc_base_table]. Qed.
Lemma nouter_iter_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (nouter_iter n c) = hw_cert_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_cert_desc_count_table]. Qed.
Lemma nouter_iter_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (nouter_iter n c) = hw_cert_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_cert_desc_valid_table]. Qed.
Lemma nouter_iter_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (nouter_iter n c) = hw_cert_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_cert_desc_next_id]. Qed.
Lemma nouter_iter_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (nouter_iter n c) = hw_desc_meta_subtype_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_desc_meta_subtype_table]. Qed.
Lemma nouter_iter_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (nouter_iter n c) = hw_desc_meta_kind_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_desc_meta_kind_table]. Qed.
Lemma nouter_iter_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (nouter_iter n c) = hw_desc_meta_inline_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_desc_meta_inline_len_table]. Qed.
Lemma nouter_iter_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (nouter_iter n c) = hw_desc_meta_aux_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_desc_meta_aux_table]. Qed.
Lemma nouter_iter_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (nouter_iter n c) = hw_desc_meta_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_desc_meta_valid_table]. Qed.
Lemma nouter_iter_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (nouter_iter n c) = hw_desc_meta_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_desc_meta_next_id]. Qed.
Lemma nouter_iter_keeps_wc_same_00 : forall n c, hw_wc_same_00 (nouter_iter n c) = hw_wc_same_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_same_00]. Qed.
Lemma nouter_iter_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (nouter_iter n c) = hw_wc_diff_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_diff_00]. Qed.
Lemma nouter_iter_keeps_wc_same_01 : forall n c, hw_wc_same_01 (nouter_iter n c) = hw_wc_same_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_same_01]. Qed.
Lemma nouter_iter_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (nouter_iter n c) = hw_wc_diff_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_diff_01]. Qed.
Lemma nouter_iter_keeps_wc_same_10 : forall n c, hw_wc_same_10 (nouter_iter n c) = hw_wc_same_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_same_10]. Qed.
Lemma nouter_iter_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (nouter_iter n c) = hw_wc_diff_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_diff_10]. Qed.
Lemma nouter_iter_keeps_wc_same_11 : forall n c, hw_wc_same_11 (nouter_iter n c) = hw_wc_same_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_same_11]. Qed.
Lemma nouter_iter_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (nouter_iter n c) = hw_wc_diff_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [nouter_iter]; rewrite IH; apply nouter_step_keeps_wc_diff_11]. Qed.

Theorem nouter_run : forall rem c rawsrc rawdst src dst b i out e,
  e - i = rem -> i < e ->
  normalization_prefix_invariant rawsrc rawdst src dst b i out e ->
  hw_mc_phase c = natToWord 4 8 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 (S i) ->
  hw_mc_write_ptr c = natToWord 5 e -> hw_mc_duplicate c = false -> hw_mc_norm_ptr c = natToWord 5 out ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  exists labels src' dst' out',
    Multistep thieleCore (hwb_regs c) (hwb_regs (nouter_iter rem c)) labels /\
    normalization_prefix_invariant rawsrc rawdst src' dst' b e out' e /\
    hw_mc_phase (nouter_iter rem c) = natToWord 4 11 /\
    hw_mc_write_ptr (nouter_iter rem c) = natToWord 5 out' /\
    hw_coupling_pair_src_table (nouter_iter rem c) = src' /\
    hw_coupling_pair_dst_table (nouter_iter rem c) = dst'.
Proof.
  induction rem as [|n IH]; intros c rawsrc rawdst src dst b i out e Hn Hi Hinv Hp Hic Hj Hw Hd Ho Hs Ht; [lia|].
  pose proof Hinv as [Hb _].
  destruct (nouter_step_facts c src dst i out e Hi ltac:(lia) Hp Hic Hj Hw Hd Ho Hs Ht)
    as [Hex [Pp [Pi [Pj [Pw [Pd [Po [Ps Pt]]]]]]]].
  pose proof (normalization_prefix_preserved rawsrc rawdst src dst b i out e Hinv Hi) as Hinv1.
  cbv zeta in Hinv1, Pw, Po, Ps, Pt.
  cbn [nouter_iter].
  destruct (Nat.eq_dec (S i) e) as [E|E].
  - assert (n = 0) by lia. subst n. cbn [nouter_iter].
    rewrite (proj2 (Nat.eqb_eq _ _) E) in Pp, Pw.
    eexists; exists (emitted_table src i out (scan_seen src dst i (S i) (e - S i))),
      (emitted_table dst i out (scan_seen src dst i (S i) (e - S i))),
      (next_output out (scan_seen src dst i (S i) (e - S i))).
    split; [exact Hex|].
    split; [set (d := scan_seen src dst i (S i) (e - S i)) in Hinv1 |- *; clearbody d; rewrite E in Hinv1; exact Hinv1|].
    split; [exact Pp|]. split; [exact Pw|]. split; [exact Ps|exact Pt].
  - rewrite (proj2 (Nat.eqb_neq _ _) E) in Pp, Pw.
    destruct (IH (nouter_step c) rawsrc rawdst _ _ b (S i) _ e ltac:(lia) ltac:(lia) Hinv1
      Pp Pi Pj Pw Pd Po Ps Pt) as [ls [src' [dst' [out' [Hrun [Hinv' [Fp [Fw [Fs Ft]]]]]]]]].
    exists (ls ++ ([normalization_label "mc_normalize_emit"] ++ repeat (normalization_label "mc_normalize_scan") (e - i))),
      src', dst', out'.
    split; [eapply normalization_multistep_trans; eassumption|].
    split; [exact Hinv'|]. split; [exact Fp|]. split; [exact Fw|]. split; [exact Fs|exact Ft].
Qed.
