(** CouplingFsmLoad.v: the MORPH loading loop at the typed boundary.
    [mload_loop] states the tables, pointers and phases after [n] firings of
    the loading rule; [mload_multistep] shows those firings are an actual Kami
    execution. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop MorphLoading RuleEnabled FsmDecoded ChshRetire.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma rule_in_index : forall n, n <= 11 -> In (normalization_rule n) (getRules thieleCore).
Proof.
  intros n Hn. rewrite cpu_rules_listed. apply in_map. cbn [In].
  assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11) by lia.
  intuition.
Qed.

(** * One firing of the loading rule *)

Lemma mcload_keeps_pc : forall c, hw_pc (mcload_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mu : forall c, hw_mu (mcload_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_err : forall c, hw_err (mcload_next c) = hw_err c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_halted : forall c, hw_halted (mcload_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_regs : forall c, hw_regs (mcload_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mem : forall c, hw_mem (mcload_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_imem : forall c, hw_imem (mcload_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_partition_ops : forall c, hw_partition_ops (mcload_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mdl_ops : forall c, hw_mdl_ops (mcload_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_info_gain : forall c, hw_info_gain (mcload_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_error_code : forall c, hw_error_code (mcload_next c) = hw_error_code c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_logic_acc : forall c, hw_logic_acc (mcload_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_cert_addr : forall c, hw_cert_addr (mcload_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_active_module : forall c, hw_active_module (mcload_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mstatus : forall c, hw_mstatus (mcload_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mcycle_lo : forall c, hw_mcycle_lo (mcload_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mcycle_hi : forall c, hw_mcycle_hi (mcload_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_minstret_lo : forall c, hw_minstret_lo (mcload_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_minstret_hi : forall c, hw_minstret_hi (mcload_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_trap_vector : forall c, hw_trap_vector (mcload_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_certified : forall c, hw_certified (mcload_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_phase : forall c, hw_lassert_phase (mcload_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_kind : forall c, hw_lassert_kind (mcload_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_fbase : forall c, hw_lassert_fbase (mcload_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_cbase : forall c, hw_lassert_cbase (mcload_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_flen : forall c, hw_lassert_flen (mcload_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_clen : forall c, hw_lassert_clen (mcload_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_nvars : forall c, hw_lassert_nvars (mcload_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_fptr : forall c, hw_lassert_fptr (mcload_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_cptr : forall c, hw_lassert_cptr (mcload_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mcload_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mcload_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mcload_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mcload_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mcload_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_phase : forall c, hw_chsh_phase (mcload_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n00 : forall c, hw_chsh_n00 (mcload_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n01 : forall c, hw_chsh_n01 (mcload_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n10 : forall c, hw_chsh_n10 (mcload_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n11 : forall c, hw_chsh_n11 (mcload_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d00 : forall c, hw_chsh_d00 (mcload_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d01 : forall c, hw_chsh_d01 (mcload_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d10 : forall c, hw_chsh_d10 (mcload_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d11 : forall c, hw_chsh_d11 (mcload_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mcload_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mcload_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mcload_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mcload_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mcload_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mcload_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mcload_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mcload_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mcload_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mcload_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mcload_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mcload_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mcload_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mcload_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mcload_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mcload_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mcload_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mcload_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mcload_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mcload_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mcload_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mcload_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mcload_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mcload_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mcload_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mcload_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_chsh_check_result : forall c, hw_chsh_check_result (mcload_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mcload_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mcload_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mcload_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mu_tensor : forall c, hw_mu_tensor (mcload_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_module_tensors : forall c, hw_module_tensors (mcload_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_csr_status : forall c, hw_csr_status (mcload_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_csr_heap_base : forall c, hw_csr_heap_base (mcload_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_ptTable : forall c, hw_ptTable (mcload_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_pt_next_id : forall c, hw_pt_next_id (mcload_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_morph_src_table : forall c, hw_morph_src_table (mcload_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_morph_dst_table : forall c, hw_morph_dst_table (mcload_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mcload_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_morph_valid_table : forall c, hw_morph_valid_table (mcload_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_morph_identity_table : forall c, hw_morph_identity_table (mcload_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_morph_next_id : forall c, hw_morph_next_id (mcload_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mcload_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mcload_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mcload_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mcload_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mcload_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mcload_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mcload_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_op : forall c, hw_mc_op (mcload_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_mem_base : forall c, hw_mc_mem_base (mcload_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_pair_count : forall c, hw_mc_pair_count (mcload_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_src1_base : forall c, hw_mc_src1_base (mcload_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_src1_count : forall c, hw_mc_src1_count (mcload_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_src2_base : forall c, hw_mc_src2_base (mcload_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_src2_count : forall c, hw_mc_src2_count (mcload_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_j : forall c, hw_mc_j (mcload_next c) = hw_mc_j c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mcload_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mcload_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_write_base : forall c, hw_mc_write_base (mcload_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (mcload_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_duplicate : forall c, hw_mc_duplicate (mcload_next c) = hw_mc_duplicate c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mcload_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mcload_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mcload_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mcload_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_mc_cost : forall c, hw_mc_cost (mcload_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mcload_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mcload_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mcload_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mcload_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mcload_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mcload_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mcload_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mcload_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mcload_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mcload_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mcload_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mcload_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mcload_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mcload_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_same_00 : forall c, hw_wc_same_00 (mcload_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mcload_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_same_01 : forall c, hw_wc_same_01 (mcload_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mcload_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_same_10 : forall c, hw_wc_same_10 (mcload_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mcload_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_same_11 : forall c, hw_wc_same_11 (mcload_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mcload_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mcload_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma mcload_src : forall c, hw_coupling_pair_src_table (mcload_next c) =
  put_vector (hw_coupling_pair_src_table c) (pair_index (hw_mc_write_ptr c)) (hw_mem c (mem_index (hw_mc_read_ptr c))).
Proof. reflexivity. Qed.
Lemma mcload_dst : forall c, hw_coupling_pair_dst_table (mcload_next c) =
  put_vector (hw_coupling_pair_dst_table c) (pair_index (hw_mc_write_ptr c))
    (hw_mem c (mem_index (wplus (hw_mc_read_ptr c) (natToWord 32 1)))).
Proof. reflexivity. Qed.
Lemma mcload_valid : forall c, hw_coupling_pair_valid_table (mcload_next c) =
  put_vector (hw_coupling_pair_valid_table c) (pair_index (hw_mc_write_ptr c)) true.
Proof. reflexivity. Qed.
Lemma mcload_read_ptr : forall c, hw_mc_read_ptr (mcload_next c) = wplus (hw_mc_read_ptr c) (natToWord 32 2).
Proof. reflexivity. Qed.
Lemma mcload_write_ptr : forall c, hw_mc_write_ptr (mcload_next c) = wplus (hw_mc_write_ptr c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcload_i : forall c, hw_mc_i (mcload_next c) = wplus (hw_mc_i c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcload_phase : forall c, hw_mc_phase (mcload_next c) =
  if weq (wplus (hw_mc_i c) (natToWord 5 1)) (hw_mc_pair_count c) then WO~0~1~0~1 else WO~0~0~1~0.
Proof.
  intro c. change (hw_mc_phase (mcload_next c)) with (if mcload_mc_last c then WO~0~1~0~1 else WO~0~0~1~0).
  change (mcload_mc_last c) with (if isEq (Bit 5) (wplus (hw_mc_i c) (natToWord 5 1)) (hw_mc_pair_count c) then true else false).
  destruct (isEq _ _ _) as [E|E]; destruct (weq _ _) as [E'|E']; congruence.
Qed.

(** * The loading loop *)

Fixpoint mload_iter (n : nat) (c : HWB) : HWB :=
  match n with
  | O => c
  | S m => mload_iter m (mcload_next c)
  end.

Fixpoint mload_labels (n : nat) : list LabelT :=
  match n with
  | O => nil
  | S m => mload_labels m ++ [normalization_label "mc_morph_loop"]
  end.

Lemma mload_iter_keeps_pc : forall n c, hw_pc (mload_iter n c) = hw_pc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mu : forall n c, hw_mu (mload_iter n c) = hw_mu c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_err : forall n c, hw_err (mload_iter n c) = hw_err c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_halted : forall n c, hw_halted (mload_iter n c) = hw_halted c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_regs : forall n c, hw_regs (mload_iter n c) = hw_regs c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mem : forall n c, hw_mem (mload_iter n c) = hw_mem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_imem : forall n c, hw_imem (mload_iter n c) = hw_imem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_partition_ops : forall n c, hw_partition_ops (mload_iter n c) = hw_partition_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mdl_ops : forall n c, hw_mdl_ops (mload_iter n c) = hw_mdl_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_info_gain : forall n c, hw_info_gain (mload_iter n c) = hw_info_gain c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_error_code : forall n c, hw_error_code (mload_iter n c) = hw_error_code c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_logic_acc : forall n c, hw_logic_acc (mload_iter n c) = hw_logic_acc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_cert_addr : forall n c, hw_cert_addr (mload_iter n c) = hw_cert_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_active_module : forall n c, hw_active_module (mload_iter n c) = hw_active_module c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mstatus : forall n c, hw_mstatus (mload_iter n c) = hw_mstatus c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mcycle_lo : forall n c, hw_mcycle_lo (mload_iter n c) = hw_mcycle_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mcycle_hi : forall n c, hw_mcycle_hi (mload_iter n c) = hw_mcycle_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_minstret_lo : forall n c, hw_minstret_lo (mload_iter n c) = hw_minstret_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_minstret_hi : forall n c, hw_minstret_hi (mload_iter n c) = hw_minstret_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_trap_vector : forall n c, hw_trap_vector (mload_iter n c) = hw_trap_vector c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_certified : forall n c, hw_certified (mload_iter n c) = hw_certified c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_phase : forall n c, hw_lassert_phase (mload_iter n c) = hw_lassert_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_kind : forall n c, hw_lassert_kind (mload_iter n c) = hw_lassert_kind c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_fbase : forall n c, hw_lassert_fbase (mload_iter n c) = hw_lassert_fbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_cbase : forall n c, hw_lassert_cbase (mload_iter n c) = hw_lassert_cbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_flen : forall n c, hw_lassert_flen (mload_iter n c) = hw_lassert_flen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_clen : forall n c, hw_lassert_clen (mload_iter n c) = hw_lassert_clen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_nvars : forall n c, hw_lassert_nvars (mload_iter n c) = hw_lassert_nvars c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_fptr : forall n c, hw_lassert_fptr (mload_iter n c) = hw_lassert_fptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_cptr : forall n c, hw_lassert_cptr (mload_iter n c) = hw_lassert_cptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (mload_iter n c) = hw_lassert_fbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (mload_iter n c) = hw_lassert_cbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (mload_iter n c) = hw_lassert_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (mload_iter n c) = hw_lassert_counter_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (mload_iter n c) = hw_lassert_counter_seen_fail c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_phase : forall n c, hw_chsh_phase (mload_iter n c) = hw_chsh_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n00 : forall n c, hw_chsh_n00 (mload_iter n c) = hw_chsh_n00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n01 : forall n c, hw_chsh_n01 (mload_iter n c) = hw_chsh_n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n10 : forall n c, hw_chsh_n10 (mload_iter n c) = hw_chsh_n10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n11 : forall n c, hw_chsh_n11 (mload_iter n c) = hw_chsh_n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d00 : forall n c, hw_chsh_d00 (mload_iter n c) = hw_chsh_d00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d01 : forall n c, hw_chsh_d01 (mload_iter n c) = hw_chsh_d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d10 : forall n c, hw_chsh_d10 (mload_iter n c) = hw_chsh_d10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d11 : forall n c, hw_chsh_d11 (mload_iter n c) = hw_chsh_d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (mload_iter n c) = hw_chsh_sign00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (mload_iter n c) = hw_chsh_sign01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (mload_iter n c) = hw_chsh_sign10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (mload_iter n c) = hw_chsh_sign11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (mload_iter n c) = hw_chsh_n00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (mload_iter n c) = hw_chsh_n01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (mload_iter n c) = hw_chsh_n10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (mload_iter n c) = hw_chsh_n11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (mload_iter n c) = hw_chsh_d00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (mload_iter n c) = hw_chsh_d01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (mload_iter n c) = hw_chsh_d10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (mload_iter n c) = hw_chsh_d11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (mload_iter n c) = hw_chsh_A_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (mload_iter n c) = hw_chsh_A_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (mload_iter n c) = hw_chsh_A_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (mload_iter n c) = hw_chsh_B_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (mload_iter n c) = hw_chsh_B_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (mload_iter n c) = hw_chsh_B_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (mload_iter n c) = hw_chsh_d00d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (mload_iter n c) = hw_chsh_n10n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (mload_iter n c) = hw_chsh_d10d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (mload_iter n c) = hw_chsh_n00n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (mload_iter n c) = hw_chsh_abs_C1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (mload_iter n c) = hw_chsh_abs_C2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (mload_iter n c) = hw_chsh_C_sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (mload_iter n c) = hw_chsh_A_times_B c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_chsh_check_result : forall n c, hw_chsh_check_result (mload_iter n c) = hw_chsh_check_result c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (mload_iter n c) = hw_bus_load_instr_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (mload_iter n c) = hw_bus_load_instr_data c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (mload_iter n c) = hw_bus_load_instr_kick c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mu_tensor : forall n c, hw_mu_tensor (mload_iter n c) = hw_mu_tensor c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_module_tensors : forall n c, hw_module_tensors (mload_iter n c) = hw_module_tensors c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_csr_status : forall n c, hw_csr_status (mload_iter n c) = hw_csr_status c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_csr_heap_base : forall n c, hw_csr_heap_base (mload_iter n c) = hw_csr_heap_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_ptTable : forall n c, hw_ptTable (mload_iter n c) = hw_ptTable c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_pt_next_id : forall n c, hw_pt_next_id (mload_iter n c) = hw_pt_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_morph_src_table : forall n c, hw_morph_src_table (mload_iter n c) = hw_morph_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_morph_dst_table : forall n c, hw_morph_dst_table (mload_iter n c) = hw_morph_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (mload_iter n c) = hw_morph_coupling_desc_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_morph_valid_table : forall n c, hw_morph_valid_table (mload_iter n c) = hw_morph_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_morph_identity_table : forall n c, hw_morph_identity_table (mload_iter n c) = hw_morph_identity_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_morph_next_id : forall n c, hw_morph_next_id (mload_iter n c) = hw_morph_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_desc_base_table : forall n c, hw_coupling_desc_base_table (mload_iter n c) = hw_coupling_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_desc_count_table : forall n c, hw_coupling_desc_count_table (mload_iter n c) = hw_coupling_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_desc_valid_table : forall n c, hw_coupling_desc_valid_table (mload_iter n c) = hw_coupling_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (mload_iter n c) = hw_coupling_desc_label_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (mload_iter n c) = hw_coupling_desc_label_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_desc_next_id : forall n c, hw_coupling_desc_next_id (mload_iter n c) = hw_coupling_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_coupling_pair_next_id : forall n c, hw_coupling_pair_next_id (mload_iter n c) = hw_coupling_pair_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_op : forall n c, hw_mc_op (mload_iter n c) = hw_mc_op c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_mem_base : forall n c, hw_mc_mem_base (mload_iter n c) = hw_mc_mem_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_pair_count : forall n c, hw_mc_pair_count (mload_iter n c) = hw_mc_pair_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_src1_base : forall n c, hw_mc_src1_base (mload_iter n c) = hw_mc_src1_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_src1_count : forall n c, hw_mc_src1_count (mload_iter n c) = hw_mc_src1_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_src2_base : forall n c, hw_mc_src2_base (mload_iter n c) = hw_mc_src2_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_src2_count : forall n c, hw_mc_src2_count (mload_iter n c) = hw_mc_src2_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_j : forall n c, hw_mc_j (mload_iter n c) = hw_mc_j c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (mload_iter n c) = hw_mc_is_id1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (mload_iter n c) = hw_mc_is_id2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_write_base : forall n c, hw_mc_write_base (mload_iter n c) = hw_mc_write_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_norm_ptr : forall n c, hw_mc_norm_ptr (mload_iter n c) = hw_mc_norm_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_duplicate : forall n c, hw_mc_duplicate (mload_iter n c) = hw_mc_duplicate c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (mload_iter n c) = hw_mc_dst_reg c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (mload_iter n c) = hw_mc_morph_slot c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (mload_iter n c) = hw_mc_new_src_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (mload_iter n c) = hw_mc_new_dst_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_mc_cost : forall n c, hw_mc_cost (mload_iter n c) = hw_mc_cost c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (mload_iter n c) = hw_formula_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (mload_iter n c) = hw_formula_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (mload_iter n c) = hw_formula_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (mload_iter n c) = hw_formula_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (mload_iter n c) = hw_cert_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (mload_iter n c) = hw_cert_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (mload_iter n c) = hw_cert_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (mload_iter n c) = hw_cert_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (mload_iter n c) = hw_desc_meta_subtype_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (mload_iter n c) = hw_desc_meta_kind_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (mload_iter n c) = hw_desc_meta_inline_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (mload_iter n c) = hw_desc_meta_aux_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (mload_iter n c) = hw_desc_meta_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (mload_iter n c) = hw_desc_meta_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_same_00 : forall n c, hw_wc_same_00 (mload_iter n c) = hw_wc_same_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (mload_iter n c) = hw_wc_diff_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_same_01 : forall n c, hw_wc_same_01 (mload_iter n c) = hw_wc_same_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (mload_iter n c) = hw_wc_diff_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_same_10 : forall n c, hw_wc_same_10 (mload_iter n c) = hw_wc_same_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (mload_iter n c) = hw_wc_diff_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_same_11 : forall n c, hw_wc_same_11 (mload_iter n c) = hw_wc_same_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.
Lemma mload_iter_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (mload_iter n c) = hw_wc_diff_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [mload_iter]; rewrite IH; reflexivity]. Qed.

Lemma weq_nat5 : forall a b, a < 32 -> b < 32 ->
  (if weq (natToWord 5 a) (natToWord 5 b) then true else false) = Nat.eqb a b.
Proof. intros a b Ha Hb. exact (bounded_word_eqb a b Ha Hb). Qed.

Theorem mload_loop : forall n c r out i count src dst valid,
  count - i = n -> i < count <= 16 ->
  hw_mc_phase c = WO~0~0~1~0 -> hw_mc_read_ptr c = r ->
  hw_mc_write_ptr c = natToWord 5 out -> hw_mc_i c = natToWord 5 i ->
  hw_mc_pair_count c = natToWord 5 count ->
  hw_coupling_pair_src_table c = src -> hw_coupling_pair_dst_table c = dst ->
  hw_coupling_pair_valid_table c = valid ->
  (forall m, m < n -> hw_mc_phase (mload_iter m c) = WO~0~0~1~0) /\
  hw_mc_phase (mload_iter n c) = WO~0~1~0~1 /\
  hw_mc_write_ptr (mload_iter n c) = natToWord 5 (out + n) /\
  hw_coupling_pair_src_table (mload_iter n c) = loaded_table (hw_mem c) r out n src 0 /\
  hw_coupling_pair_dst_table (mload_iter n c) = loaded_table (hw_mem c) r out n dst 1 /\
  hw_coupling_pair_valid_table (mload_iter n c) = loaded_valid out n valid.
Proof.
  induction n as [|n IH]; intros c r out i count src dst valid Hn Hb Hp Hr Ho Hi Hc Hs Hd Hv; [lia|].
  assert (Ph : hw_mc_phase (mcload_next c) = if Nat.eqb (S i) count then WO~0~1~0~1 else WO~0~0~1~0).
  { rewrite mcload_phase, Hi, Hc, <- natToWord_plus, Nat.add_1_r.
    pose proof (weq_nat5 (S i) count ltac:(lia) ltac:(lia)) as E.
    destruct (weq _ _); destruct (Nat.eqb (S i) count); congruence. }
  assert (S0 : hw_coupling_pair_src_table (mcload_next c) =
    put_vector src (pair_index (natToWord 5 out)) (hw_mem c (mem_index (wplus r (natToWord 32 0))))).
  { rewrite mcload_src, Hs, Ho, Hr, wplus_comm, wplus_unit. reflexivity. }
  assert (D0 : hw_coupling_pair_dst_table (mcload_next c) =
    put_vector dst (pair_index (natToWord 5 out)) (hw_mem c (mem_index (wplus r (natToWord 32 1))))).
  { rewrite mcload_dst, Hd, Ho, Hr. reflexivity. }
  assert (V0 : hw_coupling_pair_valid_table (mcload_next c) = load_valid_next out valid).
  { rewrite mcload_valid, Hv, Ho. reflexivity. }
  assert (O0 : hw_mc_write_ptr (mcload_next c) = natToWord 5 (S out)).
  { rewrite mcload_write_ptr, Ho, <- natToWord_plus, Nat.add_1_r. reflexivity. }
  destruct (Nat.eqb_spec (S i) count) as [E|E].
  - assert (n = 0) by lia. subst n. cbn [mload_iter loaded_table loaded_valid].
    split; [intros m Hm; assert (m = 0) by lia; subst m; exact Hp|].
    split; [rewrite Ph; reflexivity|].
    split; [rewrite O0, Nat.add_1_r; reflexivity|].
    split; [exact S0|]. split; [exact D0|exact V0].
  - destruct (IH (mcload_next c) (wplus r (natToWord 32 2)) (S out) (S i) count
      (put_vector src (pair_index (natToWord 5 out)) (hw_mem c (mem_index (wplus r (natToWord 32 0)))))
      (put_vector dst (pair_index (natToWord 5 out)) (hw_mem c (mem_index (wplus r (natToWord 32 1)))))
      (load_valid_next out valid)
      ltac:(lia) ltac:(lia) ltac:(rewrite Ph; reflexivity) ltac:(rewrite mcload_read_ptr, Hr; reflexivity)
      O0 ltac:(rewrite mcload_i, Hi, <- natToWord_plus, Nat.add_1_r; reflexivity)
      ltac:(rewrite mcload_keeps_mc_pair_count; exact Hc) S0 D0 V0)
      as [IHp [IHf [IHo [IHs [IHd IHv]]]]].
    rewrite mcload_keeps_mem in IHs, IHd.
    cbn [mload_iter loaded_table loaded_valid].
    split; [intros m Hm; destruct m as [|m]; [exact Hp|cbn [mload_iter]; apply IHp; lia]|].
    split; [exact IHf|].
    split; [rewrite IHo; f_equal; lia|].
    split; [exact IHs|]. split; [exact IHd|exact IHv].
Qed.

Lemma mload_multistep : forall n c,
  (forall m, m < n -> hw_mc_phase (mload_iter m c) = WO~0~0~1~0) ->
  Multistep thieleCore (hwb_regs c) (hwb_regs (mload_iter n c)) (mload_labels n).
Proof.
  induction n as [|n IH]; intros c H.
  - constructor. reflexivity.
  - cbn [mload_iter mload_labels].
    assert (G : evalExpr (((Var type (SyntaxKind (Bit 4)) (hw_mc_phase c)) == $$(WO~0~0~1~0)))%kami_expr = true).
    { cbn [evalExpr evalConstT]. change (hw_mc_phase c) with (hw_mc_phase (mload_iter 0 c)). rewrite (H 0 ltac:(lia)). reflexivity. }
    destruct (mcload_enabled c G) as [u [Hu Eu]].
    apply (normalization_multistep_trans _ (hwb_regs (mcload_next c))).
    + rewrite <- Eu. apply normalization_substep_execution.
      exact (cpu_rule_substep _ _ _ (rule_in_index 4 ltac:(lia)) Hu).
    + apply IH. intros m Hm. exact (H (S m) ltac:(lia)).
Qed.
