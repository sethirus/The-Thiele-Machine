(** CouplingFsmJoin.v: the coupling join loop at the typed boundary (COMPOSE of
    two non-identity morphisms). [join_run]: the firings append the matching
    candidate pairs in row order and end at phase 5; [join_multistep]: they are
    an actual Kami execution. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop NormalizationPrefix MorphLoading MorphCopy MorphJoin RuleEnabled FsmDecoded ChshRetire
  CouplingFsmEnds CouplingFsmLoad CouplingFsmNorm.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma mcjoin_keeps_pc : forall c, hw_pc (mcjoin_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mu : forall c, hw_mu (mcjoin_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_halted : forall c, hw_halted (mcjoin_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_regs : forall c, hw_regs (mcjoin_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mem : forall c, hw_mem (mcjoin_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_imem : forall c, hw_imem (mcjoin_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_partition_ops : forall c, hw_partition_ops (mcjoin_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mdl_ops : forall c, hw_mdl_ops (mcjoin_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_info_gain : forall c, hw_info_gain (mcjoin_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_logic_acc : forall c, hw_logic_acc (mcjoin_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_cert_addr : forall c, hw_cert_addr (mcjoin_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_active_module : forall c, hw_active_module (mcjoin_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mstatus : forall c, hw_mstatus (mcjoin_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mcycle_lo : forall c, hw_mcycle_lo (mcjoin_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mcycle_hi : forall c, hw_mcycle_hi (mcjoin_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_minstret_lo : forall c, hw_minstret_lo (mcjoin_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_minstret_hi : forall c, hw_minstret_hi (mcjoin_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_trap_vector : forall c, hw_trap_vector (mcjoin_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_certified : forall c, hw_certified (mcjoin_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_phase : forall c, hw_lassert_phase (mcjoin_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_kind : forall c, hw_lassert_kind (mcjoin_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_fbase : forall c, hw_lassert_fbase (mcjoin_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_cbase : forall c, hw_lassert_cbase (mcjoin_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_flen : forall c, hw_lassert_flen (mcjoin_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_clen : forall c, hw_lassert_clen (mcjoin_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_nvars : forall c, hw_lassert_nvars (mcjoin_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_fptr : forall c, hw_lassert_fptr (mcjoin_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_cptr : forall c, hw_lassert_cptr (mcjoin_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mcjoin_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mcjoin_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mcjoin_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mcjoin_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mcjoin_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_phase : forall c, hw_chsh_phase (mcjoin_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n00 : forall c, hw_chsh_n00 (mcjoin_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n01 : forall c, hw_chsh_n01 (mcjoin_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n10 : forall c, hw_chsh_n10 (mcjoin_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n11 : forall c, hw_chsh_n11 (mcjoin_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d00 : forall c, hw_chsh_d00 (mcjoin_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d01 : forall c, hw_chsh_d01 (mcjoin_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d10 : forall c, hw_chsh_d10 (mcjoin_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d11 : forall c, hw_chsh_d11 (mcjoin_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mcjoin_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mcjoin_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mcjoin_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mcjoin_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mcjoin_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mcjoin_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mcjoin_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mcjoin_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mcjoin_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mcjoin_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mcjoin_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mcjoin_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mcjoin_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mcjoin_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mcjoin_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mcjoin_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mcjoin_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mcjoin_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mcjoin_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mcjoin_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mcjoin_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mcjoin_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mcjoin_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mcjoin_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mcjoin_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mcjoin_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_chsh_check_result : forall c, hw_chsh_check_result (mcjoin_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mcjoin_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mcjoin_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mcjoin_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mu_tensor : forall c, hw_mu_tensor (mcjoin_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_module_tensors : forall c, hw_module_tensors (mcjoin_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_csr_status : forall c, hw_csr_status (mcjoin_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_csr_heap_base : forall c, hw_csr_heap_base (mcjoin_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_ptTable : forall c, hw_ptTable (mcjoin_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_pt_next_id : forall c, hw_pt_next_id (mcjoin_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_morph_src_table : forall c, hw_morph_src_table (mcjoin_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_morph_dst_table : forall c, hw_morph_dst_table (mcjoin_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mcjoin_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_morph_valid_table : forall c, hw_morph_valid_table (mcjoin_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_morph_identity_table : forall c, hw_morph_identity_table (mcjoin_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_morph_next_id : forall c, hw_morph_next_id (mcjoin_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mcjoin_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mcjoin_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mcjoin_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mcjoin_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mcjoin_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mcjoin_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mcjoin_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_op : forall c, hw_mc_op (mcjoin_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_mem_base : forall c, hw_mc_mem_base (mcjoin_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_pair_count : forall c, hw_mc_pair_count (mcjoin_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (mcjoin_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_src1_base : forall c, hw_mc_src1_base (mcjoin_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_src1_count : forall c, hw_mc_src1_count (mcjoin_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_src2_base : forall c, hw_mc_src2_base (mcjoin_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_src2_count : forall c, hw_mc_src2_count (mcjoin_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mcjoin_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mcjoin_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_write_base : forall c, hw_mc_write_base (mcjoin_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (mcjoin_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_duplicate : forall c, hw_mc_duplicate (mcjoin_next c) = hw_mc_duplicate c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mcjoin_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mcjoin_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mcjoin_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mcjoin_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_mc_cost : forall c, hw_mc_cost (mcjoin_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mcjoin_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mcjoin_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mcjoin_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mcjoin_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mcjoin_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mcjoin_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mcjoin_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mcjoin_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mcjoin_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mcjoin_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mcjoin_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mcjoin_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mcjoin_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mcjoin_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_same_00 : forall c, hw_wc_same_00 (mcjoin_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mcjoin_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_same_01 : forall c, hw_wc_same_01 (mcjoin_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mcjoin_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_same_10 : forall c, hw_wc_same_10 (mcjoin_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mcjoin_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_same_11 : forall c, hw_wc_same_11 (mcjoin_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mcjoin_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mcjoin_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Definition cjoin_args (c : HWB) := (hw_mc_i c, hw_mc_j c, hw_mc_src1_count c, hw_mc_src2_count c).
Definition cjoin_emits (c : HWB) := join_emits (hw_mc_i c) (hw_mc_j c) (hw_mc_src1_count c) (hw_mc_src2_count c)
  (hw_mc_write_ptr c) (hw_mc_src1_base c) (hw_mc_src2_base c) (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c).
Definition cjoin_overflow (c : HWB) := join_overflow (hw_mc_i c) (hw_mc_j c) (hw_mc_src1_count c) (hw_mc_src2_count c)
  (hw_mc_write_ptr c) (hw_mc_src1_base c) (hw_mc_src2_base c) (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c).

Lemma mcjoin_src : forall c, hw_coupling_pair_src_table (mcjoin_next c) =
  if cjoin_emits c then put_vector (hw_coupling_pair_src_table c) (pair_index (hw_mc_write_ptr c))
    (hw_coupling_pair_src_table c (join_index (hw_mc_src1_base c) (hw_mc_i c))) else hw_coupling_pair_src_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_dst : forall c, hw_coupling_pair_dst_table (mcjoin_next c) =
  if cjoin_emits c then put_vector (hw_coupling_pair_dst_table c) (pair_index (hw_mc_write_ptr c))
    (hw_coupling_pair_dst_table c (join_index (hw_mc_src2_base c) (hw_mc_j c))) else hw_coupling_pair_dst_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_valid : forall c, hw_coupling_pair_valid_table (mcjoin_next c) =
  if cjoin_emits c then put_vector (hw_coupling_pair_valid_table c) (pair_index (hw_mc_write_ptr c)) true
  else hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma mcjoin_write_ptr : forall c, hw_mc_write_ptr (mcjoin_next c) =
  if cjoin_emits c then wplus (hw_mc_write_ptr c) (natToWord 5 1) else hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma mcjoin_j : forall c, hw_mc_j (mcjoin_next c) =
  if join_wrap (hw_mc_j c) (hw_mc_src2_count c) then natToWord 5 0 else wplus (hw_mc_j c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcjoin_i : forall c, hw_mc_i (mcjoin_next c) =
  if join_wrap (hw_mc_j c) (hw_mc_src2_count c) then wplus (hw_mc_i c) (natToWord 5 1) else hw_mc_i c.
Proof. reflexivity. Qed.
Lemma mcjoin_phase : forall c, hw_mc_phase (mcjoin_next c) =
  if cjoin_overflow c then natToWord 4 0
  else if orb (join_empty (hw_mc_src1_count c) (hw_mc_src2_count c))
              (join_done (hw_mc_i c) (hw_mc_j c) (hw_mc_src1_count c) (hw_mc_src2_count c))
       then natToWord 4 5 else natToWord 4 7.
Proof. reflexivity. Qed.
Lemma mcjoin_err : forall c, hw_err (mcjoin_next c) = orb (hw_err c) (cjoin_overflow c).
Proof. reflexivity. Qed.
Lemma mcjoin_error_code : forall c, hw_error_code (mcjoin_next c) =
  if cjoin_overflow c then ERR_COUPLING_INVALID else hw_error_code c.
Proof. reflexivity. Qed.

Fixpoint join_iter (n : nat) (c : HWB) : HWB :=
  match n with
  | O => c
  | S m => join_iter m (mcjoin_next c)
  end.

Lemma join_iter_keeps_pc : forall n c, hw_pc (join_iter n c) = hw_pc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_pc]. Qed.
Lemma join_iter_keeps_mu : forall n c, hw_mu (join_iter n c) = hw_mu c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mu]. Qed.
Lemma join_iter_keeps_halted : forall n c, hw_halted (join_iter n c) = hw_halted c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_halted]. Qed.
Lemma join_iter_keeps_regs : forall n c, hw_regs (join_iter n c) = hw_regs c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_regs]. Qed.
Lemma join_iter_keeps_mem : forall n c, hw_mem (join_iter n c) = hw_mem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mem]. Qed.
Lemma join_iter_keeps_imem : forall n c, hw_imem (join_iter n c) = hw_imem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_imem]. Qed.
Lemma join_iter_keeps_partition_ops : forall n c, hw_partition_ops (join_iter n c) = hw_partition_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_partition_ops]. Qed.
Lemma join_iter_keeps_mdl_ops : forall n c, hw_mdl_ops (join_iter n c) = hw_mdl_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mdl_ops]. Qed.
Lemma join_iter_keeps_info_gain : forall n c, hw_info_gain (join_iter n c) = hw_info_gain c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_info_gain]. Qed.
Lemma join_iter_keeps_logic_acc : forall n c, hw_logic_acc (join_iter n c) = hw_logic_acc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_logic_acc]. Qed.
Lemma join_iter_keeps_cert_addr : forall n c, hw_cert_addr (join_iter n c) = hw_cert_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_cert_addr]. Qed.
Lemma join_iter_keeps_active_module : forall n c, hw_active_module (join_iter n c) = hw_active_module c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_active_module]. Qed.
Lemma join_iter_keeps_mstatus : forall n c, hw_mstatus (join_iter n c) = hw_mstatus c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mstatus]. Qed.
Lemma join_iter_keeps_mcycle_lo : forall n c, hw_mcycle_lo (join_iter n c) = hw_mcycle_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mcycle_lo]. Qed.
Lemma join_iter_keeps_mcycle_hi : forall n c, hw_mcycle_hi (join_iter n c) = hw_mcycle_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mcycle_hi]. Qed.
Lemma join_iter_keeps_minstret_lo : forall n c, hw_minstret_lo (join_iter n c) = hw_minstret_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_minstret_lo]. Qed.
Lemma join_iter_keeps_minstret_hi : forall n c, hw_minstret_hi (join_iter n c) = hw_minstret_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_minstret_hi]. Qed.
Lemma join_iter_keeps_trap_vector : forall n c, hw_trap_vector (join_iter n c) = hw_trap_vector c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_trap_vector]. Qed.
Lemma join_iter_keeps_certified : forall n c, hw_certified (join_iter n c) = hw_certified c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_certified]. Qed.
Lemma join_iter_keeps_lassert_phase : forall n c, hw_lassert_phase (join_iter n c) = hw_lassert_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_phase]. Qed.
Lemma join_iter_keeps_lassert_kind : forall n c, hw_lassert_kind (join_iter n c) = hw_lassert_kind c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_kind]. Qed.
Lemma join_iter_keeps_lassert_fbase : forall n c, hw_lassert_fbase (join_iter n c) = hw_lassert_fbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_fbase]. Qed.
Lemma join_iter_keeps_lassert_cbase : forall n c, hw_lassert_cbase (join_iter n c) = hw_lassert_cbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_cbase]. Qed.
Lemma join_iter_keeps_lassert_flen : forall n c, hw_lassert_flen (join_iter n c) = hw_lassert_flen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_flen]. Qed.
Lemma join_iter_keeps_lassert_clen : forall n c, hw_lassert_clen (join_iter n c) = hw_lassert_clen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_clen]. Qed.
Lemma join_iter_keeps_lassert_nvars : forall n c, hw_lassert_nvars (join_iter n c) = hw_lassert_nvars c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_nvars]. Qed.
Lemma join_iter_keeps_lassert_fptr : forall n c, hw_lassert_fptr (join_iter n c) = hw_lassert_fptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_fptr]. Qed.
Lemma join_iter_keeps_lassert_cptr : forall n c, hw_lassert_cptr (join_iter n c) = hw_lassert_cptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_cptr]. Qed.
Lemma join_iter_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (join_iter n c) = hw_lassert_fbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_fbuf]. Qed.
Lemma join_iter_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (join_iter n c) = hw_lassert_cbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_cbuf]. Qed.
Lemma join_iter_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (join_iter n c) = hw_lassert_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_clause_sat]. Qed.
Lemma join_iter_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (join_iter n c) = hw_lassert_counter_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_counter_clause_sat]. Qed.
Lemma join_iter_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (join_iter n c) = hw_lassert_counter_seen_fail c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_lassert_counter_seen_fail]. Qed.
Lemma join_iter_keeps_chsh_phase : forall n c, hw_chsh_phase (join_iter n c) = hw_chsh_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_phase]. Qed.
Lemma join_iter_keeps_chsh_n00 : forall n c, hw_chsh_n00 (join_iter n c) = hw_chsh_n00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n00]. Qed.
Lemma join_iter_keeps_chsh_n01 : forall n c, hw_chsh_n01 (join_iter n c) = hw_chsh_n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n01]. Qed.
Lemma join_iter_keeps_chsh_n10 : forall n c, hw_chsh_n10 (join_iter n c) = hw_chsh_n10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n10]. Qed.
Lemma join_iter_keeps_chsh_n11 : forall n c, hw_chsh_n11 (join_iter n c) = hw_chsh_n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n11]. Qed.
Lemma join_iter_keeps_chsh_d00 : forall n c, hw_chsh_d00 (join_iter n c) = hw_chsh_d00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d00]. Qed.
Lemma join_iter_keeps_chsh_d01 : forall n c, hw_chsh_d01 (join_iter n c) = hw_chsh_d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d01]. Qed.
Lemma join_iter_keeps_chsh_d10 : forall n c, hw_chsh_d10 (join_iter n c) = hw_chsh_d10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d10]. Qed.
Lemma join_iter_keeps_chsh_d11 : forall n c, hw_chsh_d11 (join_iter n c) = hw_chsh_d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d11]. Qed.
Lemma join_iter_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (join_iter n c) = hw_chsh_sign00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_sign00]. Qed.
Lemma join_iter_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (join_iter n c) = hw_chsh_sign01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_sign01]. Qed.
Lemma join_iter_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (join_iter n c) = hw_chsh_sign10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_sign10]. Qed.
Lemma join_iter_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (join_iter n c) = hw_chsh_sign11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_sign11]. Qed.
Lemma join_iter_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (join_iter n c) = hw_chsh_n00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n00sq]. Qed.
Lemma join_iter_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (join_iter n c) = hw_chsh_n01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n01sq]. Qed.
Lemma join_iter_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (join_iter n c) = hw_chsh_n10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n10sq]. Qed.
Lemma join_iter_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (join_iter n c) = hw_chsh_n11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n11sq]. Qed.
Lemma join_iter_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (join_iter n c) = hw_chsh_d00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d00sq]. Qed.
Lemma join_iter_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (join_iter n c) = hw_chsh_d01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d01sq]. Qed.
Lemma join_iter_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (join_iter n c) = hw_chsh_d10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d10sq]. Qed.
Lemma join_iter_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (join_iter n c) = hw_chsh_d11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d11sq]. Qed.
Lemma join_iter_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (join_iter n c) = hw_chsh_A_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_A_pos]. Qed.
Lemma join_iter_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (join_iter n c) = hw_chsh_A_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_A_neg_a]. Qed.
Lemma join_iter_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (join_iter n c) = hw_chsh_A_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_A_neg_b]. Qed.
Lemma join_iter_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (join_iter n c) = hw_chsh_B_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_B_pos]. Qed.
Lemma join_iter_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (join_iter n c) = hw_chsh_B_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_B_neg_a]. Qed.
Lemma join_iter_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (join_iter n c) = hw_chsh_B_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_B_neg_b]. Qed.
Lemma join_iter_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (join_iter n c) = hw_chsh_d00d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d00d01]. Qed.
Lemma join_iter_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (join_iter n c) = hw_chsh_n10n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n10n11]. Qed.
Lemma join_iter_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (join_iter n c) = hw_chsh_d10d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_d10d11]. Qed.
Lemma join_iter_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (join_iter n c) = hw_chsh_n00n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_n00n01]. Qed.
Lemma join_iter_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (join_iter n c) = hw_chsh_abs_C1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_abs_C1]. Qed.
Lemma join_iter_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (join_iter n c) = hw_chsh_abs_C2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_abs_C2]. Qed.
Lemma join_iter_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (join_iter n c) = hw_chsh_C_sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_C_sq]. Qed.
Lemma join_iter_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (join_iter n c) = hw_chsh_A_times_B c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_A_times_B]. Qed.
Lemma join_iter_keeps_chsh_check_result : forall n c, hw_chsh_check_result (join_iter n c) = hw_chsh_check_result c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_chsh_check_result]. Qed.
Lemma join_iter_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (join_iter n c) = hw_bus_load_instr_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_bus_load_instr_addr]. Qed.
Lemma join_iter_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (join_iter n c) = hw_bus_load_instr_data c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_bus_load_instr_data]. Qed.
Lemma join_iter_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (join_iter n c) = hw_bus_load_instr_kick c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_bus_load_instr_kick]. Qed.
Lemma join_iter_keeps_mu_tensor : forall n c, hw_mu_tensor (join_iter n c) = hw_mu_tensor c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mu_tensor]. Qed.
Lemma join_iter_keeps_module_tensors : forall n c, hw_module_tensors (join_iter n c) = hw_module_tensors c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_module_tensors]. Qed.
Lemma join_iter_keeps_csr_status : forall n c, hw_csr_status (join_iter n c) = hw_csr_status c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_csr_status]. Qed.
Lemma join_iter_keeps_csr_heap_base : forall n c, hw_csr_heap_base (join_iter n c) = hw_csr_heap_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_csr_heap_base]. Qed.
Lemma join_iter_keeps_ptTable : forall n c, hw_ptTable (join_iter n c) = hw_ptTable c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_ptTable]. Qed.
Lemma join_iter_keeps_pt_next_id : forall n c, hw_pt_next_id (join_iter n c) = hw_pt_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_pt_next_id]. Qed.
Lemma join_iter_keeps_morph_src_table : forall n c, hw_morph_src_table (join_iter n c) = hw_morph_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_morph_src_table]. Qed.
Lemma join_iter_keeps_morph_dst_table : forall n c, hw_morph_dst_table (join_iter n c) = hw_morph_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_morph_dst_table]. Qed.
Lemma join_iter_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (join_iter n c) = hw_morph_coupling_desc_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_morph_coupling_desc_table]. Qed.
Lemma join_iter_keeps_morph_valid_table : forall n c, hw_morph_valid_table (join_iter n c) = hw_morph_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_morph_valid_table]. Qed.
Lemma join_iter_keeps_morph_identity_table : forall n c, hw_morph_identity_table (join_iter n c) = hw_morph_identity_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_morph_identity_table]. Qed.
Lemma join_iter_keeps_morph_next_id : forall n c, hw_morph_next_id (join_iter n c) = hw_morph_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_morph_next_id]. Qed.
Lemma join_iter_keeps_coupling_desc_base_table : forall n c, hw_coupling_desc_base_table (join_iter n c) = hw_coupling_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_desc_base_table]. Qed.
Lemma join_iter_keeps_coupling_desc_count_table : forall n c, hw_coupling_desc_count_table (join_iter n c) = hw_coupling_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_desc_count_table]. Qed.
Lemma join_iter_keeps_coupling_desc_valid_table : forall n c, hw_coupling_desc_valid_table (join_iter n c) = hw_coupling_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_desc_valid_table]. Qed.
Lemma join_iter_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (join_iter n c) = hw_coupling_desc_label_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_desc_label_table]. Qed.
Lemma join_iter_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (join_iter n c) = hw_coupling_desc_label_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_desc_label_len_table]. Qed.
Lemma join_iter_keeps_coupling_desc_next_id : forall n c, hw_coupling_desc_next_id (join_iter n c) = hw_coupling_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_desc_next_id]. Qed.
Lemma join_iter_keeps_coupling_pair_next_id : forall n c, hw_coupling_pair_next_id (join_iter n c) = hw_coupling_pair_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_coupling_pair_next_id]. Qed.
Lemma join_iter_keeps_mc_op : forall n c, hw_mc_op (join_iter n c) = hw_mc_op c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_op]. Qed.
Lemma join_iter_keeps_mc_mem_base : forall n c, hw_mc_mem_base (join_iter n c) = hw_mc_mem_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_mem_base]. Qed.
Lemma join_iter_keeps_mc_pair_count : forall n c, hw_mc_pair_count (join_iter n c) = hw_mc_pair_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_pair_count]. Qed.
Lemma join_iter_keeps_mc_read_ptr : forall n c, hw_mc_read_ptr (join_iter n c) = hw_mc_read_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_read_ptr]. Qed.
Lemma join_iter_keeps_mc_src1_base : forall n c, hw_mc_src1_base (join_iter n c) = hw_mc_src1_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_src1_base]. Qed.
Lemma join_iter_keeps_mc_src1_count : forall n c, hw_mc_src1_count (join_iter n c) = hw_mc_src1_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_src1_count]. Qed.
Lemma join_iter_keeps_mc_src2_base : forall n c, hw_mc_src2_base (join_iter n c) = hw_mc_src2_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_src2_base]. Qed.
Lemma join_iter_keeps_mc_src2_count : forall n c, hw_mc_src2_count (join_iter n c) = hw_mc_src2_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_src2_count]. Qed.
Lemma join_iter_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (join_iter n c) = hw_mc_is_id1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_is_id1]. Qed.
Lemma join_iter_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (join_iter n c) = hw_mc_is_id2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_is_id2]. Qed.
Lemma join_iter_keeps_mc_write_base : forall n c, hw_mc_write_base (join_iter n c) = hw_mc_write_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_write_base]. Qed.
Lemma join_iter_keeps_mc_norm_ptr : forall n c, hw_mc_norm_ptr (join_iter n c) = hw_mc_norm_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_norm_ptr]. Qed.
Lemma join_iter_keeps_mc_duplicate : forall n c, hw_mc_duplicate (join_iter n c) = hw_mc_duplicate c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_duplicate]. Qed.
Lemma join_iter_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (join_iter n c) = hw_mc_dst_reg c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_dst_reg]. Qed.
Lemma join_iter_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (join_iter n c) = hw_mc_morph_slot c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_morph_slot]. Qed.
Lemma join_iter_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (join_iter n c) = hw_mc_new_src_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_new_src_mod]. Qed.
Lemma join_iter_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (join_iter n c) = hw_mc_new_dst_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_new_dst_mod]. Qed.
Lemma join_iter_keeps_mc_cost : forall n c, hw_mc_cost (join_iter n c) = hw_mc_cost c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_mc_cost]. Qed.
Lemma join_iter_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (join_iter n c) = hw_formula_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_formula_desc_base_table]. Qed.
Lemma join_iter_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (join_iter n c) = hw_formula_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_formula_desc_count_table]. Qed.
Lemma join_iter_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (join_iter n c) = hw_formula_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_formula_desc_valid_table]. Qed.
Lemma join_iter_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (join_iter n c) = hw_formula_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_formula_desc_next_id]. Qed.
Lemma join_iter_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (join_iter n c) = hw_cert_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_cert_desc_base_table]. Qed.
Lemma join_iter_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (join_iter n c) = hw_cert_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_cert_desc_count_table]. Qed.
Lemma join_iter_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (join_iter n c) = hw_cert_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_cert_desc_valid_table]. Qed.
Lemma join_iter_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (join_iter n c) = hw_cert_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_cert_desc_next_id]. Qed.
Lemma join_iter_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (join_iter n c) = hw_desc_meta_subtype_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_desc_meta_subtype_table]. Qed.
Lemma join_iter_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (join_iter n c) = hw_desc_meta_kind_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_desc_meta_kind_table]. Qed.
Lemma join_iter_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (join_iter n c) = hw_desc_meta_inline_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_desc_meta_inline_len_table]. Qed.
Lemma join_iter_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (join_iter n c) = hw_desc_meta_aux_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_desc_meta_aux_table]. Qed.
Lemma join_iter_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (join_iter n c) = hw_desc_meta_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_desc_meta_valid_table]. Qed.
Lemma join_iter_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (join_iter n c) = hw_desc_meta_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_desc_meta_next_id]. Qed.
Lemma join_iter_keeps_wc_same_00 : forall n c, hw_wc_same_00 (join_iter n c) = hw_wc_same_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_same_00]. Qed.
Lemma join_iter_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (join_iter n c) = hw_wc_diff_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_diff_00]. Qed.
Lemma join_iter_keeps_wc_same_01 : forall n c, hw_wc_same_01 (join_iter n c) = hw_wc_same_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_same_01]. Qed.
Lemma join_iter_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (join_iter n c) = hw_wc_diff_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_diff_01]. Qed.
Lemma join_iter_keeps_wc_same_10 : forall n c, hw_wc_same_10 (join_iter n c) = hw_wc_same_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_same_10]. Qed.
Lemma join_iter_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (join_iter n c) = hw_wc_diff_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_diff_10]. Qed.
Lemma join_iter_keeps_wc_same_11 : forall n c, hw_wc_same_11 (join_iter n c) = hw_wc_same_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_same_11]. Qed.
Lemma join_iter_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (join_iter n c) = hw_wc_diff_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [join_iter]; rewrite IH; apply mcjoin_keeps_wc_diff_11]. Qed.

(** * One admitted join firing over natural numbers *)

Lemma join_step_facts : forall c rawsrc rawdst b out i j c1 c2 a1 a2,
  i < c1 <= 16 -> j < c2 <= 16 -> b <= out <= 16 -> a1 + c1 <= b -> a2 + c2 <= b ->
  low_agrees b (hw_coupling_pair_src_table c) rawsrc -> low_agrees b (hw_coupling_pair_dst_table c) rawdst ->
  (candidate_match rawsrc rawdst a1 a2 i j = true -> out < 16) ->
  hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 j ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_ptr c = natToWord 5 out ->
  let matched := candidate_match rawsrc rawdst a1 a2 i j in
  hw_mc_phase (mcjoin_next c) = natToWord 4 (if join_terminal i j c1 c2 then 5 else 7) /\
  hw_mc_i (mcjoin_next c) = natToWord 5 (join_cursor_i i j c2) /\
  hw_mc_j (mcjoin_next c) = natToWord 5 (join_cursor_j j c2) /\
  hw_mc_write_ptr (mcjoin_next c) = natToWord 5 (join_out out matched) /\
  hw_coupling_pair_src_table (mcjoin_next c) = join_table (hw_coupling_pair_src_table c) out (pair_at rawsrc (a1 + i)) matched /\
  hw_coupling_pair_dst_table (mcjoin_next c) = join_table (hw_coupling_pair_dst_table c) out (pair_at rawdst (a2 + j)) matched /\
  hw_coupling_pair_valid_table (mcjoin_next c) = join_valid_table (hw_coupling_pair_valid_table c) out matched /\
  hw_err (mcjoin_next c) = hw_err c /\ hw_error_code (mcjoin_next c) = hw_error_code c.
Proof.
  intros c rawsrc rawdst b out i j c1 c2 a1 a2 Hi Hj Hb Ha1 Ha2 HlS HlD Hroom Hic Hjc Hc1 Hc2 Ha1c Ha2c Hw matched.
  assert (Hm : candidate_match (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c) a1 a2 i j = matched).
  { unfold matched, candidate_match. rewrite HlD, HlS by lia. reflexivity. }
  destruct (join_admitted_controls i j c1 c2 out a1 a2 (hw_coupling_pair_src_table c) (hw_coupling_pair_dst_table c)
    Hi Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intro E; apply Hroom; rewrite Hm in E; exact E)) as [Hem Hov].
  assert (Em : cjoin_emits c = matched) by (unfold cjoin_emits; rewrite Hic, Hjc, Hc1, Hc2, Hw, Ha1c, Ha2c, Hem; exact Hm).
  assert (Ov : cjoin_overflow c = false) by (unfold cjoin_overflow; rewrite Hic, Hjc, Hc1, Hc2, Hw, Ha1c, Ha2c; exact Hov).
  assert (Emp : join_empty (hw_mc_src1_count c) (hw_mc_src2_count c) = false).
  { rewrite Hc1, Hc2, join_empty_nat by lia.
    rewrite (proj2 (Nat.eqb_neq c1 0)), (proj2 (Nat.eqb_neq c2 0)) by lia. reflexivity. }
  assert (Wr : join_wrap (hw_mc_j c) (hw_mc_src2_count c) = Nat.eqb (S j) c2) by (rewrite Hjc, Hc2; apply join_wrap_nat; lia).
  assert (Dn : join_done (hw_mc_i c) (hw_mc_j c) (hw_mc_src1_count c) (hw_mc_src2_count c) = join_terminal i j c1 c2)
    by (rewrite Hic, Hjc, Hc1, Hc2; apply join_done_nat; lia).
  split; [rewrite mcjoin_phase, Ov, Emp, Dn; cbn [orb]; destruct (join_terminal i j c1 c2); reflexivity|].
  split; [rewrite mcjoin_i, Wr, Hic; unfold join_cursor_i; destruct (Nat.eqb (S j) c2); [apply succ_word5|reflexivity]|].
  split; [rewrite mcjoin_j, Wr, Hjc; unfold join_cursor_j; destruct (Nat.eqb (S j) c2); [reflexivity|apply succ_word5]|].
  split; [rewrite mcjoin_write_ptr, Em, Hw; unfold join_out; destruct matched; [apply succ_word5|reflexivity]|].
  split.
  { rewrite mcjoin_src, Em, Hw, Hic, Ha1c, join_index_nat by lia. unfold join_table, append_pair.
    destruct matched; [|reflexivity]. f_equal. exact (HlS (a1 + i) ltac:(lia)). }
  split.
  { rewrite mcjoin_dst, Em, Hw, Hjc, Ha2c, join_index_nat by lia. unfold join_table, append_pair.
    destruct matched; [|reflexivity]. f_equal. exact (HlD (a2 + j) ltac:(lia)). }
  split; [rewrite mcjoin_valid, Em, Hw; unfold join_valid_table; destruct matched; reflexivity|].
  rewrite mcjoin_err, mcjoin_error_code, Ov, orb_false_r. split; reflexivity.
Qed.

(** * The join loop *)

Theorem join_run : forall n c rawsrc rawdst b out i j c1 c2 a1 a2,
  List.length (candidate_indices i j c1 c2) = n ->
  i < c1 <= 16 -> j < c2 <= 16 -> b <= out ->
  out + List.length (remaining_join rawsrc rawdst a1 a2 i j c1 c2) <= 16 ->
  a1 + c1 <= b -> a2 + c2 <= b ->
  low_agrees b (hw_coupling_pair_src_table c) rawsrc -> low_agrees b (hw_coupling_pair_dst_table c) rawdst ->
  hw_mc_phase c = natToWord 4 7 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 j ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_ptr c = natToWord 5 out ->
  let rest := remaining_join rawsrc rawdst a1 a2 i j c1 c2 in
  (forall m, m < n -> hw_mc_phase (join_iter m c) = natToWord 4 7) /\
  hw_mc_phase (join_iter n c) = natToWord 4 5 /\
  hw_mc_write_ptr (join_iter n c) = natToWord 5 (out + List.length rest) /\
  hw_coupling_pair_src_table (join_iter n c) = store_pairs (hw_coupling_pair_src_table c) out rest true /\
  hw_coupling_pair_dst_table (join_iter n c) = store_pairs (hw_coupling_pair_dst_table c) out rest false /\
  hw_coupling_pair_valid_table (join_iter n c) = loaded_valid out (List.length rest) (hw_coupling_pair_valid_table c) /\
  hw_err (join_iter n c) = hw_err c /\ hw_error_code (join_iter n c) = hw_error_code c.
Proof.
  induction n as [|n IH]; intros c rawsrc rawdst b out i j c1 c2 a1 a2 Hn Hi Hj Hb Hcap Ha1 Ha2 HlS HlD
    Hp Hic Hjc Hc1 Hc2 Ha1c Ha2c Hw rest.
  - rewrite candidate_indices_cons in Hn by lia. discriminate.
  - set (matched := candidate_match rawsrc rawdst a1 a2 i j).
    set (ni := join_cursor_i i j c2). set (nj := join_cursor_j j c2).
    set (tail := remaining_join rawsrc rawdst a1 a2 ni nj c1 c2).
    assert (Hcons : rest = List.app (if matched then [candidate_pair rawsrc rawdst a1 a2 i j] else nil) tail)
      by (apply remaining_join_cons; lia).
    assert (Hroom : matched = true -> out < 16).
    { intros E. fold rest in Hcap. rewrite Hcons, E in Hcap. cbn [List.app List.length] in Hcap. lia. }
    destruct (join_step_facts c rawsrc rawdst b out i j c1 c2 a1 a2 Hi Hj ltac:(fold rest in Hcap; destruct matched eqn:M; [specialize (Hroom eq_refl)|]; lia)
      Ha1 Ha2 HlS HlD Hroom Hic Hjc Hc1 Hc2 Ha1c Ha2c Hw)
      as [Pp [Pi [Pj [Pw [Ps [Pd [Pv [Pe Pc]]]]]]]].
    fold matched ni nj in Pp, Pi, Pj, Pw, Ps, Pd, Pv.
    cbn [join_iter].
    destruct (join_terminal i j c1 c2) eqn:Eterm.
    + destruct (join_terminal_cursors i j c1 c2 Eterm) as [Eni [Enj [Ei Ej]]].
      assert (n = 0) by (rewrite candidate_indices_length in Hn by lia; nia). subst n. cbn [join_iter].
      assert (Etail : tail = nil) by (unfold tail, ni, nj; rewrite Eni, Enj; apply remaining_join_terminal).
      fold rest. rewrite Hcons, Etail, app_nil_r.
      split; [intros m Hm; assert (m = 0) by lia; subst m; exact Hp|].
      split; [exact Pp|].
      unfold join_out, join_table, join_valid_table, candidate_pair, append_pair in *.
      destruct matched; cbn [List.length store_pairs loaded_valid fst snd].
      * rewrite Pw, Ps, Pd, Pv, Pe, Pc. repeat split; try reflexivity. f_equal. lia.
      * rewrite Pw, Ps, Pd, Pv, Pe, Pc. repeat split; try reflexivity. f_equal. lia.
    + destruct (join_next_bounds i j c1 c2 ltac:(lia) ltac:(lia) Eterm) as [Hni Hnj].
      assert (Hnn : List.length (candidate_indices ni nj c1 c2) = n).
      { rewrite candidate_indices_cons in Hn by lia. cbn [List.length] in Hn. apply Nat.succ_inj in Hn. exact Hn. }
      assert (Hcapn : join_out out matched + List.length tail <= 16).
      { fold rest in Hcap. rewrite Hcons in Hcap. unfold join_out. destruct matched; cbn [List.app List.length] in *; lia. }
      destruct (IH (mcjoin_next c) rawsrc rawdst b (join_out out matched) ni nj c1 c2 a1 a2 Hnn
        ltac:(unfold ni; lia) ltac:(unfold nj; lia) ltac:(unfold join_out; destruct matched; lia) Hcapn Ha1 Ha2
        ltac:(rewrite Ps; apply (join_table_preserves_low b out _ rawsrc _ matched ltac:(fold rest in Hcap; destruct matched; [specialize (Hroom eq_refl)|]; lia) Hroom HlS))
        ltac:(rewrite Pd; apply (join_table_preserves_low b out _ rawdst _ matched ltac:(fold rest in Hcap; destruct matched; [specialize (Hroom eq_refl)|]; lia) Hroom HlD))
        Pp Pi Pj ltac:(rewrite mcjoin_keeps_mc_src1_count; exact Hc1) ltac:(rewrite mcjoin_keeps_mc_src2_count; exact Hc2)
        ltac:(rewrite mcjoin_keeps_mc_src1_base; exact Ha1c) ltac:(rewrite mcjoin_keeps_mc_src2_base; exact Ha2c) Pw)
        as [Qm [Qp [Qw [Qs [Qd [Qv [Qe Qc]]]]]]].
      fold tail in Qw, Qs, Qd, Qv.
      split; [intros m Hm; destruct m as [|m]; [exact Hp|cbn [join_iter]; apply Qm; lia]|].
      split; [exact Qp|].
      fold rest. rewrite Hcons.
      rewrite Ps in Qs. rewrite Pd in Qd. rewrite Pv in Qv. rewrite Pe in Qe. rewrite Pc in Qc.
      unfold join_out, join_table, join_valid_table, candidate_pair, append_pair in *.
      destruct matched; cbn [List.app List.length store_pairs loaded_valid fst snd].
      * split; [rewrite Qw; f_equal; lia|]. split; [exact Qs|]. split; [exact Qd|]. split; [exact Qv|]. split; [exact Qe|exact Qc].
      * split; [exact Qw|]. split; [exact Qs|]. split; [exact Qd|]. split; [exact Qv|]. split; [exact Qe|exact Qc].
Qed.

Lemma join_multistep : forall n c,
  (forall m, m < n -> hw_mc_phase (join_iter m c) = natToWord 4 7) ->
  exists l, Multistep thieleCore (hwb_regs c) (hwb_regs (join_iter n c)) l.
Proof.
  induction n as [|n IH]; intros c H.
  - exists nil. constructor. reflexivity.
  - assert (G : evalExpr (((Var type (SyntaxKind (Bit 4)) (hw_mc_phase c)) == $$(WO~0~1~1~1)))%kami_expr = true).
    { cbn [evalExpr evalConstT]. change (hw_mc_phase c) with (hw_mc_phase (join_iter 0 c)). rewrite (H 0 ltac:(lia)). reflexivity. }
    destruct (mcjoin_enabled c G) as [u [Hu Eu]].
    destruct (IH (mcjoin_next c) ltac:(intros m Hm; exact (H (S m) ltac:(lia)))) as [l Hl].
    eexists. cbn [join_iter]. apply (normalization_multistep_trans _ (hwb_regs (mcjoin_next c))); [|exact Hl].
    rewrite <- Eu. apply normalization_substep_execution.
    exact (cpu_rule_substep _ _ _ (rule_in_index 6 ltac:(lia)) Hu).
Qed.
