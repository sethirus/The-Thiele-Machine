(** CouplingFsmCopy.v: the coupling copy loop at the typed boundary (COMPOSE
    with an identity side). [copy_run]: the firings append the remaining source
    pairs after the write pointer and end at phase 5; [copy_multistep]: they are
    an actual Kami execution. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep ActionEvaluator
  CoreRules CoreExecution NormalizationSteps NormalizationExecution NormalizationRetirement
  NormalizationLoop NormalizationPrefix MorphLoading MorphCopy RuleEnabled FsmDecoded ChshRetire
  CouplingFsmEnds CouplingFsmLoad CouplingFsmNorm.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** * One firing of the copy rule *)

Lemma mccopy_keeps_pc : forall c, hw_pc (mccopy_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mu : forall c, hw_mu (mccopy_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_halted : forall c, hw_halted (mccopy_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_regs : forall c, hw_regs (mccopy_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mem : forall c, hw_mem (mccopy_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_imem : forall c, hw_imem (mccopy_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_partition_ops : forall c, hw_partition_ops (mccopy_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mdl_ops : forall c, hw_mdl_ops (mccopy_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_info_gain : forall c, hw_info_gain (mccopy_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_logic_acc : forall c, hw_logic_acc (mccopy_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_cert_addr : forall c, hw_cert_addr (mccopy_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_active_module : forall c, hw_active_module (mccopy_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mstatus : forall c, hw_mstatus (mccopy_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mcycle_lo : forall c, hw_mcycle_lo (mccopy_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mcycle_hi : forall c, hw_mcycle_hi (mccopy_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_minstret_lo : forall c, hw_minstret_lo (mccopy_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_minstret_hi : forall c, hw_minstret_hi (mccopy_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_trap_vector : forall c, hw_trap_vector (mccopy_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_certified : forall c, hw_certified (mccopy_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_phase : forall c, hw_lassert_phase (mccopy_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_kind : forall c, hw_lassert_kind (mccopy_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_fbase : forall c, hw_lassert_fbase (mccopy_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_cbase : forall c, hw_lassert_cbase (mccopy_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_flen : forall c, hw_lassert_flen (mccopy_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_clen : forall c, hw_lassert_clen (mccopy_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_nvars : forall c, hw_lassert_nvars (mccopy_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_fptr : forall c, hw_lassert_fptr (mccopy_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_cptr : forall c, hw_lassert_cptr (mccopy_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mccopy_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mccopy_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mccopy_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mccopy_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mccopy_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_phase : forall c, hw_chsh_phase (mccopy_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n00 : forall c, hw_chsh_n00 (mccopy_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n01 : forall c, hw_chsh_n01 (mccopy_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n10 : forall c, hw_chsh_n10 (mccopy_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n11 : forall c, hw_chsh_n11 (mccopy_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d00 : forall c, hw_chsh_d00 (mccopy_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d01 : forall c, hw_chsh_d01 (mccopy_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d10 : forall c, hw_chsh_d10 (mccopy_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d11 : forall c, hw_chsh_d11 (mccopy_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mccopy_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mccopy_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mccopy_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mccopy_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mccopy_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mccopy_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mccopy_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mccopy_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mccopy_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mccopy_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mccopy_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mccopy_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mccopy_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mccopy_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mccopy_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mccopy_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mccopy_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mccopy_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mccopy_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mccopy_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mccopy_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mccopy_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mccopy_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mccopy_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mccopy_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mccopy_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_chsh_check_result : forall c, hw_chsh_check_result (mccopy_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mccopy_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mccopy_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mccopy_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mu_tensor : forall c, hw_mu_tensor (mccopy_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_module_tensors : forall c, hw_module_tensors (mccopy_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_csr_status : forall c, hw_csr_status (mccopy_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_csr_heap_base : forall c, hw_csr_heap_base (mccopy_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_ptTable : forall c, hw_ptTable (mccopy_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_pt_next_id : forall c, hw_pt_next_id (mccopy_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_morph_src_table : forall c, hw_morph_src_table (mccopy_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_morph_dst_table : forall c, hw_morph_dst_table (mccopy_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mccopy_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_morph_valid_table : forall c, hw_morph_valid_table (mccopy_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_morph_identity_table : forall c, hw_morph_identity_table (mccopy_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_morph_next_id : forall c, hw_morph_next_id (mccopy_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mccopy_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mccopy_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mccopy_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mccopy_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mccopy_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mccopy_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mccopy_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_op : forall c, hw_mc_op (mccopy_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_mem_base : forall c, hw_mc_mem_base (mccopy_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_pair_count : forall c, hw_mc_pair_count (mccopy_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (mccopy_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_src1_base : forall c, hw_mc_src1_base (mccopy_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_src1_count : forall c, hw_mc_src1_count (mccopy_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_src2_base : forall c, hw_mc_src2_base (mccopy_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_src2_count : forall c, hw_mc_src2_count (mccopy_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mccopy_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mccopy_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_write_base : forall c, hw_mc_write_base (mccopy_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (mccopy_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_duplicate : forall c, hw_mc_duplicate (mccopy_next c) = hw_mc_duplicate c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mccopy_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mccopy_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mccopy_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mccopy_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_mc_cost : forall c, hw_mc_cost (mccopy_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mccopy_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mccopy_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mccopy_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mccopy_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mccopy_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mccopy_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mccopy_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mccopy_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mccopy_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mccopy_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mccopy_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mccopy_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mccopy_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mccopy_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_same_00 : forall c, hw_wc_same_00 (mccopy_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mccopy_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_same_01 : forall c, hw_wc_same_01 (mccopy_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mccopy_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_same_10 : forall c, hw_wc_same_10 (mccopy_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mccopy_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_same_11 : forall c, hw_wc_same_11 (mccopy_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mccopy_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mccopy_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Definition ccopy_done (c : HWB) := copy_done (hw_mc_i c) (hw_mc_j c) (hw_mc_src1_count c) (hw_mc_src2_count c).
Definition ccopy_blocked (c : HWB) := orb (ccopy_done c) (copy_full (hw_mc_write_ptr c)).
Definition ccopy_overflow (c : HWB) := andb (negb (ccopy_done c)) (copy_full (hw_mc_write_ptr c)).
Definition ccopy_index (c : HWB) :=
  copy_index (hw_mc_i c) (hw_mc_j c) (hw_mc_src1_count c) (hw_mc_src1_base c) (hw_mc_src2_base c).

Lemma mccopy_src : forall c, hw_coupling_pair_src_table (mccopy_next c) =
  if ccopy_blocked c then hw_coupling_pair_src_table c
  else put_vector (hw_coupling_pair_src_table c) (pair_index (hw_mc_write_ptr c)) (hw_coupling_pair_src_table c (ccopy_index c)).
Proof. reflexivity. Qed.
Lemma mccopy_dst : forall c, hw_coupling_pair_dst_table (mccopy_next c) =
  if ccopy_blocked c then hw_coupling_pair_dst_table c
  else put_vector (hw_coupling_pair_dst_table c) (pair_index (hw_mc_write_ptr c)) (hw_coupling_pair_dst_table c (ccopy_index c)).
Proof. reflexivity. Qed.
Lemma mccopy_valid : forall c, hw_coupling_pair_valid_table (mccopy_next c) =
  if ccopy_blocked c then hw_coupling_pair_valid_table c
  else put_vector (hw_coupling_pair_valid_table c) (pair_index (hw_mc_write_ptr c)) true.
Proof. reflexivity. Qed.
Lemma mccopy_i : forall c, hw_mc_i (mccopy_next c) =
  if copy_first (hw_mc_i c) (hw_mc_src1_count c) then wplus (hw_mc_i c) (natToWord 5 1) else hw_mc_i c.
Proof. reflexivity. Qed.
Lemma mccopy_j : forall c, hw_mc_j (mccopy_next c) =
  if copy_first (hw_mc_i c) (hw_mc_src1_count c) then hw_mc_j c else wplus (hw_mc_j c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mccopy_write_ptr : forall c, hw_mc_write_ptr (mccopy_next c) =
  if ccopy_blocked c then hw_mc_write_ptr c else wplus (hw_mc_write_ptr c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mccopy_phase : forall c, hw_mc_phase (mccopy_next c) =
  if ccopy_overflow c then natToWord 4 0 else if ccopy_done c then natToWord 4 5 else natToWord 4 4.
Proof. reflexivity. Qed.
Lemma mccopy_err : forall c, hw_err (mccopy_next c) = orb (hw_err c) (ccopy_overflow c).
Proof. reflexivity. Qed.
Lemma mccopy_error_code : forall c, hw_error_code (mccopy_next c) =
  if ccopy_overflow c then ERR_COUPLING_INVALID else hw_error_code c.
Proof. reflexivity. Qed.

Fixpoint copy_iter (n : nat) (c : HWB) : HWB :=
  match n with
  | O => c
  | S m => copy_iter m (mccopy_next c)
  end.

Lemma copy_iter_keeps_pc : forall n c, hw_pc (copy_iter n c) = hw_pc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_pc]. Qed.
Lemma copy_iter_keeps_mu : forall n c, hw_mu (copy_iter n c) = hw_mu c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mu]. Qed.
Lemma copy_iter_keeps_halted : forall n c, hw_halted (copy_iter n c) = hw_halted c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_halted]. Qed.
Lemma copy_iter_keeps_regs : forall n c, hw_regs (copy_iter n c) = hw_regs c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_regs]. Qed.
Lemma copy_iter_keeps_mem : forall n c, hw_mem (copy_iter n c) = hw_mem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mem]. Qed.
Lemma copy_iter_keeps_imem : forall n c, hw_imem (copy_iter n c) = hw_imem c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_imem]. Qed.
Lemma copy_iter_keeps_partition_ops : forall n c, hw_partition_ops (copy_iter n c) = hw_partition_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_partition_ops]. Qed.
Lemma copy_iter_keeps_mdl_ops : forall n c, hw_mdl_ops (copy_iter n c) = hw_mdl_ops c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mdl_ops]. Qed.
Lemma copy_iter_keeps_info_gain : forall n c, hw_info_gain (copy_iter n c) = hw_info_gain c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_info_gain]. Qed.
Lemma copy_iter_keeps_logic_acc : forall n c, hw_logic_acc (copy_iter n c) = hw_logic_acc c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_logic_acc]. Qed.
Lemma copy_iter_keeps_cert_addr : forall n c, hw_cert_addr (copy_iter n c) = hw_cert_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_cert_addr]. Qed.
Lemma copy_iter_keeps_active_module : forall n c, hw_active_module (copy_iter n c) = hw_active_module c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_active_module]. Qed.
Lemma copy_iter_keeps_mstatus : forall n c, hw_mstatus (copy_iter n c) = hw_mstatus c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mstatus]. Qed.
Lemma copy_iter_keeps_mcycle_lo : forall n c, hw_mcycle_lo (copy_iter n c) = hw_mcycle_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mcycle_lo]. Qed.
Lemma copy_iter_keeps_mcycle_hi : forall n c, hw_mcycle_hi (copy_iter n c) = hw_mcycle_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mcycle_hi]. Qed.
Lemma copy_iter_keeps_minstret_lo : forall n c, hw_minstret_lo (copy_iter n c) = hw_minstret_lo c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_minstret_lo]. Qed.
Lemma copy_iter_keeps_minstret_hi : forall n c, hw_minstret_hi (copy_iter n c) = hw_minstret_hi c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_minstret_hi]. Qed.
Lemma copy_iter_keeps_trap_vector : forall n c, hw_trap_vector (copy_iter n c) = hw_trap_vector c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_trap_vector]. Qed.
Lemma copy_iter_keeps_certified : forall n c, hw_certified (copy_iter n c) = hw_certified c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_certified]. Qed.
Lemma copy_iter_keeps_lassert_phase : forall n c, hw_lassert_phase (copy_iter n c) = hw_lassert_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_phase]. Qed.
Lemma copy_iter_keeps_lassert_kind : forall n c, hw_lassert_kind (copy_iter n c) = hw_lassert_kind c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_kind]. Qed.
Lemma copy_iter_keeps_lassert_fbase : forall n c, hw_lassert_fbase (copy_iter n c) = hw_lassert_fbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_fbase]. Qed.
Lemma copy_iter_keeps_lassert_cbase : forall n c, hw_lassert_cbase (copy_iter n c) = hw_lassert_cbase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_cbase]. Qed.
Lemma copy_iter_keeps_lassert_flen : forall n c, hw_lassert_flen (copy_iter n c) = hw_lassert_flen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_flen]. Qed.
Lemma copy_iter_keeps_lassert_clen : forall n c, hw_lassert_clen (copy_iter n c) = hw_lassert_clen c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_clen]. Qed.
Lemma copy_iter_keeps_lassert_nvars : forall n c, hw_lassert_nvars (copy_iter n c) = hw_lassert_nvars c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_nvars]. Qed.
Lemma copy_iter_keeps_lassert_fptr : forall n c, hw_lassert_fptr (copy_iter n c) = hw_lassert_fptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_fptr]. Qed.
Lemma copy_iter_keeps_lassert_cptr : forall n c, hw_lassert_cptr (copy_iter n c) = hw_lassert_cptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_cptr]. Qed.
Lemma copy_iter_keeps_lassert_fbuf : forall n c, hw_lassert_fbuf (copy_iter n c) = hw_lassert_fbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_fbuf]. Qed.
Lemma copy_iter_keeps_lassert_cbuf : forall n c, hw_lassert_cbuf (copy_iter n c) = hw_lassert_cbuf c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_cbuf]. Qed.
Lemma copy_iter_keeps_lassert_clause_sat : forall n c, hw_lassert_clause_sat (copy_iter n c) = hw_lassert_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_clause_sat]. Qed.
Lemma copy_iter_keeps_lassert_counter_clause_sat : forall n c, hw_lassert_counter_clause_sat (copy_iter n c) = hw_lassert_counter_clause_sat c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_counter_clause_sat]. Qed.
Lemma copy_iter_keeps_lassert_counter_seen_fail : forall n c, hw_lassert_counter_seen_fail (copy_iter n c) = hw_lassert_counter_seen_fail c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_lassert_counter_seen_fail]. Qed.
Lemma copy_iter_keeps_chsh_phase : forall n c, hw_chsh_phase (copy_iter n c) = hw_chsh_phase c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_phase]. Qed.
Lemma copy_iter_keeps_chsh_n00 : forall n c, hw_chsh_n00 (copy_iter n c) = hw_chsh_n00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n00]. Qed.
Lemma copy_iter_keeps_chsh_n01 : forall n c, hw_chsh_n01 (copy_iter n c) = hw_chsh_n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n01]. Qed.
Lemma copy_iter_keeps_chsh_n10 : forall n c, hw_chsh_n10 (copy_iter n c) = hw_chsh_n10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n10]. Qed.
Lemma copy_iter_keeps_chsh_n11 : forall n c, hw_chsh_n11 (copy_iter n c) = hw_chsh_n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n11]. Qed.
Lemma copy_iter_keeps_chsh_d00 : forall n c, hw_chsh_d00 (copy_iter n c) = hw_chsh_d00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d00]. Qed.
Lemma copy_iter_keeps_chsh_d01 : forall n c, hw_chsh_d01 (copy_iter n c) = hw_chsh_d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d01]. Qed.
Lemma copy_iter_keeps_chsh_d10 : forall n c, hw_chsh_d10 (copy_iter n c) = hw_chsh_d10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d10]. Qed.
Lemma copy_iter_keeps_chsh_d11 : forall n c, hw_chsh_d11 (copy_iter n c) = hw_chsh_d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d11]. Qed.
Lemma copy_iter_keeps_chsh_sign00 : forall n c, hw_chsh_sign00 (copy_iter n c) = hw_chsh_sign00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_sign00]. Qed.
Lemma copy_iter_keeps_chsh_sign01 : forall n c, hw_chsh_sign01 (copy_iter n c) = hw_chsh_sign01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_sign01]. Qed.
Lemma copy_iter_keeps_chsh_sign10 : forall n c, hw_chsh_sign10 (copy_iter n c) = hw_chsh_sign10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_sign10]. Qed.
Lemma copy_iter_keeps_chsh_sign11 : forall n c, hw_chsh_sign11 (copy_iter n c) = hw_chsh_sign11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_sign11]. Qed.
Lemma copy_iter_keeps_chsh_n00sq : forall n c, hw_chsh_n00sq (copy_iter n c) = hw_chsh_n00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n00sq]. Qed.
Lemma copy_iter_keeps_chsh_n01sq : forall n c, hw_chsh_n01sq (copy_iter n c) = hw_chsh_n01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n01sq]. Qed.
Lemma copy_iter_keeps_chsh_n10sq : forall n c, hw_chsh_n10sq (copy_iter n c) = hw_chsh_n10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n10sq]. Qed.
Lemma copy_iter_keeps_chsh_n11sq : forall n c, hw_chsh_n11sq (copy_iter n c) = hw_chsh_n11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n11sq]. Qed.
Lemma copy_iter_keeps_chsh_d00sq : forall n c, hw_chsh_d00sq (copy_iter n c) = hw_chsh_d00sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d00sq]. Qed.
Lemma copy_iter_keeps_chsh_d01sq : forall n c, hw_chsh_d01sq (copy_iter n c) = hw_chsh_d01sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d01sq]. Qed.
Lemma copy_iter_keeps_chsh_d10sq : forall n c, hw_chsh_d10sq (copy_iter n c) = hw_chsh_d10sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d10sq]. Qed.
Lemma copy_iter_keeps_chsh_d11sq : forall n c, hw_chsh_d11sq (copy_iter n c) = hw_chsh_d11sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d11sq]. Qed.
Lemma copy_iter_keeps_chsh_A_pos : forall n c, hw_chsh_A_pos (copy_iter n c) = hw_chsh_A_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_A_pos]. Qed.
Lemma copy_iter_keeps_chsh_A_neg_a : forall n c, hw_chsh_A_neg_a (copy_iter n c) = hw_chsh_A_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_A_neg_a]. Qed.
Lemma copy_iter_keeps_chsh_A_neg_b : forall n c, hw_chsh_A_neg_b (copy_iter n c) = hw_chsh_A_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_A_neg_b]. Qed.
Lemma copy_iter_keeps_chsh_B_pos : forall n c, hw_chsh_B_pos (copy_iter n c) = hw_chsh_B_pos c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_B_pos]. Qed.
Lemma copy_iter_keeps_chsh_B_neg_a : forall n c, hw_chsh_B_neg_a (copy_iter n c) = hw_chsh_B_neg_a c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_B_neg_a]. Qed.
Lemma copy_iter_keeps_chsh_B_neg_b : forall n c, hw_chsh_B_neg_b (copy_iter n c) = hw_chsh_B_neg_b c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_B_neg_b]. Qed.
Lemma copy_iter_keeps_chsh_d00d01 : forall n c, hw_chsh_d00d01 (copy_iter n c) = hw_chsh_d00d01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d00d01]. Qed.
Lemma copy_iter_keeps_chsh_n10n11 : forall n c, hw_chsh_n10n11 (copy_iter n c) = hw_chsh_n10n11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n10n11]. Qed.
Lemma copy_iter_keeps_chsh_d10d11 : forall n c, hw_chsh_d10d11 (copy_iter n c) = hw_chsh_d10d11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_d10d11]. Qed.
Lemma copy_iter_keeps_chsh_n00n01 : forall n c, hw_chsh_n00n01 (copy_iter n c) = hw_chsh_n00n01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_n00n01]. Qed.
Lemma copy_iter_keeps_chsh_abs_C1 : forall n c, hw_chsh_abs_C1 (copy_iter n c) = hw_chsh_abs_C1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_abs_C1]. Qed.
Lemma copy_iter_keeps_chsh_abs_C2 : forall n c, hw_chsh_abs_C2 (copy_iter n c) = hw_chsh_abs_C2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_abs_C2]. Qed.
Lemma copy_iter_keeps_chsh_C_sq : forall n c, hw_chsh_C_sq (copy_iter n c) = hw_chsh_C_sq c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_C_sq]. Qed.
Lemma copy_iter_keeps_chsh_A_times_B : forall n c, hw_chsh_A_times_B (copy_iter n c) = hw_chsh_A_times_B c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_A_times_B]. Qed.
Lemma copy_iter_keeps_chsh_check_result : forall n c, hw_chsh_check_result (copy_iter n c) = hw_chsh_check_result c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_chsh_check_result]. Qed.
Lemma copy_iter_keeps_bus_load_instr_addr : forall n c, hw_bus_load_instr_addr (copy_iter n c) = hw_bus_load_instr_addr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_bus_load_instr_addr]. Qed.
Lemma copy_iter_keeps_bus_load_instr_data : forall n c, hw_bus_load_instr_data (copy_iter n c) = hw_bus_load_instr_data c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_bus_load_instr_data]. Qed.
Lemma copy_iter_keeps_bus_load_instr_kick : forall n c, hw_bus_load_instr_kick (copy_iter n c) = hw_bus_load_instr_kick c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_bus_load_instr_kick]. Qed.
Lemma copy_iter_keeps_mu_tensor : forall n c, hw_mu_tensor (copy_iter n c) = hw_mu_tensor c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mu_tensor]. Qed.
Lemma copy_iter_keeps_module_tensors : forall n c, hw_module_tensors (copy_iter n c) = hw_module_tensors c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_module_tensors]. Qed.
Lemma copy_iter_keeps_csr_status : forall n c, hw_csr_status (copy_iter n c) = hw_csr_status c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_csr_status]. Qed.
Lemma copy_iter_keeps_csr_heap_base : forall n c, hw_csr_heap_base (copy_iter n c) = hw_csr_heap_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_csr_heap_base]. Qed.
Lemma copy_iter_keeps_ptTable : forall n c, hw_ptTable (copy_iter n c) = hw_ptTable c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_ptTable]. Qed.
Lemma copy_iter_keeps_pt_next_id : forall n c, hw_pt_next_id (copy_iter n c) = hw_pt_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_pt_next_id]. Qed.
Lemma copy_iter_keeps_morph_src_table : forall n c, hw_morph_src_table (copy_iter n c) = hw_morph_src_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_morph_src_table]. Qed.
Lemma copy_iter_keeps_morph_dst_table : forall n c, hw_morph_dst_table (copy_iter n c) = hw_morph_dst_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_morph_dst_table]. Qed.
Lemma copy_iter_keeps_morph_coupling_desc_table : forall n c, hw_morph_coupling_desc_table (copy_iter n c) = hw_morph_coupling_desc_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_morph_coupling_desc_table]. Qed.
Lemma copy_iter_keeps_morph_valid_table : forall n c, hw_morph_valid_table (copy_iter n c) = hw_morph_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_morph_valid_table]. Qed.
Lemma copy_iter_keeps_morph_identity_table : forall n c, hw_morph_identity_table (copy_iter n c) = hw_morph_identity_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_morph_identity_table]. Qed.
Lemma copy_iter_keeps_morph_next_id : forall n c, hw_morph_next_id (copy_iter n c) = hw_morph_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_morph_next_id]. Qed.
Lemma copy_iter_keeps_coupling_desc_base_table : forall n c, hw_coupling_desc_base_table (copy_iter n c) = hw_coupling_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_desc_base_table]. Qed.
Lemma copy_iter_keeps_coupling_desc_count_table : forall n c, hw_coupling_desc_count_table (copy_iter n c) = hw_coupling_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_desc_count_table]. Qed.
Lemma copy_iter_keeps_coupling_desc_valid_table : forall n c, hw_coupling_desc_valid_table (copy_iter n c) = hw_coupling_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_desc_valid_table]. Qed.
Lemma copy_iter_keeps_coupling_desc_label_table : forall n c, hw_coupling_desc_label_table (copy_iter n c) = hw_coupling_desc_label_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_desc_label_table]. Qed.
Lemma copy_iter_keeps_coupling_desc_label_len_table : forall n c, hw_coupling_desc_label_len_table (copy_iter n c) = hw_coupling_desc_label_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_desc_label_len_table]. Qed.
Lemma copy_iter_keeps_coupling_desc_next_id : forall n c, hw_coupling_desc_next_id (copy_iter n c) = hw_coupling_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_desc_next_id]. Qed.
Lemma copy_iter_keeps_coupling_pair_next_id : forall n c, hw_coupling_pair_next_id (copy_iter n c) = hw_coupling_pair_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_coupling_pair_next_id]. Qed.
Lemma copy_iter_keeps_mc_op : forall n c, hw_mc_op (copy_iter n c) = hw_mc_op c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_op]. Qed.
Lemma copy_iter_keeps_mc_mem_base : forall n c, hw_mc_mem_base (copy_iter n c) = hw_mc_mem_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_mem_base]. Qed.
Lemma copy_iter_keeps_mc_pair_count : forall n c, hw_mc_pair_count (copy_iter n c) = hw_mc_pair_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_pair_count]. Qed.
Lemma copy_iter_keeps_mc_read_ptr : forall n c, hw_mc_read_ptr (copy_iter n c) = hw_mc_read_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_read_ptr]. Qed.
Lemma copy_iter_keeps_mc_src1_base : forall n c, hw_mc_src1_base (copy_iter n c) = hw_mc_src1_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_src1_base]. Qed.
Lemma copy_iter_keeps_mc_src1_count : forall n c, hw_mc_src1_count (copy_iter n c) = hw_mc_src1_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_src1_count]. Qed.
Lemma copy_iter_keeps_mc_src2_base : forall n c, hw_mc_src2_base (copy_iter n c) = hw_mc_src2_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_src2_base]. Qed.
Lemma copy_iter_keeps_mc_src2_count : forall n c, hw_mc_src2_count (copy_iter n c) = hw_mc_src2_count c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_src2_count]. Qed.
Lemma copy_iter_keeps_mc_is_id1 : forall n c, hw_mc_is_id1 (copy_iter n c) = hw_mc_is_id1 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_is_id1]. Qed.
Lemma copy_iter_keeps_mc_is_id2 : forall n c, hw_mc_is_id2 (copy_iter n c) = hw_mc_is_id2 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_is_id2]. Qed.
Lemma copy_iter_keeps_mc_write_base : forall n c, hw_mc_write_base (copy_iter n c) = hw_mc_write_base c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_write_base]. Qed.
Lemma copy_iter_keeps_mc_norm_ptr : forall n c, hw_mc_norm_ptr (copy_iter n c) = hw_mc_norm_ptr c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_norm_ptr]. Qed.
Lemma copy_iter_keeps_mc_duplicate : forall n c, hw_mc_duplicate (copy_iter n c) = hw_mc_duplicate c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_duplicate]. Qed.
Lemma copy_iter_keeps_mc_dst_reg : forall n c, hw_mc_dst_reg (copy_iter n c) = hw_mc_dst_reg c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_dst_reg]. Qed.
Lemma copy_iter_keeps_mc_morph_slot : forall n c, hw_mc_morph_slot (copy_iter n c) = hw_mc_morph_slot c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_morph_slot]. Qed.
Lemma copy_iter_keeps_mc_new_src_mod : forall n c, hw_mc_new_src_mod (copy_iter n c) = hw_mc_new_src_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_new_src_mod]. Qed.
Lemma copy_iter_keeps_mc_new_dst_mod : forall n c, hw_mc_new_dst_mod (copy_iter n c) = hw_mc_new_dst_mod c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_new_dst_mod]. Qed.
Lemma copy_iter_keeps_mc_cost : forall n c, hw_mc_cost (copy_iter n c) = hw_mc_cost c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_mc_cost]. Qed.
Lemma copy_iter_keeps_formula_desc_base_table : forall n c, hw_formula_desc_base_table (copy_iter n c) = hw_formula_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_formula_desc_base_table]. Qed.
Lemma copy_iter_keeps_formula_desc_count_table : forall n c, hw_formula_desc_count_table (copy_iter n c) = hw_formula_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_formula_desc_count_table]. Qed.
Lemma copy_iter_keeps_formula_desc_valid_table : forall n c, hw_formula_desc_valid_table (copy_iter n c) = hw_formula_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_formula_desc_valid_table]. Qed.
Lemma copy_iter_keeps_formula_desc_next_id : forall n c, hw_formula_desc_next_id (copy_iter n c) = hw_formula_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_formula_desc_next_id]. Qed.
Lemma copy_iter_keeps_cert_desc_base_table : forall n c, hw_cert_desc_base_table (copy_iter n c) = hw_cert_desc_base_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_cert_desc_base_table]. Qed.
Lemma copy_iter_keeps_cert_desc_count_table : forall n c, hw_cert_desc_count_table (copy_iter n c) = hw_cert_desc_count_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_cert_desc_count_table]. Qed.
Lemma copy_iter_keeps_cert_desc_valid_table : forall n c, hw_cert_desc_valid_table (copy_iter n c) = hw_cert_desc_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_cert_desc_valid_table]. Qed.
Lemma copy_iter_keeps_cert_desc_next_id : forall n c, hw_cert_desc_next_id (copy_iter n c) = hw_cert_desc_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_cert_desc_next_id]. Qed.
Lemma copy_iter_keeps_desc_meta_subtype_table : forall n c, hw_desc_meta_subtype_table (copy_iter n c) = hw_desc_meta_subtype_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_desc_meta_subtype_table]. Qed.
Lemma copy_iter_keeps_desc_meta_kind_table : forall n c, hw_desc_meta_kind_table (copy_iter n c) = hw_desc_meta_kind_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_desc_meta_kind_table]. Qed.
Lemma copy_iter_keeps_desc_meta_inline_len_table : forall n c, hw_desc_meta_inline_len_table (copy_iter n c) = hw_desc_meta_inline_len_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_desc_meta_inline_len_table]. Qed.
Lemma copy_iter_keeps_desc_meta_aux_table : forall n c, hw_desc_meta_aux_table (copy_iter n c) = hw_desc_meta_aux_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_desc_meta_aux_table]. Qed.
Lemma copy_iter_keeps_desc_meta_valid_table : forall n c, hw_desc_meta_valid_table (copy_iter n c) = hw_desc_meta_valid_table c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_desc_meta_valid_table]. Qed.
Lemma copy_iter_keeps_desc_meta_next_id : forall n c, hw_desc_meta_next_id (copy_iter n c) = hw_desc_meta_next_id c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_desc_meta_next_id]. Qed.
Lemma copy_iter_keeps_wc_same_00 : forall n c, hw_wc_same_00 (copy_iter n c) = hw_wc_same_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_same_00]. Qed.
Lemma copy_iter_keeps_wc_diff_00 : forall n c, hw_wc_diff_00 (copy_iter n c) = hw_wc_diff_00 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_diff_00]. Qed.
Lemma copy_iter_keeps_wc_same_01 : forall n c, hw_wc_same_01 (copy_iter n c) = hw_wc_same_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_same_01]. Qed.
Lemma copy_iter_keeps_wc_diff_01 : forall n c, hw_wc_diff_01 (copy_iter n c) = hw_wc_diff_01 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_diff_01]. Qed.
Lemma copy_iter_keeps_wc_same_10 : forall n c, hw_wc_same_10 (copy_iter n c) = hw_wc_same_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_same_10]. Qed.
Lemma copy_iter_keeps_wc_diff_10 : forall n c, hw_wc_diff_10 (copy_iter n c) = hw_wc_diff_10 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_diff_10]. Qed.
Lemma copy_iter_keeps_wc_same_11 : forall n c, hw_wc_same_11 (copy_iter n c) = hw_wc_same_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_same_11]. Qed.
Lemma copy_iter_keeps_wc_diff_11 : forall n c, hw_wc_diff_11 (copy_iter n c) = hw_wc_diff_11 c.
Proof. induction n as [|n IH]; intro c; [reflexivity|cbn [copy_iter]; rewrite IH; apply mccopy_keeps_wc_diff_11]. Qed.

(** * The copy loop *)

Theorem copy_run : forall n c rawsrc rawdst b out i j c1 c2 a1 a2,
  c1 - i + (c2 - j) = n -> i <= c1 <= 16 -> j <= c2 <= 16 -> b <= out -> out + n <= 16 ->
  a1 + c1 <= b -> a2 + c2 <= b ->
  low_agrees b (hw_coupling_pair_src_table c) rawsrc -> low_agrees b (hw_coupling_pair_dst_table c) rawdst ->
  hw_mc_phase c = natToWord 4 4 -> hw_mc_i c = natToWord 5 i -> hw_mc_j c = natToWord 5 j ->
  hw_mc_src1_count c = natToWord 5 c1 -> hw_mc_src2_count c = natToWord 5 c2 ->
  hw_mc_src1_base c = natToWord 4 a1 -> hw_mc_src2_base c = natToWord 4 a2 ->
  hw_mc_write_ptr c = natToWord 5 out ->
  (forall m, m <= n -> hw_mc_phase (copy_iter m c) = natToWord 4 4) /\
  hw_mc_phase (copy_iter (S n) c) = natToWord 4 5 /\
  hw_mc_write_ptr (copy_iter (S n) c) = natToWord 5 (out + n) /\
  hw_coupling_pair_src_table (copy_iter (S n) c) =
    store_pairs (hw_coupling_pair_src_table c) out (remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j) true /\
  hw_coupling_pair_dst_table (copy_iter (S n) c) =
    store_pairs (hw_coupling_pair_dst_table c) out (remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j) false /\
  hw_coupling_pair_valid_table (copy_iter (S n) c) = loaded_valid out n (hw_coupling_pair_valid_table c) /\
  hw_err (copy_iter (S n) c) = hw_err c /\ hw_error_code (copy_iter (S n) c) = hw_error_code c.
Proof.
  induction n as [|n IH]; intros c rawsrc rawdst b out i j c1 c2 a1 a2 Hn Hi Hj Hb Hsp Ha1 Ha2 HlS HlD
    Hp Hic Hjc Hc1 Hc2 Ha1c Ha2c Hw.
  - assert (i = c1) by lia. assert (j = c2) by lia. subst i j.
    assert (D : ccopy_done c = true) by (unfold ccopy_done; rewrite Hic, Hjc, Hc1, Hc2; apply copy_done_control; lia).
    assert (B : ccopy_blocked c = true) by (unfold ccopy_blocked; rewrite D; reflexivity).
    assert (O : ccopy_overflow c = false) by (unfold ccopy_overflow; rewrite D; reflexivity).
    cbn [copy_iter].
    split; [intros m Hm; assert (m = 0) by lia; subst m; exact Hp|].
    rewrite mccopy_phase, O, D. split; [reflexivity|].
    rewrite mccopy_write_ptr, B, Hw, Nat.add_0_r. split; [reflexivity|].
    unfold remaining_pairs. rewrite !Nat.sub_diag. cbn [table_slice seq map List.app store_pairs loaded_valid].
    rewrite mccopy_src, mccopy_dst, mccopy_valid, B. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite mccopy_err, mccopy_error_code, O, orb_false_r. split; reflexivity.
  - assert (Hactive : i < c1 \/ j < c2) by lia.
    assert (D : ccopy_done c = false).
    { unfold ccopy_done. rewrite Hic, Hjc, Hc1, Hc2. destruct (Nat.lt_ge_cases i c1).
      - apply copy_active_first_control; lia.
      - assert (i = c1) by lia. subst. apply copy_active_second_control; lia. }
    assert (F : copy_full (hw_mc_write_ptr c) = false) by (rewrite Hw, copy_full_nat by lia; apply Nat.eqb_neq; lia).
    assert (B : ccopy_blocked c = false) by (unfold ccopy_blocked; rewrite D, F; reflexivity).
    assert (O : ccopy_overflow c = false) by (unfold ccopy_overflow; rewrite D, F; reflexivity).
    set (idx := source_index i j c1 a1 a2).
    assert (Hidx : idx < b) by (unfold idx, source_index; destruct (Nat.ltb_spec i c1); lia).
    assert (I : ccopy_index c = pair_index (natToWord 5 idx)).
    { unfold ccopy_index, idx, source_index. rewrite Hic, Hjc, Hc1, Ha1c, Ha2c.
      destruct (Nat.ltb_spec i c1) as [L|L].
      - apply copy_index_first_nat; lia.
      - eapply copy_index_second_nat with (c2 := c2); lia. }
    assert (S1 : hw_coupling_pair_src_table (mccopy_next c) =
      append_pair (hw_coupling_pair_src_table c) out (pair_at rawsrc idx)).
    { rewrite mccopy_src, B, I, Hw. unfold append_pair. f_equal. exact (HlS idx Hidx). }
    assert (D1 : hw_coupling_pair_dst_table (mccopy_next c) =
      append_pair (hw_coupling_pair_dst_table c) out (pair_at rawdst idx)).
    { rewrite mccopy_dst, B, I, Hw. unfold append_pair. f_equal. exact (HlD idx Hidx). }
    assert (FirstE : copy_first (hw_mc_i c) (hw_mc_src1_count c) = Nat.ltb i c1)
      by (rewrite Hic, Hc1; apply copy_first_nat; lia).
    destruct (IH (mccopy_next c) rawsrc rawdst b (S out) (cursor_i i c1) (cursor_j i j c1) c1 c2 a1 a2)
      as [Pm [Pp [Pw [Ps [Pd [Pv [Pe Pc]]]]]]].
    + unfold cursor_i, cursor_j. destruct (Nat.ltb_spec i c1); lia.
    + unfold cursor_i. destruct (Nat.ltb_spec i c1); lia.
    + unfold cursor_j. destruct (Nat.ltb_spec i c1); lia.
    + lia.
    + lia.
    + exact Ha1.
    + exact Ha2.
    + rewrite S1. apply append_pair_preserves_low; [lia|exact HlS].
    + rewrite D1. apply append_pair_preserves_low; [lia|exact HlD].
    + rewrite mccopy_phase, O, D. reflexivity.
    + rewrite mccopy_i, FirstE, Hic. unfold cursor_i. destruct (Nat.ltb i c1); [apply succ_word5|reflexivity].
    + rewrite mccopy_j, FirstE, Hjc. unfold cursor_j. destruct (Nat.ltb i c1); [reflexivity|apply succ_word5].
    + rewrite mccopy_keeps_mc_src1_count. exact Hc1.
    + rewrite mccopy_keeps_mc_src2_count. exact Hc2.
    + rewrite mccopy_keeps_mc_src1_base. exact Ha1c.
    + rewrite mccopy_keeps_mc_src2_base. exact Ha2c.
    + rewrite mccopy_write_ptr, B, Hw. apply succ_word5.
    + split; [intros m Hm; destruct m as [|m]; [exact Hp|cbn [copy_iter]; apply Pm; lia]|].
      cbn [copy_iter] in Pp, Pw, Ps, Pd, Pv, Pe, Pc |- *.
      split; [exact Pp|]. split; [rewrite Pw; f_equal; lia|].
      rewrite (remaining_pairs_cons rawsrc rawdst a1 c1 a2 c2 i j) by lia.
      rewrite S1 in Ps. rewrite D1 in Pd. rewrite mccopy_valid, B, Hw in Pv.
      cbn [store_pairs loaded_valid]. fold idx. unfold table_pair. cbn [fst snd].
      split; [exact Ps|]. split; [exact Pd|]. split; [exact Pv|].
      rewrite Pe, Pc, mccopy_err, mccopy_error_code, O, orb_false_r. split; reflexivity.
Qed.

Lemma copy_multistep : forall n c,
  (forall m, m < n -> hw_mc_phase (copy_iter m c) = natToWord 4 4) ->
  exists l, Multistep thieleCore (hwb_regs c) (hwb_regs (copy_iter n c)) l.
Proof.
  induction n as [|n IH]; intros c H.
  - exists nil. constructor. reflexivity.
  - assert (G : evalExpr (((Var type (SyntaxKind (Bit 4)) (hw_mc_phase c)) == $$(WO~0~1~0~0)))%kami_expr = true).
    { cbn [evalExpr evalConstT]. change (hw_mc_phase c) with (hw_mc_phase (copy_iter 0 c)). rewrite (H 0 ltac:(lia)). reflexivity. }
    destruct (mccopy_enabled c G) as [u [Hu Eu]].
    destruct (IH (mccopy_next c) ltac:(intros m Hm; exact (H (S m) ltac:(lia)))) as [l Hl].
    eexists. cbn [copy_iter]. apply (normalization_multistep_trans _ (hwb_regs (mccopy_next c))); [|exact Hl].
    rewrite <- Eu. apply normalization_substep_execution.
    exact (cpu_rule_substep _ _ _ (rule_in_index 5 ltac:(lia)) Hu).
Qed.
