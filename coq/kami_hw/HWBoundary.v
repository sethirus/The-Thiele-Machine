(** HWBoundary.v: a typed record with one field per register of the actual
    CPU [thieleCore], generated from the register declarations of
    ThieleCPUCore.v, and its Kami register map.  Every field is an arbitrary
    value of the declared kind; no invariant is imposed here. *)

Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore.
From Coq Require Import String List.
Import ListNotations.
Open Scope string_scope.

Record HWB := {
  hw_pc : type (Bit WordSz);
  hw_mu : type (Bit WordSz);
  hw_err : type (Bool);
  hw_halted : type (Bool);
  hw_regs : type (Vector (Bit WordSz) RegIdxSz);
  hw_mem : type (Vector (Bit WordSz) MemAddrSz);
  hw_imem : type (Vector (Bit InstrSz) MemAddrSz);
  hw_partition_ops : type (Bit WordSz);
  hw_mdl_ops : type (Bit WordSz);
  hw_info_gain : type (Bit WordSz);
  hw_error_code : type (Bit WordSz);
  hw_logic_acc : type (Bit WordSz);
  hw_cert_addr : type (Bit WordSz);
  hw_active_module : type (Bit PTableIdxSz);
  hw_mstatus : type (Bit WordSz);
  hw_mcycle_lo : type (Bit WordSz);
  hw_mcycle_hi : type (Bit WordSz);
  hw_minstret_lo : type (Bit WordSz);
  hw_minstret_hi : type (Bit WordSz);
  hw_trap_vector : type (Bit WordSz);
  hw_certified : type (Bool);
  hw_lassert_phase : type (Bit 3);
  hw_lassert_kind : type (Bool);
  hw_lassert_fbase : type (Bit WordSz);
  hw_lassert_cbase : type (Bit WordSz);
  hw_lassert_flen : type (Bit WordSz);
  hw_lassert_clen : type (Bit WordSz);
  hw_lassert_nvars : type (Bit WordSz);
  hw_lassert_fptr : type (Bit WordSz);
  hw_lassert_cptr : type (Bit WordSz);
  hw_lassert_fbuf : type (Vector (Bit WordSz) 6);
  hw_lassert_cbuf : type (Vector (Bit WordSz) 6);
  hw_lassert_clause_sat : type (Bool);
  hw_lassert_counter_clause_sat : type (Bool);
  hw_lassert_counter_seen_fail : type (Bool);
  hw_chsh_phase : type (Bit 5);
  hw_chsh_n00 : type (Bit 64);
  hw_chsh_n01 : type (Bit 64);
  hw_chsh_n10 : type (Bit 64);
  hw_chsh_n11 : type (Bit 64);
  hw_chsh_d00 : type (Bit 64);
  hw_chsh_d01 : type (Bit 64);
  hw_chsh_d10 : type (Bit 64);
  hw_chsh_d11 : type (Bit 64);
  hw_chsh_sign00 : type (Bool);
  hw_chsh_sign01 : type (Bool);
  hw_chsh_sign10 : type (Bool);
  hw_chsh_sign11 : type (Bool);
  hw_chsh_n00sq : type (Bit 128);
  hw_chsh_n01sq : type (Bit 128);
  hw_chsh_n10sq : type (Bit 128);
  hw_chsh_n11sq : type (Bit 128);
  hw_chsh_d00sq : type (Bit 128);
  hw_chsh_d01sq : type (Bit 128);
  hw_chsh_d10sq : type (Bit 128);
  hw_chsh_d11sq : type (Bit 128);
  hw_chsh_A_pos : type (Bit 256);
  hw_chsh_A_neg_a : type (Bit 256);
  hw_chsh_A_neg_b : type (Bit 256);
  hw_chsh_B_pos : type (Bit 256);
  hw_chsh_B_neg_a : type (Bit 256);
  hw_chsh_B_neg_b : type (Bit 256);
  hw_chsh_d00d01 : type (Bit 128);
  hw_chsh_n10n11 : type (Bit 128);
  hw_chsh_d10d11 : type (Bit 128);
  hw_chsh_n00n01 : type (Bit 128);
  hw_chsh_abs_C1 : type (Bit 256);
  hw_chsh_abs_C2 : type (Bit 256);
  hw_chsh_C_sq : type (Bit 384);
  hw_chsh_A_times_B : type (Bit 384);
  hw_chsh_check_result : type (Bool);
  hw_bus_load_instr_addr : type (Bit MemAddrSz);
  hw_bus_load_instr_data : type (Bit InstrSz);
  hw_bus_load_instr_kick : type (Bool);
  hw_mu_tensor : type (Vector (Bit WordSz) MuTensorIdxSz);
  hw_module_tensors : type (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz);
  hw_csr_status : type (Bit WordSz);
  hw_csr_heap_base : type (Bit WordSz);
  hw_ptTable : type (Vector (Bit WordSz) PTableIdxSz);
  hw_pt_next_id : type (Bit PTableNextIdSz);
  hw_morph_src_table : type (Vector (Bit PTableIdxSz) MorphTableIdxSz);
  hw_morph_dst_table : type (Vector (Bit PTableIdxSz) MorphTableIdxSz);
  hw_morph_coupling_desc_table : type (Vector (Bit DescIdxSz) MorphTableIdxSz);
  hw_morph_valid_table : type (Vector Bool MorphTableIdxSz);
  hw_morph_identity_table : type (Vector Bool MorphTableIdxSz);
  hw_morph_next_id : type (Bit MorphTableNextIdSz);
  hw_coupling_desc_base_table : type (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz);
  hw_coupling_desc_count_table : type (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz);
  hw_coupling_desc_valid_table : type (Vector Bool CouplingDescIdxSz);
  hw_coupling_desc_label_table : type (Vector (Bit WordSz) CouplingDescIdxSz);
  hw_coupling_desc_label_len_table : type (Vector (Bit 6) CouplingDescIdxSz);
  hw_coupling_desc_next_id : type (Bit DescTableNextIdSz);
  hw_coupling_pair_src_table : type (Vector (Bit WordSz) CouplingPairIdxSz);
  hw_coupling_pair_dst_table : type (Vector (Bit WordSz) CouplingPairIdxSz);
  hw_coupling_pair_valid_table : type (Vector Bool CouplingPairIdxSz);
  hw_coupling_pair_next_id : type (Bit DescTableNextIdSz);
  hw_mc_phase : type (Bit 4);
  hw_mc_op : type (Bit 2);
  hw_mc_mem_base : type (Bit WordSz);
  hw_mc_pair_count : type (Bit CouplingPairCountSz);
  hw_mc_read_ptr : type (Bit WordSz);
  hw_mc_src1_base : type (Bit CouplingPairIdxSz);
  hw_mc_src1_count : type (Bit CouplingPairCountSz);
  hw_mc_src2_base : type (Bit CouplingPairIdxSz);
  hw_mc_src2_count : type (Bit CouplingPairCountSz);
  hw_mc_i : type (Bit CouplingPairCountSz);
  hw_mc_j : type (Bit CouplingPairCountSz);
  hw_mc_is_id1 : type (Bool);
  hw_mc_is_id2 : type (Bool);
  hw_mc_write_base : type (Bit DescTableNextIdSz);
  hw_mc_write_ptr : type (Bit DescTableNextIdSz);
  hw_mc_norm_ptr : type (Bit DescTableNextIdSz);
  hw_mc_duplicate : type (Bool);
  hw_mc_dst_reg : type (Bit RegIdxSz);
  hw_mc_morph_slot : type (Bit MorphTableIdxSz);
  hw_mc_new_src_mod : type (Bit PTableIdxSz);
  hw_mc_new_dst_mod : type (Bit PTableIdxSz);
  hw_mc_cost : type (Bit WordSz);
  hw_formula_desc_base_table : type (Vector (Bit WordSz) FormulaDescIdxSz);
  hw_formula_desc_count_table : type (Vector (Bit WordSz) FormulaDescIdxSz);
  hw_formula_desc_valid_table : type (Vector Bool FormulaDescIdxSz);
  hw_formula_desc_next_id : type (Bit DescTableNextIdSz);
  hw_cert_desc_base_table : type (Vector (Bit WordSz) CertDescIdxSz);
  hw_cert_desc_count_table : type (Vector (Bit WordSz) CertDescIdxSz);
  hw_cert_desc_valid_table : type (Vector Bool CertDescIdxSz);
  hw_cert_desc_next_id : type (Bit DescTableNextIdSz);
  hw_desc_meta_subtype_table : type (Vector (Bit FormatSubtypeSz) DescMetaIdxSz);
  hw_desc_meta_kind_table : type (Vector (Bit DescKindFieldSz) DescMetaIdxSz);
  hw_desc_meta_inline_len_table : type (Vector (Bit InlineLenSz) DescMetaIdxSz);
  hw_desc_meta_aux_table : type (Vector (Bit WordSz) DescMetaIdxSz);
  hw_desc_meta_valid_table : type (Vector Bool DescMetaIdxSz);
  hw_desc_meta_next_id : type (Bit DescTableNextIdSz);
  hw_wc_same_00 : type (Bit WordSz);
  hw_wc_diff_00 : type (Bit WordSz);
  hw_wc_same_01 : type (Bit WordSz);
  hw_wc_diff_01 : type (Bit WordSz);
  hw_wc_same_10 : type (Bit WordSz);
  hw_wc_diff_10 : type (Bit WordSz);
  hw_wc_same_11 : type (Bit WordSz);
  hw_wc_diff_11 : type (Bit WordSz)
}.

Definition hwb_reg (k : Kind) (v : type k) : sigT (fullType type) :=
  existT (fullType type) (SyntaxKind k) v.

Definition hwb_regs (b : HWB) : RegsT :=
  M.add "pc" (hwb_reg (Bit WordSz) b.(hw_pc))
  (M.add "mu" (hwb_reg (Bit WordSz) b.(hw_mu))
  (M.add "err" (hwb_reg (Bool) b.(hw_err))
  (M.add "halted" (hwb_reg (Bool) b.(hw_halted))
  (M.add "regs" (hwb_reg (Vector (Bit WordSz) RegIdxSz) b.(hw_regs))
  (M.add "mem" (hwb_reg (Vector (Bit WordSz) MemAddrSz) b.(hw_mem))
  (M.add "imem" (hwb_reg (Vector (Bit InstrSz) MemAddrSz) b.(hw_imem))
  (M.add "partition_ops" (hwb_reg (Bit WordSz) b.(hw_partition_ops))
  (M.add "mdl_ops" (hwb_reg (Bit WordSz) b.(hw_mdl_ops))
  (M.add "info_gain" (hwb_reg (Bit WordSz) b.(hw_info_gain))
  (M.add "error_code" (hwb_reg (Bit WordSz) b.(hw_error_code))
  (M.add "logic_acc" (hwb_reg (Bit WordSz) b.(hw_logic_acc))
  (M.add "cert_addr" (hwb_reg (Bit WordSz) b.(hw_cert_addr))
  (M.add "active_module" (hwb_reg (Bit PTableIdxSz) b.(hw_active_module))
  (M.add "mstatus" (hwb_reg (Bit WordSz) b.(hw_mstatus))
  (M.add "mcycle_lo" (hwb_reg (Bit WordSz) b.(hw_mcycle_lo))
  (M.add "mcycle_hi" (hwb_reg (Bit WordSz) b.(hw_mcycle_hi))
  (M.add "minstret_lo" (hwb_reg (Bit WordSz) b.(hw_minstret_lo))
  (M.add "minstret_hi" (hwb_reg (Bit WordSz) b.(hw_minstret_hi))
  (M.add "trap_vector" (hwb_reg (Bit WordSz) b.(hw_trap_vector))
  (M.add "certified" (hwb_reg (Bool) b.(hw_certified))
  (M.add "lassert_phase" (hwb_reg (Bit 3) b.(hw_lassert_phase))
  (M.add "lassert_kind" (hwb_reg (Bool) b.(hw_lassert_kind))
  (M.add "lassert_fbase" (hwb_reg (Bit WordSz) b.(hw_lassert_fbase))
  (M.add "lassert_cbase" (hwb_reg (Bit WordSz) b.(hw_lassert_cbase))
  (M.add "lassert_flen" (hwb_reg (Bit WordSz) b.(hw_lassert_flen))
  (M.add "lassert_clen" (hwb_reg (Bit WordSz) b.(hw_lassert_clen))
  (M.add "lassert_nvars" (hwb_reg (Bit WordSz) b.(hw_lassert_nvars))
  (M.add "lassert_fptr" (hwb_reg (Bit WordSz) b.(hw_lassert_fptr))
  (M.add "lassert_cptr" (hwb_reg (Bit WordSz) b.(hw_lassert_cptr))
  (M.add "lassert_fbuf" (hwb_reg (Vector (Bit WordSz) 6) b.(hw_lassert_fbuf))
  (M.add "lassert_cbuf" (hwb_reg (Vector (Bit WordSz) 6) b.(hw_lassert_cbuf))
  (M.add "lassert_clause_sat" (hwb_reg (Bool) b.(hw_lassert_clause_sat))
  (M.add "lassert_counter_clause_sat" (hwb_reg (Bool) b.(hw_lassert_counter_clause_sat))
  (M.add "lassert_counter_seen_fail" (hwb_reg (Bool) b.(hw_lassert_counter_seen_fail))
  (M.add "chsh_phase" (hwb_reg (Bit 5) b.(hw_chsh_phase))
  (M.add "chsh_n00" (hwb_reg (Bit 64) b.(hw_chsh_n00))
  (M.add "chsh_n01" (hwb_reg (Bit 64) b.(hw_chsh_n01))
  (M.add "chsh_n10" (hwb_reg (Bit 64) b.(hw_chsh_n10))
  (M.add "chsh_n11" (hwb_reg (Bit 64) b.(hw_chsh_n11))
  (M.add "chsh_d00" (hwb_reg (Bit 64) b.(hw_chsh_d00))
  (M.add "chsh_d01" (hwb_reg (Bit 64) b.(hw_chsh_d01))
  (M.add "chsh_d10" (hwb_reg (Bit 64) b.(hw_chsh_d10))
  (M.add "chsh_d11" (hwb_reg (Bit 64) b.(hw_chsh_d11))
  (M.add "chsh_sign00" (hwb_reg (Bool) b.(hw_chsh_sign00))
  (M.add "chsh_sign01" (hwb_reg (Bool) b.(hw_chsh_sign01))
  (M.add "chsh_sign10" (hwb_reg (Bool) b.(hw_chsh_sign10))
  (M.add "chsh_sign11" (hwb_reg (Bool) b.(hw_chsh_sign11))
  (M.add "chsh_n00sq" (hwb_reg (Bit 128) b.(hw_chsh_n00sq))
  (M.add "chsh_n01sq" (hwb_reg (Bit 128) b.(hw_chsh_n01sq))
  (M.add "chsh_n10sq" (hwb_reg (Bit 128) b.(hw_chsh_n10sq))
  (M.add "chsh_n11sq" (hwb_reg (Bit 128) b.(hw_chsh_n11sq))
  (M.add "chsh_d00sq" (hwb_reg (Bit 128) b.(hw_chsh_d00sq))
  (M.add "chsh_d01sq" (hwb_reg (Bit 128) b.(hw_chsh_d01sq))
  (M.add "chsh_d10sq" (hwb_reg (Bit 128) b.(hw_chsh_d10sq))
  (M.add "chsh_d11sq" (hwb_reg (Bit 128) b.(hw_chsh_d11sq))
  (M.add "chsh_A_pos" (hwb_reg (Bit 256) b.(hw_chsh_A_pos))
  (M.add "chsh_A_neg_a" (hwb_reg (Bit 256) b.(hw_chsh_A_neg_a))
  (M.add "chsh_A_neg_b" (hwb_reg (Bit 256) b.(hw_chsh_A_neg_b))
  (M.add "chsh_B_pos" (hwb_reg (Bit 256) b.(hw_chsh_B_pos))
  (M.add "chsh_B_neg_a" (hwb_reg (Bit 256) b.(hw_chsh_B_neg_a))
  (M.add "chsh_B_neg_b" (hwb_reg (Bit 256) b.(hw_chsh_B_neg_b))
  (M.add "chsh_d00d01" (hwb_reg (Bit 128) b.(hw_chsh_d00d01))
  (M.add "chsh_n10n11" (hwb_reg (Bit 128) b.(hw_chsh_n10n11))
  (M.add "chsh_d10d11" (hwb_reg (Bit 128) b.(hw_chsh_d10d11))
  (M.add "chsh_n00n01" (hwb_reg (Bit 128) b.(hw_chsh_n00n01))
  (M.add "chsh_abs_C1" (hwb_reg (Bit 256) b.(hw_chsh_abs_C1))
  (M.add "chsh_abs_C2" (hwb_reg (Bit 256) b.(hw_chsh_abs_C2))
  (M.add "chsh_C_sq" (hwb_reg (Bit 384) b.(hw_chsh_C_sq))
  (M.add "chsh_A_times_B" (hwb_reg (Bit 384) b.(hw_chsh_A_times_B))
  (M.add "chsh_check_result" (hwb_reg (Bool) b.(hw_chsh_check_result))
  (M.add "bus_load_instr_addr" (hwb_reg (Bit MemAddrSz) b.(hw_bus_load_instr_addr))
  (M.add "bus_load_instr_data" (hwb_reg (Bit InstrSz) b.(hw_bus_load_instr_data))
  (M.add "bus_load_instr_kick" (hwb_reg (Bool) b.(hw_bus_load_instr_kick))
  (M.add "mu_tensor" (hwb_reg (Vector (Bit WordSz) MuTensorIdxSz) b.(hw_mu_tensor))
  (M.add "module_tensors" (hwb_reg (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz) b.(hw_module_tensors))
  (M.add "csr_status" (hwb_reg (Bit WordSz) b.(hw_csr_status))
  (M.add "csr_heap_base" (hwb_reg (Bit WordSz) b.(hw_csr_heap_base))
  (M.add "ptTable" (hwb_reg (Vector (Bit WordSz) PTableIdxSz) b.(hw_ptTable))
  (M.add "pt_next_id" (hwb_reg (Bit PTableNextIdSz) b.(hw_pt_next_id))
  (M.add "morph_src_table" (hwb_reg (Vector (Bit PTableIdxSz) MorphTableIdxSz) b.(hw_morph_src_table))
  (M.add "morph_dst_table" (hwb_reg (Vector (Bit PTableIdxSz) MorphTableIdxSz) b.(hw_morph_dst_table))
  (M.add "morph_coupling_desc_table" (hwb_reg (Vector (Bit DescIdxSz) MorphTableIdxSz) b.(hw_morph_coupling_desc_table))
  (M.add "morph_valid_table" (hwb_reg (Vector Bool MorphTableIdxSz) b.(hw_morph_valid_table))
  (M.add "morph_identity_table" (hwb_reg (Vector Bool MorphTableIdxSz) b.(hw_morph_identity_table))
  (M.add "morph_next_id" (hwb_reg (Bit MorphTableNextIdSz) b.(hw_morph_next_id))
  (M.add "coupling_desc_base_table" (hwb_reg (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz) b.(hw_coupling_desc_base_table))
  (M.add "coupling_desc_count_table" (hwb_reg (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz) b.(hw_coupling_desc_count_table))
  (M.add "coupling_desc_valid_table" (hwb_reg (Vector Bool CouplingDescIdxSz) b.(hw_coupling_desc_valid_table))
  (M.add "coupling_desc_label_table" (hwb_reg (Vector (Bit WordSz) CouplingDescIdxSz) b.(hw_coupling_desc_label_table))
  (M.add "coupling_desc_label_len_table" (hwb_reg (Vector (Bit 6) CouplingDescIdxSz) b.(hw_coupling_desc_label_len_table))
  (M.add "coupling_desc_next_id" (hwb_reg (Bit DescTableNextIdSz) b.(hw_coupling_desc_next_id))
  (M.add "coupling_pair_src_table" (hwb_reg (Vector (Bit WordSz) CouplingPairIdxSz) b.(hw_coupling_pair_src_table))
  (M.add "coupling_pair_dst_table" (hwb_reg (Vector (Bit WordSz) CouplingPairIdxSz) b.(hw_coupling_pair_dst_table))
  (M.add "coupling_pair_valid_table" (hwb_reg (Vector Bool CouplingPairIdxSz) b.(hw_coupling_pair_valid_table))
  (M.add "coupling_pair_next_id" (hwb_reg (Bit DescTableNextIdSz) b.(hw_coupling_pair_next_id))
  (M.add "mc_phase" (hwb_reg (Bit 4) b.(hw_mc_phase))
  (M.add "mc_op" (hwb_reg (Bit 2) b.(hw_mc_op))
  (M.add "mc_mem_base" (hwb_reg (Bit WordSz) b.(hw_mc_mem_base))
  (M.add "mc_pair_count" (hwb_reg (Bit CouplingPairCountSz) b.(hw_mc_pair_count))
  (M.add "mc_read_ptr" (hwb_reg (Bit WordSz) b.(hw_mc_read_ptr))
  (M.add "mc_src1_base" (hwb_reg (Bit CouplingPairIdxSz) b.(hw_mc_src1_base))
  (M.add "mc_src1_count" (hwb_reg (Bit CouplingPairCountSz) b.(hw_mc_src1_count))
  (M.add "mc_src2_base" (hwb_reg (Bit CouplingPairIdxSz) b.(hw_mc_src2_base))
  (M.add "mc_src2_count" (hwb_reg (Bit CouplingPairCountSz) b.(hw_mc_src2_count))
  (M.add "mc_i" (hwb_reg (Bit CouplingPairCountSz) b.(hw_mc_i))
  (M.add "mc_j" (hwb_reg (Bit CouplingPairCountSz) b.(hw_mc_j))
  (M.add "mc_is_id1" (hwb_reg (Bool) b.(hw_mc_is_id1))
  (M.add "mc_is_id2" (hwb_reg (Bool) b.(hw_mc_is_id2))
  (M.add "mc_write_base" (hwb_reg (Bit DescTableNextIdSz) b.(hw_mc_write_base))
  (M.add "mc_write_ptr" (hwb_reg (Bit DescTableNextIdSz) b.(hw_mc_write_ptr))
  (M.add "mc_norm_ptr" (hwb_reg (Bit DescTableNextIdSz) b.(hw_mc_norm_ptr))
  (M.add "mc_duplicate" (hwb_reg (Bool) b.(hw_mc_duplicate))
  (M.add "mc_dst_reg" (hwb_reg (Bit RegIdxSz) b.(hw_mc_dst_reg))
  (M.add "mc_morph_slot" (hwb_reg (Bit MorphTableIdxSz) b.(hw_mc_morph_slot))
  (M.add "mc_new_src_mod" (hwb_reg (Bit PTableIdxSz) b.(hw_mc_new_src_mod))
  (M.add "mc_new_dst_mod" (hwb_reg (Bit PTableIdxSz) b.(hw_mc_new_dst_mod))
  (M.add "mc_cost" (hwb_reg (Bit WordSz) b.(hw_mc_cost))
  (M.add "formula_desc_base_table" (hwb_reg (Vector (Bit WordSz) FormulaDescIdxSz) b.(hw_formula_desc_base_table))
  (M.add "formula_desc_count_table" (hwb_reg (Vector (Bit WordSz) FormulaDescIdxSz) b.(hw_formula_desc_count_table))
  (M.add "formula_desc_valid_table" (hwb_reg (Vector Bool FormulaDescIdxSz) b.(hw_formula_desc_valid_table))
  (M.add "formula_desc_next_id" (hwb_reg (Bit DescTableNextIdSz) b.(hw_formula_desc_next_id))
  (M.add "cert_desc_base_table" (hwb_reg (Vector (Bit WordSz) CertDescIdxSz) b.(hw_cert_desc_base_table))
  (M.add "cert_desc_count_table" (hwb_reg (Vector (Bit WordSz) CertDescIdxSz) b.(hw_cert_desc_count_table))
  (M.add "cert_desc_valid_table" (hwb_reg (Vector Bool CertDescIdxSz) b.(hw_cert_desc_valid_table))
  (M.add "cert_desc_next_id" (hwb_reg (Bit DescTableNextIdSz) b.(hw_cert_desc_next_id))
  (M.add "desc_meta_subtype_table" (hwb_reg (Vector (Bit FormatSubtypeSz) DescMetaIdxSz) b.(hw_desc_meta_subtype_table))
  (M.add "desc_meta_kind_table" (hwb_reg (Vector (Bit DescKindFieldSz) DescMetaIdxSz) b.(hw_desc_meta_kind_table))
  (M.add "desc_meta_inline_len_table" (hwb_reg (Vector (Bit InlineLenSz) DescMetaIdxSz) b.(hw_desc_meta_inline_len_table))
  (M.add "desc_meta_aux_table" (hwb_reg (Vector (Bit WordSz) DescMetaIdxSz) b.(hw_desc_meta_aux_table))
  (M.add "desc_meta_valid_table" (hwb_reg (Vector Bool DescMetaIdxSz) b.(hw_desc_meta_valid_table))
  (M.add "desc_meta_next_id" (hwb_reg (Bit DescTableNextIdSz) b.(hw_desc_meta_next_id))
  (M.add "wc_same_00" (hwb_reg (Bit WordSz) b.(hw_wc_same_00))
  (M.add "wc_diff_00" (hwb_reg (Bit WordSz) b.(hw_wc_diff_00))
  (M.add "wc_same_01" (hwb_reg (Bit WordSz) b.(hw_wc_same_01))
  (M.add "wc_diff_01" (hwb_reg (Bit WordSz) b.(hw_wc_diff_01))
  (M.add "wc_same_10" (hwb_reg (Bit WordSz) b.(hw_wc_same_10))
  (M.add "wc_diff_10" (hwb_reg (Bit WordSz) b.(hw_wc_diff_10))
  (M.add "wc_same_11" (hwb_reg (Bit WordSz) b.(hw_wc_same_11))
  (M.add "wc_diff_11" (hwb_reg (Bit WordSz) b.(hw_wc_diff_11))
  (M.empty _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
