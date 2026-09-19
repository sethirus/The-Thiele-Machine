(** Completeness of HWB for the exact CoreTyping schema; no reachability
    or arithmetic invariant is required. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary ActionEvaluator CoreTyping DispatchExecution CoreExecution.
Import ListNotations.
Open Scope string_scope.

Definition typed_register_value (old : RegsT) (name : string) (k : Kind) : type k :=
  match action_read_syntax old name k with
  | Some value => value
  | None => getDefaultConstNative k
  end.

Lemma typed_register_value_find : forall old name k,
  register_kind old name = Some (SyntaxKind k) ->
  M.find name old = Some (hwb_reg k (typed_register_value old name k)).
Proof.
  intros old name k H. unfold register_kind in H.
  destruct (M.find name old) as [[actual value]|] eqn:E; [|discriminate].
  cbn in H. inversion H; subst actual.
  unfold typed_register_value, action_read_syntax.
  rewrite E, kind_eq. reflexivity.
Qed.

Lemma cpu_kind_pc : cpu_register_kind "pc" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mu : cpu_register_kind "mu" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_err : cpu_register_kind "err" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_halted : cpu_register_kind "halted" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_regs : cpu_register_kind "regs" = Some (SyntaxKind (Vector (Bit WordSz) RegIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mem : cpu_register_kind "mem" = Some (SyntaxKind (Vector (Bit WordSz) MemAddrSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_imem : cpu_register_kind "imem" = Some (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_partition_ops : cpu_register_kind "partition_ops" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mdl_ops : cpu_register_kind "mdl_ops" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_info_gain : cpu_register_kind "info_gain" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_error_code : cpu_register_kind "error_code" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_logic_acc : cpu_register_kind "logic_acc" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_cert_addr : cpu_register_kind "cert_addr" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_active_module : cpu_register_kind "active_module" = Some (SyntaxKind (Bit PTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mstatus : cpu_register_kind "mstatus" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mcycle_lo : cpu_register_kind "mcycle_lo" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mcycle_hi : cpu_register_kind "mcycle_hi" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_minstret_lo : cpu_register_kind "minstret_lo" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_minstret_hi : cpu_register_kind "minstret_hi" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_trap_vector : cpu_register_kind "trap_vector" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_certified : cpu_register_kind "certified" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_phase : cpu_register_kind "lassert_phase" = Some (SyntaxKind (Bit 3)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_kind : cpu_register_kind "lassert_kind" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_fbase : cpu_register_kind "lassert_fbase" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_cbase : cpu_register_kind "lassert_cbase" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_flen : cpu_register_kind "lassert_flen" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_clen : cpu_register_kind "lassert_clen" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_nvars : cpu_register_kind "lassert_nvars" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_fptr : cpu_register_kind "lassert_fptr" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_cptr : cpu_register_kind "lassert_cptr" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_fbuf : cpu_register_kind "lassert_fbuf" = Some (SyntaxKind (Vector (Bit WordSz) 6)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_cbuf : cpu_register_kind "lassert_cbuf" = Some (SyntaxKind (Vector (Bit WordSz) 6)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_clause_sat : cpu_register_kind "lassert_clause_sat" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_counter_clause_sat : cpu_register_kind "lassert_counter_clause_sat" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_lassert_counter_seen_fail : cpu_register_kind "lassert_counter_seen_fail" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_phase : cpu_register_kind "chsh_phase" = Some (SyntaxKind (Bit 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n00 : cpu_register_kind "chsh_n00" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n01 : cpu_register_kind "chsh_n01" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n10 : cpu_register_kind "chsh_n10" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n11 : cpu_register_kind "chsh_n11" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d00 : cpu_register_kind "chsh_d00" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d01 : cpu_register_kind "chsh_d01" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d10 : cpu_register_kind "chsh_d10" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d11 : cpu_register_kind "chsh_d11" = Some (SyntaxKind (Bit 64)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_sign00 : cpu_register_kind "chsh_sign00" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_sign01 : cpu_register_kind "chsh_sign01" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_sign10 : cpu_register_kind "chsh_sign10" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_sign11 : cpu_register_kind "chsh_sign11" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n00sq : cpu_register_kind "chsh_n00sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n01sq : cpu_register_kind "chsh_n01sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n10sq : cpu_register_kind "chsh_n10sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n11sq : cpu_register_kind "chsh_n11sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d00sq : cpu_register_kind "chsh_d00sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d01sq : cpu_register_kind "chsh_d01sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d10sq : cpu_register_kind "chsh_d10sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d11sq : cpu_register_kind "chsh_d11sq" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_A_pos : cpu_register_kind "chsh_A_pos" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_A_neg_a : cpu_register_kind "chsh_A_neg_a" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_A_neg_b : cpu_register_kind "chsh_A_neg_b" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_B_pos : cpu_register_kind "chsh_B_pos" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_B_neg_a : cpu_register_kind "chsh_B_neg_a" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_B_neg_b : cpu_register_kind "chsh_B_neg_b" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d00d01 : cpu_register_kind "chsh_d00d01" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n10n11 : cpu_register_kind "chsh_n10n11" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_d10d11 : cpu_register_kind "chsh_d10d11" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_n00n01 : cpu_register_kind "chsh_n00n01" = Some (SyntaxKind (Bit 128)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_abs_C1 : cpu_register_kind "chsh_abs_C1" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_abs_C2 : cpu_register_kind "chsh_abs_C2" = Some (SyntaxKind (Bit 256)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_C_sq : cpu_register_kind "chsh_C_sq" = Some (SyntaxKind (Bit 384)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_A_times_B : cpu_register_kind "chsh_A_times_B" = Some (SyntaxKind (Bit 384)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_chsh_check_result : cpu_register_kind "chsh_check_result" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_bus_load_instr_addr : cpu_register_kind "bus_load_instr_addr" = Some (SyntaxKind (Bit MemAddrSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_bus_load_instr_data : cpu_register_kind "bus_load_instr_data" = Some (SyntaxKind (Bit InstrSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_bus_load_instr_kick : cpu_register_kind "bus_load_instr_kick" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mu_tensor : cpu_register_kind "mu_tensor" = Some (SyntaxKind (Vector (Bit WordSz) MuTensorIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_module_tensors : cpu_register_kind "module_tensors" = Some (SyntaxKind (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_csr_status : cpu_register_kind "csr_status" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_csr_heap_base : cpu_register_kind "csr_heap_base" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_ptTable : cpu_register_kind "ptTable" = Some (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_pt_next_id : cpu_register_kind "pt_next_id" = Some (SyntaxKind (Bit PTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_morph_src_table : cpu_register_kind "morph_src_table" = Some (SyntaxKind (Vector (Bit PTableIdxSz) MorphTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_morph_dst_table : cpu_register_kind "morph_dst_table" = Some (SyntaxKind (Vector (Bit PTableIdxSz) MorphTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_morph_coupling_desc_table : cpu_register_kind "morph_coupling_desc_table" = Some (SyntaxKind (Vector (Bit DescIdxSz) MorphTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_morph_valid_table : cpu_register_kind "morph_valid_table" = Some (SyntaxKind (Vector Bool MorphTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_morph_identity_table : cpu_register_kind "morph_identity_table" = Some (SyntaxKind (Vector Bool MorphTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_morph_next_id : cpu_register_kind "morph_next_id" = Some (SyntaxKind (Bit MorphTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_desc_base_table : cpu_register_kind "coupling_desc_base_table" = Some (SyntaxKind (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_desc_count_table : cpu_register_kind "coupling_desc_count_table" = Some (SyntaxKind (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_desc_valid_table : cpu_register_kind "coupling_desc_valid_table" = Some (SyntaxKind (Vector Bool CouplingDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_desc_label_table : cpu_register_kind "coupling_desc_label_table" = Some (SyntaxKind (Vector (Bit WordSz) CouplingDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_desc_label_len_table : cpu_register_kind "coupling_desc_label_len_table" = Some (SyntaxKind (Vector (Bit 6) CouplingDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_desc_next_id : cpu_register_kind "coupling_desc_next_id" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_pair_src_table : cpu_register_kind "coupling_pair_src_table" = Some (SyntaxKind (Vector (Bit WordSz) CouplingPairIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_pair_dst_table : cpu_register_kind "coupling_pair_dst_table" = Some (SyntaxKind (Vector (Bit WordSz) CouplingPairIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_pair_valid_table : cpu_register_kind "coupling_pair_valid_table" = Some (SyntaxKind (Vector Bool CouplingPairIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_coupling_pair_next_id : cpu_register_kind "coupling_pair_next_id" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_phase : cpu_register_kind "mc_phase" = Some (SyntaxKind (Bit 4)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_op : cpu_register_kind "mc_op" = Some (SyntaxKind (Bit 2)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_mem_base : cpu_register_kind "mc_mem_base" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_pair_count : cpu_register_kind "mc_pair_count" = Some (SyntaxKind (Bit CouplingPairCountSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_read_ptr : cpu_register_kind "mc_read_ptr" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_src1_base : cpu_register_kind "mc_src1_base" = Some (SyntaxKind (Bit CouplingPairIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_src1_count : cpu_register_kind "mc_src1_count" = Some (SyntaxKind (Bit CouplingPairCountSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_src2_base : cpu_register_kind "mc_src2_base" = Some (SyntaxKind (Bit CouplingPairIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_src2_count : cpu_register_kind "mc_src2_count" = Some (SyntaxKind (Bit CouplingPairCountSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_i : cpu_register_kind "mc_i" = Some (SyntaxKind (Bit CouplingPairCountSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_j : cpu_register_kind "mc_j" = Some (SyntaxKind (Bit CouplingPairCountSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_is_id1 : cpu_register_kind "mc_is_id1" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_is_id2 : cpu_register_kind "mc_is_id2" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_write_base : cpu_register_kind "mc_write_base" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_write_ptr : cpu_register_kind "mc_write_ptr" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_norm_ptr : cpu_register_kind "mc_norm_ptr" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_duplicate : cpu_register_kind "mc_duplicate" = Some (SyntaxKind (Bool)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_dst_reg : cpu_register_kind "mc_dst_reg" = Some (SyntaxKind (Bit RegIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_morph_slot : cpu_register_kind "mc_morph_slot" = Some (SyntaxKind (Bit MorphTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_new_src_mod : cpu_register_kind "mc_new_src_mod" = Some (SyntaxKind (Bit PTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_new_dst_mod : cpu_register_kind "mc_new_dst_mod" = Some (SyntaxKind (Bit PTableIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_mc_cost : cpu_register_kind "mc_cost" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_formula_desc_base_table : cpu_register_kind "formula_desc_base_table" = Some (SyntaxKind (Vector (Bit WordSz) FormulaDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_formula_desc_count_table : cpu_register_kind "formula_desc_count_table" = Some (SyntaxKind (Vector (Bit WordSz) FormulaDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_formula_desc_valid_table : cpu_register_kind "formula_desc_valid_table" = Some (SyntaxKind (Vector Bool FormulaDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_formula_desc_next_id : cpu_register_kind "formula_desc_next_id" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_cert_desc_base_table : cpu_register_kind "cert_desc_base_table" = Some (SyntaxKind (Vector (Bit WordSz) CertDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_cert_desc_count_table : cpu_register_kind "cert_desc_count_table" = Some (SyntaxKind (Vector (Bit WordSz) CertDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_cert_desc_valid_table : cpu_register_kind "cert_desc_valid_table" = Some (SyntaxKind (Vector Bool CertDescIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_cert_desc_next_id : cpu_register_kind "cert_desc_next_id" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_desc_meta_subtype_table : cpu_register_kind "desc_meta_subtype_table" = Some (SyntaxKind (Vector (Bit FormatSubtypeSz) DescMetaIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_desc_meta_kind_table : cpu_register_kind "desc_meta_kind_table" = Some (SyntaxKind (Vector (Bit DescKindFieldSz) DescMetaIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_desc_meta_inline_len_table : cpu_register_kind "desc_meta_inline_len_table" = Some (SyntaxKind (Vector (Bit InlineLenSz) DescMetaIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_desc_meta_aux_table : cpu_register_kind "desc_meta_aux_table" = Some (SyntaxKind (Vector (Bit WordSz) DescMetaIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_desc_meta_valid_table : cpu_register_kind "desc_meta_valid_table" = Some (SyntaxKind (Vector Bool DescMetaIdxSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_desc_meta_next_id : cpu_register_kind "desc_meta_next_id" = Some (SyntaxKind (Bit DescTableNextIdSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_same_00 : cpu_register_kind "wc_same_00" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_diff_00 : cpu_register_kind "wc_diff_00" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_same_01 : cpu_register_kind "wc_same_01" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_diff_01 : cpu_register_kind "wc_diff_01" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_same_10 : cpu_register_kind "wc_same_10" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_diff_10 : cpu_register_kind "wc_diff_10" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_same_11 : cpu_register_kind "wc_same_11" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.
Lemma cpu_kind_wc_diff_11 : cpu_register_kind "wc_diff_11" = Some (SyntaxKind (Bit WordSz)).
Proof. vm_compute. reflexivity. Qed.

Definition hwb_of_regs (old : RegsT) (H : registers_match cpu_register_kind old) : HWB :=
  {| hw_pc := typed_register_value old "pc" (Bit WordSz);
     hw_mu := typed_register_value old "mu" (Bit WordSz);
     hw_err := typed_register_value old "err" (Bool);
     hw_halted := typed_register_value old "halted" (Bool);
     hw_regs := typed_register_value old "regs" (Vector (Bit WordSz) RegIdxSz);
     hw_mem := typed_register_value old "mem" (Vector (Bit WordSz) MemAddrSz);
     hw_imem := typed_register_value old "imem" (Vector (Bit InstrSz) MemAddrSz);
     hw_partition_ops := typed_register_value old "partition_ops" (Bit WordSz);
     hw_mdl_ops := typed_register_value old "mdl_ops" (Bit WordSz);
     hw_info_gain := typed_register_value old "info_gain" (Bit WordSz);
     hw_error_code := typed_register_value old "error_code" (Bit WordSz);
     hw_logic_acc := typed_register_value old "logic_acc" (Bit WordSz);
     hw_cert_addr := typed_register_value old "cert_addr" (Bit WordSz);
     hw_active_module := typed_register_value old "active_module" (Bit PTableIdxSz);
     hw_mstatus := typed_register_value old "mstatus" (Bit WordSz);
     hw_mcycle_lo := typed_register_value old "mcycle_lo" (Bit WordSz);
     hw_mcycle_hi := typed_register_value old "mcycle_hi" (Bit WordSz);
     hw_minstret_lo := typed_register_value old "minstret_lo" (Bit WordSz);
     hw_minstret_hi := typed_register_value old "minstret_hi" (Bit WordSz);
     hw_trap_vector := typed_register_value old "trap_vector" (Bit WordSz);
     hw_certified := typed_register_value old "certified" (Bool);
     hw_lassert_phase := typed_register_value old "lassert_phase" (Bit 3);
     hw_lassert_kind := typed_register_value old "lassert_kind" (Bool);
     hw_lassert_fbase := typed_register_value old "lassert_fbase" (Bit WordSz);
     hw_lassert_cbase := typed_register_value old "lassert_cbase" (Bit WordSz);
     hw_lassert_flen := typed_register_value old "lassert_flen" (Bit WordSz);
     hw_lassert_clen := typed_register_value old "lassert_clen" (Bit WordSz);
     hw_lassert_nvars := typed_register_value old "lassert_nvars" (Bit WordSz);
     hw_lassert_fptr := typed_register_value old "lassert_fptr" (Bit WordSz);
     hw_lassert_cptr := typed_register_value old "lassert_cptr" (Bit WordSz);
     hw_lassert_fbuf := typed_register_value old "lassert_fbuf" (Vector (Bit WordSz) 6);
     hw_lassert_cbuf := typed_register_value old "lassert_cbuf" (Vector (Bit WordSz) 6);
     hw_lassert_clause_sat := typed_register_value old "lassert_clause_sat" (Bool);
     hw_lassert_counter_clause_sat := typed_register_value old "lassert_counter_clause_sat" (Bool);
     hw_lassert_counter_seen_fail := typed_register_value old "lassert_counter_seen_fail" (Bool);
     hw_chsh_phase := typed_register_value old "chsh_phase" (Bit 5);
     hw_chsh_n00 := typed_register_value old "chsh_n00" (Bit 64);
     hw_chsh_n01 := typed_register_value old "chsh_n01" (Bit 64);
     hw_chsh_n10 := typed_register_value old "chsh_n10" (Bit 64);
     hw_chsh_n11 := typed_register_value old "chsh_n11" (Bit 64);
     hw_chsh_d00 := typed_register_value old "chsh_d00" (Bit 64);
     hw_chsh_d01 := typed_register_value old "chsh_d01" (Bit 64);
     hw_chsh_d10 := typed_register_value old "chsh_d10" (Bit 64);
     hw_chsh_d11 := typed_register_value old "chsh_d11" (Bit 64);
     hw_chsh_sign00 := typed_register_value old "chsh_sign00" (Bool);
     hw_chsh_sign01 := typed_register_value old "chsh_sign01" (Bool);
     hw_chsh_sign10 := typed_register_value old "chsh_sign10" (Bool);
     hw_chsh_sign11 := typed_register_value old "chsh_sign11" (Bool);
     hw_chsh_n00sq := typed_register_value old "chsh_n00sq" (Bit 128);
     hw_chsh_n01sq := typed_register_value old "chsh_n01sq" (Bit 128);
     hw_chsh_n10sq := typed_register_value old "chsh_n10sq" (Bit 128);
     hw_chsh_n11sq := typed_register_value old "chsh_n11sq" (Bit 128);
     hw_chsh_d00sq := typed_register_value old "chsh_d00sq" (Bit 128);
     hw_chsh_d01sq := typed_register_value old "chsh_d01sq" (Bit 128);
     hw_chsh_d10sq := typed_register_value old "chsh_d10sq" (Bit 128);
     hw_chsh_d11sq := typed_register_value old "chsh_d11sq" (Bit 128);
     hw_chsh_A_pos := typed_register_value old "chsh_A_pos" (Bit 256);
     hw_chsh_A_neg_a := typed_register_value old "chsh_A_neg_a" (Bit 256);
     hw_chsh_A_neg_b := typed_register_value old "chsh_A_neg_b" (Bit 256);
     hw_chsh_B_pos := typed_register_value old "chsh_B_pos" (Bit 256);
     hw_chsh_B_neg_a := typed_register_value old "chsh_B_neg_a" (Bit 256);
     hw_chsh_B_neg_b := typed_register_value old "chsh_B_neg_b" (Bit 256);
     hw_chsh_d00d01 := typed_register_value old "chsh_d00d01" (Bit 128);
     hw_chsh_n10n11 := typed_register_value old "chsh_n10n11" (Bit 128);
     hw_chsh_d10d11 := typed_register_value old "chsh_d10d11" (Bit 128);
     hw_chsh_n00n01 := typed_register_value old "chsh_n00n01" (Bit 128);
     hw_chsh_abs_C1 := typed_register_value old "chsh_abs_C1" (Bit 256);
     hw_chsh_abs_C2 := typed_register_value old "chsh_abs_C2" (Bit 256);
     hw_chsh_C_sq := typed_register_value old "chsh_C_sq" (Bit 384);
     hw_chsh_A_times_B := typed_register_value old "chsh_A_times_B" (Bit 384);
     hw_chsh_check_result := typed_register_value old "chsh_check_result" (Bool);
     hw_bus_load_instr_addr := typed_register_value old "bus_load_instr_addr" (Bit MemAddrSz);
     hw_bus_load_instr_data := typed_register_value old "bus_load_instr_data" (Bit InstrSz);
     hw_bus_load_instr_kick := typed_register_value old "bus_load_instr_kick" (Bool);
     hw_mu_tensor := typed_register_value old "mu_tensor" (Vector (Bit WordSz) MuTensorIdxSz);
     hw_module_tensors := typed_register_value old "module_tensors" (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz);
     hw_csr_status := typed_register_value old "csr_status" (Bit WordSz);
     hw_csr_heap_base := typed_register_value old "csr_heap_base" (Bit WordSz);
     hw_ptTable := typed_register_value old "ptTable" (Vector (Bit WordSz) PTableIdxSz);
     hw_pt_next_id := typed_register_value old "pt_next_id" (Bit PTableNextIdSz);
     hw_morph_src_table := typed_register_value old "morph_src_table" (Vector (Bit PTableIdxSz) MorphTableIdxSz);
     hw_morph_dst_table := typed_register_value old "morph_dst_table" (Vector (Bit PTableIdxSz) MorphTableIdxSz);
     hw_morph_coupling_desc_table := typed_register_value old "morph_coupling_desc_table" (Vector (Bit DescIdxSz) MorphTableIdxSz);
     hw_morph_valid_table := typed_register_value old "morph_valid_table" (Vector Bool MorphTableIdxSz);
     hw_morph_identity_table := typed_register_value old "morph_identity_table" (Vector Bool MorphTableIdxSz);
     hw_morph_next_id := typed_register_value old "morph_next_id" (Bit MorphTableNextIdSz);
     hw_coupling_desc_base_table := typed_register_value old "coupling_desc_base_table" (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz);
     hw_coupling_desc_count_table := typed_register_value old "coupling_desc_count_table" (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz);
     hw_coupling_desc_valid_table := typed_register_value old "coupling_desc_valid_table" (Vector Bool CouplingDescIdxSz);
     hw_coupling_desc_label_table := typed_register_value old "coupling_desc_label_table" (Vector (Bit WordSz) CouplingDescIdxSz);
     hw_coupling_desc_label_len_table := typed_register_value old "coupling_desc_label_len_table" (Vector (Bit 6) CouplingDescIdxSz);
     hw_coupling_desc_next_id := typed_register_value old "coupling_desc_next_id" (Bit DescTableNextIdSz);
     hw_coupling_pair_src_table := typed_register_value old "coupling_pair_src_table" (Vector (Bit WordSz) CouplingPairIdxSz);
     hw_coupling_pair_dst_table := typed_register_value old "coupling_pair_dst_table" (Vector (Bit WordSz) CouplingPairIdxSz);
     hw_coupling_pair_valid_table := typed_register_value old "coupling_pair_valid_table" (Vector Bool CouplingPairIdxSz);
     hw_coupling_pair_next_id := typed_register_value old "coupling_pair_next_id" (Bit DescTableNextIdSz);
     hw_mc_phase := typed_register_value old "mc_phase" (Bit 4);
     hw_mc_op := typed_register_value old "mc_op" (Bit 2);
     hw_mc_mem_base := typed_register_value old "mc_mem_base" (Bit WordSz);
     hw_mc_pair_count := typed_register_value old "mc_pair_count" (Bit CouplingPairCountSz);
     hw_mc_read_ptr := typed_register_value old "mc_read_ptr" (Bit WordSz);
     hw_mc_src1_base := typed_register_value old "mc_src1_base" (Bit CouplingPairIdxSz);
     hw_mc_src1_count := typed_register_value old "mc_src1_count" (Bit CouplingPairCountSz);
     hw_mc_src2_base := typed_register_value old "mc_src2_base" (Bit CouplingPairIdxSz);
     hw_mc_src2_count := typed_register_value old "mc_src2_count" (Bit CouplingPairCountSz);
     hw_mc_i := typed_register_value old "mc_i" (Bit CouplingPairCountSz);
     hw_mc_j := typed_register_value old "mc_j" (Bit CouplingPairCountSz);
     hw_mc_is_id1 := typed_register_value old "mc_is_id1" (Bool);
     hw_mc_is_id2 := typed_register_value old "mc_is_id2" (Bool);
     hw_mc_write_base := typed_register_value old "mc_write_base" (Bit DescTableNextIdSz);
     hw_mc_write_ptr := typed_register_value old "mc_write_ptr" (Bit DescTableNextIdSz);
     hw_mc_norm_ptr := typed_register_value old "mc_norm_ptr" (Bit DescTableNextIdSz);
     hw_mc_duplicate := typed_register_value old "mc_duplicate" (Bool);
     hw_mc_dst_reg := typed_register_value old "mc_dst_reg" (Bit RegIdxSz);
     hw_mc_morph_slot := typed_register_value old "mc_morph_slot" (Bit MorphTableIdxSz);
     hw_mc_new_src_mod := typed_register_value old "mc_new_src_mod" (Bit PTableIdxSz);
     hw_mc_new_dst_mod := typed_register_value old "mc_new_dst_mod" (Bit PTableIdxSz);
     hw_mc_cost := typed_register_value old "mc_cost" (Bit WordSz);
     hw_formula_desc_base_table := typed_register_value old "formula_desc_base_table" (Vector (Bit WordSz) FormulaDescIdxSz);
     hw_formula_desc_count_table := typed_register_value old "formula_desc_count_table" (Vector (Bit WordSz) FormulaDescIdxSz);
     hw_formula_desc_valid_table := typed_register_value old "formula_desc_valid_table" (Vector Bool FormulaDescIdxSz);
     hw_formula_desc_next_id := typed_register_value old "formula_desc_next_id" (Bit DescTableNextIdSz);
     hw_cert_desc_base_table := typed_register_value old "cert_desc_base_table" (Vector (Bit WordSz) CertDescIdxSz);
     hw_cert_desc_count_table := typed_register_value old "cert_desc_count_table" (Vector (Bit WordSz) CertDescIdxSz);
     hw_cert_desc_valid_table := typed_register_value old "cert_desc_valid_table" (Vector Bool CertDescIdxSz);
     hw_cert_desc_next_id := typed_register_value old "cert_desc_next_id" (Bit DescTableNextIdSz);
     hw_desc_meta_subtype_table := typed_register_value old "desc_meta_subtype_table" (Vector (Bit FormatSubtypeSz) DescMetaIdxSz);
     hw_desc_meta_kind_table := typed_register_value old "desc_meta_kind_table" (Vector (Bit DescKindFieldSz) DescMetaIdxSz);
     hw_desc_meta_inline_len_table := typed_register_value old "desc_meta_inline_len_table" (Vector (Bit InlineLenSz) DescMetaIdxSz);
     hw_desc_meta_aux_table := typed_register_value old "desc_meta_aux_table" (Vector (Bit WordSz) DescMetaIdxSz);
     hw_desc_meta_valid_table := typed_register_value old "desc_meta_valid_table" (Vector Bool DescMetaIdxSz);
     hw_desc_meta_next_id := typed_register_value old "desc_meta_next_id" (Bit DescTableNextIdSz);
     hw_wc_same_00 := typed_register_value old "wc_same_00" (Bit WordSz);
     hw_wc_diff_00 := typed_register_value old "wc_diff_00" (Bit WordSz);
     hw_wc_same_01 := typed_register_value old "wc_same_01" (Bit WordSz);
     hw_wc_diff_01 := typed_register_value old "wc_diff_01" (Bit WordSz);
     hw_wc_same_10 := typed_register_value old "wc_same_10" (Bit WordSz);
     hw_wc_diff_10 := typed_register_value old "wc_diff_10" (Bit WordSz);
     hw_wc_same_11 := typed_register_value old "wc_same_11" (Bit WordSz);
     hw_wc_diff_11 := typed_register_value old "wc_diff_11" (Bit WordSz) |}.

Lemma cpu_register_names : namesOf (getRegInits thieleCore) = ["pc"; "mu"; "err"; "halted"; "regs"; "mem"; "imem"; "partition_ops"; "mdl_ops"; "info_gain"; "error_code"; "logic_acc"; "cert_addr"; "active_module"; "mstatus"; "mcycle_lo"; "mcycle_hi"; "minstret_lo"; "minstret_hi"; "trap_vector"; "certified"; "lassert_phase"; "lassert_kind"; "lassert_fbase"; "lassert_cbase"; "lassert_flen"; "lassert_clen"; "lassert_nvars"; "lassert_fptr"; "lassert_cptr"; "lassert_fbuf"; "lassert_cbuf"; "lassert_clause_sat"; "lassert_counter_clause_sat"; "lassert_counter_seen_fail"; "chsh_phase"; "chsh_n00"; "chsh_n01"; "chsh_n10"; "chsh_n11"; "chsh_d00"; "chsh_d01"; "chsh_d10"; "chsh_d11"; "chsh_sign00"; "chsh_sign01"; "chsh_sign10"; "chsh_sign11"; "chsh_n00sq"; "chsh_n01sq"; "chsh_n10sq"; "chsh_n11sq"; "chsh_d00sq"; "chsh_d01sq"; "chsh_d10sq"; "chsh_d11sq"; "chsh_A_pos"; "chsh_A_neg_a"; "chsh_A_neg_b"; "chsh_B_pos"; "chsh_B_neg_a"; "chsh_B_neg_b"; "chsh_d00d01"; "chsh_n10n11"; "chsh_d10d11"; "chsh_n00n01"; "chsh_abs_C1"; "chsh_abs_C2"; "chsh_C_sq"; "chsh_A_times_B"; "chsh_check_result"; "bus_load_instr_addr"; "bus_load_instr_data"; "bus_load_instr_kick"; "mu_tensor"; "module_tensors"; "csr_status"; "csr_heap_base"; "ptTable"; "pt_next_id"; "morph_src_table"; "morph_dst_table"; "morph_coupling_desc_table"; "morph_valid_table"; "morph_identity_table"; "morph_next_id"; "coupling_desc_base_table"; "coupling_desc_count_table"; "coupling_desc_valid_table"; "coupling_desc_label_table"; "coupling_desc_label_len_table"; "coupling_desc_next_id"; "coupling_pair_src_table"; "coupling_pair_dst_table"; "coupling_pair_valid_table"; "coupling_pair_next_id"; "mc_phase"; "mc_op"; "mc_mem_base"; "mc_pair_count"; "mc_read_ptr"; "mc_src1_base"; "mc_src1_count"; "mc_src2_base"; "mc_src2_count"; "mc_i"; "mc_j"; "mc_is_id1"; "mc_is_id2"; "mc_write_base"; "mc_write_ptr"; "mc_norm_ptr"; "mc_duplicate"; "mc_dst_reg"; "mc_morph_slot"; "mc_new_src_mod"; "mc_new_dst_mod"; "mc_cost"; "formula_desc_base_table"; "formula_desc_count_table"; "formula_desc_valid_table"; "formula_desc_next_id"; "cert_desc_base_table"; "cert_desc_count_table"; "cert_desc_valid_table"; "cert_desc_next_id"; "desc_meta_subtype_table"; "desc_meta_kind_table"; "desc_meta_inline_len_table"; "desc_meta_aux_table"; "desc_meta_valid_table"; "desc_meta_next_id"; "wc_same_00"; "wc_diff_00"; "wc_same_01"; "wc_diff_01"; "wc_same_10"; "wc_diff_10"; "wc_same_11"; "wc_diff_11"].
Proof. vm_compute. reflexivity. Qed.

Theorem hwb_of_regs_complete : forall old (H : registers_match cpu_register_kind old),
  old = hwb_regs (hwb_of_regs old H).
Proof.
  intros old H. M.ext name.
  unfold hwb_regs.
  destruct (string_dec name "pc") as [E|N_pc].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_pc].
    apply typed_register_value_find. rewrite H. exact cpu_kind_pc. }
  rewrite M.find_add_2 by exact N_pc.
  destruct (string_dec name "mu") as [E|N_mu].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mu].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mu. }
  rewrite M.find_add_2 by exact N_mu.
  destruct (string_dec name "err") as [E|N_err].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_err].
    apply typed_register_value_find. rewrite H. exact cpu_kind_err. }
  rewrite M.find_add_2 by exact N_err.
  destruct (string_dec name "halted") as [E|N_halted].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_halted].
    apply typed_register_value_find. rewrite H. exact cpu_kind_halted. }
  rewrite M.find_add_2 by exact N_halted.
  destruct (string_dec name "regs") as [E|N_regs].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_regs].
    apply typed_register_value_find. rewrite H. exact cpu_kind_regs. }
  rewrite M.find_add_2 by exact N_regs.
  destruct (string_dec name "mem") as [E|N_mem].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mem].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mem. }
  rewrite M.find_add_2 by exact N_mem.
  destruct (string_dec name "imem") as [E|N_imem].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_imem].
    apply typed_register_value_find. rewrite H. exact cpu_kind_imem. }
  rewrite M.find_add_2 by exact N_imem.
  destruct (string_dec name "partition_ops") as [E|N_partition_ops].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_partition_ops].
    apply typed_register_value_find. rewrite H. exact cpu_kind_partition_ops. }
  rewrite M.find_add_2 by exact N_partition_ops.
  destruct (string_dec name "mdl_ops") as [E|N_mdl_ops].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mdl_ops].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mdl_ops. }
  rewrite M.find_add_2 by exact N_mdl_ops.
  destruct (string_dec name "info_gain") as [E|N_info_gain].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_info_gain].
    apply typed_register_value_find. rewrite H. exact cpu_kind_info_gain. }
  rewrite M.find_add_2 by exact N_info_gain.
  destruct (string_dec name "error_code") as [E|N_error_code].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_error_code].
    apply typed_register_value_find. rewrite H. exact cpu_kind_error_code. }
  rewrite M.find_add_2 by exact N_error_code.
  destruct (string_dec name "logic_acc") as [E|N_logic_acc].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_logic_acc].
    apply typed_register_value_find. rewrite H. exact cpu_kind_logic_acc. }
  rewrite M.find_add_2 by exact N_logic_acc.
  destruct (string_dec name "cert_addr") as [E|N_cert_addr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_cert_addr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_cert_addr. }
  rewrite M.find_add_2 by exact N_cert_addr.
  destruct (string_dec name "active_module") as [E|N_active_module].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_active_module].
    apply typed_register_value_find. rewrite H. exact cpu_kind_active_module. }
  rewrite M.find_add_2 by exact N_active_module.
  destruct (string_dec name "mstatus") as [E|N_mstatus].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mstatus].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mstatus. }
  rewrite M.find_add_2 by exact N_mstatus.
  destruct (string_dec name "mcycle_lo") as [E|N_mcycle_lo].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mcycle_lo].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mcycle_lo. }
  rewrite M.find_add_2 by exact N_mcycle_lo.
  destruct (string_dec name "mcycle_hi") as [E|N_mcycle_hi].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mcycle_hi].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mcycle_hi. }
  rewrite M.find_add_2 by exact N_mcycle_hi.
  destruct (string_dec name "minstret_lo") as [E|N_minstret_lo].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_minstret_lo].
    apply typed_register_value_find. rewrite H. exact cpu_kind_minstret_lo. }
  rewrite M.find_add_2 by exact N_minstret_lo.
  destruct (string_dec name "minstret_hi") as [E|N_minstret_hi].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_minstret_hi].
    apply typed_register_value_find. rewrite H. exact cpu_kind_minstret_hi. }
  rewrite M.find_add_2 by exact N_minstret_hi.
  destruct (string_dec name "trap_vector") as [E|N_trap_vector].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_trap_vector].
    apply typed_register_value_find. rewrite H. exact cpu_kind_trap_vector. }
  rewrite M.find_add_2 by exact N_trap_vector.
  destruct (string_dec name "certified") as [E|N_certified].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_certified].
    apply typed_register_value_find. rewrite H. exact cpu_kind_certified. }
  rewrite M.find_add_2 by exact N_certified.
  destruct (string_dec name "lassert_phase") as [E|N_lassert_phase].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_phase].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_phase. }
  rewrite M.find_add_2 by exact N_lassert_phase.
  destruct (string_dec name "lassert_kind") as [E|N_lassert_kind].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_kind].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_kind. }
  rewrite M.find_add_2 by exact N_lassert_kind.
  destruct (string_dec name "lassert_fbase") as [E|N_lassert_fbase].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_fbase].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_fbase. }
  rewrite M.find_add_2 by exact N_lassert_fbase.
  destruct (string_dec name "lassert_cbase") as [E|N_lassert_cbase].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_cbase].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_cbase. }
  rewrite M.find_add_2 by exact N_lassert_cbase.
  destruct (string_dec name "lassert_flen") as [E|N_lassert_flen].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_flen].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_flen. }
  rewrite M.find_add_2 by exact N_lassert_flen.
  destruct (string_dec name "lassert_clen") as [E|N_lassert_clen].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_clen].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_clen. }
  rewrite M.find_add_2 by exact N_lassert_clen.
  destruct (string_dec name "lassert_nvars") as [E|N_lassert_nvars].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_nvars].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_nvars. }
  rewrite M.find_add_2 by exact N_lassert_nvars.
  destruct (string_dec name "lassert_fptr") as [E|N_lassert_fptr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_fptr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_fptr. }
  rewrite M.find_add_2 by exact N_lassert_fptr.
  destruct (string_dec name "lassert_cptr") as [E|N_lassert_cptr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_cptr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_cptr. }
  rewrite M.find_add_2 by exact N_lassert_cptr.
  destruct (string_dec name "lassert_fbuf") as [E|N_lassert_fbuf].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_fbuf].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_fbuf. }
  rewrite M.find_add_2 by exact N_lassert_fbuf.
  destruct (string_dec name "lassert_cbuf") as [E|N_lassert_cbuf].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_cbuf].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_cbuf. }
  rewrite M.find_add_2 by exact N_lassert_cbuf.
  destruct (string_dec name "lassert_clause_sat") as [E|N_lassert_clause_sat].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_clause_sat].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_clause_sat. }
  rewrite M.find_add_2 by exact N_lassert_clause_sat.
  destruct (string_dec name "lassert_counter_clause_sat") as [E|N_lassert_counter_clause_sat].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_counter_clause_sat].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_counter_clause_sat. }
  rewrite M.find_add_2 by exact N_lassert_counter_clause_sat.
  destruct (string_dec name "lassert_counter_seen_fail") as [E|N_lassert_counter_seen_fail].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_lassert_counter_seen_fail].
    apply typed_register_value_find. rewrite H. exact cpu_kind_lassert_counter_seen_fail. }
  rewrite M.find_add_2 by exact N_lassert_counter_seen_fail.
  destruct (string_dec name "chsh_phase") as [E|N_chsh_phase].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_phase].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_phase. }
  rewrite M.find_add_2 by exact N_chsh_phase.
  destruct (string_dec name "chsh_n00") as [E|N_chsh_n00].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n00].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n00. }
  rewrite M.find_add_2 by exact N_chsh_n00.
  destruct (string_dec name "chsh_n01") as [E|N_chsh_n01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n01. }
  rewrite M.find_add_2 by exact N_chsh_n01.
  destruct (string_dec name "chsh_n10") as [E|N_chsh_n10].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n10].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n10. }
  rewrite M.find_add_2 by exact N_chsh_n10.
  destruct (string_dec name "chsh_n11") as [E|N_chsh_n11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n11. }
  rewrite M.find_add_2 by exact N_chsh_n11.
  destruct (string_dec name "chsh_d00") as [E|N_chsh_d00].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d00].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d00. }
  rewrite M.find_add_2 by exact N_chsh_d00.
  destruct (string_dec name "chsh_d01") as [E|N_chsh_d01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d01. }
  rewrite M.find_add_2 by exact N_chsh_d01.
  destruct (string_dec name "chsh_d10") as [E|N_chsh_d10].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d10].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d10. }
  rewrite M.find_add_2 by exact N_chsh_d10.
  destruct (string_dec name "chsh_d11") as [E|N_chsh_d11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d11. }
  rewrite M.find_add_2 by exact N_chsh_d11.
  destruct (string_dec name "chsh_sign00") as [E|N_chsh_sign00].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_sign00].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_sign00. }
  rewrite M.find_add_2 by exact N_chsh_sign00.
  destruct (string_dec name "chsh_sign01") as [E|N_chsh_sign01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_sign01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_sign01. }
  rewrite M.find_add_2 by exact N_chsh_sign01.
  destruct (string_dec name "chsh_sign10") as [E|N_chsh_sign10].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_sign10].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_sign10. }
  rewrite M.find_add_2 by exact N_chsh_sign10.
  destruct (string_dec name "chsh_sign11") as [E|N_chsh_sign11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_sign11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_sign11. }
  rewrite M.find_add_2 by exact N_chsh_sign11.
  destruct (string_dec name "chsh_n00sq") as [E|N_chsh_n00sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n00sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n00sq. }
  rewrite M.find_add_2 by exact N_chsh_n00sq.
  destruct (string_dec name "chsh_n01sq") as [E|N_chsh_n01sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n01sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n01sq. }
  rewrite M.find_add_2 by exact N_chsh_n01sq.
  destruct (string_dec name "chsh_n10sq") as [E|N_chsh_n10sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n10sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n10sq. }
  rewrite M.find_add_2 by exact N_chsh_n10sq.
  destruct (string_dec name "chsh_n11sq") as [E|N_chsh_n11sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n11sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n11sq. }
  rewrite M.find_add_2 by exact N_chsh_n11sq.
  destruct (string_dec name "chsh_d00sq") as [E|N_chsh_d00sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d00sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d00sq. }
  rewrite M.find_add_2 by exact N_chsh_d00sq.
  destruct (string_dec name "chsh_d01sq") as [E|N_chsh_d01sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d01sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d01sq. }
  rewrite M.find_add_2 by exact N_chsh_d01sq.
  destruct (string_dec name "chsh_d10sq") as [E|N_chsh_d10sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d10sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d10sq. }
  rewrite M.find_add_2 by exact N_chsh_d10sq.
  destruct (string_dec name "chsh_d11sq") as [E|N_chsh_d11sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d11sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d11sq. }
  rewrite M.find_add_2 by exact N_chsh_d11sq.
  destruct (string_dec name "chsh_A_pos") as [E|N_chsh_A_pos].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_A_pos].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_A_pos. }
  rewrite M.find_add_2 by exact N_chsh_A_pos.
  destruct (string_dec name "chsh_A_neg_a") as [E|N_chsh_A_neg_a].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_A_neg_a].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_A_neg_a. }
  rewrite M.find_add_2 by exact N_chsh_A_neg_a.
  destruct (string_dec name "chsh_A_neg_b") as [E|N_chsh_A_neg_b].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_A_neg_b].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_A_neg_b. }
  rewrite M.find_add_2 by exact N_chsh_A_neg_b.
  destruct (string_dec name "chsh_B_pos") as [E|N_chsh_B_pos].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_B_pos].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_B_pos. }
  rewrite M.find_add_2 by exact N_chsh_B_pos.
  destruct (string_dec name "chsh_B_neg_a") as [E|N_chsh_B_neg_a].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_B_neg_a].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_B_neg_a. }
  rewrite M.find_add_2 by exact N_chsh_B_neg_a.
  destruct (string_dec name "chsh_B_neg_b") as [E|N_chsh_B_neg_b].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_B_neg_b].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_B_neg_b. }
  rewrite M.find_add_2 by exact N_chsh_B_neg_b.
  destruct (string_dec name "chsh_d00d01") as [E|N_chsh_d00d01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d00d01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d00d01. }
  rewrite M.find_add_2 by exact N_chsh_d00d01.
  destruct (string_dec name "chsh_n10n11") as [E|N_chsh_n10n11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n10n11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n10n11. }
  rewrite M.find_add_2 by exact N_chsh_n10n11.
  destruct (string_dec name "chsh_d10d11") as [E|N_chsh_d10d11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_d10d11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_d10d11. }
  rewrite M.find_add_2 by exact N_chsh_d10d11.
  destruct (string_dec name "chsh_n00n01") as [E|N_chsh_n00n01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_n00n01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_n00n01. }
  rewrite M.find_add_2 by exact N_chsh_n00n01.
  destruct (string_dec name "chsh_abs_C1") as [E|N_chsh_abs_C1].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_abs_C1].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_abs_C1. }
  rewrite M.find_add_2 by exact N_chsh_abs_C1.
  destruct (string_dec name "chsh_abs_C2") as [E|N_chsh_abs_C2].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_abs_C2].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_abs_C2. }
  rewrite M.find_add_2 by exact N_chsh_abs_C2.
  destruct (string_dec name "chsh_C_sq") as [E|N_chsh_C_sq].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_C_sq].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_C_sq. }
  rewrite M.find_add_2 by exact N_chsh_C_sq.
  destruct (string_dec name "chsh_A_times_B") as [E|N_chsh_A_times_B].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_A_times_B].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_A_times_B. }
  rewrite M.find_add_2 by exact N_chsh_A_times_B.
  destruct (string_dec name "chsh_check_result") as [E|N_chsh_check_result].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_chsh_check_result].
    apply typed_register_value_find. rewrite H. exact cpu_kind_chsh_check_result. }
  rewrite M.find_add_2 by exact N_chsh_check_result.
  destruct (string_dec name "bus_load_instr_addr") as [E|N_bus_load_instr_addr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_bus_load_instr_addr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_bus_load_instr_addr. }
  rewrite M.find_add_2 by exact N_bus_load_instr_addr.
  destruct (string_dec name "bus_load_instr_data") as [E|N_bus_load_instr_data].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_bus_load_instr_data].
    apply typed_register_value_find. rewrite H. exact cpu_kind_bus_load_instr_data. }
  rewrite M.find_add_2 by exact N_bus_load_instr_data.
  destruct (string_dec name "bus_load_instr_kick") as [E|N_bus_load_instr_kick].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_bus_load_instr_kick].
    apply typed_register_value_find. rewrite H. exact cpu_kind_bus_load_instr_kick. }
  rewrite M.find_add_2 by exact N_bus_load_instr_kick.
  destruct (string_dec name "mu_tensor") as [E|N_mu_tensor].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mu_tensor].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mu_tensor. }
  rewrite M.find_add_2 by exact N_mu_tensor.
  destruct (string_dec name "module_tensors") as [E|N_module_tensors].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_module_tensors].
    apply typed_register_value_find. rewrite H. exact cpu_kind_module_tensors. }
  rewrite M.find_add_2 by exact N_module_tensors.
  destruct (string_dec name "csr_status") as [E|N_csr_status].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_csr_status].
    apply typed_register_value_find. rewrite H. exact cpu_kind_csr_status. }
  rewrite M.find_add_2 by exact N_csr_status.
  destruct (string_dec name "csr_heap_base") as [E|N_csr_heap_base].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_csr_heap_base].
    apply typed_register_value_find. rewrite H. exact cpu_kind_csr_heap_base. }
  rewrite M.find_add_2 by exact N_csr_heap_base.
  destruct (string_dec name "ptTable") as [E|N_ptTable].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_ptTable].
    apply typed_register_value_find. rewrite H. exact cpu_kind_ptTable. }
  rewrite M.find_add_2 by exact N_ptTable.
  destruct (string_dec name "pt_next_id") as [E|N_pt_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_pt_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_pt_next_id. }
  rewrite M.find_add_2 by exact N_pt_next_id.
  destruct (string_dec name "morph_src_table") as [E|N_morph_src_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_morph_src_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_morph_src_table. }
  rewrite M.find_add_2 by exact N_morph_src_table.
  destruct (string_dec name "morph_dst_table") as [E|N_morph_dst_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_morph_dst_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_morph_dst_table. }
  rewrite M.find_add_2 by exact N_morph_dst_table.
  destruct (string_dec name "morph_coupling_desc_table") as [E|N_morph_coupling_desc_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_morph_coupling_desc_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_morph_coupling_desc_table. }
  rewrite M.find_add_2 by exact N_morph_coupling_desc_table.
  destruct (string_dec name "morph_valid_table") as [E|N_morph_valid_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_morph_valid_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_morph_valid_table. }
  rewrite M.find_add_2 by exact N_morph_valid_table.
  destruct (string_dec name "morph_identity_table") as [E|N_morph_identity_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_morph_identity_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_morph_identity_table. }
  rewrite M.find_add_2 by exact N_morph_identity_table.
  destruct (string_dec name "morph_next_id") as [E|N_morph_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_morph_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_morph_next_id. }
  rewrite M.find_add_2 by exact N_morph_next_id.
  destruct (string_dec name "coupling_desc_base_table") as [E|N_coupling_desc_base_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_desc_base_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_desc_base_table. }
  rewrite M.find_add_2 by exact N_coupling_desc_base_table.
  destruct (string_dec name "coupling_desc_count_table") as [E|N_coupling_desc_count_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_desc_count_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_desc_count_table. }
  rewrite M.find_add_2 by exact N_coupling_desc_count_table.
  destruct (string_dec name "coupling_desc_valid_table") as [E|N_coupling_desc_valid_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_desc_valid_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_desc_valid_table. }
  rewrite M.find_add_2 by exact N_coupling_desc_valid_table.
  destruct (string_dec name "coupling_desc_label_table") as [E|N_coupling_desc_label_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_desc_label_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_desc_label_table. }
  rewrite M.find_add_2 by exact N_coupling_desc_label_table.
  destruct (string_dec name "coupling_desc_label_len_table") as [E|N_coupling_desc_label_len_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_desc_label_len_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_desc_label_len_table. }
  rewrite M.find_add_2 by exact N_coupling_desc_label_len_table.
  destruct (string_dec name "coupling_desc_next_id") as [E|N_coupling_desc_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_desc_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_desc_next_id. }
  rewrite M.find_add_2 by exact N_coupling_desc_next_id.
  destruct (string_dec name "coupling_pair_src_table") as [E|N_coupling_pair_src_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_pair_src_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_pair_src_table. }
  rewrite M.find_add_2 by exact N_coupling_pair_src_table.
  destruct (string_dec name "coupling_pair_dst_table") as [E|N_coupling_pair_dst_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_pair_dst_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_pair_dst_table. }
  rewrite M.find_add_2 by exact N_coupling_pair_dst_table.
  destruct (string_dec name "coupling_pair_valid_table") as [E|N_coupling_pair_valid_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_pair_valid_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_pair_valid_table. }
  rewrite M.find_add_2 by exact N_coupling_pair_valid_table.
  destruct (string_dec name "coupling_pair_next_id") as [E|N_coupling_pair_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_coupling_pair_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_coupling_pair_next_id. }
  rewrite M.find_add_2 by exact N_coupling_pair_next_id.
  destruct (string_dec name "mc_phase") as [E|N_mc_phase].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_phase].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_phase. }
  rewrite M.find_add_2 by exact N_mc_phase.
  destruct (string_dec name "mc_op") as [E|N_mc_op].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_op].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_op. }
  rewrite M.find_add_2 by exact N_mc_op.
  destruct (string_dec name "mc_mem_base") as [E|N_mc_mem_base].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_mem_base].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_mem_base. }
  rewrite M.find_add_2 by exact N_mc_mem_base.
  destruct (string_dec name "mc_pair_count") as [E|N_mc_pair_count].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_pair_count].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_pair_count. }
  rewrite M.find_add_2 by exact N_mc_pair_count.
  destruct (string_dec name "mc_read_ptr") as [E|N_mc_read_ptr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_read_ptr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_read_ptr. }
  rewrite M.find_add_2 by exact N_mc_read_ptr.
  destruct (string_dec name "mc_src1_base") as [E|N_mc_src1_base].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_src1_base].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_src1_base. }
  rewrite M.find_add_2 by exact N_mc_src1_base.
  destruct (string_dec name "mc_src1_count") as [E|N_mc_src1_count].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_src1_count].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_src1_count. }
  rewrite M.find_add_2 by exact N_mc_src1_count.
  destruct (string_dec name "mc_src2_base") as [E|N_mc_src2_base].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_src2_base].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_src2_base. }
  rewrite M.find_add_2 by exact N_mc_src2_base.
  destruct (string_dec name "mc_src2_count") as [E|N_mc_src2_count].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_src2_count].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_src2_count. }
  rewrite M.find_add_2 by exact N_mc_src2_count.
  destruct (string_dec name "mc_i") as [E|N_mc_i].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_i].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_i. }
  rewrite M.find_add_2 by exact N_mc_i.
  destruct (string_dec name "mc_j") as [E|N_mc_j].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_j].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_j. }
  rewrite M.find_add_2 by exact N_mc_j.
  destruct (string_dec name "mc_is_id1") as [E|N_mc_is_id1].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_is_id1].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_is_id1. }
  rewrite M.find_add_2 by exact N_mc_is_id1.
  destruct (string_dec name "mc_is_id2") as [E|N_mc_is_id2].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_is_id2].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_is_id2. }
  rewrite M.find_add_2 by exact N_mc_is_id2.
  destruct (string_dec name "mc_write_base") as [E|N_mc_write_base].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_write_base].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_write_base. }
  rewrite M.find_add_2 by exact N_mc_write_base.
  destruct (string_dec name "mc_write_ptr") as [E|N_mc_write_ptr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_write_ptr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_write_ptr. }
  rewrite M.find_add_2 by exact N_mc_write_ptr.
  destruct (string_dec name "mc_norm_ptr") as [E|N_mc_norm_ptr].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_norm_ptr].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_norm_ptr. }
  rewrite M.find_add_2 by exact N_mc_norm_ptr.
  destruct (string_dec name "mc_duplicate") as [E|N_mc_duplicate].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_duplicate].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_duplicate. }
  rewrite M.find_add_2 by exact N_mc_duplicate.
  destruct (string_dec name "mc_dst_reg") as [E|N_mc_dst_reg].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_dst_reg].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_dst_reg. }
  rewrite M.find_add_2 by exact N_mc_dst_reg.
  destruct (string_dec name "mc_morph_slot") as [E|N_mc_morph_slot].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_morph_slot].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_morph_slot. }
  rewrite M.find_add_2 by exact N_mc_morph_slot.
  destruct (string_dec name "mc_new_src_mod") as [E|N_mc_new_src_mod].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_new_src_mod].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_new_src_mod. }
  rewrite M.find_add_2 by exact N_mc_new_src_mod.
  destruct (string_dec name "mc_new_dst_mod") as [E|N_mc_new_dst_mod].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_new_dst_mod].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_new_dst_mod. }
  rewrite M.find_add_2 by exact N_mc_new_dst_mod.
  destruct (string_dec name "mc_cost") as [E|N_mc_cost].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_mc_cost].
    apply typed_register_value_find. rewrite H. exact cpu_kind_mc_cost. }
  rewrite M.find_add_2 by exact N_mc_cost.
  destruct (string_dec name "formula_desc_base_table") as [E|N_formula_desc_base_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_formula_desc_base_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_formula_desc_base_table. }
  rewrite M.find_add_2 by exact N_formula_desc_base_table.
  destruct (string_dec name "formula_desc_count_table") as [E|N_formula_desc_count_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_formula_desc_count_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_formula_desc_count_table. }
  rewrite M.find_add_2 by exact N_formula_desc_count_table.
  destruct (string_dec name "formula_desc_valid_table") as [E|N_formula_desc_valid_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_formula_desc_valid_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_formula_desc_valid_table. }
  rewrite M.find_add_2 by exact N_formula_desc_valid_table.
  destruct (string_dec name "formula_desc_next_id") as [E|N_formula_desc_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_formula_desc_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_formula_desc_next_id. }
  rewrite M.find_add_2 by exact N_formula_desc_next_id.
  destruct (string_dec name "cert_desc_base_table") as [E|N_cert_desc_base_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_cert_desc_base_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_cert_desc_base_table. }
  rewrite M.find_add_2 by exact N_cert_desc_base_table.
  destruct (string_dec name "cert_desc_count_table") as [E|N_cert_desc_count_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_cert_desc_count_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_cert_desc_count_table. }
  rewrite M.find_add_2 by exact N_cert_desc_count_table.
  destruct (string_dec name "cert_desc_valid_table") as [E|N_cert_desc_valid_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_cert_desc_valid_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_cert_desc_valid_table. }
  rewrite M.find_add_2 by exact N_cert_desc_valid_table.
  destruct (string_dec name "cert_desc_next_id") as [E|N_cert_desc_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_cert_desc_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_cert_desc_next_id. }
  rewrite M.find_add_2 by exact N_cert_desc_next_id.
  destruct (string_dec name "desc_meta_subtype_table") as [E|N_desc_meta_subtype_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_desc_meta_subtype_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_desc_meta_subtype_table. }
  rewrite M.find_add_2 by exact N_desc_meta_subtype_table.
  destruct (string_dec name "desc_meta_kind_table") as [E|N_desc_meta_kind_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_desc_meta_kind_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_desc_meta_kind_table. }
  rewrite M.find_add_2 by exact N_desc_meta_kind_table.
  destruct (string_dec name "desc_meta_inline_len_table") as [E|N_desc_meta_inline_len_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_desc_meta_inline_len_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_desc_meta_inline_len_table. }
  rewrite M.find_add_2 by exact N_desc_meta_inline_len_table.
  destruct (string_dec name "desc_meta_aux_table") as [E|N_desc_meta_aux_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_desc_meta_aux_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_desc_meta_aux_table. }
  rewrite M.find_add_2 by exact N_desc_meta_aux_table.
  destruct (string_dec name "desc_meta_valid_table") as [E|N_desc_meta_valid_table].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_desc_meta_valid_table].
    apply typed_register_value_find. rewrite H. exact cpu_kind_desc_meta_valid_table. }
  rewrite M.find_add_2 by exact N_desc_meta_valid_table.
  destruct (string_dec name "desc_meta_next_id") as [E|N_desc_meta_next_id].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_desc_meta_next_id].
    apply typed_register_value_find. rewrite H. exact cpu_kind_desc_meta_next_id. }
  rewrite M.find_add_2 by exact N_desc_meta_next_id.
  destruct (string_dec name "wc_same_00") as [E|N_wc_same_00].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_same_00].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_same_00. }
  rewrite M.find_add_2 by exact N_wc_same_00.
  destruct (string_dec name "wc_diff_00") as [E|N_wc_diff_00].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_diff_00].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_diff_00. }
  rewrite M.find_add_2 by exact N_wc_diff_00.
  destruct (string_dec name "wc_same_01") as [E|N_wc_same_01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_same_01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_same_01. }
  rewrite M.find_add_2 by exact N_wc_same_01.
  destruct (string_dec name "wc_diff_01") as [E|N_wc_diff_01].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_diff_01].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_diff_01. }
  rewrite M.find_add_2 by exact N_wc_diff_01.
  destruct (string_dec name "wc_same_10") as [E|N_wc_same_10].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_same_10].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_same_10. }
  rewrite M.find_add_2 by exact N_wc_same_10.
  destruct (string_dec name "wc_diff_10") as [E|N_wc_diff_10].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_diff_10].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_diff_10. }
  rewrite M.find_add_2 by exact N_wc_diff_10.
  destruct (string_dec name "wc_same_11") as [E|N_wc_same_11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_same_11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_same_11. }
  rewrite M.find_add_2 by exact N_wc_same_11.
  destruct (string_dec name "wc_diff_11") as [E|N_wc_diff_11].
  { subst name. rewrite M.find_add_1. cbn [hwb_of_regs hw_wc_diff_11].
    apply typed_register_value_find. rewrite H. exact cpu_kind_wc_diff_11. }
  rewrite M.find_add_2 by exact N_wc_diff_11.
    rewrite M.find_empty.
    specialize (H name). unfold register_kind in H.
    assert (Hnone : cpu_register_kind name = None).
    { unfold cpu_register_kind, register_kind, dispatch_reset_state, initRegs.
      assert (Habs : ~ List.In name (namesOf (rawInitRegs (getRegInits thieleCore)))).
      { rewrite <- rawInitRegs_namesOf.
        rewrite cpu_register_names.
        cbn. intro Hin.
        destruct Hin as [Hin|Hin]. { apply N_pc. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mu. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_err. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_halted. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_regs. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mem. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_imem. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_partition_ops. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mdl_ops. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_info_gain. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_error_code. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_logic_acc. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_cert_addr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_active_module. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mstatus. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mcycle_lo. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mcycle_hi. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_minstret_lo. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_minstret_hi. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_trap_vector. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_certified. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_phase. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_kind. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_fbase. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_cbase. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_flen. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_clen. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_nvars. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_fptr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_cptr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_fbuf. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_cbuf. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_clause_sat. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_counter_clause_sat. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_lassert_counter_seen_fail. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_phase. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n00. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n10. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n11. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d00. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d10. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d11. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_sign00. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_sign01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_sign10. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_sign11. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n00sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n01sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n10sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n11sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d00sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d01sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d10sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d11sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_A_pos. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_A_neg_a. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_A_neg_b. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_B_pos. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_B_neg_a. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_B_neg_b. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d00d01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n10n11. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_d10d11. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_n00n01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_abs_C1. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_abs_C2. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_C_sq. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_A_times_B. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_chsh_check_result. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_bus_load_instr_addr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_bus_load_instr_data. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_bus_load_instr_kick. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mu_tensor. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_module_tensors. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_csr_status. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_csr_heap_base. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_ptTable. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_pt_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_morph_src_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_morph_dst_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_morph_coupling_desc_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_morph_valid_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_morph_identity_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_morph_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_desc_base_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_desc_count_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_desc_valid_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_desc_label_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_desc_label_len_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_desc_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_pair_src_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_pair_dst_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_pair_valid_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_coupling_pair_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_phase. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_op. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_mem_base. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_pair_count. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_read_ptr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_src1_base. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_src1_count. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_src2_base. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_src2_count. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_i. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_j. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_is_id1. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_is_id2. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_write_base. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_write_ptr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_norm_ptr. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_duplicate. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_dst_reg. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_morph_slot. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_new_src_mod. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_new_dst_mod. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_mc_cost. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_formula_desc_base_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_formula_desc_count_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_formula_desc_valid_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_formula_desc_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_cert_desc_base_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_cert_desc_count_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_cert_desc_valid_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_cert_desc_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_desc_meta_subtype_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_desc_meta_kind_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_desc_meta_inline_len_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_desc_meta_aux_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_desc_meta_valid_table. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_desc_meta_next_id. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_same_00. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_diff_00. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_same_01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_diff_01. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_same_10. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_diff_10. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_same_11. symmetry. exact Hin. }
        destruct Hin as [Hin|Hin]. { apply N_wc_diff_11. symmetry. exact Hin. }
        exact Hin. }
      erewrite M.find_KeysSubset.
      - reflexivity.
      - apply makeMap_KeysSubset.
      - exact Habs. }
    rewrite Hnone in H.
    destruct (M.find name old) as [[k v]|]; [discriminate|reflexivity].
Qed.

Theorem cpu_register_map_has_boundary : forall old,
  registers_match cpu_register_kind old -> exists b : HWB, old = hwb_regs b.
Proof. intros old H. exists (hwb_of_regs old H). apply hwb_of_regs_complete. Qed.

Corollary cpu_reset_run_has_boundary : forall fuel,
  exists b : HWB, fst (run_cpu_rules fuel dispatch_reset_state) = hwb_regs b.
Proof.
  intro fuel. apply cpu_register_map_has_boundary.
  apply cpu_reset_run_register_schema.
Qed.
