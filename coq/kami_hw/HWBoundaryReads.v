(** Typed reads of every hardware boundary field. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes HWBoundary ActionEvaluator.
From Coq Require Import String.
Open Scope string_scope.

Lemma hwb_read_pc : forall b,
  action_read (hwb_regs b) "pc" (SyntaxKind (Bit WordSz)) = Some (hw_pc b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mu : forall b,
  action_read (hwb_regs b) "mu" (SyntaxKind (Bit WordSz)) = Some (hw_mu b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_err : forall b,
  action_read (hwb_regs b) "err" (SyntaxKind (Bool)) = Some (hw_err b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_halted : forall b,
  action_read (hwb_regs b) "halted" (SyntaxKind (Bool)) = Some (hw_halted b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_regs : forall b,
  action_read (hwb_regs b) "regs" (SyntaxKind (Vector (Bit WordSz) RegIdxSz)) = Some (hw_regs b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mem : forall b,
  action_read (hwb_regs b) "mem" (SyntaxKind (Vector (Bit WordSz) MemAddrSz)) = Some (hw_mem b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_imem : forall b,
  action_read (hwb_regs b) "imem" (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)) = Some (hw_imem b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_partition_ops : forall b,
  action_read (hwb_regs b) "partition_ops" (SyntaxKind (Bit WordSz)) = Some (hw_partition_ops b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mdl_ops : forall b,
  action_read (hwb_regs b) "mdl_ops" (SyntaxKind (Bit WordSz)) = Some (hw_mdl_ops b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_info_gain : forall b,
  action_read (hwb_regs b) "info_gain" (SyntaxKind (Bit WordSz)) = Some (hw_info_gain b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_error_code : forall b,
  action_read (hwb_regs b) "error_code" (SyntaxKind (Bit WordSz)) = Some (hw_error_code b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_logic_acc : forall b,
  action_read (hwb_regs b) "logic_acc" (SyntaxKind (Bit WordSz)) = Some (hw_logic_acc b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_cert_addr : forall b,
  action_read (hwb_regs b) "cert_addr" (SyntaxKind (Bit WordSz)) = Some (hw_cert_addr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_active_module : forall b,
  action_read (hwb_regs b) "active_module" (SyntaxKind (Bit PTableIdxSz)) = Some (hw_active_module b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mstatus : forall b,
  action_read (hwb_regs b) "mstatus" (SyntaxKind (Bit WordSz)) = Some (hw_mstatus b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mcycle_lo : forall b,
  action_read (hwb_regs b) "mcycle_lo" (SyntaxKind (Bit WordSz)) = Some (hw_mcycle_lo b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mcycle_hi : forall b,
  action_read (hwb_regs b) "mcycle_hi" (SyntaxKind (Bit WordSz)) = Some (hw_mcycle_hi b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_minstret_lo : forall b,
  action_read (hwb_regs b) "minstret_lo" (SyntaxKind (Bit WordSz)) = Some (hw_minstret_lo b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_minstret_hi : forall b,
  action_read (hwb_regs b) "minstret_hi" (SyntaxKind (Bit WordSz)) = Some (hw_minstret_hi b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_trap_vector : forall b,
  action_read (hwb_regs b) "trap_vector" (SyntaxKind (Bit WordSz)) = Some (hw_trap_vector b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_certified : forall b,
  action_read (hwb_regs b) "certified" (SyntaxKind (Bool)) = Some (hw_certified b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_phase : forall b,
  action_read (hwb_regs b) "lassert_phase" (SyntaxKind (Bit 3)) = Some (hw_lassert_phase b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_kind : forall b,
  action_read (hwb_regs b) "lassert_kind" (SyntaxKind (Bool)) = Some (hw_lassert_kind b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_fbase : forall b,
  action_read (hwb_regs b) "lassert_fbase" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_fbase b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_cbase : forall b,
  action_read (hwb_regs b) "lassert_cbase" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_cbase b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_flen : forall b,
  action_read (hwb_regs b) "lassert_flen" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_flen b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_clen : forall b,
  action_read (hwb_regs b) "lassert_clen" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_clen b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_nvars : forall b,
  action_read (hwb_regs b) "lassert_nvars" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_nvars b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_fptr : forall b,
  action_read (hwb_regs b) "lassert_fptr" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_fptr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_cptr : forall b,
  action_read (hwb_regs b) "lassert_cptr" (SyntaxKind (Bit WordSz)) = Some (hw_lassert_cptr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_fbuf : forall b,
  action_read (hwb_regs b) "lassert_fbuf" (SyntaxKind (Vector (Bit WordSz) 6)) = Some (hw_lassert_fbuf b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_cbuf : forall b,
  action_read (hwb_regs b) "lassert_cbuf" (SyntaxKind (Vector (Bit WordSz) 6)) = Some (hw_lassert_cbuf b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_clause_sat : forall b,
  action_read (hwb_regs b) "lassert_clause_sat" (SyntaxKind (Bool)) = Some (hw_lassert_clause_sat b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_counter_clause_sat : forall b,
  action_read (hwb_regs b) "lassert_counter_clause_sat" (SyntaxKind (Bool)) = Some (hw_lassert_counter_clause_sat b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_lassert_counter_seen_fail : forall b,
  action_read (hwb_regs b) "lassert_counter_seen_fail" (SyntaxKind (Bool)) = Some (hw_lassert_counter_seen_fail b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_phase : forall b,
  action_read (hwb_regs b) "chsh_phase" (SyntaxKind (Bit 5)) = Some (hw_chsh_phase b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n00 : forall b,
  action_read (hwb_regs b) "chsh_n00" (SyntaxKind (Bit 64)) = Some (hw_chsh_n00 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n01 : forall b,
  action_read (hwb_regs b) "chsh_n01" (SyntaxKind (Bit 64)) = Some (hw_chsh_n01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n10 : forall b,
  action_read (hwb_regs b) "chsh_n10" (SyntaxKind (Bit 64)) = Some (hw_chsh_n10 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n11 : forall b,
  action_read (hwb_regs b) "chsh_n11" (SyntaxKind (Bit 64)) = Some (hw_chsh_n11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d00 : forall b,
  action_read (hwb_regs b) "chsh_d00" (SyntaxKind (Bit 64)) = Some (hw_chsh_d00 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d01 : forall b,
  action_read (hwb_regs b) "chsh_d01" (SyntaxKind (Bit 64)) = Some (hw_chsh_d01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d10 : forall b,
  action_read (hwb_regs b) "chsh_d10" (SyntaxKind (Bit 64)) = Some (hw_chsh_d10 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d11 : forall b,
  action_read (hwb_regs b) "chsh_d11" (SyntaxKind (Bit 64)) = Some (hw_chsh_d11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_sign00 : forall b,
  action_read (hwb_regs b) "chsh_sign00" (SyntaxKind (Bool)) = Some (hw_chsh_sign00 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_sign01 : forall b,
  action_read (hwb_regs b) "chsh_sign01" (SyntaxKind (Bool)) = Some (hw_chsh_sign01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_sign10 : forall b,
  action_read (hwb_regs b) "chsh_sign10" (SyntaxKind (Bool)) = Some (hw_chsh_sign10 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_sign11 : forall b,
  action_read (hwb_regs b) "chsh_sign11" (SyntaxKind (Bool)) = Some (hw_chsh_sign11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n00sq : forall b,
  action_read (hwb_regs b) "chsh_n00sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_n00sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n01sq : forall b,
  action_read (hwb_regs b) "chsh_n01sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_n01sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n10sq : forall b,
  action_read (hwb_regs b) "chsh_n10sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_n10sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n11sq : forall b,
  action_read (hwb_regs b) "chsh_n11sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_n11sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d00sq : forall b,
  action_read (hwb_regs b) "chsh_d00sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_d00sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d01sq : forall b,
  action_read (hwb_regs b) "chsh_d01sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_d01sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d10sq : forall b,
  action_read (hwb_regs b) "chsh_d10sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_d10sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d11sq : forall b,
  action_read (hwb_regs b) "chsh_d11sq" (SyntaxKind (Bit 128)) = Some (hw_chsh_d11sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_A_pos : forall b,
  action_read (hwb_regs b) "chsh_A_pos" (SyntaxKind (Bit 256)) = Some (hw_chsh_A_pos b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_A_neg_a : forall b,
  action_read (hwb_regs b) "chsh_A_neg_a" (SyntaxKind (Bit 256)) = Some (hw_chsh_A_neg_a b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_A_neg_b : forall b,
  action_read (hwb_regs b) "chsh_A_neg_b" (SyntaxKind (Bit 256)) = Some (hw_chsh_A_neg_b b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_B_pos : forall b,
  action_read (hwb_regs b) "chsh_B_pos" (SyntaxKind (Bit 256)) = Some (hw_chsh_B_pos b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_B_neg_a : forall b,
  action_read (hwb_regs b) "chsh_B_neg_a" (SyntaxKind (Bit 256)) = Some (hw_chsh_B_neg_a b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_B_neg_b : forall b,
  action_read (hwb_regs b) "chsh_B_neg_b" (SyntaxKind (Bit 256)) = Some (hw_chsh_B_neg_b b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d00d01 : forall b,
  action_read (hwb_regs b) "chsh_d00d01" (SyntaxKind (Bit 128)) = Some (hw_chsh_d00d01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n10n11 : forall b,
  action_read (hwb_regs b) "chsh_n10n11" (SyntaxKind (Bit 128)) = Some (hw_chsh_n10n11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_d10d11 : forall b,
  action_read (hwb_regs b) "chsh_d10d11" (SyntaxKind (Bit 128)) = Some (hw_chsh_d10d11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_n00n01 : forall b,
  action_read (hwb_regs b) "chsh_n00n01" (SyntaxKind (Bit 128)) = Some (hw_chsh_n00n01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_abs_C1 : forall b,
  action_read (hwb_regs b) "chsh_abs_C1" (SyntaxKind (Bit 256)) = Some (hw_chsh_abs_C1 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_abs_C2 : forall b,
  action_read (hwb_regs b) "chsh_abs_C2" (SyntaxKind (Bit 256)) = Some (hw_chsh_abs_C2 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_C_sq : forall b,
  action_read (hwb_regs b) "chsh_C_sq" (SyntaxKind (Bit 384)) = Some (hw_chsh_C_sq b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_A_times_B : forall b,
  action_read (hwb_regs b) "chsh_A_times_B" (SyntaxKind (Bit 384)) = Some (hw_chsh_A_times_B b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_chsh_check_result : forall b,
  action_read (hwb_regs b) "chsh_check_result" (SyntaxKind (Bool)) = Some (hw_chsh_check_result b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_bus_load_instr_addr : forall b,
  action_read (hwb_regs b) "bus_load_instr_addr" (SyntaxKind (Bit MemAddrSz)) = Some (hw_bus_load_instr_addr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_bus_load_instr_data : forall b,
  action_read (hwb_regs b) "bus_load_instr_data" (SyntaxKind (Bit InstrSz)) = Some (hw_bus_load_instr_data b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_bus_load_instr_kick : forall b,
  action_read (hwb_regs b) "bus_load_instr_kick" (SyntaxKind (Bool)) = Some (hw_bus_load_instr_kick b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mu_tensor : forall b,
  action_read (hwb_regs b) "mu_tensor" (SyntaxKind (Vector (Bit WordSz) MuTensorIdxSz)) = Some (hw_mu_tensor b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_module_tensors : forall b,
  action_read (hwb_regs b) "module_tensors" (SyntaxKind (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz)) = Some (hw_module_tensors b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_csr_status : forall b,
  action_read (hwb_regs b) "csr_status" (SyntaxKind (Bit WordSz)) = Some (hw_csr_status b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_csr_heap_base : forall b,
  action_read (hwb_regs b) "csr_heap_base" (SyntaxKind (Bit WordSz)) = Some (hw_csr_heap_base b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_ptTable : forall b,
  action_read (hwb_regs b) "ptTable" (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) = Some (hw_ptTable b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_pt_next_id : forall b,
  action_read (hwb_regs b) "pt_next_id" (SyntaxKind (Bit PTableNextIdSz)) = Some (hw_pt_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_morph_src_table : forall b,
  action_read (hwb_regs b) "morph_src_table" (SyntaxKind (Vector (Bit PTableIdxSz) MorphTableIdxSz)) = Some (hw_morph_src_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_morph_dst_table : forall b,
  action_read (hwb_regs b) "morph_dst_table" (SyntaxKind (Vector (Bit PTableIdxSz) MorphTableIdxSz)) = Some (hw_morph_dst_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_morph_coupling_desc_table : forall b,
  action_read (hwb_regs b) "morph_coupling_desc_table" (SyntaxKind (Vector (Bit DescIdxSz) MorphTableIdxSz)) = Some (hw_morph_coupling_desc_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_morph_valid_table : forall b,
  action_read (hwb_regs b) "morph_valid_table" (SyntaxKind (Vector Bool MorphTableIdxSz)) = Some (hw_morph_valid_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_morph_identity_table : forall b,
  action_read (hwb_regs b) "morph_identity_table" (SyntaxKind (Vector Bool MorphTableIdxSz)) = Some (hw_morph_identity_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_morph_next_id : forall b,
  action_read (hwb_regs b) "morph_next_id" (SyntaxKind (Bit MorphTableNextIdSz)) = Some (hw_morph_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_desc_base_table : forall b,
  action_read (hwb_regs b) "coupling_desc_base_table" (SyntaxKind (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz)) = Some (hw_coupling_desc_base_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_desc_count_table : forall b,
  action_read (hwb_regs b) "coupling_desc_count_table" (SyntaxKind (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz)) = Some (hw_coupling_desc_count_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_desc_valid_table : forall b,
  action_read (hwb_regs b) "coupling_desc_valid_table" (SyntaxKind (Vector Bool CouplingDescIdxSz)) = Some (hw_coupling_desc_valid_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_desc_label_table : forall b,
  action_read (hwb_regs b) "coupling_desc_label_table" (SyntaxKind (Vector (Bit WordSz) CouplingDescIdxSz)) = Some (hw_coupling_desc_label_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_desc_label_len_table : forall b,
  action_read (hwb_regs b) "coupling_desc_label_len_table" (SyntaxKind (Vector (Bit 6) CouplingDescIdxSz)) = Some (hw_coupling_desc_label_len_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_desc_next_id : forall b,
  action_read (hwb_regs b) "coupling_desc_next_id" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_coupling_desc_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_pair_src_table : forall b,
  action_read (hwb_regs b) "coupling_pair_src_table" (SyntaxKind (Vector (Bit WordSz) CouplingPairIdxSz)) = Some (hw_coupling_pair_src_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_pair_dst_table : forall b,
  action_read (hwb_regs b) "coupling_pair_dst_table" (SyntaxKind (Vector (Bit WordSz) CouplingPairIdxSz)) = Some (hw_coupling_pair_dst_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_pair_valid_table : forall b,
  action_read (hwb_regs b) "coupling_pair_valid_table" (SyntaxKind (Vector Bool CouplingPairIdxSz)) = Some (hw_coupling_pair_valid_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_coupling_pair_next_id : forall b,
  action_read (hwb_regs b) "coupling_pair_next_id" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_coupling_pair_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_phase : forall b,
  action_read (hwb_regs b) "mc_phase" (SyntaxKind (Bit 4)) = Some (hw_mc_phase b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_op : forall b,
  action_read (hwb_regs b) "mc_op" (SyntaxKind (Bit 2)) = Some (hw_mc_op b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_mem_base : forall b,
  action_read (hwb_regs b) "mc_mem_base" (SyntaxKind (Bit WordSz)) = Some (hw_mc_mem_base b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_pair_count : forall b,
  action_read (hwb_regs b) "mc_pair_count" (SyntaxKind (Bit CouplingPairCountSz)) = Some (hw_mc_pair_count b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_read_ptr : forall b,
  action_read (hwb_regs b) "mc_read_ptr" (SyntaxKind (Bit WordSz)) = Some (hw_mc_read_ptr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_src1_base : forall b,
  action_read (hwb_regs b) "mc_src1_base" (SyntaxKind (Bit CouplingPairIdxSz)) = Some (hw_mc_src1_base b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_src1_count : forall b,
  action_read (hwb_regs b) "mc_src1_count" (SyntaxKind (Bit CouplingPairCountSz)) = Some (hw_mc_src1_count b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_src2_base : forall b,
  action_read (hwb_regs b) "mc_src2_base" (SyntaxKind (Bit CouplingPairIdxSz)) = Some (hw_mc_src2_base b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_src2_count : forall b,
  action_read (hwb_regs b) "mc_src2_count" (SyntaxKind (Bit CouplingPairCountSz)) = Some (hw_mc_src2_count b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_i : forall b,
  action_read (hwb_regs b) "mc_i" (SyntaxKind (Bit CouplingPairCountSz)) = Some (hw_mc_i b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_j : forall b,
  action_read (hwb_regs b) "mc_j" (SyntaxKind (Bit CouplingPairCountSz)) = Some (hw_mc_j b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_is_id1 : forall b,
  action_read (hwb_regs b) "mc_is_id1" (SyntaxKind (Bool)) = Some (hw_mc_is_id1 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_is_id2 : forall b,
  action_read (hwb_regs b) "mc_is_id2" (SyntaxKind (Bool)) = Some (hw_mc_is_id2 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_write_base : forall b,
  action_read (hwb_regs b) "mc_write_base" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_mc_write_base b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_write_ptr : forall b,
  action_read (hwb_regs b) "mc_write_ptr" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_mc_write_ptr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_norm_ptr : forall b,
  action_read (hwb_regs b) "mc_norm_ptr" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_mc_norm_ptr b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_duplicate : forall b,
  action_read (hwb_regs b) "mc_duplicate" (SyntaxKind (Bool)) = Some (hw_mc_duplicate b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_dst_reg : forall b,
  action_read (hwb_regs b) "mc_dst_reg" (SyntaxKind (Bit RegIdxSz)) = Some (hw_mc_dst_reg b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_morph_slot : forall b,
  action_read (hwb_regs b) "mc_morph_slot" (SyntaxKind (Bit MorphTableIdxSz)) = Some (hw_mc_morph_slot b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_new_src_mod : forall b,
  action_read (hwb_regs b) "mc_new_src_mod" (SyntaxKind (Bit PTableIdxSz)) = Some (hw_mc_new_src_mod b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_new_dst_mod : forall b,
  action_read (hwb_regs b) "mc_new_dst_mod" (SyntaxKind (Bit PTableIdxSz)) = Some (hw_mc_new_dst_mod b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_mc_cost : forall b,
  action_read (hwb_regs b) "mc_cost" (SyntaxKind (Bit WordSz)) = Some (hw_mc_cost b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_formula_desc_base_table : forall b,
  action_read (hwb_regs b) "formula_desc_base_table" (SyntaxKind (Vector (Bit WordSz) FormulaDescIdxSz)) = Some (hw_formula_desc_base_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_formula_desc_count_table : forall b,
  action_read (hwb_regs b) "formula_desc_count_table" (SyntaxKind (Vector (Bit WordSz) FormulaDescIdxSz)) = Some (hw_formula_desc_count_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_formula_desc_valid_table : forall b,
  action_read (hwb_regs b) "formula_desc_valid_table" (SyntaxKind (Vector Bool FormulaDescIdxSz)) = Some (hw_formula_desc_valid_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_formula_desc_next_id : forall b,
  action_read (hwb_regs b) "formula_desc_next_id" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_formula_desc_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_cert_desc_base_table : forall b,
  action_read (hwb_regs b) "cert_desc_base_table" (SyntaxKind (Vector (Bit WordSz) CertDescIdxSz)) = Some (hw_cert_desc_base_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_cert_desc_count_table : forall b,
  action_read (hwb_regs b) "cert_desc_count_table" (SyntaxKind (Vector (Bit WordSz) CertDescIdxSz)) = Some (hw_cert_desc_count_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_cert_desc_valid_table : forall b,
  action_read (hwb_regs b) "cert_desc_valid_table" (SyntaxKind (Vector Bool CertDescIdxSz)) = Some (hw_cert_desc_valid_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_cert_desc_next_id : forall b,
  action_read (hwb_regs b) "cert_desc_next_id" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_cert_desc_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_desc_meta_subtype_table : forall b,
  action_read (hwb_regs b) "desc_meta_subtype_table" (SyntaxKind (Vector (Bit FormatSubtypeSz) DescMetaIdxSz)) = Some (hw_desc_meta_subtype_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_desc_meta_kind_table : forall b,
  action_read (hwb_regs b) "desc_meta_kind_table" (SyntaxKind (Vector (Bit DescKindFieldSz) DescMetaIdxSz)) = Some (hw_desc_meta_kind_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_desc_meta_inline_len_table : forall b,
  action_read (hwb_regs b) "desc_meta_inline_len_table" (SyntaxKind (Vector (Bit InlineLenSz) DescMetaIdxSz)) = Some (hw_desc_meta_inline_len_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_desc_meta_aux_table : forall b,
  action_read (hwb_regs b) "desc_meta_aux_table" (SyntaxKind (Vector (Bit WordSz) DescMetaIdxSz)) = Some (hw_desc_meta_aux_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_desc_meta_valid_table : forall b,
  action_read (hwb_regs b) "desc_meta_valid_table" (SyntaxKind (Vector Bool DescMetaIdxSz)) = Some (hw_desc_meta_valid_table b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_desc_meta_next_id : forall b,
  action_read (hwb_regs b) "desc_meta_next_id" (SyntaxKind (Bit DescTableNextIdSz)) = Some (hw_desc_meta_next_id b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_same_00 : forall b,
  action_read (hwb_regs b) "wc_same_00" (SyntaxKind (Bit WordSz)) = Some (hw_wc_same_00 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_diff_00 : forall b,
  action_read (hwb_regs b) "wc_diff_00" (SyntaxKind (Bit WordSz)) = Some (hw_wc_diff_00 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_same_01 : forall b,
  action_read (hwb_regs b) "wc_same_01" (SyntaxKind (Bit WordSz)) = Some (hw_wc_same_01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_diff_01 : forall b,
  action_read (hwb_regs b) "wc_diff_01" (SyntaxKind (Bit WordSz)) = Some (hw_wc_diff_01 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_same_10 : forall b,
  action_read (hwb_regs b) "wc_same_10" (SyntaxKind (Bit WordSz)) = Some (hw_wc_same_10 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_diff_10 : forall b,
  action_read (hwb_regs b) "wc_diff_10" (SyntaxKind (Bit WordSz)) = Some (hw_wc_diff_10 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_same_11 : forall b,
  action_read (hwb_regs b) "wc_same_11" (SyntaxKind (Bit WordSz)) = Some (hw_wc_same_11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma hwb_read_wc_diff_11 : forall b,
  action_read (hwb_regs b) "wc_diff_11" (SyntaxKind (Bit WordSz)) = Some (hw_wc_diff_11 b).
Proof.
  intros. vm_compute. reflexivity.
Qed.

