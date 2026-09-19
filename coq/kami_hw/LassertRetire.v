(** LassertRetire.v: retirement of LASSERT. The kernel's check at a boundary is
    the hardware scan over the formula words; the UNSAT kind retires in the step
    firing and the SAT kind in the step, header and scan firings, each an actual
    Kami execution whose final snapshot is the [kami_step] result; while a SAT
    LASSERT runs, the header rule and then the scan rule are the only enabled
    rules. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String Arith Lia Bool List FunctionalExtensionality.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval StepWordFacts
  StepFields StepRefineCommon StepRefine ImplementationContract Abstraction EmbedStep
  ChshArith LassertSpec LassertWord LassertStepFields FsmDecoded ChshRetire
  ActionEvaluator CoreRules CoreExecution DispatchExecution NormalizationSteps NormalizationExecution
  NormalizationRetirement RuleEnabled.
Require Import Kernel.VMState Kernel.VMStep Kernel.CertCheck.
Import VMStep.VMStep.
Local Open Scope nat_scope.

(** * The kernel's LASSERT check at a boundary *)

Lemma read_mem_hw : forall b a, read_mem (abs_phase1 (hwb_snapshot b)) a = mem_at b a.
Proof.
  intros b a. rewrite abs_phase1_read_mem. cbn [snap_mem hwb_snapshot]. unfold hwb_vector_nat, mem_at.
  change MEM_SIZE with 128.
  rewrite (proj2 (Nat.ltb_lt _ _)) by (apply Nat.mod_upper_bound; discriminate). reflexivity.
Qed.

Lemma read_reg_hw : forall b (r : word RegIdxSz),
  read_reg (abs_phase1 (hwb_snapshot b)) (wordToNat r) = wordToNat (hw_regs b r).
Proof.
  intros b r. rewrite abs_phase1_read_reg. cbn [snap_regs hwb_snapshot].
  change RegCount with (2 ^ RegIdxSz). apply hwb_vector_nat_at_mod.
Qed.

Lemma map_seq_shift : forall (g : nat -> nat) n start,
  map g (seq start n) = map (fun j => g (start + j)) (seq 0 n).
Proof.
  intros g n. revert g. induction n as [|n IH]; intros g start; [reflexivity|].
  cbn [seq map]. rewrite Nat.add_0_r. f_equal.
  rewrite (IH g (S start)), (IH (fun j => g (start + j)) 1). apply map_ext. intro j. f_equal. lia.
Qed.

Definition lassert_words (b : HWB) (fb : nat) : list nat :=
  map (fun j => mem_at b (fb + 3 + j)) (seq 0 (mem_at b fb)).

Lemma lassert_exec_ok_hw : forall b (al bl : word RegIdxSz) flen,
  lassert_exec_ok (abs_phase1 (hwb_snapshot b)) (wordToNat al) (wordToNat bl) true flen =
  let fb := wordToNat (hw_regs b al) in
  let cb := wordToNat (hw_regs b bl) in
  let hf := mem_at b fb in let nv := mem_at b (fb + 1) in let n := mem_at b (fb + 2) in
  andb (Nat.eqb hf flen)
    (andb (CertCheck.check_model_binary_fn (hf :: nv :: n :: lassert_words b fb) (fun v => mem_at b (cb + v)))
          (CertCheck.check_countermodel_binary_fn (hf :: nv :: n :: lassert_words b fb)
             (fun v => mem_at b (cb + nv + v)))).
Proof.
  intros b al bl flen. unfold lassert_exec_ok, lassert_hw_flen, lassert_check_ok.
  rewrite !read_reg_hw, read_mem_hw. cbv zeta.
  set (s := abs_phase1 (hwb_snapshot b)).
  set (fb := wordToNat (hw_regs b al)). set (cb := wordToNat (hw_regs b bl)).
  replace (map (fun i => read_mem s (fb + i)) (seq 0 (3 + mem_at b fb)))
    with (mem_at b fb :: mem_at b (fb + 1) :: mem_at b (fb + 2) :: lassert_words b fb).
  2:{ unfold s. cbn [seq map Nat.add]. rewrite Nat.add_0_r, !read_mem_hw. unfold lassert_words.
      rewrite (map_seq_shift _ _ 3). do 3 f_equal. apply map_ext. intro j. rewrite read_mem_hw. f_equal. lia. }
  cbv iota beta.
  replace (fun var => read_mem s (cb + var)) with (fun v => mem_at b (cb + v))
    by (extensionality v; symmetry; apply read_mem_hw).
  replace (fun var => read_mem s (cb + mem_at b (fb + 1) + var)) with (fun v => mem_at b (cb + mem_at b (fb + 1) + v))
    by (extensionality v; symmetry; apply read_mem_hw).
  reflexivity.
Qed.

(** * The header firing *)

Lemma small_lt_pow2_32 : forall k, k < 16 -> k < pow2 32.
Proof.
  intros k H. eapply Nat.lt_le_trans; [exact H|].
  change 16 with (2 ^ 4). apply Nat.pow_le_mono_r; lia.
Qed.

Lemma lhdr_phase : forall b, hw_lassert_phase (lhdr_next b) = WO~0~1~0.
Proof. reflexivity. Qed.
Lemma lhdr_flags : forall b,
  hw_lassert_clause_sat (lhdr_next b) = false /\ hw_lassert_counter_clause_sat (lhdr_next b) = false /\
  hw_lassert_counter_seen_fail (lhdr_next b) = false.
Proof. repeat split. Qed.

Lemma lhdr_flen_nat : forall b,
  wordToNat (hw_lassert_flen (lhdr_next b)) = mem_at b (wordToNat (hw_lassert_fbase b)).
Proof. intro b. exact (read_mem_trunc b (hw_lassert_fbase b)). Qed.

Lemma mem_at_wplus_const : forall b (x : word WordSz) k, k < pow2 32 ->
  mem_at b (wordToNat (wplus x (natToWord WordSz k))) = mem_at b (wordToNat x + k).
Proof.
  intros b x k Hk. rewrite <- mem_at_mod, wordToNat_wplus_mod_128, mem_at_mod.
  rewrite wordToNat_natToWord_idempotent' by exact Hk. reflexivity.
Qed.

Lemma lhdr_nvars_nat : forall b,
  wordToNat (hw_lassert_nvars (lhdr_next b)) = mem_at b (wordToNat (hw_lassert_fbase b) + 1).
Proof.
  intro b. change (hw_lassert_nvars (lhdr_next b)) with (hw_mem b (split1 MemAddrSz 25 (wplus (hw_lassert_fbase b) (natToWord WordSz 1)))).
  rewrite read_mem_trunc. apply mem_at_wplus_const. apply small_lt_pow2_32; lia.
Qed.

Lemma lhdr_clen_nat : forall b,
  wordToNat (hw_lassert_clen (lhdr_next b)) = mem_at b (wordToNat (hw_lassert_fbase b) + 2).
Proof.
  intro b. change (hw_lassert_clen (lhdr_next b)) with (hw_mem b (split1 MemAddrSz 25 (wplus (hw_lassert_fbase b) (natToWord WordSz 2)))).
  rewrite read_mem_trunc. apply mem_at_wplus_const. apply small_lt_pow2_32; lia.
Qed.

Lemma lhdr_fptr_nat : forall b, wordToNat (hw_lassert_fbase b) + 3 < pow2 32 ->
  wordToNat (hw_lassert_fptr (lhdr_next b)) = wordToNat (hw_lassert_fbase b) + 3.
Proof.
  intros b H. change (hw_lassert_fptr (lhdr_next b)) with (wplus (hw_lassert_fbase b) (natToWord WordSz 3)).
  rewrite wordToNat_wplus'; rewrite wordToNat_natToWord_idempotent' by (apply small_lt_pow2_32; lia); [reflexivity|exact H].
Qed.

Lemma lscan_mu_fail_nat : forall c,
  wordToNat (hw_mu c) + wordToNat (hw_lassert_flen c) * 8 + wordToNat (hw_lassert_cptr c) + 1 < pow2 32 ->
  wordToNat (lscan_mu_fail c) =
  wordToNat (hw_mu c) + wordToNat (hw_lassert_flen c) * 8 + wordToNat (hw_lassert_cptr c) + 1.
Proof.
  intros c H.
  change (lscan_mu_fail c) with (wplus (wplus (wplus (hw_mu c) (wlshift (hw_lassert_flen c) 3)) (hw_lassert_cptr c)) (natToWord WordSz 1)).
  assert (S3 : wordToNat (wlshift (hw_lassert_flen c) 3) = wordToNat (hw_lassert_flen c) * 8).
  { rewrite wordToNat_wlshift. change (pow2 3) with 8. f_equal. apply Nat.mod_small.
    change (pow2 (WordSz - 3)) with (pow2 29).
    assert (P : pow2 32 = pow2 29 * 8) by (change 8 with (pow2 3); rewrite <- Nat.pow_add_r; reflexivity).
    rewrite P in H. lia. }
  assert (O : wordToNat (natToWord WordSz 1) = 1) by reflexivity.
  assert (A1 : wordToNat (wplus (hw_mu c) (wlshift (hw_lassert_flen c) 3)) =
                wordToNat (hw_mu c) + wordToNat (hw_lassert_flen c) * 8).
  { rewrite wordToNat_wplus', S3; [reflexivity|]. rewrite S3. change (pow2 WordSz) with (pow2 32). lia. }
  assert (A2 : wordToNat (wplus (wplus (hw_mu c) (wlshift (hw_lassert_flen c) 3)) (hw_lassert_cptr c)) =
                wordToNat (hw_mu c) + wordToNat (hw_lassert_flen c) * 8 + wordToNat (hw_lassert_cptr c)).
  { rewrite wordToNat_wplus', A1; [reflexivity|]. rewrite A1. change (pow2 WordSz) with (pow2 32). lia. }
  rewrite wordToNat_wplus', A2, O; [reflexivity|]. rewrite A2, O. change (pow2 WordSz) with (pow2 32). lia.
Qed.


(** * Frames through the header firing and the scan loop *)

Lemma lhdr_keeps_pc : forall c, hw_pc (lhdr_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mu : forall c, hw_mu (lhdr_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_err : forall c, hw_err (lhdr_next c) = hw_err c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_halted : forall c, hw_halted (lhdr_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_regs : forall c, hw_regs (lhdr_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mem : forall c, hw_mem (lhdr_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_imem : forall c, hw_imem (lhdr_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_partition_ops : forall c, hw_partition_ops (lhdr_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mdl_ops : forall c, hw_mdl_ops (lhdr_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_info_gain : forall c, hw_info_gain (lhdr_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_error_code : forall c, hw_error_code (lhdr_next c) = hw_error_code c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_logic_acc : forall c, hw_logic_acc (lhdr_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_cert_addr : forall c, hw_cert_addr (lhdr_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_active_module : forall c, hw_active_module (lhdr_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mstatus : forall c, hw_mstatus (lhdr_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mcycle_lo : forall c, hw_mcycle_lo (lhdr_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mcycle_hi : forall c, hw_mcycle_hi (lhdr_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_minstret_lo : forall c, hw_minstret_lo (lhdr_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_minstret_hi : forall c, hw_minstret_hi (lhdr_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_trap_vector : forall c, hw_trap_vector (lhdr_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_certified : forall c, hw_certified (lhdr_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_lassert_kind : forall c, hw_lassert_kind (lhdr_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_lassert_fbase : forall c, hw_lassert_fbase (lhdr_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_lassert_cbase : forall c, hw_lassert_cbase (lhdr_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_lassert_cptr : forall c, hw_lassert_cptr (lhdr_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (lhdr_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (lhdr_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_phase : forall c, hw_chsh_phase (lhdr_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n00 : forall c, hw_chsh_n00 (lhdr_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n01 : forall c, hw_chsh_n01 (lhdr_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n10 : forall c, hw_chsh_n10 (lhdr_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n11 : forall c, hw_chsh_n11 (lhdr_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d00 : forall c, hw_chsh_d00 (lhdr_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d01 : forall c, hw_chsh_d01 (lhdr_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d10 : forall c, hw_chsh_d10 (lhdr_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d11 : forall c, hw_chsh_d11 (lhdr_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (lhdr_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (lhdr_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (lhdr_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (lhdr_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (lhdr_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (lhdr_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (lhdr_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (lhdr_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (lhdr_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (lhdr_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (lhdr_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (lhdr_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (lhdr_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (lhdr_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (lhdr_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (lhdr_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (lhdr_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (lhdr_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (lhdr_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (lhdr_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (lhdr_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (lhdr_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (lhdr_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (lhdr_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (lhdr_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (lhdr_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_chsh_check_result : forall c, hw_chsh_check_result (lhdr_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (lhdr_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (lhdr_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (lhdr_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mu_tensor : forall c, hw_mu_tensor (lhdr_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_module_tensors : forall c, hw_module_tensors (lhdr_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_csr_status : forall c, hw_csr_status (lhdr_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_csr_heap_base : forall c, hw_csr_heap_base (lhdr_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_ptTable : forall c, hw_ptTable (lhdr_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_pt_next_id : forall c, hw_pt_next_id (lhdr_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_morph_src_table : forall c, hw_morph_src_table (lhdr_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_morph_dst_table : forall c, hw_morph_dst_table (lhdr_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (lhdr_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_morph_valid_table : forall c, hw_morph_valid_table (lhdr_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_morph_identity_table : forall c, hw_morph_identity_table (lhdr_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_morph_next_id : forall c, hw_morph_next_id (lhdr_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (lhdr_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (lhdr_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (lhdr_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (lhdr_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (lhdr_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (lhdr_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_pair_src_table : forall c, hw_coupling_pair_src_table (lhdr_next c) = hw_coupling_pair_src_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_pair_dst_table : forall c, hw_coupling_pair_dst_table (lhdr_next c) = hw_coupling_pair_dst_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (lhdr_next c) = hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (lhdr_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_phase : forall c, hw_mc_phase (lhdr_next c) = hw_mc_phase c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_op : forall c, hw_mc_op (lhdr_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_mem_base : forall c, hw_mc_mem_base (lhdr_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_pair_count : forall c, hw_mc_pair_count (lhdr_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (lhdr_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_src1_base : forall c, hw_mc_src1_base (lhdr_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_src1_count : forall c, hw_mc_src1_count (lhdr_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_src2_base : forall c, hw_mc_src2_base (lhdr_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_src2_count : forall c, hw_mc_src2_count (lhdr_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_i : forall c, hw_mc_i (lhdr_next c) = hw_mc_i c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_j : forall c, hw_mc_j (lhdr_next c) = hw_mc_j c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (lhdr_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (lhdr_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_write_base : forall c, hw_mc_write_base (lhdr_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_write_ptr : forall c, hw_mc_write_ptr (lhdr_next c) = hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (lhdr_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_duplicate : forall c, hw_mc_duplicate (lhdr_next c) = hw_mc_duplicate c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (lhdr_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (lhdr_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (lhdr_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (lhdr_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_mc_cost : forall c, hw_mc_cost (lhdr_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (lhdr_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (lhdr_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (lhdr_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (lhdr_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (lhdr_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (lhdr_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (lhdr_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (lhdr_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (lhdr_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (lhdr_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (lhdr_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (lhdr_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (lhdr_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (lhdr_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_same_00 : forall c, hw_wc_same_00 (lhdr_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (lhdr_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_same_01 : forall c, hw_wc_same_01 (lhdr_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (lhdr_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_same_10 : forall c, hw_wc_same_10 (lhdr_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (lhdr_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_same_11 : forall c, hw_wc_same_11 (lhdr_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma lhdr_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (lhdr_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma lscan_iter_rich : forall n c, hwb_rich (lscan_iter n c) = hwb_rich c.
Proof. intros n c. unfold hwb_rich. rewrite lscan_iter_keeps_cert_desc_base_table, lscan_iter_keeps_cert_desc_count_table, lscan_iter_keeps_cert_desc_next_id, lscan_iter_keeps_cert_desc_valid_table, lscan_iter_keeps_coupling_desc_base_table, lscan_iter_keeps_coupling_desc_count_table, lscan_iter_keeps_coupling_desc_label_table, lscan_iter_keeps_coupling_desc_label_len_table, lscan_iter_keeps_coupling_desc_next_id, lscan_iter_keeps_coupling_desc_valid_table, lscan_iter_keeps_coupling_pair_dst_table, lscan_iter_keeps_coupling_pair_next_id, lscan_iter_keeps_coupling_pair_src_table, lscan_iter_keeps_coupling_pair_valid_table, lscan_iter_keeps_desc_meta_aux_table, lscan_iter_keeps_desc_meta_inline_len_table, lscan_iter_keeps_desc_meta_kind_table, lscan_iter_keeps_desc_meta_next_id, lscan_iter_keeps_desc_meta_subtype_table, lscan_iter_keeps_desc_meta_valid_table, lscan_iter_keeps_formula_desc_base_table, lscan_iter_keeps_formula_desc_count_table, lscan_iter_keeps_formula_desc_next_id, lscan_iter_keeps_formula_desc_valid_table, lscan_iter_keeps_morph_coupling_desc_table, lscan_iter_keeps_morph_dst_table, lscan_iter_keeps_morph_identity_table, lscan_iter_keeps_morph_next_id, lscan_iter_keeps_morph_src_table, lscan_iter_keeps_morph_valid_table. reflexivity. Qed.

Lemma lhdr_rich : forall c, hwb_rich (lhdr_next c) = hwb_rich c.
Proof. reflexivity. Qed.

Lemma lassert_exec_false : forall s freg creg flen, lassert_exec_ok s freg creg false flen = false.
Proof. intros. unfold lassert_exec_ok, lassert_check_ok. cbv zeta. apply andb_false_r. Qed.

Lemma lassert_unsat_mu_nat : forall b (al : word RegIdxSz) (c : word 8) flen,
  mem_at b (wordToNat (hw_regs b al)) = flen ->
  wordToNat (hw_mu b) + flen * 8 + wordToNat c + 1 < pow2 32 ->
  wordToNat (wplus (wplus (wplus (hw_mu b) (wlshift (hw_mem b (split1 7 25 (hw_regs b al))) (wordToNat (WO~0~0~0~0~1~1))))
     (zext c 24)) (natToWord WordSz 1)) = wordToNat (hw_mu b) + (flen * 8 + S (wordToNat c)).
Proof.
  intros b al c flen Hf Hm.
  assert (Hh : wordToNat (hw_mem b (split1 7 25 (hw_regs b al))) = flen) by (rewrite read_mem_trunc7; exact Hf).
  change (wordToNat (WO~0~0~0~0~1~1)) with 3.
  assert (S3 : wordToNat (wlshift (hw_mem b (split1 7 25 (hw_regs b al))) 3) = flen * 8).
  { rewrite wordToNat_wlshift, Hh. change (pow2 3) with 8. f_equal. apply Nat.mod_small.
    change (pow2 (WordSz - 3)) with (pow2 29).
    assert (P : pow2 32 = pow2 29 * 8) by (change 8 with (pow2 3); rewrite <- Nat.pow_add_r; reflexivity).
    rewrite P in Hm. lia. }
  assert (A1 : wordToNat (wplus (hw_mu b) (wlshift (hw_mem b (split1 7 25 (hw_regs b al))) 3)) = wordToNat (hw_mu b) + flen * 8).
  { rewrite wordToNat_wplus', S3; [reflexivity|]. rewrite S3. change (pow2 WordSz) with (pow2 32). lia. }
  assert (A2 : wordToNat (wplus (wplus (hw_mu b) (wlshift (hw_mem b (split1 7 25 (hw_regs b al))) 3)) (zext c 24)) =
               wordToNat (hw_mu b) + flen * 8 + wordToNat c).
  { rewrite wordToNat_wplus', A1, wordToNat_zext8_32; [reflexivity|]. rewrite A1, wordToNat_zext8_32.
    change (pow2 WordSz) with (pow2 32). lia. }
  rewrite wordToNat_wplus', A2; [change (wordToNat (natToWord WordSz 1)) with 1; lia|].
  rewrite A2. change (wordToNat (natToWord WordSz 1)) with 1. change (pow2 WordSz) with (pow2 32). lia.
Qed.

(** * LASSERT with the UNSAT kind: one step-rule firing *)

Theorem lassert_unsat_refines : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen,
  step_fetched b = lassert_unsat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false -> hw_err b = false -> hw_halted b = false ->
  wordToNat (hw_trap_vector b) = LASSERT_TRAP_PC ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) = flen ->
  wordToNat (hw_mu b) + flen * 8 + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) + 1 < pow2 32 ->
  hwb_snapshot (step_next b) =
  kami_step (hwb_snapshot b) (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) false flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb Herr Hhalt Htrap Hflen Hmu.
  unfold hwb_snapshot at 1.
  rewrite (step_rich_frame b (step_lassert_unsat_morph_valid_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_morph_src_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_morph_dst_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_morph_coupling_desc_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_morph_identity_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_morph_next_id a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_coupling_desc_label_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_unsat_coupling_desc_label_len_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)).
  rewrite (step_lassert_unsat_pc a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_mu a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_err a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_halted a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_regs a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_mem a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_error_code a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_cert_addr a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_partition_ops a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_mdl_ops a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_info_gain a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_mu_tensor a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_module_tensors a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_ptTable a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_pt_next_id a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_certified a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_same_00 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_diff_00 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_same_01 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_diff_01 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_same_10 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_diff_10 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_same_11 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_unsat_wc_diff_11 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  rewrite step_keeps_csr_status, step_keeps_csr_heap_base, step_keeps_logic_acc, step_keeps_mstatus.
  unfold kami_step. snap_projections. rewrite lassert_exec_false. cbv beta iota zeta.
  rewrite ?Herr, ?Hhalt.
  apply kami_snapshot_ext; snap_projections.
  all: first [ syntactic | exact Htrap | exact wordToNat_err_logic
             | exact (lassert_unsat_mu_nat b _ _ flen Hflen Hmu) ].
Qed.

(** * LASSERT with the SAT kind: the step firing, the header firing and the scan *)

Lemma nth_lassert_words : forall b fb j, j < mem_at b fb ->
  List.nth j (lassert_words b fb) 0 = mem_at b (fb + 3 + j).
Proof.
  intros b fb j Hj. unfold lassert_words.
  set (g := fun j => mem_at b (fb + 3 + j)).
  rewrite (nth_indep (map g (seq 0 (mem_at b fb))) 0 (g 0)) by (rewrite map_length, seq_length; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma lassert_words_bound : forall b fb, Forall (fun w => w < 2 ^ 32) (lassert_words b fb).
Proof.
  intros b fb. apply Forall_forall. intros w Hw. unfold lassert_words in Hw.
  apply in_map_iff in Hw. destruct Hw as [j [E _]]. subst w. unfold mem_at.
  change (2 ^ 32) with (pow2 WordSz). apply wordToNat_bound.
Qed.

Theorem lassert_sat_refines : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen,
  step_fetched b = lassert_sat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false -> hw_err b = false -> hw_halted b = false ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_trap_vector b) = LASSERT_TRAP_PC ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) = flen ->
  wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 3 + flen < pow2 32 ->
  1 <= mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) <= count_zeros (lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)))) ->
  wordToNat (hw_mu b) + flen * 8 + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) + 1 < pow2 32 ->
  exists n, 1 <= n <= flen /\
    (forall m, m < n -> hw_lassert_phase (lscan_iter m (lhdr_next (step_next b))) = WO~0~1~0) /\
    hw_lassert_phase (lscan_iter n (lhdr_next (step_next b))) = WO~0~0~0 /\
    hwb_snapshot (lscan_iter n (lhdr_next (step_next b))) =
    kami_step (hwb_snapshot b) (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) true flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb Herr Hhalt Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu.
  pose proof (step_lassert_sat_mem a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as Mem1.
  pose proof (step_lassert_sat_lassert_fbase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as Fb1.
  pose proof (step_lassert_sat_lassert_cbase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as Cb1.
  pose proof (step_lassert_sat_lassert_cptr a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as Cp1.
  set (st1 := step_next b) in *. set (st2 := lhdr_next st1).
  assert (MemAt : forall a, mem_at st2 a = mem_at b a) by (intro a; unfold mem_at, st2; rewrite lhdr_keeps_mem, Mem1; reflexivity).
  assert (Cl2 : wordToNat (hw_lassert_clen st2) = mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2)).
  { unfold st2. rewrite lhdr_clen_nat, Fb1. unfold mem_at. rewrite Mem1. reflexivity. }
  assert (Nv2 : wordToNat (hw_lassert_nvars st2) = mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 1)).
  { unfold st2. rewrite lhdr_nvars_nat, Fb1. unfold mem_at. rewrite Mem1. reflexivity. }
  assert (Fl2 : wordToNat (hw_lassert_flen st2) = flen).
  { unfold st2. rewrite lhdr_flen_nat, Fb1. unfold mem_at in *. rewrite Mem1. exact Hflen. }
  assert (Fp2 : wordToNat (hw_lassert_fptr st2) = wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 3).
  { unfold st2. rewrite lhdr_fptr_nat, Fb1; [reflexivity|]. rewrite Fb1. lia. }
  assert (Cb2 : hw_lassert_cbase st2 = hw_regs b (bits4 b0 b1 b2 b3)) by (unfold st2; rewrite lhdr_keeps_lassert_cbase; exact Cb1).
  assert (Cp2 : hw_lassert_cptr st2 = zext (bits8 c0 c1 c2 c3 c4 c5 c6 c7) 24) by (unfold st2; rewrite lhdr_keeps_lassert_cptr; exact Cp1).
  set (r := andb (CertCheck.check_model_binary_fn
                    (mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) :: mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 1) :: mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) :: lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))))
                    (fun v => mem_at b (wordToNat (hw_regs b (bits4 b0 b1 b2 b3)) + v)))
                 (CertCheck.check_countermodel_binary_fn
                    (mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) :: mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 1) :: mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) :: lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))))
                    (fun v => mem_at b (wordToNat (hw_regs b (bits4 b0 b1 b2 b3)) + mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 1) + v)))).
  assert (Len : List.length (lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)))) = flen) by (unfold lassert_words; rewrite map_length, seq_length; exact Hflen).
  destruct (lscan_loop (lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)))) st2 r) as [n [Hn [H1 [Hph [HP [HPc [HM [HE HC]]]]]]]].
  { unfold st2. apply lhdr_phase. }
  { intros j Hj. rewrite Len in Hj. rewrite Fp2, MemAt, nth_lassert_words by (rewrite Hflen; exact Hj). f_equal. }
  { rewrite Fp2, Len. exact Hfit. }
  { rewrite Cl2. exact Hcl1. }
  { rewrite Cl2. unfold st2. rewrite (proj1 (lhdr_flags st1)), (proj1 (proj2 (lhdr_flags st1))), (proj2 (proj2 (lhdr_flags st1))).
     fold st2.
     replace (gm st2) with (fun v => mem_at b (wordToNat (hw_regs b (bits4 b0 b1 b2 b3)) + v)) by (extensionality v; unfold gm; rewrite Cb2, MemAt; reflexivity).
     replace (gc st2) with (fun v => mem_at b (wordToNat (hw_regs b (bits4 b0 b1 b2 b3)) + mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 1) + v))
       by (extensionality v; unfold gc; rewrite Cb2, Nv2, MemAt; reflexivity).
     unfold r. apply hw_scan_certcheck; [exact Hcl1|exact Hcl2|apply lassert_words_bound]. }
  exists n. split; [rewrite Len in Hn; lia|]. split; [exact Hph|]. split; [exact HP|].
  unfold hwb_snapshot at 1.
  rewrite lscan_iter_rich.
  rewrite HPc, HM, HE, HC.
  rewrite (lscan_iter_keeps_halted n), (lscan_iter_keeps_regs n), (lscan_iter_keeps_mem n), (lscan_iter_keeps_cert_addr n), (lscan_iter_keeps_partition_ops n), (lscan_iter_keeps_mdl_ops n), (lscan_iter_keeps_info_gain n), (lscan_iter_keeps_mu_tensor n), (lscan_iter_keeps_module_tensors n), (lscan_iter_keeps_ptTable n), (lscan_iter_keeps_pt_next_id n), (lscan_iter_keeps_certified n), (lscan_iter_keeps_wc_same_00 n), (lscan_iter_keeps_wc_diff_00 n), (lscan_iter_keeps_wc_same_01 n), (lscan_iter_keeps_wc_diff_01 n), (lscan_iter_keeps_wc_same_10 n), (lscan_iter_keeps_wc_diff_10 n), (lscan_iter_keeps_wc_same_11 n), (lscan_iter_keeps_wc_diff_11 n), (lscan_iter_keeps_csr_status n), (lscan_iter_keeps_csr_heap_base n), (lscan_iter_keeps_logic_acc n), (lscan_iter_keeps_mstatus n).
  unfold st2. rewrite lhdr_rich, lhdr_keeps_halted, lhdr_keeps_regs, lhdr_keeps_mem, lhdr_keeps_cert_addr, lhdr_keeps_partition_ops, lhdr_keeps_mdl_ops, lhdr_keeps_info_gain, lhdr_keeps_mu_tensor, lhdr_keeps_module_tensors, lhdr_keeps_ptTable, lhdr_keeps_pt_next_id, lhdr_keeps_certified, lhdr_keeps_wc_same_00, lhdr_keeps_wc_diff_00, lhdr_keeps_wc_same_01, lhdr_keeps_wc_diff_01, lhdr_keeps_wc_same_10, lhdr_keeps_wc_diff_10, lhdr_keeps_wc_same_11, lhdr_keeps_wc_diff_11, lhdr_keeps_pc, lhdr_keeps_err, lhdr_keeps_error_code, lhdr_keeps_trap_vector, lhdr_keeps_csr_status, lhdr_keeps_csr_heap_base, lhdr_keeps_logic_acc, lhdr_keeps_mstatus.
  unfold st1. rewrite (step_rich_frame b (step_lassert_sat_morph_valid_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_morph_src_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_morph_dst_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_morph_coupling_desc_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_morph_identity_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_morph_next_id a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_coupling_desc_label_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) (step_lassert_sat_coupling_desc_label_len_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)).
  unfold st1. rewrite (step_lassert_sat_halted a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_regs a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_mem a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_cert_addr a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_partition_ops a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_mdl_ops a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_info_gain a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_mu_tensor a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_module_tensors a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_ptTable a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_pt_next_id a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_certified a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_same_00 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_diff_00 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_same_01 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_diff_01 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_same_10 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_diff_10 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_same_11 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_wc_diff_11 a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_pc a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_err a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), (step_lassert_sat_error_code a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  rewrite step_keeps_csr_status, step_keeps_csr_heap_base, step_keeps_logic_acc, step_keeps_mstatus, step_keeps_trap_vector.
  assert (MuF : wordToNat (lscan_mu_fail st2) = wordToNat (hw_mu b) + (flen * 8 + S (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7)))).
  { rewrite lscan_mu_fail_nat.
     - unfold st2 at 1. rewrite lhdr_keeps_mu. unfold st1. rewrite (step_lassert_sat_mu a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), Fl2, Cp2, wordToNat_zext8_32. lia.
     - unfold st2 at 1. rewrite lhdr_keeps_mu. unfold st1. rewrite (step_lassert_sat_mu a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb), Fl2, Cp2, wordToNat_zext8_32. lia. }
  unfold kami_step. snap_projections. rewrite lassert_exec_ok_hw. cbv zeta.
  rewrite (proj2 (Nat.eqb_eq _ _) Hflen). cbn [andb].
  fold r. rewrite ?Herr, ?Hhalt.
  destruct r; cbv beta iota.
  all: apply kami_snapshot_ext; snap_projections.
  all: first [ syntactic | close_pc | exact Htrap | exact wordToNat_err_logic | exact MuF ].
Qed.

(** * Actual execution and exclusivity *)

Lemma rule_in_index : forall n, n <= 11 -> In (normalization_rule n) (getRules thieleCore).
Proof.
  intros n Hn. rewrite cpu_rules_listed. apply in_map. cbn [In].
  assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11) by lia.
  intuition.
Qed.

Fixpoint lscan_labels (n : nat) : list LabelT :=
  match n with
  | O => nil
  | S m => lscan_labels m ++ [normalization_label "lassert_fsm_scan"]
  end.

Lemma lscan_iter_multistep : forall n c,
  (forall m, m < n -> hw_lassert_phase (lscan_iter m c) = WO~0~1~0) ->
  Multistep thieleCore (hwb_regs c) (hwb_regs (lscan_iter n c)) (lscan_labels n).
Proof.
  induction n as [|n IH]; intros c H.
  - constructor. reflexivity.
  - cbn [lscan_iter lscan_labels].
    assert (G : evalExpr (((Var type (SyntaxKind (Bit 3)) (hw_lassert_phase c)) == $$(WO~0~1~0)))%kami_expr = true).
    { cbn [evalExpr evalConstT]. change (hw_lassert_phase c) with (hw_lassert_phase (lscan_iter 0 c)). rewrite (H 0 ltac:(lia)). reflexivity. }
    destruct (lscan_enabled c G) as [u [Hu Eu]].
    apply (normalization_multistep_trans _ (hwb_regs (lscan_next c))).
    + rewrite <- Eu. apply normalization_substep_execution.
      exact (cpu_rule_substep _ _ _ (rule_in_index 2 ltac:(lia)) Hu).
    + apply IH. intros m Hm. exact (H (S m) ltac:(lia)).
Qed.

(** From a live boundary, the step firing, the header firing and the scan
    firings of a SAT LASSERT are an actual Kami execution, and they retire to
    the [kami_step] result. *)
Theorem lassert_sat_execution : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen,
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
    Multistep thieleCore (hwb_regs b) (hwb_regs (lscan_iter n (lhdr_next (step_next b))))
      (lscan_labels n ++ [normalization_label "lassert_fsm_header"] ++ [normalization_label "step"]) /\
    hwb_snapshot (lscan_iter n (lhdr_next (step_next b))) =
    kami_step (hwb_snapshot b) (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) true flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb Hlive Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu.
  pose proof Hlive as [Hh [He _]].
  destruct (lassert_sat_refines a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb He Hh Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu)
    as [n [Hn [Hph [_ Hsnap]]]].
  exists n. split; [exact Hn|]. split; [|exact Hsnap].
  rewrite app_assoc.
  apply (normalization_multistep_trans _ (hwb_regs (step_next b))); [exact (live_step_multistep b Hlive)|].
  assert (G : evalExpr (((Var type (SyntaxKind (Bit 3)) (hw_lassert_phase (step_next b))) == $$(WO~0~0~1)))%kami_expr = true).
  { cbn [evalExpr evalConstT]. rewrite (step_lassert_sat_lassert_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). reflexivity. }
  destruct (lhdr_enabled (step_next b) G) as [u [Hu Eu]].
  apply (normalization_multistep_trans _ (hwb_regs (lhdr_next (step_next b)))).
  - rewrite <- Eu. apply normalization_substep_execution.
    exact (cpu_rule_substep _ _ _ (rule_in_index 1 ltac:(lia)) Hu).
  - apply lscan_iter_multistep. exact Hph.
Qed.

(** The UNSAT kind retires in the step firing alone, an actual Kami execution. *)
Theorem lassert_unsat_execution : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen,
  step_fetched b = lassert_unsat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_trap_vector b) = LASSERT_TRAP_PC ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) = flen ->
  wordToNat (hw_mu b) + flen * 8 + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) + 1 < pow2 32 ->
  Multistep thieleCore (hwb_regs b) (hwb_regs (step_next b)) [normalization_label "step"] /\
  hwb_snapshot (step_next b) =
  kami_step (hwb_snapshot b) (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) false flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))).
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb Hlive Htrap Hflen Hmu.
  pose proof Hlive as [Hh [He _]].
  split; [exact (live_step_multistep b Hlive)|].
  exact (lassert_unsat_refines a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb He Hh Htrap Hflen Hmu).
Qed.

(** While the SAT LASSERT runs, the header rule and then the scan rule are the
    only rules that can fire. *)
Theorem lassert_only_rule_enabled : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) c r,
  step_fetched b = lassert_sat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 -> hwb_bianchi b = false ->
  hw_lassert_phase c = WO~0~0~1 \/ hw_lassert_phase c = WO~0~1~0 ->
  hw_chsh_phase c = hw_chsh_phase (step_next b) -> hw_mc_phase c = hw_mc_phase (step_next b) ->
  In r (getRules thieleCore) -> eval_cpu_rule (hwb_regs c) r <> None ->
  (hw_lassert_phase c = WO~0~0~1 -> r = normalization_rule 1) /\
  (hw_lassert_phase c = WO~0~1~0 -> r = normalization_rule 2).
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b c r Hf Hb Hphase Hc Hm Hin Hr.
  rewrite (step_lassert_sat_chsh_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) in Hc.
  rewrite (step_lassert_sat_mc_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) in Hm.
  rewrite cpu_rules_listed in Hin. apply in_map_iff in Hin. destruct Hin as [k [Hrk Hk]]. subst r.
  cbn [In] in Hk.
  assert (Lne0 : hw_lassert_phase c <> natToWord 3 0) by (destruct Hphase as [E|E]; rewrite E; word_ne).
  repeat destruct Hk as [Hk|Hk]; try contradiction; subst k.
  - exfalso. apply Hr. change (normalization_rule 0) with dispatch_rule. rewrite eval_cpu_rule_dispatch.
    apply step_rule_disabled. unfold step_guards.
    destruct (weq (hw_lassert_phase c) (natToWord 3 0)) as [E|_]; [contradiction|].
    rewrite !andb_false_l, !andb_false_r. reflexivity.
  - split; [reflexivity|]. intro E. exfalso. apply Hr. apply lassert_fsm_header_disabled. rewrite E. word_ne.
  - split; [|reflexivity]. intro E. exfalso. apply Hr. apply lassert_fsm_scan_disabled. rewrite E. word_ne.
  - exfalso. apply Hr. apply mc_morph_header_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_morph_loop_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_copy_loop_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_join_loop_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_normalize_start_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_normalize_scan_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_normalize_emit_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply mc_commit_disabled. rewrite Hm. word_ne.
  - exfalso. apply Hr. apply chsh_lassert_fsm_disabled. exact Hc.
Qed.
