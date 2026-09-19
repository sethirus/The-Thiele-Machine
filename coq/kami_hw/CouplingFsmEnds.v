(** CouplingFsmEnds.v: the coupling FSM's header, normalization-start and
    commit rules at the typed boundary. Frame and write equations of each
    rule's next state, and [mchdr_fits_nat], the header's capacity check over
    natural numbers. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext NormalizationSteps DispatchObservation
  StepRefineCommon FsmDecoded.
Local Open Scope nat_scope.

(** * Header *)

Lemma ext5_32 : forall w : word 5, evalZeroExtendTrunc 32 w = zext w 27.
Proof.
  intro w. unfold evalZeroExtendTrunc.
  destruct (Compare_dec.lt_dec 5 32) as [H|H]; [|exfalso; lia].
  clear_concrete_word_casts. reflexivity.
Qed.

Lemma half_room : forall w : word 7,
  wordToNat (wrshift (wminus (natToWord 32 127) (zext w 25)) (wordToNat (natToWord 32 1))) = (127 - wordToNat w) / 2.
Proof.
  intro w. unfold wrshift. change (wordToNat (natToWord 32 1)) with 1.
  replace (Nat.add_comm 1 32) with (@eq_refl nat 33) by (apply Eqdep_dec.UIP_dec; exact Nat.eq_dec).
  rewrite <- (natToWord_wordToNat w).
  pose proof (wordToNat_bound w) as Hb. change (pow2 7) with 128 in Hb.
  generalize (wordToNat w) Hb. clear w Hb. intros n Hn.
  do 128 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma lt32_pow2_32 : forall k, k < 32 -> k < pow2 32.
Proof. intros k H. apply (Nat.lt_le_trans _ (2 ^ 5)); [exact H|]. change (pow2 32) with (2 ^ 32). apply Nat.pow_le_mono_r; lia. Qed.

Lemma mchdr_room_form : forall c,
  mchdr_mc_room c = evalZeroExtendTrunc 32 (wminus (natToWord 5 16) (hw_coupling_pair_next_id c)).
Proof. reflexivity. Qed.

Lemma mchdr_fits_form : forall c, mchdr_mc_fits c =
  andb (negb (if wlt_dec (mchdr_mc_room c) (mchdr_mc_raw_count c) then true else false))
       (negb (if wlt_dec (wrshift (wminus (natToWord 32 127) (hw_mc_mem_base c)) (wordToNat (natToWord 32 1)))
                         (mchdr_mc_raw_count c) then true else false)).
Proof. reflexivity. Qed.

Lemma mchdr_fits_nat : forall c (base : word 7) P count,
  hw_mc_mem_base c = zext base 25 -> hw_coupling_pair_next_id c = natToWord 5 P -> P <= 16 ->
  mchdr_mc_raw_count c = natToWord 32 count -> count + P <= 16 -> 2 * count + wordToNat base <= 127 ->
  mchdr_mc_fits c = true.
Proof.
  intros c base P count Hb Hp HP Hr Hc Hs.
  rewrite mchdr_fits_form, mchdr_room_form, Hb, Hp, Hr, ext5_32.
  assert (Wc : wordToNat (natToWord 32 count) = count) by (apply wordToNat_natToWord_2; apply lt32_pow2_32; lia).
  lazymatch goal with |- context [@wlt_dec ?sz (zext ?x ?n) ?y] => destruct (@wlt_dec sz (zext x n) y) as [L1|L1] end.
  - exfalso. apply wlt_lt in L1.
    rewrite (@Kami.Lib.Word.wordToNat_natToWord_2 _ count) in L1 by (apply lt32_pow2_32; lia).
    change (@wordToNat WordSz) with (@wordToNat (5 + 27)) in L1.
    rewrite wordToNat_zext, wordToNat_wminus_le in L1.
    + rewrite !wordToNat_natToWord_2 in L1 by (cbn; lia). lia.
    + rewrite !wordToNat_natToWord_2 by (cbn; lia). lia.
  - lazymatch goal with |- context [@wlt_dec ?sz (@wrshift ?s2 ?x ?n) ?y] => destruct (@wlt_dec sz (@wrshift s2 x n) y) as [L2|L2] end.
    + exfalso. apply wlt_lt in L2. rewrite (@Kami.Lib.Word.wordToNat_natToWord_2 _ count) in L2 by (apply lt32_pow2_32; lia).
      change (@wordToNat WordSz) with (@wordToNat 32) in L2. rewrite half_room in L2.
      assert (count <= (127 - wordToNat base) / 2) by (apply Nat.div_le_lower_bound; lia). lia.
    + reflexivity.
Qed.

Lemma mchdr_keeps_pc : forall c, hw_pc (mchdr_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mu : forall c, hw_mu (mchdr_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_halted : forall c, hw_halted (mchdr_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_regs : forall c, hw_regs (mchdr_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mem : forall c, hw_mem (mchdr_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_imem : forall c, hw_imem (mchdr_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_partition_ops : forall c, hw_partition_ops (mchdr_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mdl_ops : forall c, hw_mdl_ops (mchdr_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_info_gain : forall c, hw_info_gain (mchdr_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_logic_acc : forall c, hw_logic_acc (mchdr_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_cert_addr : forall c, hw_cert_addr (mchdr_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_active_module : forall c, hw_active_module (mchdr_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mstatus : forall c, hw_mstatus (mchdr_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mcycle_lo : forall c, hw_mcycle_lo (mchdr_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mcycle_hi : forall c, hw_mcycle_hi (mchdr_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_minstret_lo : forall c, hw_minstret_lo (mchdr_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_minstret_hi : forall c, hw_minstret_hi (mchdr_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_trap_vector : forall c, hw_trap_vector (mchdr_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_certified : forall c, hw_certified (mchdr_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_phase : forall c, hw_lassert_phase (mchdr_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_kind : forall c, hw_lassert_kind (mchdr_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_fbase : forall c, hw_lassert_fbase (mchdr_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_cbase : forall c, hw_lassert_cbase (mchdr_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_flen : forall c, hw_lassert_flen (mchdr_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_clen : forall c, hw_lassert_clen (mchdr_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_nvars : forall c, hw_lassert_nvars (mchdr_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_fptr : forall c, hw_lassert_fptr (mchdr_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_cptr : forall c, hw_lassert_cptr (mchdr_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mchdr_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mchdr_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mchdr_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mchdr_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mchdr_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_phase : forall c, hw_chsh_phase (mchdr_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n00 : forall c, hw_chsh_n00 (mchdr_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n01 : forall c, hw_chsh_n01 (mchdr_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n10 : forall c, hw_chsh_n10 (mchdr_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n11 : forall c, hw_chsh_n11 (mchdr_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d00 : forall c, hw_chsh_d00 (mchdr_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d01 : forall c, hw_chsh_d01 (mchdr_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d10 : forall c, hw_chsh_d10 (mchdr_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d11 : forall c, hw_chsh_d11 (mchdr_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mchdr_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mchdr_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mchdr_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mchdr_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mchdr_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mchdr_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mchdr_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mchdr_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mchdr_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mchdr_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mchdr_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mchdr_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mchdr_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mchdr_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mchdr_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mchdr_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mchdr_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mchdr_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mchdr_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mchdr_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mchdr_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mchdr_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mchdr_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mchdr_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mchdr_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mchdr_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_chsh_check_result : forall c, hw_chsh_check_result (mchdr_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mchdr_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mchdr_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mchdr_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mu_tensor : forall c, hw_mu_tensor (mchdr_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_module_tensors : forall c, hw_module_tensors (mchdr_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_csr_status : forall c, hw_csr_status (mchdr_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_csr_heap_base : forall c, hw_csr_heap_base (mchdr_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_ptTable : forall c, hw_ptTable (mchdr_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_pt_next_id : forall c, hw_pt_next_id (mchdr_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_morph_src_table : forall c, hw_morph_src_table (mchdr_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_morph_dst_table : forall c, hw_morph_dst_table (mchdr_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mchdr_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_morph_valid_table : forall c, hw_morph_valid_table (mchdr_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_morph_identity_table : forall c, hw_morph_identity_table (mchdr_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_morph_next_id : forall c, hw_morph_next_id (mchdr_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mchdr_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mchdr_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mchdr_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mchdr_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mchdr_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mchdr_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_pair_src_table : forall c, hw_coupling_pair_src_table (mchdr_next c) = hw_coupling_pair_src_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_pair_dst_table : forall c, hw_coupling_pair_dst_table (mchdr_next c) = hw_coupling_pair_dst_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (mchdr_next c) = hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mchdr_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_op : forall c, hw_mc_op (mchdr_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_mem_base : forall c, hw_mc_mem_base (mchdr_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_src1_base : forall c, hw_mc_src1_base (mchdr_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_src1_count : forall c, hw_mc_src1_count (mchdr_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_src2_base : forall c, hw_mc_src2_base (mchdr_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_src2_count : forall c, hw_mc_src2_count (mchdr_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_j : forall c, hw_mc_j (mchdr_next c) = hw_mc_j c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mchdr_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mchdr_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_write_base : forall c, hw_mc_write_base (mchdr_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_write_ptr : forall c, hw_mc_write_ptr (mchdr_next c) = hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (mchdr_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_duplicate : forall c, hw_mc_duplicate (mchdr_next c) = hw_mc_duplicate c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mchdr_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mchdr_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mchdr_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mchdr_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_mc_cost : forall c, hw_mc_cost (mchdr_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mchdr_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mchdr_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mchdr_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mchdr_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mchdr_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mchdr_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mchdr_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mchdr_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mchdr_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mchdr_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mchdr_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mchdr_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mchdr_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mchdr_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_same_00 : forall c, hw_wc_same_00 (mchdr_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mchdr_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_same_01 : forall c, hw_wc_same_01 (mchdr_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mchdr_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_same_10 : forall c, hw_wc_same_10 (mchdr_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mchdr_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_same_11 : forall c, hw_wc_same_11 (mchdr_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mchdr_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mchdr_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma mchdr_err : forall c, hw_err (mchdr_next c) = orb (hw_err c) (negb (mchdr_mc_fits c)).
Proof. reflexivity. Qed.
Lemma mchdr_error_code : forall c, hw_error_code (mchdr_next c) =
  if mchdr_mc_fits c then hw_error_code c else ERR_COUPLING_INVALID.
Proof. reflexivity. Qed.
Lemma mchdr_pair_count : forall c, hw_mc_pair_count (mchdr_next c) = split1 5 27 (mchdr_mc_raw_count c).
Proof. reflexivity. Qed.
Lemma mchdr_raw_count : forall c, mchdr_mc_raw_count c = hw_mem c (split1 7 25 (hw_mc_mem_base c)).
Proof. reflexivity. Qed.
Lemma mchdr_read_ptr : forall c, hw_mc_read_ptr (mchdr_next c) = wplus (hw_mc_mem_base c) (natToWord 32 1).
Proof. reflexivity. Qed.
Lemma mchdr_i : forall c, hw_mc_i (mchdr_next c) = natToWord 5 0.
Proof. reflexivity. Qed.
Lemma mchdr_phase : forall c, hw_mc_phase (mchdr_next c) =
  if negb (mchdr_mc_fits c) then natToWord 4 0
  else if (if weq (mchdr_mc_raw_count c) (natToWord 32 0) then true else false) then WO~0~1~0~1 else WO~0~0~1~0.
Proof. reflexivity. Qed.

(** * Normalization start *)

Lemma mcnstart_keeps_pc : forall c, hw_pc (mcnstart_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mu : forall c, hw_mu (mcnstart_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_err : forall c, hw_err (mcnstart_next c) = hw_err c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_halted : forall c, hw_halted (mcnstart_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_regs : forall c, hw_regs (mcnstart_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mem : forall c, hw_mem (mcnstart_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_imem : forall c, hw_imem (mcnstart_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_partition_ops : forall c, hw_partition_ops (mcnstart_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mdl_ops : forall c, hw_mdl_ops (mcnstart_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_info_gain : forall c, hw_info_gain (mcnstart_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_error_code : forall c, hw_error_code (mcnstart_next c) = hw_error_code c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_logic_acc : forall c, hw_logic_acc (mcnstart_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_cert_addr : forall c, hw_cert_addr (mcnstart_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_active_module : forall c, hw_active_module (mcnstart_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mstatus : forall c, hw_mstatus (mcnstart_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mcycle_lo : forall c, hw_mcycle_lo (mcnstart_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mcycle_hi : forall c, hw_mcycle_hi (mcnstart_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_minstret_lo : forall c, hw_minstret_lo (mcnstart_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_minstret_hi : forall c, hw_minstret_hi (mcnstart_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_trap_vector : forall c, hw_trap_vector (mcnstart_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_certified : forall c, hw_certified (mcnstart_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_phase : forall c, hw_lassert_phase (mcnstart_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_kind : forall c, hw_lassert_kind (mcnstart_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_fbase : forall c, hw_lassert_fbase (mcnstart_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_cbase : forall c, hw_lassert_cbase (mcnstart_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_flen : forall c, hw_lassert_flen (mcnstart_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_clen : forall c, hw_lassert_clen (mcnstart_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_nvars : forall c, hw_lassert_nvars (mcnstart_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_fptr : forall c, hw_lassert_fptr (mcnstart_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_cptr : forall c, hw_lassert_cptr (mcnstart_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mcnstart_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mcnstart_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mcnstart_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mcnstart_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mcnstart_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_phase : forall c, hw_chsh_phase (mcnstart_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n00 : forall c, hw_chsh_n00 (mcnstart_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n01 : forall c, hw_chsh_n01 (mcnstart_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n10 : forall c, hw_chsh_n10 (mcnstart_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n11 : forall c, hw_chsh_n11 (mcnstart_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d00 : forall c, hw_chsh_d00 (mcnstart_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d01 : forall c, hw_chsh_d01 (mcnstart_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d10 : forall c, hw_chsh_d10 (mcnstart_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d11 : forall c, hw_chsh_d11 (mcnstart_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mcnstart_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mcnstart_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mcnstart_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mcnstart_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mcnstart_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mcnstart_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mcnstart_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mcnstart_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mcnstart_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mcnstart_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mcnstart_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mcnstart_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mcnstart_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mcnstart_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mcnstart_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mcnstart_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mcnstart_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mcnstart_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mcnstart_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mcnstart_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mcnstart_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mcnstart_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mcnstart_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mcnstart_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mcnstart_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mcnstart_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_chsh_check_result : forall c, hw_chsh_check_result (mcnstart_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mcnstart_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mcnstart_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mcnstart_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mu_tensor : forall c, hw_mu_tensor (mcnstart_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_module_tensors : forall c, hw_module_tensors (mcnstart_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_csr_status : forall c, hw_csr_status (mcnstart_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_csr_heap_base : forall c, hw_csr_heap_base (mcnstart_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_ptTable : forall c, hw_ptTable (mcnstart_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_pt_next_id : forall c, hw_pt_next_id (mcnstart_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_morph_src_table : forall c, hw_morph_src_table (mcnstart_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_morph_dst_table : forall c, hw_morph_dst_table (mcnstart_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mcnstart_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_morph_valid_table : forall c, hw_morph_valid_table (mcnstart_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_morph_identity_table : forall c, hw_morph_identity_table (mcnstart_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_morph_next_id : forall c, hw_morph_next_id (mcnstart_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_desc_base_table : forall c, hw_coupling_desc_base_table (mcnstart_next c) = hw_coupling_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_desc_count_table : forall c, hw_coupling_desc_count_table (mcnstart_next c) = hw_coupling_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_desc_valid_table : forall c, hw_coupling_desc_valid_table (mcnstart_next c) = hw_coupling_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mcnstart_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mcnstart_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_desc_next_id : forall c, hw_coupling_desc_next_id (mcnstart_next c) = hw_coupling_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_pair_src_table : forall c, hw_coupling_pair_src_table (mcnstart_next c) = hw_coupling_pair_src_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_pair_dst_table : forall c, hw_coupling_pair_dst_table (mcnstart_next c) = hw_coupling_pair_dst_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (mcnstart_next c) = hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_coupling_pair_next_id : forall c, hw_coupling_pair_next_id (mcnstart_next c) = hw_coupling_pair_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_op : forall c, hw_mc_op (mcnstart_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_mem_base : forall c, hw_mc_mem_base (mcnstart_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_pair_count : forall c, hw_mc_pair_count (mcnstart_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (mcnstart_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_src1_base : forall c, hw_mc_src1_base (mcnstart_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_src1_count : forall c, hw_mc_src1_count (mcnstart_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_src2_base : forall c, hw_mc_src2_base (mcnstart_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_src2_count : forall c, hw_mc_src2_count (mcnstart_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mcnstart_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mcnstart_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_write_base : forall c, hw_mc_write_base (mcnstart_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_write_ptr : forall c, hw_mc_write_ptr (mcnstart_next c) = hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mcnstart_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mcnstart_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mcnstart_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mcnstart_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_mc_cost : forall c, hw_mc_cost (mcnstart_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mcnstart_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mcnstart_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mcnstart_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mcnstart_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mcnstart_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mcnstart_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mcnstart_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mcnstart_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mcnstart_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mcnstart_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mcnstart_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mcnstart_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mcnstart_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mcnstart_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_same_00 : forall c, hw_wc_same_00 (mcnstart_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mcnstart_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_same_01 : forall c, hw_wc_same_01 (mcnstart_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mcnstart_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_same_10 : forall c, hw_wc_same_10 (mcnstart_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mcnstart_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_same_11 : forall c, hw_wc_same_11 (mcnstart_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mcnstart_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mcnstart_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma mcnstart_i : forall c, hw_mc_i (mcnstart_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_j : forall c, hw_mc_j (mcnstart_next c) = wplus (hw_mc_write_base c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mcnstart_norm : forall c, hw_mc_norm_ptr (mcnstart_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mcnstart_dup : forall c, hw_mc_duplicate (mcnstart_next c) = false.
Proof. reflexivity. Qed.
Lemma mcnstart_phase : forall c, hw_mc_phase (mcnstart_next c) =
  if (if weq (hw_mc_write_base c) (hw_mc_write_ptr c) then true else false) then natToWord 4 11 else natToWord 4 8.
Proof. reflexivity. Qed.

(** * Commit *)

Lemma mccommit_keeps_pc : forall c, hw_pc (mccommit_next c) = hw_pc c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mu : forall c, hw_mu (mccommit_next c) = hw_mu c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_err : forall c, hw_err (mccommit_next c) = hw_err c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_halted : forall c, hw_halted (mccommit_next c) = hw_halted c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_regs : forall c, hw_regs (mccommit_next c) = hw_regs c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mem : forall c, hw_mem (mccommit_next c) = hw_mem c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_imem : forall c, hw_imem (mccommit_next c) = hw_imem c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_partition_ops : forall c, hw_partition_ops (mccommit_next c) = hw_partition_ops c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mdl_ops : forall c, hw_mdl_ops (mccommit_next c) = hw_mdl_ops c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_info_gain : forall c, hw_info_gain (mccommit_next c) = hw_info_gain c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_error_code : forall c, hw_error_code (mccommit_next c) = hw_error_code c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_logic_acc : forall c, hw_logic_acc (mccommit_next c) = hw_logic_acc c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_cert_addr : forall c, hw_cert_addr (mccommit_next c) = hw_cert_addr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_active_module : forall c, hw_active_module (mccommit_next c) = hw_active_module c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mstatus : forall c, hw_mstatus (mccommit_next c) = hw_mstatus c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mcycle_lo : forall c, hw_mcycle_lo (mccommit_next c) = hw_mcycle_lo c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mcycle_hi : forall c, hw_mcycle_hi (mccommit_next c) = hw_mcycle_hi c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_minstret_lo : forall c, hw_minstret_lo (mccommit_next c) = hw_minstret_lo c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_minstret_hi : forall c, hw_minstret_hi (mccommit_next c) = hw_minstret_hi c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_trap_vector : forall c, hw_trap_vector (mccommit_next c) = hw_trap_vector c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_certified : forall c, hw_certified (mccommit_next c) = hw_certified c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_phase : forall c, hw_lassert_phase (mccommit_next c) = hw_lassert_phase c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_kind : forall c, hw_lassert_kind (mccommit_next c) = hw_lassert_kind c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_fbase : forall c, hw_lassert_fbase (mccommit_next c) = hw_lassert_fbase c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_cbase : forall c, hw_lassert_cbase (mccommit_next c) = hw_lassert_cbase c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_flen : forall c, hw_lassert_flen (mccommit_next c) = hw_lassert_flen c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_clen : forall c, hw_lassert_clen (mccommit_next c) = hw_lassert_clen c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_nvars : forall c, hw_lassert_nvars (mccommit_next c) = hw_lassert_nvars c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_fptr : forall c, hw_lassert_fptr (mccommit_next c) = hw_lassert_fptr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_cptr : forall c, hw_lassert_cptr (mccommit_next c) = hw_lassert_cptr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_fbuf : forall c, hw_lassert_fbuf (mccommit_next c) = hw_lassert_fbuf c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_cbuf : forall c, hw_lassert_cbuf (mccommit_next c) = hw_lassert_cbuf c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_clause_sat : forall c, hw_lassert_clause_sat (mccommit_next c) = hw_lassert_clause_sat c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_counter_clause_sat : forall c, hw_lassert_counter_clause_sat (mccommit_next c) = hw_lassert_counter_clause_sat c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_lassert_counter_seen_fail : forall c, hw_lassert_counter_seen_fail (mccommit_next c) = hw_lassert_counter_seen_fail c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_phase : forall c, hw_chsh_phase (mccommit_next c) = hw_chsh_phase c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n00 : forall c, hw_chsh_n00 (mccommit_next c) = hw_chsh_n00 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n01 : forall c, hw_chsh_n01 (mccommit_next c) = hw_chsh_n01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n10 : forall c, hw_chsh_n10 (mccommit_next c) = hw_chsh_n10 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n11 : forall c, hw_chsh_n11 (mccommit_next c) = hw_chsh_n11 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d00 : forall c, hw_chsh_d00 (mccommit_next c) = hw_chsh_d00 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d01 : forall c, hw_chsh_d01 (mccommit_next c) = hw_chsh_d01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d10 : forall c, hw_chsh_d10 (mccommit_next c) = hw_chsh_d10 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d11 : forall c, hw_chsh_d11 (mccommit_next c) = hw_chsh_d11 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_sign00 : forall c, hw_chsh_sign00 (mccommit_next c) = hw_chsh_sign00 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_sign01 : forall c, hw_chsh_sign01 (mccommit_next c) = hw_chsh_sign01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_sign10 : forall c, hw_chsh_sign10 (mccommit_next c) = hw_chsh_sign10 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_sign11 : forall c, hw_chsh_sign11 (mccommit_next c) = hw_chsh_sign11 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n00sq : forall c, hw_chsh_n00sq (mccommit_next c) = hw_chsh_n00sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n01sq : forall c, hw_chsh_n01sq (mccommit_next c) = hw_chsh_n01sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n10sq : forall c, hw_chsh_n10sq (mccommit_next c) = hw_chsh_n10sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n11sq : forall c, hw_chsh_n11sq (mccommit_next c) = hw_chsh_n11sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d00sq : forall c, hw_chsh_d00sq (mccommit_next c) = hw_chsh_d00sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d01sq : forall c, hw_chsh_d01sq (mccommit_next c) = hw_chsh_d01sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d10sq : forall c, hw_chsh_d10sq (mccommit_next c) = hw_chsh_d10sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d11sq : forall c, hw_chsh_d11sq (mccommit_next c) = hw_chsh_d11sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_A_pos : forall c, hw_chsh_A_pos (mccommit_next c) = hw_chsh_A_pos c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_A_neg_a : forall c, hw_chsh_A_neg_a (mccommit_next c) = hw_chsh_A_neg_a c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_A_neg_b : forall c, hw_chsh_A_neg_b (mccommit_next c) = hw_chsh_A_neg_b c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_B_pos : forall c, hw_chsh_B_pos (mccommit_next c) = hw_chsh_B_pos c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_B_neg_a : forall c, hw_chsh_B_neg_a (mccommit_next c) = hw_chsh_B_neg_a c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_B_neg_b : forall c, hw_chsh_B_neg_b (mccommit_next c) = hw_chsh_B_neg_b c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d00d01 : forall c, hw_chsh_d00d01 (mccommit_next c) = hw_chsh_d00d01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n10n11 : forall c, hw_chsh_n10n11 (mccommit_next c) = hw_chsh_n10n11 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_d10d11 : forall c, hw_chsh_d10d11 (mccommit_next c) = hw_chsh_d10d11 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_n00n01 : forall c, hw_chsh_n00n01 (mccommit_next c) = hw_chsh_n00n01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_abs_C1 : forall c, hw_chsh_abs_C1 (mccommit_next c) = hw_chsh_abs_C1 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_abs_C2 : forall c, hw_chsh_abs_C2 (mccommit_next c) = hw_chsh_abs_C2 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_C_sq : forall c, hw_chsh_C_sq (mccommit_next c) = hw_chsh_C_sq c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_A_times_B : forall c, hw_chsh_A_times_B (mccommit_next c) = hw_chsh_A_times_B c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_chsh_check_result : forall c, hw_chsh_check_result (mccommit_next c) = hw_chsh_check_result c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_bus_load_instr_addr : forall c, hw_bus_load_instr_addr (mccommit_next c) = hw_bus_load_instr_addr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_bus_load_instr_data : forall c, hw_bus_load_instr_data (mccommit_next c) = hw_bus_load_instr_data c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_bus_load_instr_kick : forall c, hw_bus_load_instr_kick (mccommit_next c) = hw_bus_load_instr_kick c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mu_tensor : forall c, hw_mu_tensor (mccommit_next c) = hw_mu_tensor c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_module_tensors : forall c, hw_module_tensors (mccommit_next c) = hw_module_tensors c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_csr_status : forall c, hw_csr_status (mccommit_next c) = hw_csr_status c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_csr_heap_base : forall c, hw_csr_heap_base (mccommit_next c) = hw_csr_heap_base c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_ptTable : forall c, hw_ptTable (mccommit_next c) = hw_ptTable c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_pt_next_id : forall c, hw_pt_next_id (mccommit_next c) = hw_pt_next_id c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_morph_src_table : forall c, hw_morph_src_table (mccommit_next c) = hw_morph_src_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_morph_dst_table : forall c, hw_morph_dst_table (mccommit_next c) = hw_morph_dst_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_morph_coupling_desc_table : forall c, hw_morph_coupling_desc_table (mccommit_next c) = hw_morph_coupling_desc_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_morph_valid_table : forall c, hw_morph_valid_table (mccommit_next c) = hw_morph_valid_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_morph_identity_table : forall c, hw_morph_identity_table (mccommit_next c) = hw_morph_identity_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_morph_next_id : forall c, hw_morph_next_id (mccommit_next c) = hw_morph_next_id c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_coupling_desc_label_table : forall c, hw_coupling_desc_label_table (mccommit_next c) = hw_coupling_desc_label_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_coupling_desc_label_len_table : forall c, hw_coupling_desc_label_len_table (mccommit_next c) = hw_coupling_desc_label_len_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_coupling_pair_src_table : forall c, hw_coupling_pair_src_table (mccommit_next c) = hw_coupling_pair_src_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_coupling_pair_dst_table : forall c, hw_coupling_pair_dst_table (mccommit_next c) = hw_coupling_pair_dst_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_coupling_pair_valid_table : forall c, hw_coupling_pair_valid_table (mccommit_next c) = hw_coupling_pair_valid_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_op : forall c, hw_mc_op (mccommit_next c) = hw_mc_op c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_mem_base : forall c, hw_mc_mem_base (mccommit_next c) = hw_mc_mem_base c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_pair_count : forall c, hw_mc_pair_count (mccommit_next c) = hw_mc_pair_count c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_read_ptr : forall c, hw_mc_read_ptr (mccommit_next c) = hw_mc_read_ptr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_src1_base : forall c, hw_mc_src1_base (mccommit_next c) = hw_mc_src1_base c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_src1_count : forall c, hw_mc_src1_count (mccommit_next c) = hw_mc_src1_count c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_src2_base : forall c, hw_mc_src2_base (mccommit_next c) = hw_mc_src2_base c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_src2_count : forall c, hw_mc_src2_count (mccommit_next c) = hw_mc_src2_count c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_i : forall c, hw_mc_i (mccommit_next c) = hw_mc_i c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_j : forall c, hw_mc_j (mccommit_next c) = hw_mc_j c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_is_id1 : forall c, hw_mc_is_id1 (mccommit_next c) = hw_mc_is_id1 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_is_id2 : forall c, hw_mc_is_id2 (mccommit_next c) = hw_mc_is_id2 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_write_base : forall c, hw_mc_write_base (mccommit_next c) = hw_mc_write_base c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_write_ptr : forall c, hw_mc_write_ptr (mccommit_next c) = hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_norm_ptr : forall c, hw_mc_norm_ptr (mccommit_next c) = hw_mc_norm_ptr c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_duplicate : forall c, hw_mc_duplicate (mccommit_next c) = hw_mc_duplicate c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_dst_reg : forall c, hw_mc_dst_reg (mccommit_next c) = hw_mc_dst_reg c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_morph_slot : forall c, hw_mc_morph_slot (mccommit_next c) = hw_mc_morph_slot c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_new_src_mod : forall c, hw_mc_new_src_mod (mccommit_next c) = hw_mc_new_src_mod c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_new_dst_mod : forall c, hw_mc_new_dst_mod (mccommit_next c) = hw_mc_new_dst_mod c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_mc_cost : forall c, hw_mc_cost (mccommit_next c) = hw_mc_cost c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_formula_desc_base_table : forall c, hw_formula_desc_base_table (mccommit_next c) = hw_formula_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_formula_desc_count_table : forall c, hw_formula_desc_count_table (mccommit_next c) = hw_formula_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_formula_desc_valid_table : forall c, hw_formula_desc_valid_table (mccommit_next c) = hw_formula_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_formula_desc_next_id : forall c, hw_formula_desc_next_id (mccommit_next c) = hw_formula_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_cert_desc_base_table : forall c, hw_cert_desc_base_table (mccommit_next c) = hw_cert_desc_base_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_cert_desc_count_table : forall c, hw_cert_desc_count_table (mccommit_next c) = hw_cert_desc_count_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_cert_desc_valid_table : forall c, hw_cert_desc_valid_table (mccommit_next c) = hw_cert_desc_valid_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_cert_desc_next_id : forall c, hw_cert_desc_next_id (mccommit_next c) = hw_cert_desc_next_id c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_desc_meta_subtype_table : forall c, hw_desc_meta_subtype_table (mccommit_next c) = hw_desc_meta_subtype_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_desc_meta_kind_table : forall c, hw_desc_meta_kind_table (mccommit_next c) = hw_desc_meta_kind_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_desc_meta_inline_len_table : forall c, hw_desc_meta_inline_len_table (mccommit_next c) = hw_desc_meta_inline_len_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_desc_meta_aux_table : forall c, hw_desc_meta_aux_table (mccommit_next c) = hw_desc_meta_aux_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_desc_meta_valid_table : forall c, hw_desc_meta_valid_table (mccommit_next c) = hw_desc_meta_valid_table c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_desc_meta_next_id : forall c, hw_desc_meta_next_id (mccommit_next c) = hw_desc_meta_next_id c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_same_00 : forall c, hw_wc_same_00 (mccommit_next c) = hw_wc_same_00 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_diff_00 : forall c, hw_wc_diff_00 (mccommit_next c) = hw_wc_diff_00 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_same_01 : forall c, hw_wc_same_01 (mccommit_next c) = hw_wc_same_01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_diff_01 : forall c, hw_wc_diff_01 (mccommit_next c) = hw_wc_diff_01 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_same_10 : forall c, hw_wc_same_10 (mccommit_next c) = hw_wc_same_10 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_diff_10 : forall c, hw_wc_diff_10 (mccommit_next c) = hw_wc_diff_10 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_same_11 : forall c, hw_wc_same_11 (mccommit_next c) = hw_wc_same_11 c.
Proof. reflexivity. Qed.
Lemma mccommit_keeps_wc_diff_11 : forall c, hw_wc_diff_11 (mccommit_next c) = hw_wc_diff_11 c.
Proof. reflexivity. Qed.

Lemma mccommit_base : forall c, hw_coupling_desc_base_table (mccommit_next c) =
  put_vector (hw_coupling_desc_base_table c) (split1 4 1 (hw_coupling_desc_next_id c)) (split1 4 1 (hw_mc_write_base c)).
Proof. reflexivity. Qed.
Lemma mccommit_count : forall c, hw_coupling_desc_count_table (mccommit_next c) =
  put_vector (hw_coupling_desc_count_table c) (split1 4 1 (hw_coupling_desc_next_id c))
    (wminus (hw_mc_write_ptr c) (hw_mc_write_base c)).
Proof. reflexivity. Qed.
Lemma mccommit_valid : forall c, hw_coupling_desc_valid_table (mccommit_next c) =
  put_vector (hw_coupling_desc_valid_table c) (split1 4 1 (hw_coupling_desc_next_id c)) true.
Proof. reflexivity. Qed.
Lemma mccommit_desc_next : forall c, hw_coupling_desc_next_id (mccommit_next c) =
  wplus (hw_coupling_desc_next_id c) (natToWord 5 1).
Proof. reflexivity. Qed.
Lemma mccommit_pair_next : forall c, hw_coupling_pair_next_id (mccommit_next c) = hw_mc_write_ptr c.
Proof. reflexivity. Qed.
Lemma mccommit_phase : forall c, hw_mc_phase (mccommit_next c) = natToWord 4 0.
Proof. reflexivity. Qed.
