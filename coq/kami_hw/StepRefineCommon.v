(** Shared facts for the per-opcode refinements of the actual step rule:
    hardware word operations against the natural-number and 64-bit forms used
    by [kami_step], and the rich-state frame of the step rule. *)
Require Import Kami.Kami Kami.Lib.NatLib.
From Coq Require Import Arith Lia NArith FunctionalExtensionality Eqdep_dec.
From KamiHW Require Import ThieleTypes HWBoundary ImplementationContract Abstraction
  RuleStep StepEval StepWordFacts StepFields.
Require Import Kernel.VMState Kernel.VMStep.

(** * Truncations, extensions and concatenation *)

Lemma wordToNat_trunc7 : forall w : word WordSz,
  wordToNat (split1 7 25 w) = wordToNat w mod 128.
Proof. intro w. exact (wordToNat_split1 7 25 w). Qed.

Lemma wordToNat_trunc7_8 : forall w : word 8,
  wordToNat (split1 7 1 w) = wordToNat w mod 128.
Proof. intro w. exact (wordToNat_split1 7 1 w). Qed.

Lemma wordToNat_trunc6_7 : forall w : word 7,
  wordToNat (split1 6 1 w) = wordToNat w mod 64.
Proof. intro w. exact (wordToNat_split1 6 1 w). Qed.

Lemma wordToNat_trunc6_8 : forall w : word 8,
  wordToNat (split1 6 2 w) = wordToNat w mod 64.
Proof. intro w. exact (wordToNat_split1 6 2 w). Qed.

Lemma evalZeroExtendTrunc_up : forall n1 n2 (w : word n1),
  n1 < n2 -> wordToNat (evalZeroExtendTrunc n2 w) = wordToNat w.
Proof.
  intros n1 n2 w H. unfold evalZeroExtendTrunc.
  destruct (Compare_dec.lt_dec n1 n2) as [Hlt|Hge]; [|lia].
  unfold eq_rec_r, eq_rec. rewrite wordToNat_eq_rect. apply wordToNat_zext.
Qed.

Lemma wordToNat_zext8_ext : forall w : word 8,
  wordToNat (evalZeroExtendTrunc WordSz w) = wordToNat w.
Proof. intro w. apply evalZeroExtendTrunc_up. unfold WordSz. lia. Qed.

Lemma wordToNat_zext16_ext : forall w : word 16,
  wordToNat (evalZeroExtendTrunc WordSz w) = wordToNat w.
Proof. intro w. apply evalZeroExtendTrunc_up. unfold WordSz. lia. Qed.

Lemma wordToNat_zext7_ext : forall w : word MemAddrSz,
  wordToNat (evalZeroExtendTrunc WordSz w) = wordToNat w.
Proof. intro w. apply evalZeroExtendTrunc_up. unfold WordSz, MemAddrSz. lia. Qed.

Lemma wordToNat_combine8 : forall (lo hi : word 8),
  wordToNat (combine lo hi) = wordToNat lo + 256 * wordToNat hi.
Proof. intros. exact (wordToNat_combine lo hi). Qed.

(** * Arithmetic *)

Lemma wordToNat_wminus_le : forall sz (a b : word sz),
  wordToNat b <= wordToNat a ->
  wordToNat (wminus a b) = wordToNat a - wordToNat b.
Proof.
  intros sz a b H.
  assert (E : a = wplus (natToWord sz (wordToNat a - wordToNat b)) b).
  { apply wordToNat_inj. rewrite wordToNat_wplus.
    pose proof (wordToNat_bound a) as Ba.
    rewrite wordToNat_natToWord_2 by lia.
    replace (wordToNat a - wordToNat b + wordToNat b) with (wordToNat a) by lia.
    rewrite Nat.mod_small by exact Ba. reflexivity. }
  rewrite E at 1.
  rewrite wminus_def, <- wplus_assoc, wminus_inv.
  rewrite wplus_comm, wplus_unit.
  pose proof (wordToNat_bound a). apply wordToNat_natToWord_2. lia.
Qed.

Lemma wordToNat_wmult_bounded : forall sz (a b : word sz),
  wordToNat a * wordToNat b < pow2 sz ->
  wordToNat (wmult a b) = wordToNat a * wordToNat b.
Proof. intros. apply wordToNat_wmult'. exact H. Qed.

Lemma N_of_nat_below_pow2_32 : forall x, x < pow2 32 -> (N.of_nat x < 2 ^ 64)%N.
Proof.
  intros x Hx. assert (HN : (N.of_nat x < N.of_nat (pow2 32))%N) by lia.
  rewrite pow2_32_N in HN. eapply N.lt_trans; [exact HN|]. vm_compute. reflexivity.
Qed.

Lemma word64_sub_small : forall a b,
  b <= a -> a < pow2 32 -> word64_sub a b = a - b.
Proof.
  intros a b Hba Ha. unfold word64_sub.
  rewrite !word64_below_pow2_32 by lia.
  unfold word64_mask. rewrite N.land_ones.
  pose proof (N_of_nat_below_pow2_32 b ltac:(lia)) as Hb.
  pose proof (N_of_nat_below_pow2_32 a Ha) as Ha'.
  change (N.lxor (N.of_nat b) (N.ones 64)) with (N.lnot (N.of_nat b) 64).
  rewrite N.lnot_sub_low.
  2:{ destruct (N.eq_dec (N.of_nat b) 0) as [E|E]; [rewrite E; reflexivity|].
      apply N.log2_lt_pow2; lia. }
  rewrite N.ones_equiv.
  replace (N.of_nat a + (N.pred (2 ^ 64) - N.of_nat b + 1))%N
    with (N.of_nat (a - b) + 1 * 2 ^ 64)%N.
  2:{ rewrite Nat2N.inj_sub. assert (0 < 2 ^ 64)%N by (vm_compute; reflexivity).
      rewrite N.pred_sub. lia. }
  rewrite N.mod_add by (vm_compute; discriminate).
  rewrite N.mod_small by (pose proof (N_of_nat_below_pow2_32 (a - b) ltac:(lia)); lia).
  apply Nat2N.id.
Qed.

(** * Bitwise operations *)

Lemma testbit_wordToN_WS : forall sz (w : word sz) bit i,
  N.testbit (wordToN (WS bit w)) i =
  if N.eqb i 0 then bit else N.testbit (wordToN w) (N.pred i).
Proof.
  intros sz w bit i. destruct bit.
  - rewrite wordToN_WS_1. destruct (N.eqb_spec i 0) as [E|E].
    + subst i. apply N.testbit_odd_0.
    + replace i with (N.succ (N.pred i)) at 1 by lia.
      apply N.testbit_odd_succ. lia.
  - rewrite wordToN_WS_0. destruct (N.eqb_spec i 0) as [E|E].
    + subst i. apply N.testbit_even_0.
    + replace i with (N.succ (N.pred i)) at 1 by lia.
      apply N.testbit_even_succ. lia.
Qed.

Lemma testbit_bitwp : forall f, f false false = false ->
  forall sz (x y : word sz) i,
  N.testbit (wordToN (bitwp f x y)) i =
  f (N.testbit (wordToN x) i) (N.testbit (wordToN y) i).
Proof.
  intros f Hf sz x. induction x as [|bx n x IH]; intros y i.
  - rewrite (word0 y). cbn [bitwp wordToN]. rewrite !N.bits_0. symmetry. exact Hf.
  - destruct (shatter_word_S y) as [yb [y' Ey]]. subst y. cbn [bitwp].
    rewrite !testbit_wordToN_WS. destruct (N.eqb i 0); [reflexivity|]. apply IH.
Qed.

Lemma wordToN_wand : forall sz (x y : word sz),
  wordToN (wand x y) = N.land (wordToN x) (wordToN y).
Proof.
  intros. apply N.bits_inj. intro i. rewrite N.land_spec.
  apply testbit_bitwp. reflexivity.
Qed.

Lemma wordToN_wor : forall sz (x y : word sz),
  wordToN (wor x y) = N.lor (wordToN x) (wordToN y).
Proof.
  intros. apply N.bits_inj. intro i. rewrite N.lor_spec.
  apply testbit_bitwp. reflexivity.
Qed.

Lemma wordToN_wxor : forall sz (x y : word sz),
  wordToN (wxor x y) = N.lxor (wordToN x) (wordToN y).
Proof.
  intros. apply N.bits_inj. intro i. rewrite N.lxor_spec.
  apply testbit_bitwp. reflexivity.
Qed.

Lemma N_to_nat_wordToN : forall sz (w : word sz), N.to_nat (wordToN w) = wordToNat w.
Proof. intros. rewrite wordToN_nat. apply Nat2N.id. Qed.

Lemma word64_and_word32 : forall x y : word WordSz,
  word64_and (wordToNat x) (wordToNat y) = wordToNat (wand x y).
Proof.
  intros x y. unfold word64_and, word64_mask.
  rewrite <- !wordToN_nat, <- wordToN_wand, N.land_ones.
  rewrite N.mod_small; [apply N_to_nat_wordToN|].
  rewrite wordToN_nat. apply N_of_nat_below_pow2_32. apply wordToNat_bound.
Qed.

Lemma word64_or_word32 : forall x y : word WordSz,
  word64_or (wordToNat x) (wordToNat y) = wordToNat (wor x y).
Proof.
  intros x y. unfold word64_or, word64_mask.
  rewrite <- !wordToN_nat, !N.land_ones.
  rewrite !(N.mod_small (wordToN _)) by
    (rewrite wordToN_nat; apply N_of_nat_below_pow2_32; apply wordToNat_bound).
  rewrite <- wordToN_wor. apply N_to_nat_wordToN.
Qed.

Lemma word64_xor_word32 : forall x y : word WordSz,
  word64_xor (wordToNat x) (wordToNat y) = wordToNat (wxor x y).
Proof.
  intros x y. unfold word64_xor.
  rewrite <- !wordToN_nat, <- wordToN_wxor, N_to_nat_wordToN.
  apply word64_word32.
Qed.

(** * Shifts *)

Lemma wordToNat_wrshift : forall sz (w : word sz) n,
  wordToNat (wrshift w n) = wordToNat w / pow2 n.
Proof.
  intros sz w n. unfold wrshift.
  rewrite wordToNat_split2. unfold eq_rec_r, eq_rec.
  rewrite wordToNat_eq_rect, wordToNat_combine, wordToNat_wzero.
  rewrite Nat.mul_0_r, Nat.add_0_r. reflexivity.
Qed.

Lemma word64_shr_word32 : forall (x : word WordSz) s,
  s < 64 -> word64_shr (wordToNat x) s = wordToNat (wrshift x s).
Proof.
  intros x s Hs. unfold word64_shr, word64_mask.
  rewrite wordToNat_wrshift, N.land_ones, Nat.mod_small by exact Hs.
  rewrite N.mod_small by (apply N_of_nat_below_pow2_32; apply wordToNat_bound).
  rewrite N.shiftr_div_pow2. rewrite N2Nat.inj_div, Nat2N.id, N2Nat.inj_pow, Nat2N.id. reflexivity.
Qed.

Lemma word64_shl_word32 : forall (x : word WordSz) s,
  s < 32 -> wordToNat x * pow2 s < pow2 32 ->
  word64_shl (wordToNat x) s = wordToNat (wlshift x s).
Proof.
  intros x s Hs Hb. unfold word64_shl.
  rewrite (Nat.mod_small s 64) by lia.
  rewrite N.shiftl_mul_pow2.
  replace (N.to_nat (N.of_nat (wordToNat x) * 2 ^ N.of_nat s)) with (wordToNat x * pow2 s)
    by (rewrite N2Nat.inj_mul, Nat2N.id, N2Nat.inj_pow, Nat2N.id; reflexivity).
  rewrite word64_below_pow2_32 by exact Hb.
  rewrite wordToNat_wlshift. rewrite Nat.mod_small; [reflexivity|].
  assert (0 < pow2 s) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  replace (pow2 32) with (pow2 (32 - s) * pow2 s) in Hb
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  apply (Nat.mul_lt_mono_pos_r (pow2 s)); [lia|exact Hb].
Qed.

(** * Rich-state frame of the step rule *)

Lemma step_rich_frame : forall b,
  hw_morph_valid_table (step_next b) = hw_morph_valid_table b ->
  hw_morph_src_table (step_next b) = hw_morph_src_table b ->
  hw_morph_dst_table (step_next b) = hw_morph_dst_table b ->
  hw_morph_coupling_desc_table (step_next b) = hw_morph_coupling_desc_table b ->
  hw_morph_identity_table (step_next b) = hw_morph_identity_table b ->
  hw_morph_next_id (step_next b) = hw_morph_next_id b ->
  hw_coupling_desc_label_table (step_next b) = hw_coupling_desc_label_table b ->
  hw_coupling_desc_label_len_table (step_next b) = hw_coupling_desc_label_len_table b ->
  hwb_rich (step_next b) = hwb_rich b.
Proof.
  intros b H1 H2 H3 H4 H5 H6 H7 H8. unfold hwb_rich.
  rewrite H1, H2, H3, H4, H5, H6, H7, H8.
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_base_table,
    step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id,
    step_keeps_coupling_pair_valid_table, step_keeps_coupling_pair_src_table,
    step_keeps_coupling_pair_dst_table, step_keeps_coupling_pair_next_id,
    step_keeps_formula_desc_valid_table, step_keeps_formula_desc_base_table,
    step_keeps_formula_desc_count_table, step_keeps_formula_desc_next_id,
    step_keeps_cert_desc_valid_table, step_keeps_cert_desc_base_table,
    step_keeps_cert_desc_count_table, step_keeps_cert_desc_next_id,
    step_keeps_desc_meta_valid_table, step_keeps_desc_meta_subtype_table,
    step_keeps_desc_meta_kind_table, step_keeps_desc_meta_inline_len_table,
    step_keeps_desc_meta_aux_table, step_keeps_desc_meta_next_id.
  reflexivity.
Qed.

(** * Bounds on 32-bit values without unfolding the width *)

Lemma word32_lt_pow2_32 : forall w : word WordSz, wordToNat w < pow2 32.
Proof. intro w. exact (wordToNat_bound w). Qed.

Lemma word32_sub_lt_pow2_32 : forall x y : word WordSz,
  wordToNat x - wordToNat y < pow2 32.
Proof. intros. eapply Nat.le_lt_trans; [apply Nat.le_sub_l|apply word32_lt_pow2_32]. Qed.

Lemma word8_lt_pow2_32 : forall w : word 8, wordToNat w < pow2 32.
Proof.
  intro w. eapply Nat.lt_le_trans; [exact (wordToNat_bound w)|].
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma word64_twice_small : forall x, x < pow2 32 -> word64 (word64 x) = x.
Proof. intros x H. rewrite (word64_below_pow2_32 x H). apply word64_below_pow2_32. exact H. Qed.

Lemma wordToNat_word0_32 : wordToNat (natToWord WordSz 0) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma wordToNat_word8_32 : wordToNat (natToWord WordSz 8) = 8.
Proof. vm_compute. reflexivity. Qed.

Lemma word32_nonzero : forall w : word WordSz,
  w <> natToWord WordSz 0 -> Nat.eqb (wordToNat w) 0 = false.
Proof.
  intros w H. apply Nat.eqb_neq. intro E. apply H.
  apply wordToNat_inj. rewrite E, wordToNat_word0_32. reflexivity.
Qed.

Lemma lui_shift_bound : forall w : word 8,
  wordToNat (zext w 24) * pow2 8 < pow2 32.
Proof.
  intro w. rewrite wordToNat_zext8_32. pose proof (wordToNat_bound w) as H.
  apply Nat.lt_le_trans with (m := pow2 8 * pow2 8).
  - apply Nat.mul_lt_mono_pos_r; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia|exact H].
  - rewrite <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
Qed.

Lemma wordToNat_wplus_one_bounded : forall sz (x : word sz),
  wordToNat x + 1 < pow2 sz -> wordToNat (wplus x (natToWord sz 1)) = S (wordToNat x).
Proof.
  intros sz x H. rewrite wordToNat_wplus_bounded.
  - rewrite wordToNat_natToWord_2 by lia. lia.
  - rewrite wordToNat_natToWord_2 by lia. exact H.
Qed.

(** * Tensor indexing and zero operands *)

Definition bits2 (x0 x1 : bool) : word 2 := WS x0 (WS x1 WO).

Lemma tensor_flat_index : forall x0 x1 x2 x3 : bool,
  wordToNat (bits2 x2 x3) * 4 + wordToNat (bits2 x0 x1) = wordToNat (bits4 x0 x1 x2 x3).
Proof. intros x0 x1 x2 x3. destruct x0, x1, x2, x3; reflexivity. Qed.

Lemma bits2_lt_4 : forall x0 x1, wordToNat (bits2 x0 x1) < 4.
Proof. intros x0 x1. destruct x0, x1; cbn; lia. Qed.

Lemma hw_nfi_ok_zero : forall c : word 8,
  StepFields.hw_nfi_ok c (bits8 false false false false false false false false) = true.
Proof.
  intro c. unfold StepFields.hw_nfi_ok. destruct (wlt_dec _ _) as [H|H]; [|reflexivity].
  exfalso. apply wlt_lt in H. rewrite wordToNat_zext8_32 in H.
  change (wordToNat (zext (bits8 false false false false false false false false) 24)) with 0 in H.
  lia.
Qed.

Lemma wplus_zext_zero : forall x : word WordSz,
  wplus x (zext (bits8 false false false false false false false false) 24) = x.
Proof.
  intro x. change (zext (bits8 false false false false false false false false) 24)
    with (natToWord WordSz 0).
  rewrite wplus_comm. apply wplus_unit.
Qed.

Lemma word64_zero : word64 0 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma word4_ltb_16 : forall w : word 4, Nat.ltb (wordToNat w) 16 = true.
Proof. intro w. apply Nat.ltb_lt. exact (wordToNat_bound w). Qed.

Lemma natToWord_word4_ne : forall m (x : word 4),
  m < 16 -> m <> wordToNat x -> natToWord 4 m <> x.
Proof.
  intros m x Hm Hne E. apply Hne. rewrite <- E.
  symmetry. apply wordToNat_natToWord_idempotent'. exact Hm.
Qed.

Lemma hwb_vector_nat_swap : forall (v : word 4 -> word WordSz) (x y : word 4),
  hwb_vector_nat (n := 4)
    (fun w => if weq w y then v x else (fun w0 => if weq w0 x then v y else v w0) w) =
  fun j => if Nat.eqb j (wordToNat x) then wordToNat (v y)
           else if Nat.eqb j (wordToNat y) then wordToNat (v x)
           else hwb_vector_nat (n := 4) v j.
Proof.
  intros v x y. rewrite hwb_vector_nat_update. extensionality j.
  rewrite hwb_vector_nat_update.
  destruct (Nat.eqb_spec j (wordToNat y)) as [Ey|Ey];
    destruct (Nat.eqb_spec j (wordToNat x)) as [Ex|Ex]; try reflexivity.
  subst j. apply wordToNat_inj in Ex. subst y. reflexivity.
Qed.

Lemma hwb_vector_nat_add_at : forall (v : word 4 -> word WordSz) (x : word 4) (d : word WordSz),
  wordToNat (v x) + wordToNat d < pow2 WordSz ->
  hwb_vector_nat (n := 4) (fun w => if weq w x then wplus (v x) d else v w) =
  fun j => if Nat.eqb j (wordToNat x) then hwb_vector_nat (n := 4) v j + wordToNat d
           else hwb_vector_nat (n := 4) v j.
Proof.
  intros v x d H. rewrite hwb_vector_nat_update. extensionality j.
  destruct (Nat.eqb_spec j (wordToNat x)) as [E|E]; [|reflexivity].
  subst j. rewrite hwb_vector_nat_at. apply wordToNat_wplus_bounded. exact H.
Qed.

Lemma snap_tensor_set : forall (T : word 4 -> word 4 -> word WordSz) (ah al : word 4) (v : word WordSz),
  (fun mid i => if Nat.ltb mid 16 then hwb_vector_nat (n := 4)
     ((fun m => if weq m ah then (fun i0 => if weq i0 al then v else T ah i0) else T m)
        (natToWord 4 mid)) i else 0) =
  (fun m k => if andb (Nat.eqb m (wordToNat ah)) (Nat.eqb k (wordToNat al)) then wordToNat v
     else if Nat.ltb m 16 then hwb_vector_nat (n := 4) (T (natToWord 4 m)) k else 0).
Proof.
  intros T ah al v. extensionality m. extensionality k.
  destruct (Nat.eqb_spec m (wordToNat ah)) as [Em|Em].
  - subst m. rewrite word4_ltb_16, natToWord_wordToNat. cbn [andb].
    destruct (weq ah ah) as [_|N]; [|contradiction].
    rewrite hwb_vector_nat_update. reflexivity.
  - cbn [andb]. destruct (Nat.ltb m 16) eqn:Hm; [|reflexivity].
    apply Nat.ltb_lt in Hm.
    destruct (weq (natToWord 4 m) ah) as [E|_]; [|reflexivity].
    exfalso. exact (natToWord_word4_ne m ah Hm Em E).
Qed.

Lemma tensor_indices_ok_bits2 : forall x0 x1 x2 x3 : bool,
  VMStep.VMStep.tensor_indices_ok (wordToNat (bits2 x2 x3)) (wordToNat (bits2 x0 x1)) = true.
Proof. intros x0 x1 x2 x3. destruct x0, x1, x2, x3; reflexivity. Qed.

(** * Stack pointer and partition-table facts *)

Lemma wordToNat_hw_sp_idx : wordToNat hw_sp_idx = 15.
Proof. reflexivity. Qed.

Lemma kami_sp_reg_15 : kami_sp_reg = 15.
Proof. reflexivity. Qed.

Lemma hwb_vector_nat_sp : forall (v : type (Vector (Bit WordSz) RegIdxSz)),
  hwb_vector_nat v 15 = wordToNat (v hw_sp_idx).
Proof. intro v. rewrite <- wordToNat_hw_sp_idx. apply hwb_vector_nat_at. Qed.

Lemma pt_room_one_lt : forall b, hw_pt_room_one b = true -> wordToNat (hw_pt_next_id b) < 64.
Proof.
  intros b H. unfold hw_pt_room_one in H.
  destruct (wlt_dec _ _) as [L|_]; [|discriminate].
  apply wlt_lt in L. change (wordToNat (natToWord PTableNextIdSz 64)) with 64 in L. exact L.
Qed.

Lemma pt_room_one_of_lt : forall b, wordToNat (hw_pt_next_id b) < 64 -> hw_pt_room_one b = true.
Proof.
  intros b H. unfold hw_pt_room_one.
  destruct (wlt_dec _ _) as [_|L]; [reflexivity|].
  exfalso. apply L. apply lt_wlt.
  change (wordToNat (natToWord PTableNextIdSz 64)) with 64. exact H.
Qed.

Lemma wordToNat_wplus_7 : forall (x : word PTableNextIdSz) k,
  wordToNat x + k < 128 -> k < 128 ->
  wordToNat (wplus x (natToWord PTableNextIdSz k)) = wordToNat x + k.
Proof.
  intros x k H Hk. rewrite wordToNat_wplus_bounded.
  - rewrite wordToNat_natToWord_2; [reflexivity|]. exact Hk.
  - rewrite wordToNat_natToWord_2; [exact H|exact Hk].
Qed.

Lemma pt_room_two_of_le : forall b, wordToNat (hw_pt_next_id b) + 2 <= 64 -> hw_pt_room_two b = true.
Proof.
  intros b H. unfold hw_pt_room_two.
  destruct (wlt_dec _ _) as [L|_]; [|reflexivity].
  exfalso. apply wlt_lt in L.
  rewrite wordToNat_wplus_7 in L by lia.
  change (wordToNat (natToWord PTableNextIdSz 64)) with 64 in L. lia.
Qed.

Lemma region_ok_of_lt : forall b (addr : word MemAddrSz),
  wordToNat addr < wordToNat (hw_ptTable b (hw_active_module b)) ->
  hw_region_ok b addr = true.
Proof.
  intros b addr H. unfold hw_region_ok.
  destruct (wlt_dec _ _) as [_|L]; [reflexivity|].
  exfalso. apply L. apply lt_wlt. rewrite wordToNat_zext7_ext. exact H.
Qed.

Lemma wordToNat_trunc7_small : forall w : word WordSz,
  wordToNat w < 128 -> wordToNat (split1 7 25 w) = wordToNat w.
Proof. intros w H. rewrite wordToNat_trunc7. apply Nat.mod_small. exact H. Qed.

Lemma wordToNat_trunc6_small : forall w : word PTableNextIdSz,
  wordToNat w < 64 -> wordToNat (split1 6 1 w) = wordToNat w.
Proof. intros w H. rewrite wordToNat_trunc6_7. apply Nat.mod_small. exact H. Qed.

Lemma wordToNat_one5 : wordToNat (WO~0~0~0~0~1) = 1.
Proof. reflexivity. Qed.

Lemma half_le : forall n, n / 2 <= n.
Proof. intro n. apply Nat.div_le_upper_bound; lia. Qed.

Lemma wordToNat_word_half : forall w : word WordSz,
  wordToNat (wrshift w (wordToNat (WO~0~0~0~0~1))) = wordToNat w / 2.
Proof. intro w. rewrite wordToNat_one5, wordToNat_wrshift. reflexivity. Qed.
