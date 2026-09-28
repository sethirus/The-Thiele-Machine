(** Word and natural-number facts used by the per-opcode step refinements.
    Bounds are stated with [pow2]; no statement computes a unary numeral
    of that size. *)
Require Import Kami.Kami Kami.Lib.NatLib.
From Coq Require Import Arith Lia NArith FunctionalExtensionality.
From KamiHW Require Import ThieleTypes ImplementationContract Abstraction.
Require Import Kernel.VMState.

Lemma pow2_32_N : N.of_nat (pow2 32) = 4294967296%N.
Proof. rewrite <- Npow2_nat. rewrite N2Nat.id. vm_compute. reflexivity. Qed.

Lemma word64_below_pow2_32 : forall x, x < pow2 32 -> word64 x = x.
Proof.
  intros x Hx. unfold word64, word64_mask. rewrite N.land_ones.
  rewrite N.mod_small; [apply Nat2N.id|].
  assert (HN : (N.of_nat x < N.of_nat (pow2 32))%N) by lia.
  rewrite pow2_32_N in HN.
  eapply N.lt_trans; [exact HN|]. vm_compute. reflexivity.
Qed.

Lemma word64_word32 : forall w : word WordSz, word64 (wordToNat w) = wordToNat w.
Proof. intro w. apply word64_below_pow2_32. apply wordToNat_bound. Qed.

Lemma wordToNat_word1_32 : wordToNat (natToWord WordSz 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma wordToNat_wplus_bounded : forall sz (x y : word sz),
  wordToNat x + wordToNat y < pow2 sz ->
  wordToNat (wplus x y) = wordToNat x + wordToNat y.
Proof. intros. apply wordToNat_wplus'. exact H. Qed.

Lemma wordToNat_lt_pow2_small : forall sz (w : word sz), wordToNat w < 2 ^ sz.
Proof. intros sz w. apply wordToNat_bound. Qed.

Lemma hwb_vector_nat_at : forall n w (v : type (Vector (Bit w) n)) (i : word n),
  hwb_vector_nat v (wordToNat i) = wordToNat (v i).
Proof.
  intros n w v i. unfold hwb_vector_nat.
  rewrite (proj2 (Nat.ltb_lt _ _) (wordToNat_lt_pow2_small n i)).
  rewrite natToWord_wordToNat. reflexivity.
Qed.

Lemma hwb_vector_nat_at_mod : forall n w (v : type (Vector (Bit w) n)) (i : word n),
  hwb_vector_nat v (wordToNat i mod 2 ^ n) = wordToNat (v i).
Proof.
  intros. rewrite Nat.mod_small by apply wordToNat_lt_pow2_small.
  apply hwb_vector_nat_at.
Qed.

Lemma hwb_vector_nat_update : forall n w (v : type (Vector (Bit w) n))
    (d : word n) (x : word w),
  hwb_vector_nat (n := n) (fun i => if weq i d then x else v i) =
  fun j => if Nat.eqb j (wordToNat d) then wordToNat x else hwb_vector_nat v j.
Proof.
  intros n w v d x. extensionality j. unfold hwb_vector_nat.
  destruct (Nat.ltb j (2 ^ n)) eqn:Hj.
  - apply Nat.ltb_lt in Hj.
    destruct (weq (natToWord n j) d) as [E|N].
    + subst d. rewrite wordToNat_natToWord_idempotent'.
      * rewrite Nat.eqb_refl. reflexivity.
      * exact Hj.
    + destruct (Nat.eqb j (wordToNat d)) eqn:Ejd; [|reflexivity].
      apply Nat.eqb_eq in Ejd. subst j. rewrite natToWord_wordToNat in N.
      contradiction.
  - apply Nat.ltb_ge in Hj.
    destruct (Nat.eqb j (wordToNat d)) eqn:Ejd; [|reflexivity].
    apply Nat.eqb_eq in Ejd. subst j.
    pose proof (wordToNat_lt_pow2_small n d). lia.
Qed.

(** Two snapshots are equal when every field is equal. *)
Lemma kami_snapshot_ext : forall s t,
  snap_pc s = snap_pc t ->
  snap_mu s = snap_mu t ->
  snap_err s = snap_err t ->
  snap_halted s = snap_halted t ->
  snap_regs s = snap_regs t ->
  snap_mem s = snap_mem t ->
  snap_partition_ops s = snap_partition_ops t ->
  snap_mdl_ops s = snap_mdl_ops t ->
  snap_info_gain s = snap_info_gain t ->
  snap_error_code s = snap_error_code t ->
  snap_mu_tensor s = snap_mu_tensor t ->
  snap_pt_sizes s = snap_pt_sizes t ->
  snap_pt_next_id s = snap_pt_next_id t ->
  snap_certified s = snap_certified t ->
  snap_wc_same_00 s = snap_wc_same_00 t ->
  snap_wc_diff_00 s = snap_wc_diff_00 t ->
  snap_wc_same_01 s = snap_wc_same_01 t ->
  snap_wc_diff_01 s = snap_wc_diff_01 t ->
  snap_wc_same_10 s = snap_wc_same_10 t ->
  snap_wc_diff_10 s = snap_wc_diff_10 t ->
  snap_wc_same_11 s = snap_wc_same_11 t ->
  snap_wc_diff_11 s = snap_wc_diff_11 t ->
  snap_module_tensors s = snap_module_tensors t ->
  snap_rich_state s = snap_rich_state t ->
  snap_csr_cert_addr s = snap_csr_cert_addr t ->
  snap_csr_status s = snap_csr_status t ->
  snap_csr_err s = snap_csr_err t ->
  snap_csr_heap_base s = snap_csr_heap_base t ->
  snap_logic_acc s = snap_logic_acc t ->
  snap_mstatus s = snap_mstatus t ->
  s = t.
Proof.
  intros s t H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29.
  destruct s, t.
  cbn in *. subst. reflexivity.
Qed.

Lemma wordToNat_zext8_32 : forall w : word 8,
  @wordToNat WordSz (zext w 24) = wordToNat w.
Proof. intro w. exact (wordToNat_zext w 24). Qed.
