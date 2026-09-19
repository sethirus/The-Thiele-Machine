(** Correctness of the step rule's 32-bit tree popcount.

    Each stage of [hw_popcount32] turns n-bit fields into 2n-bit fields that
    hold the sum of each adjacent pair. A mask selects alternate fields, a
    shift moves the odd fields down, and the addition is carry-free because
    every field sum fits its 2n-bit field. After five stages the single 32-bit
    field is the number of set input bits, which is [word64_popcount] of the
    input. *)
Require Import Kami.Kami Kami.Lib.NatLib.
From Coq Require Import Arith Lia NArith List Bool.
From KamiHW Require Import ThieleTypes StepFields StepWordFacts StepRefineCommon.
Require Import Kernel.VMState.
Import ListNotations.

Local Open Scope N_scope.

(** * Fields of a natural number *)

Definition fld (w k x : N) : N := (x / 2 ^ (w * k)) mod 2 ^ w.

Lemma pow2_ne0 : forall e, 2 ^ e <> 0.
Proof. intro e. apply N.pow_nonzero. discriminate. Qed.

Lemma fld_testbit : forall w k x i,
  N.testbit (fld w k x) i = (i <? w) && N.testbit x (i + w * k).
Proof.
  intros w k x i. unfold fld. destruct (N.ltb_spec i w) as [H|H].
  - rewrite N.mod_pow2_bits_low by exact H. rewrite N.div_pow2_bits. reflexivity.
  - rewrite N.mod_pow2_bits_high by exact H. reflexivity.
Qed.

Lemma fld_0 : forall w x, fld w 0 x = x mod 2 ^ w.
Proof. intros. unfold fld. rewrite N.mul_0_r, N.pow_0_r, N.div_1_r. reflexivity. Qed.

Lemma fld_succ : forall w k x, fld w (N.succ k) x = fld w k (x / 2 ^ w).
Proof.
  intros. unfold fld. rewrite N.div_div by apply pow2_ne0.
  rewrite <- N.pow_add_r. f_equal. f_equal. f_equal. lia.
Qed.

Lemma div_add_nocarry : forall w a b,
  a mod 2 ^ w + b mod 2 ^ w < 2 ^ w ->
  (a + b) / 2 ^ w = a / 2 ^ w + b / 2 ^ w.
Proof.
  intros w a b H.
  rewrite (N.div_mod a (2 ^ w)) at 1 by apply pow2_ne0.
  rewrite (N.div_mod b (2 ^ w)) at 1 by apply pow2_ne0.
  replace (2 ^ w * (a / 2 ^ w) + a mod 2 ^ w + (2 ^ w * (b / 2 ^ w) + b mod 2 ^ w))
    with ((a / 2 ^ w + b / 2 ^ w) * 2 ^ w + (a mod 2 ^ w + b mod 2 ^ w)) by ring.
  rewrite N.div_add_l by apply pow2_ne0.
  rewrite (N.div_small _ _ H). apply N.add_0_r.
Qed.

(** Carry-free addition of fields. *)
Lemma fld_add : forall w k a b,
  (forall j, j <= k -> fld w j a + fld w j b < 2 ^ w) ->
  fld w k (a + b) = fld w k a + fld w k b.
Proof.
  intros w k. induction k using N.peano_ind; intros a b H.
  - rewrite !fld_0. rewrite N.add_mod by apply pow2_ne0.
    apply N.mod_small. specialize (H 0 (N.le_refl 0)). rewrite !fld_0 in H. exact H.
  - rewrite !fld_succ. rewrite div_add_nocarry.
    + apply IHk. intros j Hj. rewrite <- !fld_succ. apply H. lia.
    + specialize (H 0 ltac:(lia)). rewrite !fld_0 in H. exact H.
Qed.

(** * Masks *)

(** [mask n] has ones in the low n bits of each 2n-bit block of 32 bits. *)
Definition mask_ok (n m : N) : Prop :=
  forall p, N.testbit m p = (p <? 32) && (p mod (2 * n) <? n).

Lemma fld_land_mask : forall n m v k,
  0 < n -> mask_ok n m -> 2 * n * (k + 1) <= 32 ->
  fld (2 * n) k (N.land v m) = fld n (2 * k) v.
Proof.
  intros n m v k Hn Hm Hk. apply N.bits_inj. intro i.
  rewrite !fld_testbit, N.land_spec, Hm.
  destruct (N.ltb_spec i (2 * n)) as [Hi|Hi]; destruct (N.ltb_spec i n) as [Hi'|Hi'];
    cbn [andb]; try reflexivity.
  - replace (i + 2 * n * k) with (i + n * (2 * k)) by lia.
    replace ((i + n * (2 * k)) mod (2 * n)) with i.
    2:{ symmetry. replace (i + n * (2 * k)) with (i + k * (2 * n)) by lia.
        rewrite N.mod_add by lia. apply N.mod_small. exact Hi. }
    destruct (N.ltb_spec (i + n * (2 * k)) 32) as [_|H]; [|lia].
    destruct (N.ltb_spec i n) as [_|H]; [|lia].
    rewrite andb_true_r. reflexivity.
  - replace ((i + 2 * n * k) mod (2 * n)) with i.
    2:{ symmetry. replace (i + 2 * n * k) with (i + k * (2 * n)) by lia.
        rewrite N.mod_add by lia. apply N.mod_small. exact Hi. }
    destruct (N.ltb_spec i n) as [H|_]; [lia|]. rewrite !andb_false_r. reflexivity.
  - lia.
Qed.

Lemma fld_land_mask_shift : forall n m v k,
  0 < n -> mask_ok n m -> 2 * n * (k + 1) <= 32 ->
  fld (2 * n) k (N.land (v / 2 ^ n) m) = fld n (2 * k + 1) v.
Proof.
  intros n m v k Hn Hm Hk. apply N.bits_inj. intro i.
  rewrite !fld_testbit, N.land_spec, Hm, N.div_pow2_bits.
  destruct (N.ltb_spec i (2 * n)) as [Hi|Hi]; destruct (N.ltb_spec i n) as [Hi'|Hi'];
    cbn [andb]; try reflexivity.
  - replace (i + 2 * n * k + n) with (i + n * (2 * k + 1)) by lia.
    replace ((i + 2 * n * k) mod (2 * n)) with i.
    2:{ symmetry. replace (i + 2 * n * k) with (i + k * (2 * n)) by lia.
        rewrite N.mod_add by lia. apply N.mod_small. exact Hi. }
    destruct (N.ltb_spec (i + 2 * n * k) 32) as [_|H]; [|lia].
    destruct (N.ltb_spec i n) as [_|H]; [|lia].
    rewrite andb_true_r. reflexivity.
  - replace ((i + 2 * n * k) mod (2 * n)) with i.
    2:{ symmetry. replace (i + 2 * n * k) with (i + k * (2 * n)) by lia.
        rewrite N.mod_add by lia. apply N.mod_small. exact Hi. }
    destruct (N.ltb_spec i n) as [H|_]; [lia|]. rewrite !andb_false_r. reflexivity.
  - lia.
Qed.

(** * One tree stage *)

Lemma stage_index_bound : forall n K k, 2 * n * K = 32 -> k < K -> 2 * n * (k + 1) <= 32.
Proof. intros n K k HK Hk. rewrite <- HK. apply N.mul_le_mono_l. lia. Qed.

Lemma stage_fields : forall n m K v,
  0 < n -> mask_ok n m -> 2 * n * K = 32 ->
  (forall j, j < 2 * K -> fld n j v <= n) ->
  forall k, k < K ->
  fld (2 * n) k (N.land v m + N.land (v / 2 ^ n) m) = fld n (2 * k) v + fld n (2 * k + 1) v.
Proof.
  intros n m K v Hn Hm HK Hb k Hk.
  rewrite fld_add.
  - rewrite (fld_land_mask n m v k Hn Hm (stage_index_bound n K k HK Hk)).
    rewrite (fld_land_mask_shift n m v k Hn Hm (stage_index_bound n K k HK Hk)). reflexivity.
  - intros j Hj. assert (Hj' : j < K) by lia.
    rewrite (fld_land_mask n m v j Hn Hm (stage_index_bound n K j HK Hj')).
    rewrite (fld_land_mask_shift n m v j Hn Hm (stage_index_bound n K j HK Hj')).
    pose proof (Hb (2 * j) ltac:(lia)). pose proof (Hb (2 * j + 1) ltac:(lia)).
    pose proof (N.pow_gt_lin_r 2 (2 * n) ltac:(lia)). lia.
Qed.

Fixpoint fsum (w : N) (K : nat) (x : N) : N :=
  match K with
  | O => 0
  | S K' => fsum w K' x + fld w (N.of_nat K') x
  end.

Lemma fsum_stage : forall n m (K : nat) v,
  0 < n -> mask_ok n m -> 2 * n * N.of_nat K = 32 ->
  (forall j, j < 2 * N.of_nat K -> fld n j v <= n) ->
  forall K', (K' <= K)%nat ->
  fsum (2 * n) K' (N.land v m + N.land (v / 2 ^ n) m) = fsum n (2 * K') v.
Proof.
  intros n m K v Hn Hm HK Hb K'. induction K' as [|K' IH]; intro HK'; [reflexivity|].
  cbn [fsum]. rewrite IH by lia.
  rewrite (stage_fields n m (N.of_nat K) v Hn Hm HK Hb) by lia.
  replace (2 * S K')%nat with (S (S (2 * K'))) by lia. cbn [fsum].
  replace (N.of_nat (S (2 * K'))) with (2 * N.of_nat K' + 1) by lia.
  replace (N.of_nat (2 * K')) with (2 * N.of_nat K') by lia.
  lia.
Qed.

Lemma stage_bounds : forall n m K v,
  0 < n -> mask_ok n m -> 2 * n * K = 32 ->
  (forall j, j < 2 * K -> fld n j v <= n) ->
  forall k, k < K -> fld (2 * n) k (N.land v m + N.land (v / 2 ^ n) m) <= 2 * n.
Proof.
  intros n m K v Hn Hm HK Hb k Hk.
  rewrite (stage_fields n m K v Hn Hm HK Hb k Hk).
  pose proof (Hb (2 * k) ltac:(lia)). pose proof (Hb (2 * k + 1) ltac:(lia)). lia.
Qed.

Lemma land_below_pow2_31 : forall v m, N.log2 m < 31 -> N.land v m < 2 ^ 31.
Proof.
  intros v m H. destruct (N.eq_dec (N.land v m) 0) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - apply N.log2_lt_pow2; [lia|]. pose proof (N.log2_land v m). lia.
Qed.

(** * The five concrete stages *)

Lemma mask_ok_of_check : forall n m,
  m < 2 ^ 32 ->
  forallb (fun q => Bool.eqb (N.testbit m (N.of_nat q)) (N.of_nat q mod (2 * n) <? n))
    (seq 0 32) = true ->
  mask_ok n m.
Proof.
  intros n m Hm Hc p. destruct (N.ltb_spec p 32) as [Hp|Hp].
  - rewrite forallb_forall in Hc. specialize (Hc (N.to_nat p)).
    rewrite in_seq, N2Nat.id in Hc. apply Bool.eqb_prop, Hc. lia.
  - cbn [andb]. rewrite <- (N.mod_small m (2 ^ 32)) by exact Hm.
    apply N.mod_pow2_bits_high. exact Hp.
Qed.

Definition m1 : N := 1431655765.
Definition m2 : N := 858993459.
Definition m3 : N := 252645135.
Definition m4 : N := 16711935.
Definition m5 : N := 65535.

Lemma mask_ok_1 : mask_ok 1 m1.
Proof. apply mask_ok_of_check; vm_compute; reflexivity. Qed.
Lemma mask_ok_2 : mask_ok 2 m2.
Proof. apply mask_ok_of_check; vm_compute; reflexivity. Qed.
Lemma mask_ok_4 : mask_ok 4 m3.
Proof. apply mask_ok_of_check; vm_compute; reflexivity. Qed.
Lemma mask_ok_8 : mask_ok 8 m4.
Proof. apply mask_ok_of_check; vm_compute; reflexivity. Qed.
Lemma mask_ok_16 : mask_ok 16 m5.
Proof. apply mask_ok_of_check; vm_compute; reflexivity. Qed.

Definition swar_stage (n m v : N) : N := N.land v m + N.land (v / 2 ^ n) m.

Lemma fld_bit : forall j x, fld 1 j x <= 1.
Proof.
  intros j x. unfold fld. rewrite N.pow_1_r.
  pose proof (N.mod_lt (x / 2 ^ (1 * j)) 2 ltac:(lia)). lia.
Qed.

Lemma fld_1_testbit : forall j x, fld 1 j x = N.b2n (N.testbit x j).
Proof.
  intros j x. rewrite N.testbit_spec'. unfold fld. rewrite N.pow_1_r, N.mul_1_l. reflexivity.
Qed.

Lemma popcount_fsum : forall (K : nat) x,
  fsum 1 K x = N.of_nat (popcount_upto K x).
Proof.
  induction K as [|K IH]; intro x; [reflexivity|].
  cbn [fsum popcount_upto]. rewrite IH, fld_1_testbit.
  destruct (N.testbit x (N.of_nat K)); cbn [N.b2n]; lia.
Qed.

Lemma stage_small : forall n m v, N.log2 m < 31 -> swar_stage n m v < 2 ^ 32.
Proof.
  intros n m v H. unfold swar_stage.
  pose proof (land_below_pow2_31 v m H). pose proof (land_below_pow2_31 (v / 2 ^ n) m H).
  change (2 ^ 32) with (2 ^ 31 + 2 ^ 31). lia.
Qed.

Lemma swar_chain : forall x,
  swar_stage 16 m5 (swar_stage 8 m4 (swar_stage 4 m3 (swar_stage 2 m2 (swar_stage 1 m1 x)))) =
  N.of_nat (popcount_upto 32 x).
Proof.
  intro x.
  set (x1 := swar_stage 1 m1 x). set (x2 := swar_stage 2 m2 x1).
  set (x3 := swar_stage 4 m3 x2). set (x4 := swar_stage 8 m4 x3).
  set (x5 := swar_stage 16 m5 x4).
  assert (B0 : forall j, j < 2 * 16 -> fld 1 j x <= 1) by (intros; apply fld_bit).
  assert (B1 : forall j, j < 2 * 8 -> fld 2 j x1 <= 2)
    by (intros j Hj; exact (stage_bounds 1 m1 16 x ltac:(lia) mask_ok_1 eq_refl B0 j ltac:(lia))).
  assert (B2 : forall j, j < 2 * 4 -> fld 4 j x2 <= 4)
    by (intros j Hj; exact (stage_bounds 2 m2 8 x1 ltac:(lia) mask_ok_2 eq_refl B1 j ltac:(lia))).
  assert (B3 : forall j, j < 2 * 2 -> fld 8 j x3 <= 8)
    by (intros j Hj; exact (stage_bounds 4 m3 4 x2 ltac:(lia) mask_ok_4 eq_refl B2 j ltac:(lia))).
  assert (B4 : forall j, j < 2 * 1 -> fld 16 j x4 <= 16)
    by (intros j Hj; exact (stage_bounds 8 m4 2 x3 ltac:(lia) mask_ok_8 eq_refl B3 j ltac:(lia))).
  assert (S5 : fsum 32 1 x5 = fsum 16 2 x4)
    by exact (fsum_stage 16 m5 1 x4 ltac:(lia) mask_ok_16 eq_refl B4 1 (le_n 1)).
  assert (S4 : fsum 16 2 x4 = fsum 8 4 x3)
    by exact (fsum_stage 8 m4 2 x3 ltac:(lia) mask_ok_8 eq_refl B3 2 (le_n 2)).
  assert (S3 : fsum 8 4 x3 = fsum 4 8 x2)
    by exact (fsum_stage 4 m3 4 x2 ltac:(lia) mask_ok_4 eq_refl B2 4 (le_n 4)).
  assert (S2 : fsum 4 8 x2 = fsum 2 16 x1)
    by exact (fsum_stage 2 m2 8 x1 ltac:(lia) mask_ok_2 eq_refl B1 8 (le_n 8)).
  assert (S1 : fsum 2 16 x1 = fsum 1 32 x)
    by exact (fsum_stage 1 m1 16 x ltac:(lia) mask_ok_1 eq_refl B0 16 (le_n 16)).
  rewrite <- popcount_fsum, <- S1, <- S2, <- S3, <- S4, <- S5.
  cbn [fsum]. rewrite N.add_0_l, fld_0.
  symmetry. apply N.mod_small. apply stage_small. vm_compute. reflexivity.
Qed.

(** * Hardware words *)

Lemma pow2_32_N' : N.of_nat (pow2 32) = 2 ^ 32.
Proof. rewrite pow2_32_N. vm_compute. reflexivity. Qed.

Lemma wordToN_wplus_small : forall (a b : word WordSz),
  wordToN a + wordToN b < 2 ^ 32 -> wordToN (wplus a b) = wordToN a + wordToN b.
Proof.
  intros a b H. rewrite !wordToN_nat in *.
  rewrite <- pow2_32_N' in H.
  rewrite wordToNat_wplus_bounded; [lia|change (pow2 WordSz) with (pow2 32); lia].
Qed.

Lemma wordToN_wrshift : forall (a : word WordSz) s,
  wordToN (wrshift a s) = wordToN a / 2 ^ N.of_nat s.
Proof.
  intros a s. rewrite !wordToN_nat, wordToNat_wrshift.
  rewrite Nat2N.inj_div, Nat2N.inj_pow. reflexivity.
Qed.

Lemma hw_stage : forall (v mw : word WordSz) (sw : word 6) n m,
  wordToN mw = m -> N.log2 m < 31 -> N.of_nat (wordToNat sw) = n ->
  wordToN (wplus (wand v mw) (wand (wrshift v (wordToNat sw)) mw)) = swar_stage n m (wordToN v).
Proof.
  intros v mw sw n m Hm Hl Hs. unfold swar_stage.
  rewrite wordToN_wplus_small.
  - rewrite !wordToN_wand, wordToN_wrshift, Hm, Hs. reflexivity.
  - rewrite !wordToN_wand, wordToN_wrshift, Hm.
    pose proof (land_below_pow2_31 (wordToN v) m Hl).
    pose proof (land_below_pow2_31 (wordToN v / 2 ^ N.of_nat (wordToNat sw)) m Hl).
    change (2 ^ 32) with (2 ^ 31 + 2 ^ 31). lia.
Qed.

Lemma popcount_upto_high : forall k x, x < 2 ^ 32 ->
  popcount_upto (32 + k) x = popcount_upto 32 x.
Proof.
  intros k x Hx. induction k as [|k IH]; [rewrite Nat.add_0_r; reflexivity|].
  replace (32 + S k)%nat with (S (32 + k)) by lia. cbn [popcount_upto]. rewrite IH.
  rewrite <- (N.mod_small x (2 ^ 32)) at 1 by exact Hx.
  rewrite N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Theorem hw_popcount32_correct : forall w : word WordSz,
  wordToNat (hw_popcount32 w) = word64_popcount (wordToNat w).
Proof.
  intro w. unfold hw_popcount32. cbv zeta.
  rewrite <- N_to_nat_wordToN.
  rewrite (hw_stage _ _ _ 16 m5) by (vm_compute; reflexivity).
  rewrite (hw_stage _ _ _ 8 m4) by (vm_compute; reflexivity).
  rewrite (hw_stage _ _ _ 4 m3) by (vm_compute; reflexivity).
  rewrite (hw_stage _ _ _ 2 m2) by (vm_compute; reflexivity).
  rewrite (hw_stage _ _ _ 1 m1) by (vm_compute; reflexivity).
  rewrite swar_chain, Nat2N.id.
  unfold word64_popcount, word64_mask. rewrite N.land_ones.
  rewrite <- wordToN_nat.
  pose proof (wordToN_bound w) as Hb.
  rewrite N.mod_small.
  - symmetry. apply (popcount_upto_high 32).
    eapply N.lt_le_trans; [exact Hb|]. vm_compute. discriminate.
  - eapply N.lt_le_trans; [exact Hb|]. vm_compute. discriminate.
Qed.
