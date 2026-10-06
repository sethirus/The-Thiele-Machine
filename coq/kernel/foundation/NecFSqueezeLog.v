(** NecFSqueezeLog: the squeeze bound in logarithms.

    The book writes the squeeze bound two ways: m + k <= 2^cost * m, or
    cost >= log2 ((m + k) / m). For m >= 1 the two are the same statement
    ([nec_f_squeeze_real_iff]). The least whole cost that meets it is the
    ceiling of log2 ((m + k) / m) ([nec_f_least_cost_is_ceiling]), and that
    least cost exists for every m >= 1 and k ([nec_f_least_cost_exists]);
    NecFSqueeze shows it is attained by a machine meeting every premise.

    This file uses the real numbers, so its results rest on the standard
    library's classical axioms for the reals. *)

From Coq Require Import Arith Lia Reals Lra.
From Kernel Require Import PermanentCertificationEntropy.

Open Scope R_scope.

Lemma nec_f_ln_le_iff : forall x y, 0 < x -> 0 < y -> (ln x <= ln y <-> x <= y).
Proof.
  intros x y Hx Hy. split.
  - intro H. destruct (Rle_or_lt x y) as [Hle | Hlt]; [exact Hle |].
    pose proof (ln_increasing y x Hy Hlt). lra.
  - intro H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq].
    + left. apply ln_increasing; assumption.
    + subst. right. reflexivity.
Qed.

(** For m >= 1, the integer squeeze and the logarithmic squeeze agree. *)
Theorem nec_f_squeeze_real_iff :
  forall m k c : nat, (0 < m)%nat ->
    ((m + k <= 2 ^ c * m)%nat <-> log2 (INR (m + k) / INR m) <= INR c).
Proof.
  intros m k c Hm.
  assert (HmR : 0 < INR m) by (apply lt_0_INR; exact Hm).
  assert (HxR : 0 < INR (m + k) / INR m).
  { apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | exact HmR]. }
  assert (Hp : 0 < 2 ^ c) by (apply pow_lt; lra).
  assert (Hl2 := ln2_pos).
  assert (Hstep1 : log2 (INR (m + k) / INR m) <= INR c <->
                   ln (INR (m + k) / INR m) <= ln (2 ^ c)).
  { rewrite ln_pow by lra. unfold log2. split; intro H.
    - apply (Rmult_le_compat_r (ln 2)) in H; [| lra].
      unfold Rdiv in H. rewrite Rmult_assoc, Rinv_l in H by lra. lra.
    - apply (Rmult_le_reg_r (ln 2)); [exact Hl2 |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  rewrite Hstep1, nec_f_ln_le_iff by assumption.
  assert (Hstep2 : INR (m + k) / INR m <= 2 ^ c <-> INR (m + k) <= 2 ^ c * INR m).
  { split; intro H.
    - apply (Rmult_le_compat_r (INR m)) in H; [| lra].
      unfold Rdiv in H. rewrite Rmult_assoc, Rinv_l in H by lra. lra.
    - apply (Rmult_le_reg_r (INR m)); [exact HmR |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  rewrite Hstep2.
  assert (E : INR (2 ^ c * m) = 2 ^ c * INR m).
  { rewrite mult_INR, pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. }
  rewrite <- E. split; [apply le_INR | apply INR_le].
Qed.

(** The least whole cost meeting the squeeze is the ceiling of the
    logarithm: a cost c that meets it, while c - 1 does not, lies in
    [L, L + 1) where L = log2 ((m + k) / m). *)
Theorem nec_f_least_cost_is_ceiling :
  forall m k c : nat, (0 < m)%nat ->
    (m + k <= 2 ^ c * m)%nat ->
    (c = 0%nat \/ ~ (m + k <= 2 ^ (c - 1) * m)%nat) ->
    INR c - 1 < log2 (INR (m + k) / INR m) <= INR c.
Proof.
  intros m k c Hm Hc Hmin. split; [| apply nec_f_squeeze_real_iff; assumption].
  assert (HmR : 0 < INR m) by (apply lt_0_INR; exact Hm).
  destruct Hmin as [-> | Hnot].
  - simpl. unfold log2.
    assert (H1 : 1 <= INR (m + k) / INR m).
    { apply (Rmult_le_reg_r (INR m)); [exact HmR |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      rewrite Rmult_1_l, Rmult_1_r. apply le_INR. lia. }
    assert (H0 : 0 <= ln (INR (m + k) / INR m)).
    { rewrite <- ln_1. apply nec_f_ln_le_iff; lra. }
    assert (0 <= ln (INR (m + k) / INR m) / ln 2).
    { unfold Rdiv. apply Rmult_le_pos; [exact H0 | left; apply Rinv_0_lt_compat, ln2_pos]. }
    lra.
  - destruct c as [| c'].
    + exfalso. apply Hnot. simpl in *. lia.
    + rewrite (nec_f_squeeze_real_iff m k (S c' - 1) Hm) in Hnot.
      apply Rnot_le_lt in Hnot. replace (S c' - 1)%nat with c' in Hnot by lia.
      rewrite S_INR. lra.
Qed.

(** That least cost exists for every m >= 1 and every k. *)
Theorem nec_f_least_cost_exists :
  forall m k : nat, (0 < m)%nat ->
    exists c, (m + k <= 2 ^ c * m)%nat /\ (c = 0%nat \/ ~ (m + k <= 2 ^ (c - 1) * m)%nat).
Proof.
  intros m k Hm.
  assert (Hgen : forall n, (m + k <= 2 ^ n * m)%nat ->
            exists c, (m + k <= 2 ^ c * m)%nat /\ (c = 0%nat \/ ~ (m + k <= 2 ^ (c - 1) * m)%nat)).
  { induction n as [| n IH]; intro Hn.
    - exists 0%nat. split; [exact Hn | left; reflexivity].
    - destruct (le_dec (m + k) (2 ^ n * m)) as [Hle | Hgt].
      + exact (IH Hle).
      + exists (S n). split; [exact Hn | right]. replace (S n - 1)%nat with n by lia. exact Hgt. }
  apply (Hgen (m + k)%nat).
  pose proof (Nat.pow_gt_lin_r 2 (m + k)%nat ltac:(lia)) as Hlin. nia.
Qed.

(** One mark is one halving exactly when the squeeze is two: the logarithmic
    floor is one bit exactly when k = m, and below one bit when k < m. *)
Theorem nec_f_one_halving_iff :
  forall m k : nat, (0 < m)%nat -> (log2 (INR (m + k) / INR m) = 1 <-> k = m).
Proof.
  intros m k Hm.
  assert (HmR : 0 < INR m) by (apply lt_0_INR; exact Hm).
  assert (Hx : 0 < INR (m + k) / INR m) by (apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | exact HmR]).
  assert (Hl2 := ln2_pos). unfold log2. split; intro H.
  - assert (E : ln (INR (m + k) / INR m) = ln 2).
    { replace (ln (INR (m + k) / INR m)) with (ln (INR (m + k) / INR m) / ln 2 * ln 2) by (field; lra).
      rewrite H. ring. }
    apply ln_inv in E; [| exact Hx | lra].
    assert (E2 : INR (m + k) = 2 * INR m).
    { replace (INR (m + k)) with (INR (m + k) / INR m * INR m) by (field; lra). rewrite E. ring. }
    rewrite plus_INR in E2. assert (INR k = INR m) by lra. apply INR_eq. exact H0.
  - subst k. replace (INR (m + m) / INR m) with 2 by (rewrite plus_INR; field; lra). field. lra.
Qed.

Theorem nec_f_thinner_squeeze_below_one_bit :
  forall m k : nat, (0 < m)%nat -> (k < m)%nat -> log2 (INR (m + k) / INR m) < 1.
Proof.
  intros m k Hm Hk.
  assert (HmR : 0 < INR m) by (apply lt_0_INR; exact Hm).
  assert (Hx : 0 < INR (m + k) / INR m) by (apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | exact HmR]).
  assert (Hlt : INR (m + k) / INR m < 2).
  { apply (Rmult_lt_reg_r (INR m)); [exact HmR |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
    rewrite Rmult_1_r, plus_INR. apply lt_INR in Hk. lra. }
  pose proof (ln_increasing _ _ Hx Hlt) as Hln. pose proof ln2_pos. unfold log2.
  apply (Rmult_lt_reg_r (ln 2)); [lra |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Print Assumptions nec_f_squeeze_real_iff.
Print Assumptions nec_f_least_cost_is_ceiling.
Print Assumptions nec_f_least_cost_exists.
Print Assumptions nec_f_one_halving_iff.
Print Assumptions nec_f_thinner_squeeze_below_one_bit.
