(** RelaxationStretch: the mean length of a stretch with the flag up is the
    steady mass of the up-states over the flow into them.

    A finite chain with a steady spread pi (stationary, not necessarily
    reversible) and a reading that splits the states into up (U) and
    down (N). The flow into U is Phi = sum over x in N, y in U of
    pi x P x y. A stretch is entered at y in U with chance
    e y = (sum over x in N of pi x P x y) / Phi, the entrance spread, and
    lasts as long as the chain stays in U. Let v k be the spread of the
    stretches still running after k more steps (v 0 = e, and each step keeps
    the part that lands in U); the chance that a stretch lasts more than k
    steps is the total of v k, and the mean length is the sum of those
    chances over k.

    - With u k the steady mass that has stayed in U for k steps,
      u k = Phi * v k + u (k+1) ([rs_split]), so the chances add up to
      pi(U) minus what is left after n steps, over Phi ([rs_partial]).
    - Under Doeblin's condition the leftover shrinks geometrically
      ([rs_left_pow]), and the mean length of a stretch with the flag up is
      exactly pi(U) / Phi ([rs_mean_stretch]): mass over flow. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz.
Import ListNotations.
From Kernel Require Import FiniteSums.
Open Scope R_scope.

Section Stretch.

Variable X : Type.
Variable LX : list X.
Variable P : X -> X -> R.
Variable pi : X -> R.
Variable read : X -> bool.
Hypothesis P_nonneg : forall x y, 0 <= P x y.
Hypothesis P_rows : forall x, In x LX -> sumL LX (fun y => P x y) = 1.
Hypothesis pi_nonneg : forall x, 0 <= pi x.
Hypothesis pi_stationary : forall y, In y LX -> sumL LX (fun x => pi x * P x y) = pi y.
Variable delta : R.
Hypothesis delta_pos : 0 < delta.
Hypothesis doeblin : forall x y, In x LX -> In y LX -> delta * pi y <= P x y.

Definition rs_U (x : X) : R := if read x then 1 else 0.
Definition rs_N (x : X) : R := if read x then 0 else 1.

Definition rs_massU : R := sumL LX (fun x => pi x * rs_U x).
Definition rs_massN : R := sumL LX (fun x => pi x * rs_N x).

(** The flow from N into U. *)
Definition rs_Phi : R := sumL LX (fun y => sumL LX (fun x => pi x * rs_N x * P x y) * rs_U y).

Hypothesis Phi_pos : 0 < rs_Phi.

(** One step that keeps only what lands in U. *)
Definition rs_keep (w : X -> R) (y : X) : R := sumL LX (fun x => w x * P x y) * rs_U y.

Definition rs_entry (y : X) : R := sumL LX (fun x => pi x * rs_N x * P x y) * rs_U y / rs_Phi.

Fixpoint rs_v (k : nat) : X -> R := match k with 0%nat => rs_entry | S k' => rs_keep (rs_v k') end.
Fixpoint rs_u (k : nat) : X -> R := match k with 0%nat => fun y => pi y * rs_U y | S k' => rs_keep (rs_u k') end.

Definition rs_total (w : X -> R) : R := sumL LX w.

(** The chance that a stretch lasts more than k steps, summed for k < n. *)
Fixpoint rs_partial_sum (n : nat) : R :=
  match n with 0%nat => 0 | S n' => rs_partial_sum n' + rs_total (rs_v n') end.

Lemma rs_UN : forall x, rs_U x + rs_N x = 1.
Proof. intro x. unfold rs_U, rs_N. destruct (read x); lra. Qed.

Lemma rs_keep_lin : forall a w1 w2 y,
  rs_keep (fun x => a * w1 x + w2 x) y = a * rs_keep w1 y + rs_keep w2 y.
Proof.
  intros a w1 w2 y. unfold rs_keep.
  replace (sumL LX (fun x => (a * w1 x + w2 x) * P x y))
    with (a * sumL LX (fun x => w1 x * P x y) + sumL LX (fun x => w2 x * P x y)).
  - ring.
  - rewrite <- sumL_scale_l, <- sumL_plus. apply sumL_ext. intros. ring.
Qed.

Lemma rs_keep_ext : forall w1 w2 y, (forall x, In x LX -> w1 x = w2 x) -> rs_keep w1 y = rs_keep w2 y.
Proof. intros w1 w2 y H. unfold rs_keep. f_equal. apply sumL_ext. intros x Hx. rewrite H by exact Hx. reflexivity. Qed.

(** The steady mass in U splits into the stretches entered now and the
    mass that has stayed. *)
Lemma rs_split0 : forall y, In y LX -> rs_u 0 y = rs_Phi * rs_v 0 y + rs_u 1 y.
Proof.
  intros y Hy. simpl. unfold rs_entry, rs_keep.
  rewrite <- (pi_stationary y Hy).
  assert (E : sumL LX (fun x => pi x * P x y) =
              sumL LX (fun x => pi x * rs_N x * P x y) + sumL LX (fun x => pi x * rs_U x * P x y)).
  { rewrite <- sumL_plus. apply sumL_ext. intros x _. pose proof (rs_UN x). nra. }
  rewrite E. field. lra.
Qed.

Theorem rs_split : forall k y, In y LX -> rs_u k y = rs_Phi * rs_v k y + rs_u (S k) y.
Proof.
  induction k as [| k IH]; intros y Hy; [apply rs_split0; exact Hy |].
  change (rs_u (S k) y) with (rs_keep (rs_u k) y).
  change (rs_v (S k) y) with (rs_keep (rs_v k) y).
  change (rs_u (S (S k)) y) with (rs_keep (rs_u (S k)) y).
  rewrite (rs_keep_ext (rs_u k) (fun x => rs_Phi * rs_v k x + rs_u (S k) x) y) by (intros; apply IH; assumption).
  apply rs_keep_lin.
Qed.

(** The chances add up to the mass in U minus what is left, over the flow. *)
Theorem rs_partial : forall n, rs_Phi * rs_partial_sum n = rs_massU - rs_total (rs_u n).
Proof.
  induction n as [| n IH].
  - simpl. unfold rs_massU, rs_total. simpl. ring.
  - simpl rs_partial_sum. rewrite Rmult_plus_distr_l, IH.
    assert (E : rs_total (rs_u n) = rs_Phi * rs_total (rs_v n) + rs_total (rs_u (S n))).
    { unfold rs_total. rewrite <- sumL_scale_l, <- sumL_plus. apply sumL_ext. intros y Hy. apply rs_split. exact Hy. }
    lra.
Qed.

Lemma rs_sum_le : forall (L : list X) (f g : X -> R), (forall a, In a L -> f a <= g a) -> sumL L f <= sumL L g.
Proof.
  intros L f g H. induction L as [| a L IH]; simpl; [lra |].
  pose proof (H a (or_introl eq_refl)). assert (sumL L f <= sumL L g) by (apply IH; intros; apply H; right; assumption). lra.
Qed.

Lemma rs_u_nonneg : forall k x, 0 <= rs_u k x.
Proof.
  induction k as [| k IH]; intro x; simpl.
  - apply Rmult_le_pos; [apply pi_nonneg | unfold rs_U; destruct (read x); lra].
  - unfold rs_keep. apply Rmult_le_pos; [| unfold rs_U; destruct (read x); lra].
    apply sumL_nonneg. intros. apply Rmult_le_pos; [apply IH | apply P_nonneg].
Qed.

(** Each step leaves U with chance at least delta * pi(N), so what stays
    shrinks geometrically. *)
Theorem rs_left_pow : forall n, rs_total (rs_u n) <= (1 - delta * rs_massN) ^ n * rs_massU.
Proof.
  assert (Hrow : forall x, In x LX -> sumL LX (fun y => P x y * rs_U y) <= 1 - delta * rs_massN).
  { intros x Hx.
    assert (E : sumL LX (fun y => P x y * rs_U y) = 1 - sumL LX (fun y => P x y * rs_N y)).
    { rewrite <- (P_rows x Hx), <- sumL_minus. apply sumL_ext. intros y _. pose proof (rs_UN y). nra. }
    rewrite E. unfold rs_massN.
    assert (H : delta * sumL LX (fun y => pi y * rs_N y) <= sumL LX (fun y => P x y * rs_N y)).
    { rewrite <- sumL_scale_l. apply rs_sum_le. intros y Hy. pose proof (doeblin x y Hx Hy).
      unfold rs_N. destruct (read y); nra. }
    lra. }
  induction n as [| n IH].
  - simpl. rewrite Rmult_1_l. unfold rs_total, rs_massU. apply Req_le. reflexivity.
  - change (rs_u (S n)) with (rs_keep (rs_u n)). unfold rs_total, rs_keep.
    apply Rle_trans with (sumL LX (fun x => rs_u n x * (1 - delta * rs_massN))).
    + apply Rle_trans with (sumL LX (fun x => rs_u n x * sumL LX (fun y => P x y * rs_U y))).
      * apply Req_le.
        transitivity (sumL LX (fun y => sumL LX (fun x => rs_u n x * P x y * rs_U y))).
        { apply sumL_ext. intros y _. rewrite <- sumL_scale_r. reflexivity. }
        rewrite sumL_swap. apply sumL_ext. intros x _. rewrite <- sumL_scale_l.
        apply sumL_ext. intros. ring.
      * apply rs_sum_le. intros x Hx. apply Rmult_le_compat_l; [apply rs_u_nonneg | apply Hrow; exact Hx].
    + assert (Hd : 0 <= 1 - delta * rs_massN).
      { assert (Hcase : LX = [] \/ exists x0, In x0 LX).
        { destruct LX as [| x0 L]; [left; reflexivity | right; exists x0; left; reflexivity]. }
        destruct Hcase as [HL | [x0 Hx0]].
        - unfold rs_massN. rewrite HL. simpl. lra.
        - eapply Rle_trans; [| apply (Hrow x0 Hx0)].
          apply sumL_nonneg. intros y _. apply Rmult_le_pos; [apply P_nonneg | unfold rs_U; destruct (read y); lra]. }
      rewrite (sumL_scale_r X LX (1 - delta * rs_massN) (rs_u n)).
      change (sumL LX (rs_u n)) with (rs_total (rs_u n)).
      apply Rle_trans with ((1 - delta * rs_massN) * ((1 - delta * rs_massN) ^ n * rs_massU)).
      * rewrite Rmult_comm. apply Rmult_le_compat_l; [exact Hd | exact IH].
      * simpl. lra.
Qed.

Lemma rs_rate_nonneg : 0 <= 1 - delta * rs_massN.
Proof.
  assert (Hcase : LX = [] \/ exists x0, In x0 LX).
  { destruct LX as [| x0 L]; [left; reflexivity | right; exists x0; left; reflexivity]. }
  destruct Hcase as [HL | [x0 Hx0]].
  - unfold rs_massN. rewrite HL. simpl. lra.
  - assert (E : sumL LX (fun y => P x0 y * rs_U y) = 1 - sumL LX (fun y => P x0 y * rs_N y)).
    { rewrite <- (P_rows x0 Hx0), <- sumL_minus. apply sumL_ext. intros y _. pose proof (rs_UN y). nra. }
    assert (H : delta * rs_massN <= sumL LX (fun y => P x0 y * rs_N y)).
    { unfold rs_massN. rewrite <- sumL_scale_l. apply rs_sum_le. intros y Hy. pose proof (doeblin x0 y Hx0 Hy).
      unfold rs_N. destruct (read y); nra. }
    assert (H0 : 0 <= sumL LX (fun y => P x0 y * rs_U y)).
    { apply sumL_nonneg. intros y _. apply Rmult_le_pos; [apply P_nonneg | unfold rs_U; destruct (read y); lra]. }
    lra.
Qed.

(** The mean length of a stretch with the flag up is the mass of U over
    the flow into U. *)
Theorem rs_mean_stretch : rs_massN > 0 -> Un_cv rs_partial_sum (rs_massU / rs_Phi).
Proof.
  intros HmN eps Heps.
  assert (HmU : 0 <= rs_massU).
  { unfold rs_massU. apply sumL_nonneg. intros. apply Rmult_le_pos; [apply pi_nonneg | unfold rs_U; destruct (read x); lra]. }
  pose proof rs_rate_nonneg as Hc0.
  set (c := 1 - delta * rs_massN) in *.
  assert (Hc1 : c < 1) by (unfold c; nra).
  destruct (pow_lt_1_zero c ltac:(rewrite Rabs_right by lra; lra) (eps * rs_Phi / (rs_massU + 1))
    ltac:(apply Rdiv_lt_0_compat; [nra | lra])) as [N HN].
  exists N. intros n Hn. unfold R_dist.
  pose proof (rs_partial n) as Hp. pose proof (rs_left_pow n) as Hl. fold c in Hl.
  assert (Ht : 0 <= rs_total (rs_u n)) by (apply sumL_nonneg; intros; apply rs_u_nonneg).
  assert (E : rs_partial_sum n - rs_massU / rs_Phi = - (rs_total (rs_u n) / rs_Phi)).
  { assert (Hs : rs_partial_sum n = (rs_massU - rs_total (rs_u n)) / rs_Phi).
    { apply (Rmult_eq_reg_l rs_Phi); [| lra]. rewrite Hp. field. lra. }
    rewrite Hs. field. lra. }
  rewrite E, Rabs_Ropp, Rabs_right by (apply Rle_ge; unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  specialize (HN n Hn). rewrite Rabs_right in HN by (apply Rle_ge; apply pow_le; lra).
  apply (Rmult_lt_reg_r rs_Phi); [lra |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  apply Rle_lt_trans with (c ^ n * rs_massU); [exact Hl |].
  apply Rle_lt_trans with (c ^ n * (rs_massU + 1)); [apply Rmult_le_compat_l; [apply pow_le | ]; lra |].
  apply (Rmult_lt_reg_r (/ (rs_massU + 1))); [apply Rinv_0_lt_compat; lra |].
  rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra.
  replace (eps * rs_Phi * / (rs_massU + 1)) with (eps * rs_Phi / (rs_massU + 1)) by reflexivity. exact HN.
Qed.

End Stretch.

Print Assumptions rs_split.
Print Assumptions rs_partial.
Print Assumptions rs_mean_stretch.
