(** NecFEntropyTight: the entropy bounds are attained, and their side
    conditions are needed.

    - The ceiling H(q) <= log2 m after a permanent flip, the even-spread
      drop >= log2 ((m + k) / m), and the heat floor k_B T ln ((m + k) / m)
      are all attained, for every m >= 1 and every k that is a positive
      multiple of m ([nec_f_entropy_bounds_attained], [nec_f_heat_floor_attained]).
      The witness is a grid with m rows and n + 1 columns; the reading is
      "column zero" and the move sends every cell to column zero of its row,
      so k = n * m.
    - The heat floor needs k_B T >= 0: with k_B T = -1, a three-state machine
      gives off exactly Landauer's minimum and still falls below the stated
      floor ([nec_f_heat_floor_needs_nonneg_kT]).
    - "A move that forgets nothing removes no bits" needs the list of states
      to be complete ([nec_f_invariance_needs_complete_list]) and without
      repeats ([nec_f_invariance_needs_nodup]).

    This file uses the real numbers and rests on the standard library's
    classical axioms for them. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Reals Lra.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.
From Kernel Require Import FiniteCertMachine.
From Kernel Require Import NecFSqueeze.

Open Scope R_scope.

Lemma nec_f_filter_prod_fst :
  forall (A B : Type) (g : A -> bool) (l : list A) (l' : list B),
    length (filter (fun x => g (fst x)) (list_prod l l')) = (length (filter g l) * length l')%nat.
Proof.
  intros A B g l l'. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite filter_app, app_length, IH.
  destruct (g a) eqn:Hg; simpl.
  - f_equal. clear IH. induction l' as [| b l' IH']; simpl; [reflexivity |].
    rewrite Hg. simpl. rewrite IH'. reflexivity.
  - assert (Hz : filter (fun x => g (fst x)) (map (fun y => (a, y)) l') = []).
    { clear IH. induction l' as [| b l' IH']; simpl; [reflexivity | rewrite Hg; exact IH']. }
    rewrite Hz. reflexivity.
Qed.

Lemma nec_f_zero_count :
  forall p, (0 < p)%nat ->
    length (filter (fun b : NecFFin p => Nat.eqb (proj1_sig b) 0) (nec_f_enum p)) = 1%nat.
Proof.
  intros p Hp.
  assert (Hgen : forall (l : list (NecFFin p)),
             length (filter (fun b => Nat.eqb (proj1_sig b) 0) l)
             = length (filter (fun k => Nat.eqb k 0) (map (@proj1_sig _ _) l))).
  { induction l as [| a l IH]; simpl; [reflexivity |].
    destruct (Nat.eqb (proj1_sig a) 0); simpl; rewrite IH; reflexivity. }
  rewrite Hgen, nec_f_enum_values.
  destruct p as [| p]; [lia |]. simpl.
  assert (Hz : forall s n, (0 < s)%nat -> filter (fun k => Nat.eqb k 0) (seq s n) = []).
  { intros s n. revert s. induction n as [| n IH]; intros s Hs; simpl; [reflexivity |].
    destruct s; [lia |]. simpl. apply IH. lia. }
  rewrite Hz by lia. reflexivity.
Qed.

Lemma nec_f_filter_none :
  forall (A : Type) (f : A -> bool) (l : list A), (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  intros A f l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(** * The grid with m rows and n + 1 columns *)

Section GridN.

Variables (m n : nat).

Definition NecFGN : Type := (NecFFin m * NecFFin (S n))%type.

Definition nec_f_gn_col0 : NecFFin (S n) := exist _ 0%nat eq_refl.

Definition nec_f_gn_eq_dec : forall a b : NecFGN, {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2].
  destruct (nec_f_fin_eq_dec m a1 b1) as [H1 | H1];
    [destruct (nec_f_fin_eq_dec (S n) a2 b2) as [H2 | H2] |].
  - left. subst. reflexivity.
  - right. intro E. inversion E. contradiction.
  - right. intro E. inversion E. contradiction.
Defined.

Definition nec_f_gn_cert (x : NecFGN) : bool := Nat.eqb (proj1_sig (snd x)) 0.
Definition nec_f_gn_step (x : NecFGN) (_ : unit) : NecFGN := (fst x, nec_f_gn_col0).
Definition nec_f_gn_all : list NecFGN := list_prod (nec_f_enum m) (nec_f_enum (S n)).

Lemma nec_f_gn_finite : finite_states nec_f_gn_all.
Proof.
  split; [apply nec_f_nodup_prod; apply nec_f_enum_nodup |].
  intros [a b]. apply in_prod; apply nec_f_enum_full.
Qed.

Lemma nec_f_gn_permanent : permanent nec_f_gn_step nec_f_gn_cert.
Proof. intros x i _. reflexivity. Qed.

Definition nec_f_gn_C : list NecFGN := certified_states _ nec_f_gn_cert nec_f_gn_all.
Definition nec_f_gn_F : list NecFGN := filter (fun x => negb (nec_f_gn_cert x)) nec_f_gn_all.

Lemma nec_f_gn_all_length : length nec_f_gn_all = (m * S n)%nat.
Proof. unfold nec_f_gn_all, NecFGN. rewrite prod_length, !nec_f_enum_length. reflexivity. Qed.

Lemma nec_f_gn_C_length : length nec_f_gn_C = m.
Proof.
  unfold nec_f_gn_C, certified_states, nec_f_gn_all.
  transitivity (length (nec_f_enum m) *
    length (filter (fun b : NecFFin (S n) => Nat.eqb (proj1_sig b) 0) (nec_f_enum (S n))))%nat.
  - apply (nec_f_filter_prod_snd _ _ (fun b : NecFFin (S n) => Nat.eqb (proj1_sig b) 0)).
  - rewrite nec_f_zero_count, nec_f_enum_length by lia. lia.
Qed.

Lemma nec_f_gn_F_length : length nec_f_gn_F = (n * m)%nat.
Proof.
  pose proof (filter_split_length NecFGN nec_f_gn_cert nec_f_gn_all) as H.
  pose proof nec_f_gn_C_length as Hc. unfold nec_f_gn_C, certified_states in Hc.
  assert (Hc' : length (filter nec_f_gn_cert nec_f_gn_all) = m) by exact Hc.
  rewrite nec_f_gn_all_length, Hc' in H. unfold nec_f_gn_F. lia.
Qed.

Lemma nec_f_gn_flip_list : flip_list nec_f_gn_step nec_f_gn_cert tt nec_f_gn_F.
Proof.
  split; [apply NoDup_filter; exact (proj1 nec_f_gn_finite) |].
  intros t Ht. unfold nec_f_gn_F in Ht. apply filter_In in Ht as [_ H].
  apply negb_true_iff in H. split; [exact H | reflexivity].
Qed.

Lemma nec_f_gn_CF_full : forall x, In x (nec_f_gn_C ++ nec_f_gn_F).
Proof.
  intro x. apply in_or_app. destruct (nec_f_gn_cert x) eqn:Hc.
  - left. apply (certified_states_spec _ _ _ nec_f_gn_finite). exact Hc.
  - right. apply filter_In. split; [apply (proj2 nec_f_gn_finite) | rewrite Hc; reflexivity].
Qed.

Lemma nec_f_gn_CF_nodup : NoDup (nec_f_gn_C ++ nec_f_gn_F).
Proof.
  apply (certified_and_flips_nodup NecFGN unit nec_f_gn_step nec_f_gn_cert nec_f_gn_all tt).
  - exact nec_f_gn_finite.
  - exact nec_f_gn_flip_list.
Qed.

Lemma nec_f_gn_count :
  forall y,
    length (filter (fun x => if nec_f_gn_eq_dec (nec_f_gn_step x tt) y then true else false) nec_f_gn_all)
    = (if nec_f_gn_cert y then S n else 0)%nat.
Proof.
  intros [y1 y2]. unfold nec_f_gn_cert. cbn [fst snd].
  destruct (Nat.eqb (proj1_sig y2) 0) eqn:Hy.
  - apply Nat.eqb_eq in Hy.
    assert (E2 : y2 = nec_f_gn_col0) by (apply nec_f_fin_eq; simpl; exact Hy). subst y2.
    rewrite (filter_ext _ (fun x : NecFGN => (fun a => if nec_f_fin_eq_dec m y1 a then true else false) (fst x))).
    + unfold nec_f_gn_all.
      transitivity (length (filter (fun a => if nec_f_fin_eq_dec m y1 a then true else false) (nec_f_enum m))
                    * length (nec_f_enum (S n)))%nat.
      * apply (nec_f_filter_prod_fst _ _ (fun a => if nec_f_fin_eq_dec m y1 a then true else false)).
      * rewrite (filter_eq_length_one (nec_f_fin_eq_dec m)); [| apply nec_f_enum_nodup | apply nec_f_enum_full].
        rewrite nec_f_enum_length. lia.
    + intros [a b]. unfold nec_f_gn_step. cbn [fst snd].
      destruct (nec_f_gn_eq_dec (a, nec_f_gn_col0) (y1, nec_f_gn_col0)) as [E | N];
        destruct (nec_f_fin_eq_dec m y1 a) as [E' | N']; try reflexivity.
      * apply (f_equal fst) in E. simpl in E. exfalso. apply N'. symmetry. exact E.
      * exfalso. apply N. rewrite E'. reflexivity.
  - transitivity (length (@nil NecFGN)); [| reflexivity]. f_equal.
    apply nec_f_filter_none. intros x _.
    unfold nec_f_gn_step. destruct (nec_f_gn_eq_dec _ _) as [E | _]; [| reflexivity].
    inversion E as [[E1 E2]]. rewrite <- E2 in Hy. simpl in Hy. discriminate.
Qed.

Notation nec_f_gn_f := (fun s => nec_f_gn_step s tt).

Lemma nec_f_gn_push :
  (0 < m)%nat ->
  forall y, push nec_f_gn_eq_dec nec_f_gn_all nec_f_gn_f
              (uniform_on nec_f_gn_eq_dec (nec_f_gn_C ++ nec_f_gn_F)) y
            = uniform_on nec_f_gn_eq_dec nec_f_gn_C y.
Proof.
  intros Hm y. unfold push.
  assert (Hu : forall x, uniform_on nec_f_gn_eq_dec (nec_f_gn_C ++ nec_f_gn_F) x = / INR (m * S n)).
  { intro x. unfold uniform_on, in_b.
    destruct (in_dec nec_f_gn_eq_dec x (nec_f_gn_C ++ nec_f_gn_F)) as [_ | Hn];
      [| exfalso; apply Hn; apply nec_f_gn_CF_full].
    rewrite app_length, nec_f_gn_C_length, nec_f_gn_F_length.
    f_equal. f_equal. lia. }
  rewrite (rsum_ext_in nec_f_gn_all
             (fun x => if nec_f_gn_eq_dec (nec_f_gn_f x) y
                       then uniform_on nec_f_gn_eq_dec (nec_f_gn_C ++ nec_f_gn_F) x else 0)
             (fun x => if (fun x => if nec_f_gn_eq_dec (nec_f_gn_f x) y then true else false) x
                       then / INR (m * S n) else 0)).
  2: { intros x _. destruct (nec_f_gn_eq_dec (nec_f_gn_f x) y); [rewrite Hu |]; reflexivity. }
  rewrite rsum_indicator, nec_f_gn_count.
  assert (HmR : 0 < INR m) by (apply lt_0_INR; exact Hm).
  assert (HnR : 0 < INR (S n)) by (apply lt_0_INR; lia).
  unfold uniform_on, in_b.
  destruct (in_dec nec_f_gn_eq_dec y nec_f_gn_C) as [HyC | HyC];
    destruct (nec_f_gn_cert y) eqn:Hc.
  - rewrite nec_f_gn_C_length, mult_INR. field. lra.
  - exfalso. apply (certified_states_spec _ _ _ nec_f_gn_finite) in HyC. congruence.
  - exfalso. apply HyC. apply (certified_states_spec _ _ _ nec_f_gn_finite). exact Hc.
  - simpl. ring.
Qed.

End GridN.

Lemma nec_f_log2_div :
  forall a b, 0 < a -> 0 < b -> log2 a - log2 b = log2 (a / b).
Proof.
  intros a b Ha Hb. unfold log2, Rdiv. rewrite ln_mult by (try apply Rinv_0_lt_compat; assumption).
  rewrite ln_Rinv by exact Hb. field. apply Rgt_not_eq, ln2_pos.
Qed.

(** The ceiling and the even-spread drop are attained, for every m >= 1 and
    every k = n * m with n >= 1. *)
Theorem nec_f_entropy_bounds_attained :
  forall m n, (0 < m)%nat -> (0 < n)%nat ->
    finite_states (nec_f_gn_all m n) /\
    permanent (nec_f_gn_step m n) (nec_f_gn_cert m n) /\
    flip_list (nec_f_gn_step m n) (nec_f_gn_cert m n) tt (nec_f_gn_F m n) /\
    (0 < length (nec_f_gn_F m n))%nat /\
    length (nec_f_gn_C m n) = m /\
    length (nec_f_gn_F m n) = (n * m)%nat /\
    entropy (nec_f_gn_all m n)
      (push (nec_f_gn_eq_dec m n) (nec_f_gn_all m n) (fun s => nec_f_gn_step m n s tt)
         (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n)))
      = log2 (INR (length (nec_f_gn_C m n))) /\
    entropy (nec_f_gn_all m n) (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n))
    - entropy (nec_f_gn_all m n)
        (push (nec_f_gn_eq_dec m n) (nec_f_gn_all m n) (fun s => nec_f_gn_step m n s tt)
           (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n)))
      = log2 (INR (length (nec_f_gn_C m n) + length (nec_f_gn_F m n)) / INR (length (nec_f_gn_C m n))).
Proof.
  intros m n Hm Hn.
  pose proof (nec_f_gn_finite m n) as Hfin.
  assert (HCnd : NoDup (nec_f_gn_C m n)) by (apply certified_states_nodup; exact Hfin).
  assert (HFlen := nec_f_gn_F_length m n). assert (HClen := nec_f_gn_C_length m n).
  assert (Hq : entropy (nec_f_gn_all m n)
      (push (nec_f_gn_eq_dec m n) (nec_f_gn_all m n) (fun s => nec_f_gn_step m n s tt)
         (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n)))
      = log2 (INR (length (nec_f_gn_C m n)))).
  { unfold entropy.
    rewrite (rsum_ext_in _ _ (fun a => surprisal_term (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n) a)))
      by (intros a _; rewrite (nec_f_gn_push m n Hm a); reflexivity).
    apply (uniform_on_entropy (nec_f_gn_eq_dec m n)); [exact (proj1 Hfin) | exact HCnd | | lia].
    intros a _. apply (proj2 Hfin). }
  assert (Hp : entropy (nec_f_gn_all m n) (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n))
               = log2 (INR (length (nec_f_gn_C m n ++ nec_f_gn_F m n)))).
  { apply uniform_on_entropy; [exact (proj1 Hfin) | apply nec_f_gn_CF_nodup | | ].
    - intros a _. apply (proj2 Hfin).
    - rewrite app_length. lia. }
  split; [exact Hfin | split; [apply nec_f_gn_permanent | split; [apply nec_f_gn_flip_list |]]].
  split; [lia | split; [exact HClen | split; [exact HFlen | split; [exact Hq |]]]].
  rewrite Hp, Hq, app_length. apply nec_f_log2_div.
  - apply lt_0_INR. lia.
  - apply lt_0_INR. lia.
Qed.

(** The heat floor is attained: a reset that gives off exactly Landauer's
    minimum gives off exactly k_B T ln ((m + k) / m). *)
Theorem nec_f_heat_floor_attained :
  forall m n kT, (0 < m)%nat -> (0 < n)%nat ->
    let dH := entropy (nec_f_gn_all m n) (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n))
              - entropy (nec_f_gn_all m n)
                  (push (nec_f_gn_eq_dec m n) (nec_f_gn_all m n) (fun s => nec_f_gn_step m n s tt)
                     (uniform_on (nec_f_gn_eq_dec m n) (nec_f_gn_C m n ++ nec_f_gn_F m n))) in
    landauer_heat kT (kT * ln 2 * dH) dH /\
    kT * ln 2 * dH = kT * ln (INR (length (nec_f_gn_C m n) + length (nec_f_gn_F m n))
                               / INR (length (nec_f_gn_C m n))).
Proof.
  intros m n kT Hm Hn dH.
  split; [unfold landauer_heat; right; reflexivity |].
  destruct (nec_f_entropy_bounds_attained m n Hm Hn) as [_ [_ [_ [_ [_ [_ [_ Hd]]]]]]].
  unfold dH. rewrite Hd. unfold log2. field. apply Rgt_not_eq, ln2_pos.
Qed.

(** * The heat floor needs k_B T >= 0 *)

Inductive NecFThree := NecFY1 | NecFY2 | NecFS0.

Definition nec_f_three_eq_dec : forall a b : NecFThree, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition nec_f_three_cert (x : NecFThree) : bool := match x with NecFS0 => false | _ => true end.
Definition nec_f_three_step (_ : NecFThree) (_ : unit) : NecFThree := NecFY1.
Definition nec_f_three_all : list NecFThree := [NecFY1; NecFY2; NecFS0].

Lemma nec_f_three_finite : finite_states nec_f_three_all.
Proof. split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto]. Qed.

Lemma nec_f_three_C : certified_states _ nec_f_three_cert nec_f_three_all = [NecFY1; NecFY2].
Proof. reflexivity. Qed.

Definition nec_f_three_p : NecFThree -> R :=
  uniform_on nec_f_three_eq_dec ([NecFY1; NecFY2] ++ [NecFS0]).

Lemma nec_f_three_push :
  forall y, push nec_f_three_eq_dec nec_f_three_all (fun s => nec_f_three_step s tt) nec_f_three_p y
            = point_mass nec_f_three_eq_dec NecFY1 y.
Proof.
  intro y. unfold push, point_mass, nec_f_three_step.
  destruct (nec_f_three_eq_dec NecFY1 y) as [E | N].
  - destruct (uniform_on_distribution nec_f_three_eq_dec nec_f_three_all ([NecFY1; NecFY2] ++ [NecFS0])
                (proj1 nec_f_three_finite)) as [_ Hs].
    + repeat constructor; simpl; intuition discriminate.
    + intros a _. apply (proj2 nec_f_three_finite).
    + simpl. lia.
    + exact Hs.
  - apply rsum_zero. intros a _. reflexivity.
Qed.

Lemma nec_f_three_entropy_q :
  entropy nec_f_three_all (push nec_f_three_eq_dec nec_f_three_all (fun s => nec_f_three_step s tt) nec_f_three_p) = 0.
Proof.
  unfold entropy.
  rewrite (rsum_ext_in _ _ (fun a => surprisal_term (point_mass nec_f_three_eq_dec NecFY1 a)))
    by (intros a _; rewrite nec_f_three_push; reflexivity).
  unfold nec_f_three_all, rsum, point_mass, surprisal_term. simpl.
  destruct (Rlt_dec 0 1) as [_ | C]; [| lra].
  destruct (Rlt_dec 0 0) as [C | _]; [lra |].
  unfold log2. rewrite ln_1. field. apply Rgt_not_eq, ln2_pos.
Qed.

Lemma nec_f_three_entropy_p : entropy nec_f_three_all nec_f_three_p = log2 3.
Proof.
  unfold nec_f_three_p. rewrite (uniform_on_entropy nec_f_three_eq_dec).
  - simpl. f_equal. simpl. lra.
  - exact (proj1 nec_f_three_finite).
  - repeat constructor; simpl; intuition discriminate.
  - intros a _. apply (proj2 nec_f_three_finite).
  - simpl. lia.
Qed.

(** With k_B T = -1 the reset gives off exactly Landauer's minimum,
    -ln 3, and that is below the stated floor -ln (3 / 2). *)
Theorem nec_f_heat_floor_needs_nonneg_kT :
  let C := certified_states _ nec_f_three_cert nec_f_three_all in
  let F := [NecFS0] in
  let dH := entropy nec_f_three_all nec_f_three_p
            - entropy nec_f_three_all (push nec_f_three_eq_dec nec_f_three_all
                                         (fun s => nec_f_three_step s tt) nec_f_three_p) in
  finite_states nec_f_three_all /\
  permanent nec_f_three_step nec_f_three_cert /\
  flip_list nec_f_three_step nec_f_three_cert tt F /\
  nec_f_three_p = uniform_on nec_f_three_eq_dec (C ++ F) /\
  landauer_heat (-1) ((-1) * ln 2 * dH) dH /\
  ~ ((-1) * ln 2 * dH >= (-1) * ln (INR (length C + length F) / INR (length C))).
Proof.
  intros C F dH.
  split; [exact nec_f_three_finite |].
  split; [intros x i _; reflexivity |].
  split; [split; [repeat constructor; intros [] | intros t [<- | []]; split; reflexivity] |].
  split; [reflexivity |].
  split; [unfold landauer_heat; right; reflexivity |].
  unfold dH. rewrite nec_f_three_entropy_p, nec_f_three_entropy_q.
  unfold C. rewrite nec_f_three_C. simpl length. unfold F. simpl length.
  replace (INR (2 + 1) / INR 2) with (3 / 2) by (simpl; field).
  unfold log2.
  replace ((-1) * ln 2 * (ln 3 / ln 2 - 0)) with (- ln 3) by (field; apply Rgt_not_eq, ln2_pos).
  assert (Hl : ln (3 / 2) < ln 3) by (apply ln_increasing; lra).
  lra.
Qed.

(** * "A move that forgets nothing removes no bits" needs a complete list
    without repeats *)

Lemma nec_f_surprisal_half : surprisal_term (/ 2) = / 2.
Proof.
  unfold surprisal_term. destruct (Rlt_dec 0 (/ 2)) as [_ | C]; [| lra].
  unfold log2. rewrite ln_Rinv by lra. field. apply Rgt_not_eq, ln2_pos.
Qed.

Lemma nec_f_surprisal_zero : surprisal_term 0 = 0.
Proof. unfold surprisal_term. destruct (Rlt_dec 0 0); [lra | reflexivity]. Qed.

Lemma nec_f_surprisal_one : surprisal_term 1 = 0.
Proof.
  unfold surprisal_term. destruct (Rlt_dec 0 1) as [_ | C]; [| lra].
  unfold log2. rewrite ln_1. field. apply Rgt_not_eq, ln2_pos.
Qed.

Definition nec_f_half_true (b : bool) : R := if b then / 2 else 0.

(** An incomplete list: only true is listed, and negation is injective;
    the listed entropy goes from 1/2 to 0. *)
Theorem nec_f_invariance_needs_complete_list :
  NoDup [true] /\ (forall x y, negb x = negb y -> x = y) /\
  entropy [true] (push bool_dec [true] negb nec_f_half_true) <> entropy [true] nec_f_half_true.
Proof.
  split; [repeat constructor; intros [] |].
  split; [intros [] [] H; simpl in H; congruence |].
  unfold entropy, push, rsum. simpl.
  destruct (bool_dec false true) as [E | _]; [discriminate |].
  rewrite nec_f_surprisal_half. replace (0 + 0) with 0 by ring.
  rewrite nec_f_surprisal_zero. lra.
Qed.

(** A complete list with a repeat: the identity, which forgets nothing,
    takes the listed entropy from 1 to 0. *)
Theorem nec_f_invariance_needs_nodup :
  (forall a : bool, In a [true; true; false]) /\
  entropy [true; true; false] (push bool_dec [true; true; false] (fun b => b) nec_f_half_true)
    <> entropy [true; true; false] nec_f_half_true.
Proof.
  split; [intros []; simpl; tauto |].
  unfold entropy, push, rsum. simpl.
  destruct (bool_dec true true) as [_ | C]; [| congruence].
  destruct (bool_dec false true) as [E | _]; [discriminate |].
  destruct (bool_dec true false) as [E | _]; [discriminate |].
  destruct (bool_dec false false) as [_ | C]; [| congruence].
  replace (/ 2 + (/ 2 + (0 + 0))) with 1 by field.
  replace (0 + (0 + (0 + 0))) with 0 by ring.
  rewrite nec_f_surprisal_one, nec_f_surprisal_half, nec_f_surprisal_zero. lra.
Qed.

(** * The ceiling needs permanence *)

(** Negation on one bit: one yes-state, one flipped no-state, the even
    spread on both. Negation forgets nothing, so the entropy after the move
    is still one bit, above log2 1 = 0. *)
Theorem nec_f_ceiling_needs_permanent :
  let C := certified_states _ (fun b : bool => b) [false; true] in
  let p := uniform_on bool_dec (C ++ [false]) in
  finite_states [false; true] /\
  flip_list flip_step (fun b : bool => b) tt [false] /\
  distribution [false; true] p /\
  ~ permanent flip_step (fun b : bool => b) /\
  ~ (entropy [false; true] (push bool_dec [false; true] (fun s => flip_step s tt) p)
       <= log2 (INR (length C))).
Proof.
  intros C p.
  assert (Hfin : finite_states [false; true]).
  { split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto]. }
  assert (HC : C = [true]) by reflexivity.
  assert (Hd : distribution [false; true] p).
  { unfold p. rewrite HC. apply uniform_on_distribution; [exact (proj1 Hfin) | | intros a _; apply (proj2 Hfin) | simpl; lia].
    repeat constructor; simpl; intuition discriminate. }
  split; [exact Hfin |].
  split; [split; [repeat constructor; intros [] | intros t [<- | []]; split; reflexivity] |].
  split; [exact Hd |].
  split; [intro H; specialize (H true tt eq_refl); discriminate |].
  rewrite step_entropy_invariant_if_injective.
  - unfold p. rewrite HC. rewrite (uniform_on_entropy bool_dec).
    + simpl. unfold log2. rewrite ln_1. replace (1 + 1) with 2 by ring.
      assert (Hl := ln2_pos). replace (ln 2 / ln 2) with 1 by (field; lra).
      replace (0 / ln 2) with 0 by (field; lra). lra.
    + exact (proj1 Hfin).
    + repeat constructor; simpl; intuition discriminate.
    + intros a _. apply (proj2 Hfin).
    + simpl. lia.
  - exact (proj1 Hfin).
  - exact (proj2 Hfin).
  - intros a b E. destruct a, b; simpl in E; congruence.
Qed.

Print Assumptions nec_f_ceiling_needs_permanent.

Print Assumptions nec_f_entropy_bounds_attained.
Print Assumptions nec_f_heat_floor_attained.
Print Assumptions nec_f_heat_floor_needs_nonneg_kT.
Print Assumptions nec_f_invariance_needs_complete_list.
Print Assumptions nec_f_invariance_needs_nodup.
