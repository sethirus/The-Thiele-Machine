(** AxProb: probability over a fibre, and the price of collapsing it.

    A move that lands several states on one spot collapses a fibre.  What a
    prior over the states says about the lost position is its conditional
    entropy: how much is still unknown about which state the machine was in
    once it is known where it landed.

    Results (all closed, over the reals, no axiom beyond the standard ones
    the real numbers library uses; see Print Assumptions below):

      ax_fibre_gibbs        inside one landing spot of n states the loss
                            sum p ln (W / p) is at most W ln n, where W is
                            the weight of the spot (Gibbs' inequality).
      ax_loss_le            for any prior, if every landing spot receives at
                            most N states, the conditional entropy of the
                            state given its landing spot is at most the
                            total weight times ln N.
      ax_priced_loss_bits   on a finite machine whose compression is priced,
                            the conditional entropy, measured in bits, is at
                            most the cost times the total weight: the toll in
                            bits bounds the average information destroyed.
      ax_uniform_loss_exact the bound is attained: the uniform prior on a
                            fibre of size n loses exactly ln n.
      ax_priced_loss_tight  the price in bits is attained at every cost: the
                            uniform prior on a fibre of 2^c states loses
                            exactly c bits.

    Where this stops.  The price is a worst case over landing spots and the
    entropy is an average over the prior, so the bound is an inequality and
    is tight only for the uniform prior on the largest fibre.  The link
    between one unit of toll and a physical cost in heat is Landauer's
    principle, kT ln 2 per bit erased; that is a premise from physics and is
    not proved here.  What is proved is the counting statement the premise
    would be applied to. *)

From Coq Require Import List Bool Arith.PeanoNat Lia Reals Lra.
Import ListNotations.
From Kernel Require Import AxCore AxMerge AxShadow.

Open Scope R_scope.

Definition ax_rsum {A : Type} (g : A -> R) (l : list A) : R :=
  fold_right (fun x acc => g x + acc) 0 l.

Lemma ax_rsum_app_cons : forall {A : Type} (g : A -> R) x l,
  ax_rsum g (x :: l) = g x + ax_rsum g l.
Proof. reflexivity. Qed.

Lemma ax_rsum_le : forall {A : Type} (g h : A -> R) l,
  (forall x, In x l -> g x <= h x) -> ax_rsum g l <= ax_rsum h l.
Proof.
  intros A g h l. induction l as [| a l IH]; intro H; simpl.
  - lra.
  - apply Rplus_le_compat; [apply H; left; reflexivity |].
    apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma ax_rsum_ext : forall {A : Type} (g h : A -> R) l,
  (forall x, In x l -> g x = h x) -> ax_rsum g l = ax_rsum h l.
Proof.
  intros A g h l. induction l as [| a l IH]; intro H; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)). rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

Lemma ax_rsum_const : forall {A : Type} (c : R) (l : list A),
  ax_rsum (fun _ => c) l = INR (length l) * c.
Proof.
  intros A c l. induction l as [| a l IH]; simpl.
  - lra.
  - rewrite IH. destruct l; simpl; lra.
Qed.

Lemma ax_rsum_plus : forall {A : Type} (g h : A -> R) l,
  ax_rsum (fun x => g x + h x) l = ax_rsum g l + ax_rsum h l.
Proof.
  intros A g h l. induction l as [| a l IH]; simpl; [lra |]. rewrite IH. lra.
Qed.

Lemma ax_rsum_minus : forall {A : Type} (g h : A -> R) l,
  ax_rsum (fun x => g x - h x) l = ax_rsum g l - ax_rsum h l.
Proof.
  intros A g h l. induction l as [| a l IH]; simpl; [lra |]. rewrite IH. lra.
Qed.

Lemma ax_rsum_scal : forall {A : Type} (c : R) (g : A -> R) l,
  ax_rsum (fun x => c * g x) l = c * ax_rsum g l.
Proof.
  intros A c g l. induction l as [| a l IH]; simpl; [lra |]. rewrite IH. lra.
Qed.

Lemma ax_rsum_scal_r : forall {A : Type} (c : R) (g : A -> R) l,
  ax_rsum (fun x => g x * c) l = ax_rsum g l * c.
Proof.
  intros A c g l. induction l as [| a l IH]; simpl; [lra |]. rewrite IH. lra.
Qed.

Lemma ax_rsum_nonneg : forall {A : Type} (g : A -> R) l,
  (forall x, In x l -> 0 <= g x) -> 0 <= ax_rsum g l.
Proof.
  intros A g l. induction l as [| a l IH]; intro H; simpl; [lra |].
  apply Rplus_le_le_0_compat; [apply H; left; reflexivity |].
  apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma ax_rsum_ge_elt : forall {A : Type} (g : A -> R) l x,
  (forall y, In y l -> 0 <= g y) -> In x l -> g x <= ax_rsum g l.
Proof.
  intros A g l. induction l as [| a l IH]; intros x H Hx; [destruct Hx |].
  simpl. destruct Hx as [<- | Hx].
  - assert (0 <= ax_rsum g l) by (apply ax_rsum_nonneg; intros y Hy; apply H; right; exact Hy).
    lra.
  - assert (Hg : 0 <= g a) by (apply H; left; reflexivity).
    assert (g x <= ax_rsum g l) by (apply IH; [intros y Hy; apply H; right; exact Hy | exact Hx]).
    lra.
Qed.

(** ln y <= y - 1. *)
Lemma ax_ln_le_sub : forall y, 0 < y -> ln y <= y - 1.
Proof.
  intros y Hy. pose proof (exp_ineq1_le (ln y)) as H. rewrite exp_ln in H by exact Hy. lra.
Qed.

Lemma ax_ln_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [H | H].
  - left. apply ln_increasing; assumption.
  - subst. lra.
Qed.

(** One term of Gibbs' inequality. *)
Lemma ax_gibbs_term : forall w W n,
  0 <= w -> w <= W -> 1 <= n ->
  w * ln (W / w) <= W / n - w + w * ln n.
Proof.
  intros w W n Hw HwW Hn.
  assert (Hn0 : 0 < n) by lra.
  destruct (Rle_lt_or_eq_dec 0 w Hw) as [Hwpos | Hw0].
  - assert (HW : 0 < W) by lra.
    set (q := W / (n * w)).
    assert (Hq : 0 < q) by (unfold q; apply Rdiv_lt_0_compat; [exact HW | apply Rmult_lt_0_compat; assumption]).
    assert (Heq : W / w = n * q) by (unfold q; field; lra).
    rewrite Heq. rewrite ln_mult by assumption.
    pose proof (ax_ln_le_sub q Hq) as Hl.
    assert (Hwq : w * q = W / n) by (unfold q; field; lra).
    assert (w * (ln n + ln q) <= w * ln n + w * (q - 1)) by nra.
    assert (w * (q - 1) = W / n - w) by (rewrite Rmult_minus_distr_l, Hwq; lra).
    lra.
  - subst w. rewrite Rmult_0_l. rewrite Rmult_0_l.
    assert (0 <= W / n) by (unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
    lra.
Qed.

Section Loss.

Variable S : Type.
Variable p : S -> R.

Definition ax_weight (F : list S) : R := ax_rsum p F.

(** The conditional entropy of the state given a landing spot F, in nats. *)
Definition ax_fibre_loss (F : list S) : R :=
  ax_rsum (fun x => p x * ln (ax_weight F / p x)) F.

Definition ax_cond_entropy (fs : list (list S)) : R := ax_rsum ax_fibre_loss fs.
Definition ax_mass (fs : list (list S)) : R := ax_rsum ax_weight fs.

Theorem ax_fibre_gibbs : forall F,
  (forall x, In x F -> 0 <= p x) ->
  F <> [] ->
  ax_fibre_loss F <= ax_weight F * ln (INR (length F)).
Proof.
  intros F Hp Hne.
  assert (Hn : 1 <= INR (length F)).
  { destruct F as [| a F']; [contradiction |]. simpl length. rewrite S_INR.
    pose proof (pos_INR (length F')). lra. }
  unfold ax_fibre_loss.
  eapply Rle_trans.
  - apply ax_rsum_le with (h := fun x => ax_weight F / INR (length F) - p x + p x * ln (INR (length F))).
    intros x Hx. apply ax_gibbs_term; [apply Hp; exact Hx | | exact Hn].
    unfold ax_weight. apply ax_rsum_ge_elt; [exact Hp | exact Hx].
  - rewrite ax_rsum_plus, ax_rsum_minus, ax_rsum_const, ax_rsum_scal_r.
    fold (ax_weight F).
    assert (HnR : INR (length F) <> 0) by lra.
    assert (INR (length F) * (ax_weight F / INR (length F)) = ax_weight F) by (field; exact HnR).
    lra.
Qed.

Lemma ax_fibre_loss_empty : ax_fibre_loss [] = 0.
Proof. reflexivity. Qed.

Theorem ax_loss_le : forall (fs : list (list S)) (N : nat),
  (forall F, In F fs -> forall x, In x F -> 0 <= p x) ->
  (forall F, In F fs -> (length F <= N)%nat) ->
  (1 <= N)%nat ->
  ax_cond_entropy fs <= ax_mass fs * ln (INR N).
Proof.
  intros fs N Hp HN HN1.
  assert (HN1R : 1 <= INR N) by (apply (le_INR 1 N) in HN1; simpl in HN1; lra).
  assert (Hm : ax_mass fs * ln (INR N) = ax_rsum (fun F => ax_weight F * ln (INR N)) fs).
  { unfold ax_mass.
    transitivity (ln (INR N) * ax_rsum ax_weight fs); [apply Rmult_comm |].
    rewrite <- ax_rsum_scal. apply ax_rsum_ext. intros F _. apply Rmult_comm. }
  unfold ax_cond_entropy. rewrite Hm.
  apply ax_rsum_le. intros F HF.
  destruct F as [| a F'].
  - rewrite ax_fibre_loss_empty. unfold ax_weight. simpl. lra.
  - eapply Rle_trans.
    + apply ax_fibre_gibbs; [apply Hp; exact HF | discriminate].
    + assert (Hw : 0 <= ax_weight (a :: F')).
      { unfold ax_weight. apply ax_rsum_nonneg. intros x Hx. apply (Hp _ HF). exact Hx. }
      apply Rmult_le_compat_l; [exact Hw |].
      apply ax_ln_mono.
      * simpl length. rewrite S_INR. pose proof (pos_INR (length F')). lra.
      * apply le_INR. apply HN. exact HF.
Qed.

End Loss.

(** The uniform prior on a fibre of n states loses exactly ln n. *)
Theorem ax_uniform_loss_exact : forall {S : Type} (F : list S) (n : nat),
  length F = n -> (1 <= n)%nat ->
  ax_fibre_loss S (fun _ => / INR n) F = ln (INR n).
Proof.
  intros S F n Hlen Hn.
  assert (HnR : 1 <= INR n) by (apply (le_INR 1 n) in Hn; simpl in Hn; lra).
  assert (Hn0 : 0 < INR n) by lra.
  unfold ax_fibre_loss, ax_weight.
  rewrite ax_rsum_const. rewrite ax_rsum_const. rewrite Hlen.
  assert (Hw : INR n * / INR n = 1) by (field; lra).
  rewrite Hw. rewrite Rdiv_1_l, Rinv_inv.
  rewrite <- Rmult_assoc, Hw. lra.
Qed.

Lemma ax_ln_pow2 : forall c, ln (INR (2 ^ c)) = INR c * ln 2.
Proof.
  induction c as [| c IH].
  - simpl. rewrite ln_1. lra.
  - assert (Hpos : 0 < INR (2 ^ c)).
    { apply lt_0_INR. apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
    rewrite Nat.pow_succ_r', mult_INR.
    replace (INR 2) with 2 by (simpl; lra).
    rewrite ln_mult by lra. rewrite IH. rewrite S_INR. lra.
Qed.

(** Tight at every cost: the uniform prior on 2^c states loses exactly c bits. *)
Theorem ax_priced_loss_tight : forall {S : Type} (F : list S) (c : nat),
  length F = (2 ^ c)%nat ->
  ax_fibre_loss S (fun _ => / INR (2 ^ c)) F = INR c * ln 2.
Proof.
  intros S F c Hlen.
  assert (Hn : (1 <= 2 ^ c)%nat) by (apply Nat.le_succ_l; apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  rewrite (ax_uniform_loss_exact F (2 ^ c) Hlen Hn). apply ax_ln_pow2.
Qed.

(** On a finite machine with priced compression, the conditional entropy of the
    state given its landing spot, for any prior, is at most the cost in bits
    times the total weight. *)
Theorem ax_priced_loss_bits :
  forall (A : Type) (P : BPre A) (X : AxSys A P)
         (eq_dec : forall a b : ax_state A P X, {a = b} + {a <> b})
         (all : list (ax_state A P X)) (i : ax_instr A P X)
         (p : ax_state A P X -> R) (imgs : list (ax_state A P X)),
    ax_finite X all ->
    ax_compression_priced A P X eq_dec ->
    (forall x, 0 <= p x) ->
    ax_cond_entropy _ p (map (ax_step_fibre A P X eq_dec all i) imgs)
      <= ax_mass _ p (map (ax_step_fibre A P X eq_dec all i) imgs)
         * (INR (ax_cost A P X i) * ln 2).
Proof.
  intros A P X eq_dec all i p imgs Hfin Hprice Hp.
  pose proof (proj1 (ax_compression_iff_fibres A P X eq_dec all Hfin) Hprice) as Hfib.
  assert (Hle : forall F, In F (map (ax_step_fibre A P X eq_dec all i) imgs) -> (length F <= 2 ^ ax_cost A P X i)%nat).
  { intros F HF. apply in_map_iff in HF as [y [<- _]]. apply Hfib. }
  pose proof (ax_loss_le _ p (map (ax_step_fibre A P X eq_dec all i) imgs) (2 ^ ax_cost A P X i)
                (fun F _ x _ => Hp x) Hle) as H.
  assert (H1 : (1 <= 2 ^ ax_cost A P X i)%nat) by (apply Nat.le_succ_l; apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  specialize (H H1). rewrite ax_ln_pow2 in H. exact H.
Qed.

Print Assumptions ax_fibre_gibbs.
Print Assumptions ax_loss_le.
Print Assumptions ax_uniform_loss_exact.
Print Assumptions ax_priced_loss_tight.
Print Assumptions ax_priced_loss_bits.
