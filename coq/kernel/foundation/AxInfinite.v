(** AxInfinite: infinite fibres under a measure.

    AxProb proves the entropy and price relation on a finite machine.  Here
    the fibre may be infinite.  The states may be a countable set of any
    size, the prior may be any weighting of them by non-negative numbers (a
    probability, a finite measure, or the counting measure, which is
    sigma-finite and has infinite total mass), and no finiteness of the
    machine is assumed.  Only finite sums are ever taken; an infinite sum is
    always the limit of its finite partial sums, which are monotone.

    Results (all closed, over the reals with the standard axioms only):

      ax_priced_spots,          the halving price is, on a machine of any
      ax_spots_priced           size, exactly the bound "no landing spot
                                receives more than 2^cost states".
      ax_inf_loss_bits          for every prior, however large its entropy,
                                and every finite family of landing spots of
                                a priced move, the conditional entropy of
                                the state given its landing spot is at most
                                the cost in bits times the weight of the
                                family.
      ax_inf_loss_series        for a sequence of landing spots the partial
                                losses are monotone and bounded by the cost in
                                bits times the partial weights, so with finite
                                total weight the series converges and its sum
                                is at most the cost in bits times the weight.
      ax_chain_rule             the entropy of the states in a family of
                                spots is the entropy of the landing spots
                                plus the conditional entropy: the loss is a
                                difference of entropies.
      ax_gibbs_code             inside one landing spot, finitely or
                                infinitely large, the loss is at most the
                                expected length of any prefix code (lengths
                                with Kraft sum at most 1) times ln 2, plus
                                the weight left uncounted.  A spot of n
                                states with the uniform code gives the
                                finite Gibbs bound back.
      ax_collapse_unpriceable   a landing spot with infinitely many states
                                is not priced at any finite cost.
      ax_geometric_loss         on that spot the geometric prior has finite
                                loss, 2 ln 2: a toll of 2 bits covers the
                                average information destroyed.
      ax_block_loss_unbounded   a probability on the same spot with
                                infinite loss: no finite toll covers the
                                average information destroyed; every code
                                for it has unbounded expected length.
      ax_infinite_entropy_priced_ok  the priced bound still holds for that
                                prior once the collapse is finite-to-one.

    Where this stops.  The loss is an average over a prior, the price a
    worst case over the states of a spot, so for an infinite spot the two
    separate: the counting price is infinite, the measured price is finite
    for some priors and infinite for others.  Landauer's principle, kT ln 2
    of heat per bit destroyed, is a premise from physics.  It is written
    below as the named definition ax_landauer_minimum and only used as a
    premise; nothing in this file proves it. *)

From Coq Require Import List Bool Arith.PeanoNat Lia Reals Lra.
Import ListNotations.
From Kernel Require Import AxCore AxMerge AxShadow AxProb.
Require Minimal.EntitlementSmall.

Close Scope R_scope.

(** * 1. The halving price on a machine of any size *)

Section Spots.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.
Variable eq_dec : forall a b : ax_state A P X, {a = b} + {a <> b}.

Local Notation S := (ax_state A P X).

(** No landing spot of the move i receives more than 2^cost states. *)
Definition ax_spots_bounded : Prop :=
  forall i y (D : list S), NoDup D ->
    (forall x, In x D -> ax_step A P X x i = y) ->
    (length D <= 2 ^ ax_cost A P X i)%nat.

Theorem ax_priced_spots :
  ax_compression_priced A P X eq_dec -> ax_spots_bounded.
Proof.
  intros Hprice i y D Hnd Hy.
  pose proof (Hprice i D Hnd) as H.
  assert (Himg : ax_image_size A P X eq_dec i D <= 1).
  { unfold ax_image_size.
    change 1 with (length [y]).
    apply NoDup_incl_length; [apply NoDup_nodup |].
    intros z Hz. apply nodup_In in Hz. apply in_map_iff in Hz as [x [<- Hx]].
    rewrite (Hy x Hx). left. reflexivity. }
  assert (Hm : 2 ^ ax_cost A P X i * ax_image_size A P X eq_dec i D
                 <= 2 ^ ax_cost A P X i * 1)
    by (apply Nat.mul_le_mono_l; exact Himg).
  lia.
Qed.

Theorem ax_spots_priced :
  ax_spots_bounded -> ax_compression_priced A P X eq_dec.
Proof.
  intros Hb i D Hnd. unfold ax_image_size.
  set (imgs := nodup eq_dec (map (fun t => ax_step A P X t i) D)).
  apply (Minimal.EntitlementSmall.ent_fibres_count (ax_eqb A P X eq_dec)
           (ax_eqb_spec A P X eq_dec)
           (fun x => ax_step A P X x i) (2 ^ ax_cost A P X i) imgs D).
  - intros x Hx. unfold imgs. apply nodup_In. apply (in_map (fun t => ax_step A P X t i)). exact Hx.
  - intros x Hx.
    apply (Hb i (ax_step A P X x i)
             (filter (fun y => ax_eqb A P X eq_dec (ax_step A P X y i) (ax_step A P X x i)) D)).
    + apply NoDup_filter. exact Hnd.
    + intros z Hz. apply filter_In in Hz as [_ Hz].
      apply (ax_eqb_spec A P X eq_dec) in Hz. exact Hz.
Qed.

End Spots.

Open Scope R_scope.

(** * 2. The loss bound for every prior and every finite family of spots *)

Section Loss.

Variable S : Type.
Variable p : S -> R.

Lemma ax_fibre_loss_nonneg : forall F,
  (forall x, In x F -> 0 <= p x) -> 0 <= ax_fibre_loss S p F.
Proof.
  intros F Hp. unfold ax_fibre_loss. apply ax_rsum_nonneg.
  intros x Hx.
  pose proof (Hp x Hx) as Hpx.
  destruct (Rle_lt_or_eq_dec 0 (p x) Hpx) as [Hpos | Hz].
  - apply Rmult_le_pos; [exact Hpx |].
    assert (Hw : p x <= ax_weight S p F) by (unfold ax_weight; apply ax_rsum_ge_elt; [exact Hp | exact Hx]).
    rewrite <- ln_1. apply ax_ln_mono.
    + lra.
    + unfold Rdiv. rewrite <- (Rinv_r (p x)) by lra.
      apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hpos | exact Hw].
  - rewrite <- Hz. rewrite Rmult_0_l. lra.
Qed.

(** The loss of one spot as a difference: weight times ln weight minus the
    sum of p ln p. *)
Lemma ax_fibre_loss_split : forall F,
  (forall x, In x F -> 0 <= p x) ->
  ax_fibre_loss S p F =
    ax_weight S p F * ln (ax_weight S p F) - ax_rsum (fun x => p x * ln (p x)) F.
Proof.
  intros F Hp. unfold ax_fibre_loss.
  assert (Hterm : forall x, In x F ->
            p x * ln (ax_weight S p F / p x)
            = p x * ln (ax_weight S p F) - p x * ln (p x)).
  { intros x Hx. pose proof (Hp x Hx) as Hpx.
    destruct (Rle_lt_or_eq_dec 0 (p x) Hpx) as [Hpos | Hz].
    - assert (Hw : p x <= ax_weight S p F) by (unfold ax_weight; apply ax_rsum_ge_elt; [exact Hp | exact Hx]).
      assert (HW : 0 < ax_weight S p F) by lra.
      assert (Hd : ln (ax_weight S p F / p x) = ln (ax_weight S p F) - ln (p x)).
      { unfold Rdiv. rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
        rewrite ln_Rinv by lra. lra. }
      rewrite Hd. lra.
    - rewrite <- Hz. lra. }
  rewrite (ax_rsum_ext _ _ F Hterm).
  rewrite ax_rsum_minus. rewrite ax_rsum_scal_r.
  unfold ax_weight. reflexivity.
Qed.

End Loss.

Section PricedLoss.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.
Variable eq_dec : forall a b : ax_state A P X, {a = b} + {a <> b}.

Local Notation S := (ax_state A P X).

(** A listing of the states that land on each of finitely many spots. *)
Definition ax_lists_spots (i : ax_instr A P X) (ys : list S) (pre : S -> list S) : Prop :=
  forall y, In y ys -> NoDup (pre y) /\
    forall x, In x (pre y) <-> ax_step A P X x i = y.

(** Priced compression, any machine, any prior (a non-negative weight on
    every state, possibly of infinite entropy), any finite family of spots:
    the conditional entropy in bits is at most the cost times the weight. *)
Theorem ax_inf_loss_bits :
  ax_compression_priced A P X eq_dec ->
  forall (i : ax_instr A P X) (p : S -> R) (ys : list S) (pre : S -> list S),
    (forall x, 0 <= p x) ->
    ax_lists_spots i ys pre ->
    ax_cond_entropy S p (map pre ys)
      <= ax_mass S p (map pre ys) * (INR (ax_cost A P X i) * ln 2).
Proof.
  intros Hprice i p ys pre Hp Hl.
  pose proof (ax_priced_spots A P X eq_dec Hprice) as Hb.
  assert (Hle : forall F, In F (map pre ys) -> (length F <= 2 ^ ax_cost A P X i)%nat).
  { intros F HF. apply in_map_iff in HF as [y [<- Hy]].
    destruct (Hl y Hy) as [Hnd Hiff].
    apply (Hb i y (pre y) Hnd). intros x Hx. apply (proj1 (Hiff x)). exact Hx. }
  pose proof (ax_loss_le S p (map pre ys) (2 ^ ax_cost A P X i)
                (fun F _ x _ => Hp x) Hle) as H.
  assert (H1 : (1 <= 2 ^ ax_cost A P X i)%nat)
    by (apply Nat.le_succ_l; apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
  specialize (H H1). rewrite ax_ln_pow2 in H. exact H.
Qed.

End PricedLoss.

(** * 3. A sequence of spots: monotone partial losses, a convergent series *)

Section Series.

Variable St : Type.
Variable p : St -> R.
Variable spot : nat -> list St.
Hypothesis p_nonneg : forall x, 0 <= p x.

Definition ax_loss_n (n : nat) : R := ax_cond_entropy St p (map spot (seq 0 n)).
Definition ax_mass_n (n : nat) : R := ax_mass St p (map spot (seq 0 n)).

Lemma ax_loss_n_succ : forall n, ax_loss_n (S n) = ax_loss_n n + ax_fibre_loss St p (spot n).
Proof.
  intro n. unfold ax_loss_n, ax_cond_entropy. rewrite seq_S, map_app.
  simpl. clear. induction (map spot (seq 0 n)) as [| a l IH]; simpl; lra.
Qed.

Lemma ax_mass_n_succ : forall n, ax_mass_n (S n) = ax_mass_n n + ax_weight St p (spot n).
Proof.
  intro n. unfold ax_mass_n, ax_mass. rewrite seq_S, map_app.
  simpl. clear. induction (map spot (seq 0 n)) as [| a l IH]; simpl; lra.
Qed.

Lemma ax_loss_n_growing : Un_growing ax_loss_n.
Proof.
  intro n. rewrite ax_loss_n_succ.
  pose proof (ax_fibre_loss_nonneg St p (spot n) (fun x _ => p_nonneg x)). lra.
Qed.

(** If every spot receives at most N states, the partial losses are bounded by
    ln N times the partial weights. *)
Lemma ax_loss_n_le : forall N, (1 <= N)%nat ->
  (forall j, (length (spot j) <= N)%nat) ->
  forall n, ax_loss_n n <= ax_mass_n n * ln (INR N).
Proof.
  intros N HN Hs n. unfold ax_loss_n, ax_mass_n.
  apply (ax_loss_le St p (map spot (seq 0 n)) N (fun F _ x _ => p_nonneg x)); [| exact HN].
  intros F HF. apply in_map_iff in HF as [j [<- _]]. apply Hs.
Qed.

(** With finite total weight M the series of losses converges, and its sum is
    at most ln N times M. *)
Theorem ax_inf_loss_series : forall N M, (1 <= N)%nat ->
  (forall j, (length (spot j) <= N)%nat) ->
  (forall n, ax_mass_n n <= M) ->
  exists L, Un_cv ax_loss_n L /\ L <= M * ln (INR N).
Proof.
  intros N M HN Hs HM.
  assert (HlnN : 0 <= ln (INR N)).
  { rewrite <- ln_1. apply ax_ln_mono; [lra |]. apply (le_INR 1 N) in HN. simpl in HN. lra. }
  assert (Hub : has_ub ax_loss_n).
  { exists (M * ln (INR N)). intros y [n ->]. eapply Rle_trans; [apply (ax_loss_n_le N HN Hs n) |].
    apply Rmult_le_compat_r; [exact HlnN | apply HM]. }
  destruct (growing_cv ax_loss_n ax_loss_n_growing Hub) as [L HL].
  exists L. split; [exact HL |].
  apply Rnot_lt_le. intro Hlt.
  destruct (HL (L - M * ln (INR N))) as [n0 Hn0]; [lra |].
  pose proof (Hn0 n0 (le_n n0)) as Hd. unfold R_dist in Hd.
  pose proof (ax_loss_n_le N HN Hs n0) as Hb.
  assert (Hm : ax_mass_n n0 * ln (INR N) <= M * ln (INR N))
    by (apply Rmult_le_compat_r; [exact HlnN | apply HM]).
  rewrite Rabs_left1 in Hd by (pose proof (growing_cv ax_loss_n ax_loss_n_growing Hub); lra).
  lra.
Qed.

End Series.

(** * 4. The loss is a difference of entropies *)

Section Chain.

Variable St : Type.
Variable p : St -> R.

Theorem ax_chain_rule : forall fs : list (list St),
  (forall F, In F fs -> forall x, In x F -> 0 <= p x) ->
  ax_cond_entropy St p fs =
    ax_rsum (fun F => ax_weight St p F * ln (ax_weight St p F)) fs
    - ax_rsum (fun F => ax_rsum (fun x => p x * ln (p x)) F) fs.
Proof.
  intros fs Hp. unfold ax_cond_entropy.
  rewrite <- ax_rsum_minus.
  apply ax_rsum_ext. intros F HF. apply ax_fibre_loss_split. exact (Hp F HF).
Qed.

(** The entropy of the states of a family of spots, the entropy of the spots,
    and the entropy still unknown once the spot is known. *)
Definition ax_ent_states (fs : list (list St)) : R :=
  - ax_rsum (fun F => ax_rsum (fun x => p x * ln (p x)) F) fs.
Definition ax_ent_spots (fs : list (list St)) : R :=
  - ax_rsum (fun F => ax_weight St p F * ln (ax_weight St p F)) fs.

Theorem ax_entropy_split : forall fs : list (list St),
  (forall F, In F fs -> forall x, In x F -> 0 <= p x) ->
  ax_ent_states fs = ax_ent_spots fs + ax_cond_entropy St p fs.
Proof.
  intros fs Hp. unfold ax_ent_states, ax_ent_spots.
  rewrite (ax_chain_rule fs Hp). lra.
Qed.

End Chain.

Section Survive.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.
Variable eq_dec : forall a b : ax_state A P X, {a = b} + {a <> b}.

Local Notation S := (ax_state A P X).

(** A priced move cannot turn unbounded entropy into bounded entropy: the
    entropy of the states of any finite family of its landing spots exceeds
    the entropy of the spots by at most cost-in-bits times the weight.  So the
    entropy of the spots is unbounded whenever that of the states is, for
    any prior with finite total weight. *)
Theorem ax_infinite_entropy_survives :
  ax_compression_priced A P X eq_dec ->
  forall (i : ax_instr A P X) (p : S -> R) (ys : list S) (pre : S -> list S),
    (forall x, 0 <= p x) ->
    ax_lists_spots A P X i ys pre ->
    ax_ent_states S p (map pre ys)
      <= ax_ent_spots S p (map pre ys)
         + ax_mass S p (map pre ys) * (INR (ax_cost A P X i) * ln 2).
Proof.
  intros Hprice i p ys pre Hp Hl.
  assert (Hp' : forall F, In F (map pre ys) -> forall x, In x F -> 0 <= p x)
    by (intros F _ x _; apply Hp).
  rewrite (ax_entropy_split S p (map pre ys) Hp').
  pose proof (ax_inf_loss_bits A P X eq_dec Hprice i p ys pre Hp Hl) as H.
  lra.
Qed.

End Survive.

(** * 5. Gibbs for an infinite spot: the loss against a prefix code *)

(** One term.  For a code length l the number r = 2^(-l) is the weight the
    code gives the state; the term is the Gibbs term against r. *)
Lemma ax_code_term : forall w W r,
  0 <= w -> w <= W -> 0 < r ->
  w * ln (W / w) <= W * r - w + w * ln (/ r).
Proof.
  intros w W r Hw HwW Hr.
  destruct (Rle_lt_or_eq_dec 0 w Hw) as [Hpos | Hz].
  - assert (HW : 0 < W) by lra.
    set (q := W * r / w).
    assert (Hq : 0 < q) by (unfold q; apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; assumption | exact Hpos]).
    assert (Heq : W / w = q * / r) by (unfold q; field; lra).
    rewrite Heq. rewrite ln_mult by (try exact Hq; apply Rinv_0_lt_compat; exact Hr).
    pose proof (ax_ln_le_sub q Hq) as Hl.
    assert (Hwq : w * q = W * r) by (unfold q; field; lra).
    assert (w * (ln q + ln (/ r)) <= w * (q - 1) + w * ln (/ r)) by nra.
    assert (w * (q - 1) = W * r - w) by (rewrite Rmult_minus_distr_l, Hwq; lra).
    lra.
  - rewrite <- Hz. rewrite Rmult_0_l, Rmult_0_l.
    assert (0 <= W * r) by (apply Rmult_le_pos; lra). lra.
Qed.

(** Kraft: the code weights 2^(-l x) over the finite list sum to at most 1.  *)
Theorem ax_gibbs_code : forall (St : Type) (p : St -> R) (l : St -> nat) (F : list St) (W : R),
  (forall x, In x F -> 0 <= p x) ->
  ax_rsum (fun x => / INR (2 ^ l x)) F <= 1 ->
  ax_weight St p F <= W ->
  ax_rsum (fun x => p x * ln (W / p x)) F
    <= ln 2 * ax_rsum (fun x => p x * INR (l x)) F + (W - ax_weight St p F).
Proof.
  intros St p l F W Hp Hk HW.
  assert (HW0 : 0 <= W).
  { pose proof (ax_rsum_nonneg p F Hp) as H0. unfold ax_weight in HW. lra. }
  assert (Hterm : forall x, In x F ->
    p x * ln (W / p x) <= (W * / INR (2 ^ l x) - p x) + ln 2 * (p x * INR (l x))).
  { intros x Hx.
    assert (Hpos : 0 < INR (2 ^ l x))
      by (apply lt_0_INR; apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
    assert (Hr : 0 < / INR (2 ^ l x)) by (apply Rinv_0_lt_compat; exact Hpos).
    assert (Hpw : p x <= W).
    { eapply Rle_trans; [| exact HW]. unfold ax_weight. apply ax_rsum_ge_elt; [exact Hp | exact Hx]. }
    pose proof (ax_code_term (p x) W (/ INR (2 ^ l x)) (Hp x Hx) Hpw Hr) as H.
    rewrite Rinv_inv in H by lra. rewrite ax_ln_pow2 in H. nra. }
  eapply Rle_trans; [apply (ax_rsum_le _ _ F Hterm) |].
  rewrite (ax_rsum_plus (fun x => W * / INR (2 ^ l x) - p x)
                        (fun x => ln 2 * (p x * INR (l x)))).
  rewrite (ax_rsum_minus (fun x => W * / INR (2 ^ l x)) p).
  rewrite (ax_rsum_scal W (fun x => / INR (2 ^ l x))).
  rewrite (ax_rsum_scal (ln 2) (fun x => p x * INR (l x))).
  fold (ax_weight St p F).
  assert (W * ax_rsum (fun x => / INR (2 ^ l x)) F <= W * 1) by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** The uniform code on 2^c states gives the finite Gibbs bound back. *)
Corollary ax_gibbs_code_uniform : forall (St : Type) (p : St -> R) (c : nat) (F : list St),
  (forall x, In x F -> 0 <= p x) ->
  length F = (2 ^ c)%nat ->
  ax_fibre_loss St p F <= INR c * ln 2 * ax_weight St p F.
Proof.
  intros St p c F Hp Hlen.
  pose proof (ax_gibbs_code St p (fun _ => c) F (ax_weight St p F) Hp) as H.
  assert (Hk : ax_rsum (fun x => / INR (2 ^ c)) F <= 1).
  { rewrite ax_rsum_const, Hlen.
    assert (Hpos : 0 < INR (2 ^ c))
      by (apply lt_0_INR; apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
    rewrite Rinv_r by lra. lra. }
  specialize (H Hk (Rle_refl _)). cbv beta in H.
  assert (Hs : ax_rsum (fun x => p x * INR c) F = ax_weight St p F * INR c)
    by (apply ax_rsum_scal_r).
  rewrite Hs in H. unfold ax_fibre_loss. nra.
Qed.

Print Assumptions ax_priced_spots.
Print Assumptions ax_spots_priced.
Print Assumptions ax_inf_loss_bits.
Print Assumptions ax_inf_loss_series.
Print Assumptions ax_chain_rule.
Print Assumptions ax_entropy_split.
Print Assumptions ax_infinite_entropy_survives.
Print Assumptions ax_gibbs_code.
Print Assumptions ax_gibbs_code_uniform.

(** * 6. An infinite landing spot: no finite price, a finite or infinite loss *)

Definition ax_unit_pre : BPre unit :=
  {| bp_leb := fun _ _ => true; bp_refl := fun _ => eq_refl;
     bp_trans := fun _ _ _ _ _ => eq_refl |}.

(** The machine that sends every state of T to one state, by a move whose
    cost is its name. *)
Definition ax_collapse (T : Type) (t0 : T) : AxSys unit ax_unit_pre :=
  mk_axsys unit ax_unit_pre T nat (fun _ _ => t0) (fun c => c) (fun _ => tt).

Theorem ax_collapse_unpriceable : forall (T : Type) (t0 : T) (e : nat -> T),
  (forall a b, e a = e b -> a = b) ->
  (forall c, exists D : list T, NoDup D /\ (2 ^ c < length D)%nat) /\
  forall eq_dec, ~ ax_compression_priced unit ax_unit_pre (ax_collapse T t0) eq_dec.
Proof.
  intros T t0 e Hinj.
  assert (Hd : forall c, exists D : list T, NoDup D /\ (2 ^ c < length D)%nat).
  { intro c. exists (map e (seq 0 (2 ^ c + 1))). split.
    - apply FinFun.Injective_map_NoDup; [exact Hinj | apply seq_NoDup].
    - rewrite map_length, seq_length. lia. }
  split; [exact Hd |].
  intros eq_dec Hprice.
  pose proof (ax_priced_spots unit ax_unit_pre (ax_collapse T t0) eq_dec Hprice) as Hb.
  destruct (Hd 0%nat) as [D [Hnd Hlen]].
  assert (Hle : (length D <= 2 ^ 0)%nat).
  { change (length D <= 2 ^ (ax_cost unit ax_unit_pre (ax_collapse T t0) 0%nat))%nat.
    apply (Hb 0%nat t0 D Hnd). intros x _. reflexivity. }
  lia.
Qed.

Lemma ax_ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma ax_rsum_app : forall {A : Type} (g : A -> R) l1 l2,
  ax_rsum g (l1 ++ l2) = ax_rsum g l1 + ax_rsum g l2.
Proof.
  intros A g l1 l2. induction l1 as [| a l1 IH]; simpl; [lra |]. rewrite IH. lra.
Qed.

Lemma ax_rsum_seq_succ : forall (g : nat -> R) n,
  ax_rsum g (seq 0 (S n)) = ax_rsum g (seq 0 n) + g n.
Proof.
  intros g n. rewrite seq_S, ax_rsum_app. simpl. lra.
Qed.

Lemma ax_inr_pow2_succ : forall n, INR (2 ^ S n) = 2 * INR (2 ^ n).
Proof.
  intro n. rewrite Nat.pow_succ_r', mult_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity.
Qed.

Lemma ax_inr_pow2_pos : forall n, 0 < INR (2 ^ n).
Proof.
  intro n. apply lt_0_INR. apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia.
Qed.

Lemma ax_pow2_gt : forall n, (n + 1 <= 2 ^ n)%nat.
Proof.
  induction n as [| n IH]; [simpl; lia |].
  rewrite Nat.pow_succ_r'. lia.
Qed.

(** One over a power of 2 tends to 0. *)
Lemma ax_inv_pow2_cv : Un_cv (fun n => / INR (2 ^ n)) 0.
Proof.
  intros eps Heps.
  assert (Hn : exists N : nat, / eps < INR N).
  { destruct (archimed (/ eps)) as [Ha _].
    pose proof (Rinv_0_lt_compat eps Heps) as Hie.
    assert (Hz : (0 <= up (/ eps))%Z) by (apply le_IZR; simpl; lra).
    (* SAFE: Hz says 0 <= up (/ eps), so Z.to_nat is exact (Z2Nat.id below). *)
    exists (Z.to_nat (up (/ eps))).
    rewrite INR_IZR_INZ. rewrite Z2Nat.id by exact Hz. exact Ha. }
  destruct Hn as [N HN]. exists N. intros n Hn.
  unfold R_dist. rewrite Rminus_0_r.
  pose proof (ax_inr_pow2_pos n) as Hp.
  rewrite Rabs_right by (left; apply Rinv_0_lt_compat; exact Hp).
  assert (Hle : INR n + 1 <= INR (2 ^ n)).
  { pose proof (ax_pow2_gt n) as H. apply le_INR in H. rewrite plus_INR in H. simpl in H. lra. }
  assert (HnN : INR N <= INR n) by (apply le_INR; exact Hn).
  assert (H1 : / eps < INR (2 ^ n)) by lra.
  assert (H2 : 1 < eps * INR (2 ^ n)).
  { assert (E : eps * / eps = 1) by (field; lra).
    nra. }
  assert (E2 : INR (2 ^ n) * / INR (2 ^ n) = 1) by (field; lra).
  pose proof (Rinv_0_lt_compat _ Hp) as Hq.
  nra.
Qed.

(** The geometric prior on the states 0, 1, 2, ...: state j has weight 2^-(j+1).
    It is a probability on the spot. *)
Definition ax_geo (j : nat) : R := / INR (2 ^ S j).

Lemma ax_geo_mass_n : forall n, ax_rsum ax_geo (seq 0 n) = 1 - / INR (2 ^ n).
Proof.
  induction n as [| n IH].
  - simpl. rewrite Rinv_1. lra.
  - rewrite ax_rsum_seq_succ, IH. unfold ax_geo. rewrite ax_inr_pow2_succ.
    pose proof (ax_inr_pow2_pos n) as Hp.
    assert (E : / (2 * INR (2 ^ n)) = / 2 * / INR (2 ^ n)) by (apply Rinv_mult; lra).
    rewrite E. lra.
Qed.

Theorem ax_geometric_mass : Un_cv (fun n => ax_rsum ax_geo (seq 0 n)) 1.
Proof.
  intros eps Heps. destruct (ax_inv_pow2_cv eps Heps) as [N HN].
  exists N. intros n Hn. rewrite ax_geo_mass_n.
  pose proof (HN n Hn) as H. unfold R_dist in *. rewrite Rminus_0_r in H.
  replace (1 - / INR (2 ^ n) - 1) with (- / INR (2 ^ n)) by lra.
  rewrite Rabs_Ropp. exact H.
Qed.

Lemma ax_geo_moment : forall n,
  ax_rsum (fun j => ax_geo j * INR (S j)) (seq 0 n) = 2 - INR (n + 2) * / INR (2 ^ n).
Proof.
  induction n as [| n IH].
  - simpl. rewrite Rinv_1. lra.
  - rewrite ax_rsum_seq_succ, IH. unfold ax_geo. rewrite ax_inr_pow2_succ.
    pose proof (ax_inr_pow2_pos n) as Hp.
    assert (E : / (2 * INR (2 ^ n)) = / 2 * / INR (2 ^ n)) by (apply Rinv_mult; lra).
    rewrite E.
    assert (E1 : INR (S n + 2) = INR n + 3) by (rewrite plus_INR, S_INR; replace (INR 2) with 2 by (simpl; lra); lra).
    assert (E2 : INR (n + 2) = INR n + 2) by (rewrite plus_INR; replace (INR 2) with 2 by (simpl; lra); lra).
    rewrite E1, E2. rewrite S_INR.
    lra.
Qed.

(** The loss of the geometric prior on the whole spot, over the first n
    states: ln 2 (2 - (n + 2) / 2^n), which is below 2 ln 2 for every n. *)
Theorem ax_geometric_loss : forall n,
  ax_rsum (fun j => ax_geo j * ln (1 / ax_geo j)) (seq 0 n)
    = ln 2 * (2 - INR (n + 2) * / INR (2 ^ n)) /\
  ax_rsum (fun j => ax_geo j * ln (1 / ax_geo j)) (seq 0 n) <= 2 * ln 2.
Proof.
  intro n.
  assert (Hterm : forall j, In j (seq 0 n) ->
    ax_geo j * ln (1 / ax_geo j) = ln 2 * (ax_geo j * INR (S j))).
  { intros j _. unfold ax_geo.
    pose proof (ax_inr_pow2_pos (S j)) as Hp.
    replace (1 / / INR (2 ^ S j)) with (INR (2 ^ S j)) by (field; lra).
    rewrite ax_ln_pow2. ring. }
  rewrite (ax_rsum_ext _ _ _ Hterm).
  rewrite (ax_rsum_scal (ln 2) (fun j => ax_geo j * INR (S j))), ax_geo_moment.
  assert (Hln : 0 < ln 2) by exact ax_ln2_pos.
  assert (Hq : 0 <= INR (n + 2) * / INR (2 ^ n)).
  { apply Rmult_le_pos; [apply pos_INR | left; apply Rinv_0_lt_compat; apply ax_inr_pow2_pos]. }
  split; [reflexivity | nra].
Qed.

(** The block prior: block k has 2^(2^k) states, each of weight
    m_k / 2^(2^k), where m_k = 1 / ((k+1)(k+2)).  The block masses m_k sum
    to 1, so it is a probability on the countable set of pairs (k, j). *)
Definition ax_nb (k : nat) : nat := 2 ^ (2 ^ k).
Definition ax_mb (k : nat) : R := / INR ((k + 1) * (k + 2)).

Definition ax_pb (x : nat * nat) : R :=
  if (snd x <? ax_nb (fst x))%nat then ax_mb (fst x) / INR (ax_nb (fst x)) else 0.

Definition ax_blk (k : nat) : list (nat * nat) := map (fun j => (k, j)) (seq 0 (ax_nb k)).
Definition ax_eb (m : nat) : list (nat * nat) := flat_map ax_blk (seq 0 m).

Lemma ax_rsum_flat_map : forall {A B : Type} (g : B -> R) (f : A -> list B) (l : list A),
  ax_rsum g (flat_map f l) = ax_rsum (fun a => ax_rsum g (f a)) l.
Proof.
  intros A B g f l. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite ax_rsum_app, IH. reflexivity.
Qed.

Lemma ax_rsum_map : forall {A B : Type} (g : B -> R) (f : A -> B) (l : list A),
  ax_rsum g (map f l) = ax_rsum (fun a => g (f a)) l.
Proof.
  intros A B g f l. induction l as [| a l IH]; simpl; [reflexivity |]. rewrite IH. reflexivity.
Qed.

Lemma ax_nb_pos : forall k, 0 < INR (ax_nb k).
Proof. intro k. unfold ax_nb. apply ax_inr_pow2_pos. Qed.

Lemma ax_mb_pos : forall k, 0 < ax_mb k.
Proof.
  intro k. unfold ax_mb. apply Rinv_0_lt_compat. apply lt_0_INR. nia.
Qed.

Lemma ax_mb_le_1 : forall k, ax_mb k <= 1.
Proof.
  intro k. unfold ax_mb. rewrite <- Rinv_1 at 1. apply Rinv_le_contravar; [lra |].
  apply (le_INR 1). nia.
Qed.

(** Every state of block k has weight m_k / N_k. *)
Lemma ax_pb_in : forall k j, (j < ax_nb k)%nat -> ax_pb (k, j) = ax_mb k / INR (ax_nb k).
Proof.
  intros k j H. unfold ax_pb. simpl. apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

(** A function of the weight, summed over a block. *)
Lemma ax_blk_sum : forall (h : R -> R) k,
  ax_rsum (fun x => h (ax_pb x)) (ax_blk k) = INR (ax_nb k) * h (ax_mb k / INR (ax_nb k)).
Proof.
  intros h k. unfold ax_blk. rewrite ax_rsum_map.
  assert (Hc : forall j, In j (seq 0 (ax_nb k)) ->
            h (ax_pb (k, j)) = h (ax_mb k / INR (ax_nb k))).
  { intros j Hj. apply in_seq in Hj. rewrite (ax_pb_in k j) by lia. reflexivity. }
  rewrite (ax_rsum_ext _ _ _ Hc), ax_rsum_const, seq_length. reflexivity.
Qed.

(** Total weight of the first m blocks: 1 - 1/(m+1). *)
Theorem ax_block_mass_n : forall m, ax_rsum ax_pb (ax_eb m) = 1 - / INR (S m).
Proof.
  induction m as [| m IH].
  - simpl. rewrite Rinv_1. lra.
  - unfold ax_eb in *. rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r.
    rewrite ax_rsum_app, IH.
    assert (Hb : ax_rsum ax_pb (ax_blk m) = ax_mb m).
    { pose proof (ax_blk_sum (fun w => w) m) as H. cbv beta in H.
      transitivity (INR (ax_nb m) * (ax_mb m / INR (ax_nb m))); [exact H |].
      pose proof (ax_nb_pos m) as Hp. field. lra. }
    rewrite Hb. unfold ax_mb.
    replace ((m + 1) * (m + 2))%nat with (S m * S (S m))%nat by (simpl; lia).
    rewrite mult_INR.
    rewrite (S_INR (S m)).
    assert (H1 : 0 < INR (S m)) by (apply lt_0_INR; lia).
    assert (Hid : forall t : R, 0 < t -> 1 - / t + / (t * (t + 1)) = 1 - / (t + 1))
      by (intros t Ht; field; lra).
    exact (Hid (INR (S m)) H1).
Qed.

Lemma ax_pb_nonneg : forall x, 0 <= ax_pb x.
Proof.
  intros [k j]. unfold ax_pb. simpl. destruct (j <? ax_nb k)%nat; [| lra].
  unfold Rdiv. apply Rmult_le_pos; [left; apply ax_mb_pos | left; apply Rinv_0_lt_compat; apply ax_nb_pos].
Qed.

(** 3 * 2^k >= (k+1)(k+2). *)
Lemma ax_pow2_quad : forall k, ((k + 1) * (k + 2) <= 3 * 2 ^ k)%nat.
Proof.
  assert (H : forall k, ((k + 1) * (k + 2) <= 3 * 2 ^ k)%nat /\
                        ((S k + 1) * (S k + 2) <= 3 * 2 ^ S k)%nat).
  { induction k as [| k [IH1 IH2]]; [split; simpl; lia |].
    split; [exact IH2 |].
    assert (E : (2 ^ S (S k) = 2 * 2 ^ S k)%nat) by apply Nat.pow_succ_r'.
    rewrite E. nia. }
  intro k. apply (H k).
Qed.

(** A block contributes at least (ln 2)/3 to the loss against the total
    weight 1. *)
Lemma ax_block_term : forall k,
  ln 2 / 3 <= ax_rsum (fun x => ax_pb x * ln (1 / ax_pb x)) (ax_blk k).
Proof.
  intro k.
  pose proof (ax_blk_sum (fun w => w * ln (1 / w)) k) as H. cbv beta in H.
  rewrite H.
  set (N := INR (ax_nb k)). set (m := ax_mb k).
  pose proof (ax_nb_pos k) as HN. pose proof (ax_mb_pos k) as Hm. pose proof (ax_mb_le_1 k) as Hm1.
  fold N in HN. fold m in Hm, Hm1.
  assert (Hq : 0 < m / N) by (apply Rdiv_lt_0_compat; assumption).
  assert (E : N * (m / N * ln (1 / (m / N))) = m * ln (N / m)).
  { replace (1 / (m / N)) with (N / m) by (field; lra). field. lra. }
  rewrite E.
  assert (Hln : INR (2 ^ k) * ln 2 <= ln (N / m)).
  { unfold N, ax_nb. rewrite <- ax_ln_pow2. apply ax_ln_mono.
    - apply ax_inr_pow2_pos.
    - unfold Rdiv. rewrite <- (Rmult_1_r (INR (2 ^ 2 ^ k))) at 1.
      apply Rmult_le_compat_l; [left; apply ax_inr_pow2_pos |].
      rewrite <- Rinv_1 at 1. apply Rinv_le_contravar; lra. }
  assert (Hk : 1 / 3 <= m * INR (2 ^ k)).
  { unfold m, ax_mb.
    pose proof (ax_pow2_quad k) as Hq3. apply le_INR in Hq3.
    rewrite (mult_INR 3 (2 ^ k)) in Hq3. replace (INR 3) with 3 in Hq3 by (simpl; lra).
    pose proof (ax_inr_pow2_pos k) as Hp2.
    assert (Hq0 : 0 < INR ((k + 1) * (k + 2))) by (apply lt_0_INR; nia).
    assert (Hq1 : INR ((k + 1) * (k + 2)) <= 3 * INR (2 ^ k)).
    { exact Hq3. }
    apply (Rmult_le_reg_r (INR ((k + 1) * (k + 2)))); [exact Hq0 |].
    assert (E3 : / INR ((k + 1) * (k + 2)) * INR (2 ^ k) * INR ((k + 1) * (k + 2))
                 = INR (2 ^ k)) by (field; lra).
    rewrite E3. lra. }
  assert (Hln2 : 0 < ln 2) by exact ax_ln2_pos.
  nra.
Qed.

Theorem ax_block_loss_unbounded : forall B, exists m,
  B < ax_rsum (fun x => ax_pb x * ln (1 / ax_pb x)) (ax_eb m).
Proof.
  intro B.
  assert (Hln2 : 0 < ln 2) by exact ax_ln2_pos.
  assert (Hm : exists m : nat, 3 * B / ln 2 < INR m).
  { destruct (archimed (3 * B / ln 2)) as [Ha _].
    destruct (Z_le_dec 0 (up (3 * B / ln 2))) as [Hz | Hz].
    (* SAFE: Hz says 0 <= up (3 * B / ln 2), so Z.to_nat is exact (Z2Nat.id below). *)
    - exists (Z.to_nat (up (3 * B / ln 2))). rewrite INR_IZR_INZ, Z2Nat.id by exact Hz. exact Ha.
    - exists 0%nat. simpl.
      assert (Hu : IZR (up (3 * B / ln 2)) <= -1)
        by (apply IZR_le; lia).
      pose proof (archimed (3 * B / ln 2)) as [H1 H2]. lra. }
  destruct Hm as [m Hm]. exists m.
  assert (Hlow : forall n, INR n * (ln 2 / 3) <=
                  ax_rsum (fun x => ax_pb x * ln (1 / ax_pb x)) (ax_eb n)).
  { induction n as [| n IH]; [simpl; lra |].
    rewrite S_INR. unfold ax_eb in *. rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r, ax_rsum_app.
    pose proof (ax_block_term n). lra. }
  eapply Rlt_le_trans; [| apply Hlow].
  assert (H3 : 3 * B / ln 2 * ln 2 = 3 * B) by (field; lra).
  nra.
Qed.

(** No finite toll covers it: for every cost c some finite part of the spot
    already loses more than c bits. *)
Corollary ax_block_no_toll : forall c, exists m,
  INR c * ln 2 * 1 < ax_rsum (fun x => ax_pb x * ln (1 / ax_pb x)) (ax_eb m).
Proof.
  intro c. destruct (ax_block_loss_unbounded (INR c * ln 2)) as [m Hm].
  exists m. lra.
Qed.

(** * 7. Landauer's principle as a named premise *)

(** The premise from physics: no process that destroys which state of the
    landing spot F the machine was in dissipates less, on average, than kT
    times the entropy it destroys.  The definition is the number; the
    premise is the claim that heat cannot be below it.  Nothing here
    proves that claim. *)
Definition ax_landauer_minimum (kT : R) (St : Type) (p : St -> R) (F : list St) : R :=
  kT * ax_fibre_loss St p F.

(** What the counting gives: the toll, priced at kT ln 2 per unit, covers the
    minimum the premise demands, for every prior and every finite family of
    landing spots of a priced move. *)
Theorem ax_toll_covers_landauer_minimum :
  forall (A : Type) (P : BPre A) (X : AxSys A P)
         (eq_dec : forall a b : ax_state A P X, {a = b} + {a <> b})
         (i : ax_instr A P X) (p : ax_state A P X -> R)
         (ys : list (ax_state A P X)) (pre : ax_state A P X -> list (ax_state A P X)) (kT : R),
    ax_compression_priced A P X eq_dec ->
    0 <= kT ->
    (forall x, 0 <= p x) ->
    ax_lists_spots A P X i ys pre ->
    ax_rsum (ax_landauer_minimum kT (ax_state A P X) p) (map pre ys)
      <= (kT * ln 2 * INR (ax_cost A P X i)) * ax_mass (ax_state A P X) p (map pre ys).
Proof.
  intros A P X eq_dec i p ys pre kT Hprice HkT Hp Hl.
  pose proof (ax_inf_loss_bits A P X eq_dec Hprice i p ys pre Hp Hl) as H.
  unfold ax_landauer_minimum.
  assert (E : ax_rsum (fun F => kT * ax_fibre_loss (ax_state A P X) p F) (map pre ys)
              = kT * ax_cond_entropy (ax_state A P X) p (map pre ys))
    by (unfold ax_cond_entropy; apply ax_rsum_scal).
  rewrite E. nra.
Qed.

Print Assumptions ax_collapse_unpriceable.
Print Assumptions ax_geometric_mass.
Print Assumptions ax_geometric_loss.
Print Assumptions ax_block_mass_n.
Print Assumptions ax_block_loss_unbounded.
Print Assumptions ax_block_no_toll.
Print Assumptions ax_toll_covers_landauer_minimum.
