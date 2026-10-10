(** PricingOnePremise: the three roads to the toll are one premise.

    Section 4 of the book reaches the toll three ways: merge pricing
    ([merging_steps_priced], PermanentCertification), the halving price
    ([compression_priced], PermanentRecordPricing) and entropy pricing
    ([entropy_priced], PermanentCertificationEntropy). This file shows they
    are one premise in three forms.

    1. Worst-case Landauer. On a finite machine the most bits a move can
       remove from any spread is exactly log2 of its largest pile-up, the
       largest number of states it sends to one state. Every spread loses at
       most log2 K when no pile-up is bigger than K
       [entropy_drop_le_log_fibre], and the even spread on a pile-up of n
       states loses at least log2 n [entropy_drop_of_fibre]; so the even
       spread on a largest pile-up loses exactly log2 of its size, the
       maximum [worst_case_entropy_drop].
    2. With costs in whole numbers, entropy pricing (cost at least the bits
       removed from every spread) holds exactly when the halving price holds
       [entropy_priced_iff_compression_priced]: a cost at least log2 K is a
       whole number c with K <= 2^c.
    3. Merge pricing is the same premise asked only of two states. It holds
       exactly when the halving price holds for every list of at most two
       distinct states [merging_priced_iff_pair_halving] (no finiteness
       needed), and, on a finite machine, exactly when entropy pricing holds
       for every spread on at most two states
       [merging_priced_iff_pair_entropy].

    Scope. Entropy pricing, the halving price and merge pricing are named
    premises; nothing here says a device dissipates anything. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Reals Lra.
Import ListNotations.

From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.
Require Minimal.FragmentSmall.
Require Minimal.CompressionSmall2.

Open Scope R_scope.

Section OnePremise.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.
Variable all : list S.
Hypothesis Hfin : finite_states all.

Definition eqb_s (a b : S) : bool := if eq_dec a b then true else false.

(** The pile-up of [y] under [i]: the states [i] sends to [y]. *)
Definition fibre (i : I) (y : S) : list S :=
  filter (fun x => eqb_s (step x i) y) all.

(** The bits move [i] removes from the spread [p]. *)
Definition drop (i : I) (p : S -> R) : R :=
  entropy all p - entropy all (push eq_dec all (fun s => step s i) p).

Lemma all_nodup : NoDup all.
Proof. exact (proj1 Hfin). Qed.

Lemma all_in : forall s, In s all.
Proof. exact (proj2 Hfin). Qed.

Lemma ln_INR_pos_le : forall n : nat, (0 < n)%nat -> 0 <= ln (INR n).
Proof.
  intros n Hn. rewrite <- ln_1. apply ln_le_mono; [lra |].
  replace 1 with (INR 1) by reflexivity. apply le_INR. lia.
Qed.

Lemma log2_one : log2 1 = 0.
Proof. unfold log2. rewrite ln_1. unfold Rdiv. ring. Qed.

Lemma log2_pow2 : forall c : nat, log2 (INR (2 ^ c)) = INR c.
Proof.
  intro c. unfold log2. rewrite pow_INR. simpl INR at 1.
  replace (1 + 1) with 2 by ring.
  rewrite ln_pow by lra. field. apply Rgt_not_eq, ln2_pos.
Qed.

(** A whole number above the logarithm of [n] pays for [n] in halvings. *)
Lemma log2_le_nat : forall (n c : nat),
  (0 < n)%nat -> log2 (INR n) <= INR c -> (n <= 2 ^ c)%nat.
Proof.
  intros n c Hn H.
  destruct (le_lt_dec n (2 ^ c)) as [Hle | Hgt]; [exact Hle | exfalso].
  apply lt_INR in Hgt.
  assert (H2 : 0 < INR (2 ^ c)) by (apply lt_0_INR; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (Hln : ln (INR (2 ^ c)) < ln (INR n)) by (apply ln_increasing; lra).
  rewrite <- (log2_pow2 c) in H. unfold log2 in H.
  assert (Hl2 := ln2_pos).
  apply Rmult_le_compat_r with (r := ln 2) in H; [| lra].
  unfold Rdiv in H. rewrite !Rmult_assoc, Rinv_l in H by lra. lra.
Qed.

(** A probability is at most one. *)
Lemma prob_le_one : forall p x, distribution all p -> p x <= 1.
Proof.
  intros p x [Hnn Hsum].
  rewrite <- (rsum_select eq_dec all x p all_nodup (all_in x)).
  rewrite <- Hsum. apply rsum_le. intros z _.
  destruct (eq_dec x z); [lra | apply Hnn].
Qed.

Lemma entropy_nonneg : forall p, distribution all p -> 0 <= entropy all p.
Proof.
  intros p Hp. unfold entropy. apply rsum_nonneg. intro a.
  unfold surprisal_term. destruct (Rlt_dec 0 (p a)) as [Hpos | _]; [| lra].
  assert (H1 : p a <= 1) by (apply prob_le_one; exact Hp).
  assert (Hln : ln (p a) <= 0) by (rewrite <- ln_1; apply ln_le_mono; lra).
  unfold log2, Rdiv. assert (Hl2 := ln2_pos).
  assert (Hi : 0 < / ln 2) by (apply Rinv_0_lt_compat; lra).
  assert (Hq : ln (p a) * / ln 2 <= 0 * / ln 2) by (apply Rmult_le_compat_r; lra).
  assert (Hm : p a * (ln (p a) * / ln 2) <= p a * (0 * / ln 2))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(** ** 1. The bits a move removes, bounded by its pile-ups *)

(** The general bound: if, for every state [z] the spread can be in, at most
    [K] states the spread can be in land where [z] lands, the move removes
    at most [log2 K] bits. *)
Theorem entropy_drop_le_log_support_fibre :
  forall i p (K : nat),
    distribution all p -> (0 < K)%nat ->
    (forall z, 0 < p z ->
       (length (filter (fun x => positive_b (p x) && eqb_s (step z i) (step x i)) all)
          <= K)%nat) ->
    drop i p <= log2 (INR K).
Proof.
  intros i p K Hp HK Hcount.
  pose proof Hp as [Hnn Hsum].
  set (f := fun s => step s i).
  set (q := push eq_dec all f p).
  assert (HKR : 0 < INR K) by (apply lt_0_INR; exact HK).
  assert (Hl2 := ln2_pos).
  unfold drop. fold f.
  rewrite (entropy_drop_as_point_sum eq_dec all f p all_nodup all_in Hnn). fold q.
  set (U := fun x => if Rlt_dec 0 (p x) then q (f x) else 0).
  (* one term at a time *)
  assert (Hpt : forall x,
    (if Rlt_dec 0 (p x) then p x * (log2 (q (f x)) - log2 (p x)) else 0)
      <= / ln 2 * (/ INR K * U x - p x) + log2 (INR K) * p x).
  { intro x. unfold U. destruct (Rlt_dec 0 (p x)) as [Hpos | Hz].
    - assert (Hq : p x <= q (f x)) by (apply push_ge_point; [apply all_nodup | apply all_in | exact Hnn]).
      assert (Hy : 0 < q (f x) / (INR K * p x)).
      { apply Rdiv_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]. }
      assert (Hln := ln_le_minus_one _ Hy).
      unfold Rdiv in Hln. rewrite ln_mult in Hln by (try lra; apply Rinv_0_lt_compat; nra).
      rewrite ln_Rinv in Hln by nra. rewrite ln_mult in Hln by lra.
      assert (Hm : p x * (ln (q (f x)) - ln (p x)) <= / INR K * q (f x) - p x + ln (INR K) * p x).
      { assert (Hstep : p x * (ln (q (f x)) + - (ln (INR K) + ln (p x)))
                        <= p x * (q (f x) * / (INR K * p x) - 1))
          by (apply Rmult_le_compat_l; lra).
        replace (p x * (q (f x) * / (INR K * p x) - 1)) with (/ INR K * q (f x) - p x) in Hstep
          by (field; lra).
        lra. }
      unfold log2.
      replace (p x * (ln (q (f x)) / ln 2 - ln (p x) / ln 2))
        with (/ ln 2 * (p x * (ln (q (f x)) - ln (p x)))) by (field; lra).
      replace (/ ln 2 * (/ INR K * q (f x) - p x) + ln (INR K) / ln 2 * p x)
        with (/ ln 2 * (/ INR K * q (f x) - p x + ln (INR K) * p x)) by (field; lra).
      apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat; lra | exact Hm].
    - assert (Hz0 : p x = 0) by (specialize (Hnn x); lra). rewrite Hz0. lra. }
  eapply Rle_trans; [apply rsum_le; intros x _; apply Hpt |].
  rewrite rsum_plus, rsum_scal, rsum_minus, rsum_scal, rsum_scal, Hsum.
  (* the crowding sum is at most K *)
  assert (HU : rsum all U <= INR K).
  { unfold U, q, push.
    apply Rle_trans with (rsum all (fun z => p z * INR K)).
    - rewrite (rsum_ext_in all
        (fun x => if Rlt_dec 0 (p x)
                  then rsum all (fun z => if eq_dec (f z) (f x) then p z else 0) else 0)
        (fun x => rsum all (fun z =>
                    if positive_b (p x) && eqb_s (f z) (f x) then p z else 0))).
      2: { intros x _. unfold positive_b, eqb_s.
           destruct (Rlt_dec 0 (p x)); simpl.
           - apply rsum_ext_in. intros z _. destruct (eq_dec (f z) (f x)); reflexivity.
           - symmetry. apply rsum_zero. intros. reflexivity. }
      rewrite rsum_swap. apply rsum_le. intros z _.
      destruct (Rlt_dec 0 (p z)) as [Hpz | Hpz].
      + rewrite (rsum_ext_in all
          (fun x => if positive_b (p x) && eqb_s (f z) (f x) then p z else 0)
          (fun x => if (fun x => positive_b (p x) && eqb_s (step z i) (step x i)) x
                    then p z else 0)) by (intros; reflexivity).
        rewrite rsum_indicator. rewrite Rmult_comm.
        apply Rmult_le_compat_l; [lra |]. apply le_INR. apply Hcount. exact Hpz.
      + assert (Hz0 : p z = 0) by (specialize (Hnn z); lra). rewrite Hz0.
        rewrite rsum_zero by (intros; destruct (_ && _); reflexivity). lra.
    - rewrite (rsum_ext_in all (fun z => p z * INR K) (fun z => INR K * p z))
        by (intros; ring).
      rewrite rsum_scal, Hsum. lra. }
  assert (HKinv : / INR K * rsum all U <= 1).
  { apply Rmult_le_reg_l with (r := INR K); [lra |].
    rewrite <- Rmult_assoc, Rinv_r by lra. lra. }
  assert (Hil : 0 < / ln 2) by (apply Rinv_0_lt_compat; lra).
  nra.
Qed.

(** The pile-up form: no pile-up bigger than [K] means at most [log2 K]
    bits removed, from any spread. *)
Theorem entropy_drop_le_log_fibre :
  forall i p (K : nat),
    distribution all p -> (0 < K)%nat ->
    (forall y, (length (fibre i y) <= K)%nat) ->
    drop i p <= log2 (INR K).
Proof.
  intros i p K Hp HK Hfib.
  apply entropy_drop_le_log_support_fibre; [exact Hp | exact HK |].
  intros z _. eapply Nat.le_trans; [| apply (Hfib (step z i))].
  apply NoDup_incl_length; [apply NoDup_filter, all_nodup |].
  intros x Hx. apply filter_In in Hx as [Hx Hc]. apply andb_true_iff in Hc as [_ Hc].
  apply filter_In. split; [exact Hx |]. unfold eqb_s in *.
  destruct (eq_dec (step z i) (step x i)) as [E | _]; [| discriminate].
  destruct (eq_dec (step x i) (step z i)) as [_ | N]; [reflexivity | exfalso; apply N; auto].
Qed.

(** The even spread on a pile-up of [n] states loses at least [log2 n]. *)
Theorem entropy_drop_of_fibre :
  forall i y,
    (0 < length (fibre i y))%nat ->
    distribution all (uniform_on eq_dec (fibre i y)) /\
    drop i (uniform_on eq_dec (fibre i y)) >= log2 (INR (length (fibre i y))).
Proof.
  intros i y Hn.
  set (U := fibre i y).
  assert (HndU : NoDup U) by (apply NoDup_filter, all_nodup).
  assert (HsubU : forall a, In a U -> In a all) by (intros; apply all_in).
  assert (Hdist : distribution all (uniform_on eq_dec U))
    by (apply uniform_on_distribution; [apply all_nodup | exact HndU | exact HsubU | exact Hn]).
  split; [exact Hdist |].
  unfold drop.
  rewrite (uniform_on_entropy eq_dec all U all_nodup HndU HsubU Hn).
  assert (Hq : entropy all (push eq_dec all (fun s => step s i) (uniform_on eq_dec U))
               <= log2 (INR (length [y]))).
  { apply entropy_le_log_support.
    - apply all_nodup.
    - apply push_distribution; [apply all_nodup | apply all_in | exact Hdist].
    - apply (push_support eq_dec all [y] U (fun s => step s i) (uniform_on eq_dec U)
               (proj1 Hdist)).
      + intros x _ Hpx. unfold uniform_on, in_b in Hpx.
        destruct (in_dec eq_dec x U); [assumption | lra].
      + intros x Hx. unfold U, fibre in Hx. apply filter_In in Hx as [_ Hx].
        unfold eqb_s in Hx. destruct (eq_dec (step x i) y) as [E | _]; [| discriminate].
        left. symmetry. exact E.
    - simpl. lia. }
  simpl length in Hq. replace (INR 1) with 1 in Hq by reflexivity.
  rewrite log2_one in Hq. lra.
Qed.

(** Worst-case Landauer: the most bits a move removes from any spread is
    log2 of its largest pile-up, and that maximum is reached. *)
Theorem worst_case_entropy_drop :
  forall i (K : nat) y0,
    (0 < K)%nat ->
    (forall y, (length (fibre i y) <= K)%nat) ->
    length (fibre i y0) = K ->
    (forall p, distribution all p -> drop i p <= log2 (INR K)) /\
    distribution all (uniform_on eq_dec (fibre i y0)) /\
    drop i (uniform_on eq_dec (fibre i y0)) = log2 (INR K).
Proof.
  intros i K y0 HK Hfib Hy0. split.
  - intros p Hp. apply entropy_drop_le_log_fibre; assumption.
  - assert (Hn : (0 < length (fibre i y0))%nat) by lia.
    destruct (entropy_drop_of_fibre i y0 Hn) as [Hd Hge].
    split; [exact Hd |].
    rewrite Hy0 in Hge.
    pose proof (entropy_drop_le_log_fibre i _ K Hd HK Hfib). lra.
Qed.

(** ** 2. Entropy pricing is the halving price *)

Lemma compression_iff_fibre :
  compression_priced step cost eq_dec <->
  forall i y, (length (fibre i y) <= 2 ^ cost i)%nat.
Proof.
  exact (Minimal.CompressionSmall2.ent2_compression_priced_iff_fibres
           S I step cost eq_dec all Hfin).
Qed.

Theorem entropy_priced_iff_compression_priced :
  entropy_priced step eq_dec all cost <-> compression_priced step cost eq_dec.
Proof.
  rewrite compression_iff_fibre. split.
  - intros H i y.
    destruct (length (fibre i y)) as [| n] eqn:Hn; [lia |].
    assert (Hpos : (0 < length (fibre i y))%nat) by lia.
    destruct (entropy_drop_of_fibre i y Hpos) as [Hd Hge].
    pose proof (H i _ Hd) as Hc. fold (drop i (uniform_on eq_dec (fibre i y))) in Hc.
    rewrite <- Hn. apply log2_le_nat; [exact Hpos | lra].
  - intros Hfib i p Hp.
    assert (HK : (0 < 2 ^ cost i)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    pose proof (entropy_drop_le_log_fibre i p (2 ^ cost i) Hp HK (Hfib i)) as Hd.
    rewrite log2_pow2 in Hd. unfold drop in Hd. lra.
Qed.

(** ** 3. Merge pricing is the premise asked of two states *)

(** The halving price on lists of at most two states. *)
Definition pair_halving : Prop :=
  forall i D, NoDup D -> (length D <= 2)%nat ->
    (length D <= 2 ^ cost i * image_size step eq_dec i D)%nat.

Lemma image_size_one : forall i a, image_size step eq_dec i [a] = 1%nat.
Proof. intros. reflexivity. Qed.

Lemma image_size_two : forall i a b,
  image_size step eq_dec i [a; b] =
  (if eq_dec (step a i) (step b i) then 1 else 2)%nat.
Proof.
  intros i a b. unfold image_size. simpl map.
  change (nodup eq_dec [step a i; step b i]) with
    (if in_dec eq_dec (step a i) [step b i] then [step b i] else [step a i; step b i]).
  destruct (eq_dec (step a i) (step b i)) as [E | N].
  - destruct (in_dec eq_dec (step a i) [step b i]) as [_ | Hout]; [reflexivity |].
    exfalso. apply Hout. left. symmetry. exact E.
  - destruct (in_dec eq_dec (step a i) [step b i]) as [Hin | _]; [| reflexivity].
    exfalso. destruct Hin as [H | []]. apply N. symmetry. exact H.
Qed.

Theorem merging_priced_iff_pair_halving :
  merging_steps_priced step cost <-> pair_halving.
Proof.
  split.
  - intros H i D HD Hlen.
    destruct D as [| a [| b [| c D]]]; simpl in Hlen |- *; try lia.
    + rewrite image_size_one. pose proof (Nat.pow_nonzero 2 (cost i)). lia.
    + rewrite image_size_two. destruct (eq_dec (step a i) (step b i)) as [E | N].
      * assert (Hc : (cost i >= 1)%nat).
        { apply H. intro Hinj. inversion HD as [| ? ? Hnot _]; subst.
          apply Hnot. left. symmetry. apply Hinj. exact E. }
        destruct (cost i) as [| c']; [lia |]. simpl. pose proof (Nat.pow_nonzero 2 c'). lia.
      * pose proof (Nat.pow_nonzero 2 (cost i)). lia.
  - intros H i Hni.
    destruct (cost i) as [| c'] eqn:Hc; [exfalso | lia].
    apply Hni. intros a b E.
    destruct (eq_dec a b) as [Hab | Hab]; [exact Hab | exfalso].
    assert (HD : NoDup [a; b]).
    { constructor; [intros [H1 | []]; apply Hab; auto | constructor; [intros [] | constructor]]. }
    pose proof (H i [a; b] HD (le_n 2)) as Hh.
    rewrite image_size_two, Hc in Hh. simpl in Hh.
    destruct (eq_dec (step a i) (step b i)); [lia | contradiction].
Qed.

(** Entropy pricing on spreads over at most two states. *)
Definition pair_entropy_priced : Prop :=
  forall i p a b, distribution all p -> (forall x, 0 < p x -> x = a \/ x = b) ->
    INR (cost i) >= drop i p.

Theorem merging_priced_iff_pair_entropy :
  merging_steps_priced step cost <-> pair_entropy_priced.
Proof.
  split.
  - intros H i p a b Hp Hab.
    assert (Hsupp : forall x, In x all -> 0 < p x -> In x [a; b]).
    { intros x _ Hx. destruct (Hab x Hx) as [-> | ->]; simpl; auto. }
    destruct (eq_dec (step a i) (step b i)) as [E | N];
      [destruct (eq_dec a b) as [Eab | Nab] |].
    + (* the two states are one: nothing merges on the support *)
      subst b.
      assert (Hd : drop i p <= log2 (INR 1)).
      { apply entropy_drop_le_log_support_fibre; [exact Hp | lia |].
        intros z Hz. change 1%nat with (length [z]).
        apply NoDup_incl_length; [apply NoDup_filter, all_nodup |].
        intros x Hx. apply filter_In in Hx as [_ Hc]. apply andb_true_iff in Hc as [Hc _].
        unfold positive_b in Hc. destruct (Rlt_dec 0 (p x)) as [Hx | _]; [| discriminate].
        destruct (Hab x Hx) as [-> | ->]; destruct (Hab z Hz) as [-> | ->]; left; reflexivity. }
      replace (INR 1) with 1 in Hd by reflexivity. rewrite log2_one in Hd.
      pose proof (pos_INR (cost i)). lra.
    + (* a merge: priced at one, and at most one bit is removed *)
      assert (Hc : (cost i >= 1)%nat) by (apply H; intro Hinj; apply Nab, Hinj, E).
      assert (HcR : 1 <= INR (cost i)) by (replace 1 with (INR 1) by reflexivity; apply le_INR; lia).
      assert (Hle : entropy all p <= log2 (INR (length [a; b])))
        by (apply entropy_le_log_support; [apply all_nodup | exact Hp | exact Hsupp | simpl; lia]).
      assert (Hq := entropy_nonneg _ (push_distribution eq_dec all (fun s => step s i) p all_nodup all_in Hp)).
      simpl length in Hle. replace (INR 2) with 2 in Hle by (simpl; ring).
      assert (H2 : log2 2 = 1) by (unfold log2; field; apply Rgt_not_eq, ln2_pos).
      unfold drop. lra.
    + (* no merge on the support *)
      assert (Hd : drop i p <= log2 (INR 1)).
      { apply entropy_drop_le_log_support_fibre; [exact Hp | lia |].
        intros z Hz. change 1%nat with (length [z]).
        apply NoDup_incl_length; [apply NoDup_filter, all_nodup |].
        intros x Hx. apply filter_In in Hx as [_ Hc]. apply andb_true_iff in Hc as [Hc Heq].
        unfold positive_b in Hc. destruct (Rlt_dec 0 (p x)) as [Hx | _]; [| discriminate].
        unfold eqb_s in Heq. destruct (eq_dec (step z i) (step x i)) as [Ezx | _]; [| discriminate].
        destruct (Hab x Hx) as [-> | ->]; destruct (Hab z Hz) as [-> | ->];
          try (left; reflexivity); exfalso; apply N; auto. }
      replace (INR 1) with 1 in Hd by reflexivity. rewrite log2_one in Hd.
      pose proof (pos_INR (cost i)). lra.
  - intros H i Hni.
    destruct (cost i) as [| c'] eqn:Hc; [exfalso | lia].
    apply Hni. intros a b E.
    destruct (eq_dec a b) as [Hab | Hab]; [exact Hab | exfalso].
    set (U := [a; b]).
    assert (HndU : NoDup U).
    { constructor; [intros [H1 | []]; apply Hab; auto | constructor; [intros [] | constructor]]. }
    assert (HsubU : forall x, In x U -> In x all) by (intros; apply all_in).
    assert (Hdist : distribution all (uniform_on eq_dec U))
      by (apply uniform_on_distribution; [apply all_nodup | exact HndU | exact HsubU | simpl; lia]).
    assert (Hsupp : forall x, 0 < uniform_on eq_dec U x -> x = a \/ x = b).
    { intros x Hx. unfold uniform_on, in_b in Hx.
      destruct (in_dec eq_dec x U) as [[H1 | [H1 | []]] | _]; [left | right | lra]; auto. }
    pose proof (H i _ a b Hdist Hsupp) as Hp. rewrite Hc in Hp. simpl INR in Hp.
    unfold drop in Hp.
    rewrite (uniform_on_entropy eq_dec all U all_nodup HndU HsubU) in Hp by (simpl; lia).
    assert (Hq : entropy all (push eq_dec all (fun s => step s i) (uniform_on eq_dec U))
                 <= log2 (INR (length [step a i]))).
    { apply entropy_le_log_support.
      - apply all_nodup.
      - apply push_distribution; [apply all_nodup | apply all_in | exact Hdist].
      - apply (push_support eq_dec all [step a i] U (fun s => step s i)
                 (uniform_on eq_dec U) (proj1 Hdist)).
        + intros x _ Hpx. unfold uniform_on, in_b in Hpx.
          destruct (in_dec eq_dec x U); [assumption | lra].
        + intros x [<- | [<- | []]]; left; [reflexivity | exact E].
      - simpl. lia. }
    simpl length in Hq, Hp. replace (INR 1) with 1 in Hq by reflexivity.
    rewrite log2_one in Hq. replace (INR 2) with 2 in Hp by (simpl; ring).
    assert (H2 : log2 2 = 1) by (unfold log2; field; apply Rgt_not_eq, ln2_pos).
    lra.
Qed.

(** The three forms together. *)
Theorem one_premise_three_forms :
  (entropy_priced step eq_dec all cost <-> compression_priced step cost eq_dec) /\
  (compression_priced step cost eq_dec <->
     forall i y, (length (fibre i y) <= 2 ^ cost i)%nat) /\
  (merging_steps_priced step cost <-> pair_halving) /\
  (merging_steps_priced step cost <-> pair_entropy_priced).
Proof.
  split; [exact entropy_priced_iff_compression_priced |].
  split; [exact compression_iff_fibre |].
  split; [exact merging_priced_iff_pair_halving | exact merging_priced_iff_pair_entropy].
Qed.

End OnePremise.

Print Assumptions entropy_drop_le_log_support_fibre.
Print Assumptions entropy_drop_le_log_fibre.
Print Assumptions entropy_drop_of_fibre.
Print Assumptions worst_case_entropy_drop.
Print Assumptions entropy_priced_iff_compression_priced.
Print Assumptions merging_priced_iff_pair_halving.
Print Assumptions merging_priced_iff_pair_entropy.
Print Assumptions one_premise_three_forms.
