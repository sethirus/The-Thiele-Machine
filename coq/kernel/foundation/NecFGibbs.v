(** NecFGibbs: when the even-spread drop bound is met exactly.

    The theorem "Entropy after a permanent flip" says the even spread on the
    m + k states loses at least log2 ((m + k) / m) bits. NecFEntropyTight
    shows the bound is met when k is a multiple of m. Here: it is met only
    then. If the even spread loses exactly log2 ((m + k) / m) bits, then k is
    a multiple of m ([nec_f_uniform_drop_exact_only_if_divides]); otherwise
    it loses strictly more ([nec_f_uniform_drop_strict_unless_divides]).

    The tool is the equality case of the entropy bound: a spread whose
    entropy equals log2 of the size of a list covering its support puts
    chance exactly 1 / size on every state it reaches
    ([nec_f_entropy_eq_log_support]); underneath it, ln y < y - 1 for every
    positive y other than 1 ([nec_f_ln_strict]).

    This file uses the real numbers and rests on the standard library's
    classical axioms for them. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Reals Lra.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.
From Kernel Require Import NecFEntropyTight.

Open Scope R_scope.

Lemma nec_f_ln_strict : forall y, 0 < y -> y <> 1 -> ln y < y - 1.
Proof.
  intros y Hy Hne.
  set (t := sqrt y).
  assert (Ht : 0 < t) by (apply sqrt_lt_R0; exact Hy).
  assert (Htt : t * t = y) by (apply sqrt_sqrt; lra).
  assert (Ht1 : t <> 1) by (intro E; apply Hne; rewrite <- Htt, E; ring).
  assert (Hln : ln y = ln t + ln t) by (rewrite <- Htt; apply ln_mult; exact Ht).
  pose proof (ln_le_minus_one t Ht) as Hle.
  assert (Hsq : 0 < (t - 1) * (t - 1)).
  { destruct (Rlt_or_le t 1) as [H | H].
    - assert (0 < 1 - t) by lra. nra.
    - assert (1 < t) by (destruct H; [exact H | exfalso; apply Ht1; symmetry; exact H]). nra. }
  rewrite Hln. rewrite <- Htt. nra.
Qed.

Section Gibbs.

Context {A : Type}.

(** Equality in the entropy bound puts chance 1 / |Sup| on every state with
    positive chance. *)
Theorem nec_f_entropy_eq_log_support :
  forall (l Sup : list A) (r : A -> R),
    NoDup l ->
    distribution l r ->
    (forall a, In a l -> 0 < r a -> In a Sup) ->
    (0 < length Sup)%nat ->
    entropy l r = log2 (INR (length Sup)) ->
    forall a, In a l -> 0 < r a -> INR (length Sup) * r a = 1.
Proof.
  intros l Sup r Hnd [Hnn Hsum] Hsupp HSup Heq.
  set (M := INR (length Sup)).
  assert (HM : 0 < M) by (apply lt_0_INR; exact HSup).
  assert (Hl2 := ln2_pos).
  set (g := fun a => (if positive_b (r a) then / M else 0) - r a).
  set (slack := fun a => g a / ln 2 - (surprisal_term (r a) - log2 M * r a)).
  (* each slack is r a * (y - 1 - ln y) / ln 2 with y = 1 / (M r a), or zero *)
  assert (Hform : forall a, 0 < r a ->
            slack a = r a * (/ (M * r a) - 1 - ln (/ (M * r a))) / ln 2).
  { intros a Hpos. unfold slack, g, positive_b, surprisal_term, log2.
    destruct (Rlt_dec 0 (r a)) as [_ | C]; [| lra].
    rewrite ln_Rinv by nra. rewrite ln_mult by lra. field. split; lra. }
  assert (Hzero : forall a, ~ 0 < r a -> slack a = 0).
  { intros a Hnp. assert (Hz : r a = 0) by (specialize (Hnn a); lra).
    unfold slack, g, positive_b, surprisal_term.
    destruct (Rlt_dec 0 (r a)) as [C | _]; [contradiction |]. rewrite Hz. field. lra. }
  assert (Hnonneg : forall a, 0 <= slack a).
  { intro a. destruct (Rlt_dec 0 (r a)) as [Hp | Hnp]; [| rewrite (Hzero a Hnp); lra].
    rewrite (Hform a Hp).
    assert (Hy : 0 < / (M * r a)) by (apply Rinv_0_lt_compat; nra).
    pose proof (ln_le_minus_one _ Hy). unfold Rdiv.
    apply Rmult_le_pos; [nra | left; apply Rinv_0_lt_compat; exact Hl2]. }
  (* the slacks sum to at most zero *)
  assert (Hsum_slack : rsum l slack <= 0).
  { unfold slack. rewrite rsum_minus, rsum_minus, rsum_scal, Hsum.
    unfold entropy in Heq. fold M in Heq. rewrite Heq.
    unfold Rdiv. rewrite (rsum_ext_in l (fun a => g a * / ln 2) (fun a => / ln 2 * g a)) by (intros; lra).
    rewrite rsum_scal. unfold g. rewrite rsum_minus, Hsum, rsum_indicator.
    assert (Hcount : (length (filter (fun a => positive_b (r a)) l) <= length Sup)%nat).
    { apply NoDup_incl_length; [apply NoDup_filter; exact Hnd |].
      intros a Ha. apply filter_In in Ha as [Hal Hpa]. apply Hsupp; [exact Hal |].
      unfold positive_b in Hpa. destruct (Rlt_dec 0 (r a)); [assumption | discriminate]. }
    apply le_INR in Hcount. fold M in Hcount.
    assert (Hfrac : INR (length (filter (fun a => positive_b (r a)) l)) * / M - 1 <= 0).
    { apply Rmult_le_compat_r with (r := / M) in Hcount; [| left; apply Rinv_0_lt_compat; exact HM].
      rewrite Rinv_r in Hcount by lra. lra. }
    assert (Hil : 0 < / ln 2) by (apply Rinv_0_lt_compat; exact Hl2).
    nra. }
  intros a Ha Hpos.
  assert (Hs0 : slack a = 0).
  { destruct (Rle_lt_or_eq_dec 0 (slack a) (Hnonneg a)) as [Hlt | Heq0]; [| lra].
    exfalso.
    assert (0 < rsum l slack) by (apply rsum_pos_witness; [intros b _; apply Hnonneg | exists a; split; assumption]).
    lra. }
  rewrite (Hform a Hpos) in Hs0.
  set (y := / (M * r a)) in *.
  assert (Hy : 0 < y) by (unfold y; apply Rinv_0_lt_compat; nra).
  assert (Hy1 : y = 1).
  { destruct (Req_dec y 1) as [E | Ne]; [exact E | exfalso].
    pose proof (nec_f_ln_strict y Hy Ne) as Hs.
    assert (Hprod : 0 < r a * (y - 1 - ln y) / ln 2).
    { unfold Rdiv. apply Rmult_lt_0_compat; [nra | apply Rinv_0_lt_compat; exact Hl2]. }
    lra. }
  unfold y in Hy1.
  assert (Hmr : M * r a <> 0) by nra.
  rewrite <- (Rinv_inv (M * r a)), Hy1. apply Rinv_1.
Qed.

End Gibbs.

Section Uniform.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

Theorem nec_f_uniform_drop_exact_only_if_divides :
  forall all i F,
    finite_states all ->
    permanent step cert ->
    flip_list step cert i F ->
    (0 < length F)%nat ->
    entropy all (uniform_on eq_dec (certified_states S cert all ++ F))
    - entropy all (push eq_dec all (fun s => step s i) (uniform_on eq_dec (certified_states S cert all ++ F)))
      = log2 (INR (length (certified_states S cert all) + length F) / INR (length (certified_states S cert all))) ->
    exists j, length F = (j * length (certified_states S cert all))%nat.
Proof.
  intros all i F Hfin Hperm HFl HFpos Hexact.
  set (C := certified_states S cert all) in *.
  set (p := uniform_on eq_dec (C ++ F)) in *.
  set (f := fun s => step s i) in *.
  set (q := push eq_dec all f p) in *.
  assert (HndCF : NoDup (C ++ F)) by (eapply certified_and_flips_nodup; eassumption).
  assert (Hland : forall x, In x (C ++ F) -> In (f x) C)
    by (apply certified_and_flips_land_certified; assumption).
  pose proof HFl as [HndF HF].
  assert (Hex : exists s, In s F)
    by (destruct F as [| s0 F']; [simpl in HFpos; lia | exists s0; left; reflexivity]).
  destruct Hex as [s HsF].
  destruct (HF s HsF) as [Hs0 Hs1].
  assert (Hm : (0 < length C)%nat) by (eapply flip_gives_certified_state; eassumption).
  set (m := length C) in *. set (k := length F) in *.
  assert (HmR : 0 < INR m) by (apply lt_0_INR; exact Hm).
  assert (HmkR : 0 < INR (m + k)) by (apply lt_0_INR; lia).
  assert (Hlen : length (C ++ F) = (m + k)%nat) by (rewrite app_length; reflexivity).
  (* the even spread *)
  assert (Hpd : distribution all p).
  { apply uniform_on_distribution; [exact (proj1 Hfin) | exact HndCF | intros a _; apply (proj2 Hfin) | lia]. }
  assert (Hps : 0 < p s).
  { unfold p, uniform_on, in_b. destruct (in_dec eq_dec s (C ++ F)) as [_ | Hn].
    - rewrite Hlen. apply Rinv_0_lt_compat. exact HmkR.
    - exfalso. apply Hn. apply in_or_app. right. exact HsF. }
  (* entropy before and after *)
  assert (Hp_ent : entropy all p = log2 (INR (m + k))).
  { unfold p. rewrite (uniform_on_entropy eq_dec); [rewrite Hlen; reflexivity | exact (proj1 Hfin) | exact HndCF
                                                   | intros a _; apply (proj2 Hfin) | lia]. }
  assert (Hq_ent : entropy all q = log2 (INR m)).
  { rewrite <- (nec_f_log2_div (INR (m + k)) (INR m)) in Hexact by assumption.
    rewrite Hp_ent in Hexact. lra. }
  (* the pushed spread lives on C *)
  assert (Hqd : distribution all q) by (apply push_distribution; [exact (proj1 Hfin) | exact (proj2 Hfin) | exact Hpd]).
  assert (Hqsupp : forall y, In y all -> 0 < q y -> In y C).
  { intros y Hy Hpos.
    apply (push_support eq_dec all C (C ++ F) f p (proj1 Hpd)); try assumption.
    intros x Hx Hpx. destruct (in_dec eq_dec x (C ++ F)) as [Hin | Hout]; [exact Hin |].
    exfalso. unfold p, uniform_on, in_b in Hpx.
    destruct (in_dec eq_dec x (C ++ F)); [contradiction | lra]. }
  (* the equality case pins q (f s) to 1 / m *)
  assert (Hqfs : 0 < q (f s)).
  { pose proof (push_ge_point eq_dec all f p s (proj1 Hfin) (proj2 Hfin s) (proj1 Hpd)). unfold q. lra. }
  pose proof (nec_f_entropy_eq_log_support all C q (proj1 Hfin) Hqd Hqsupp Hm Hq_ent (f s) (proj2 Hfin _) Hqfs)
    as Hone.
  fold m in Hone.
  (* count the states that land on f s *)
  set (hitp := fun x => andb (if eq_dec (f x) (f s) then true else false) (in_b eq_dec (C ++ F) x)).
  assert (Hq_count : q (f s) = INR (length (filter hitp all)) * / INR (m + k)).
  { unfold q, push. rewrite <- rsum_indicator.
    apply rsum_ext_in. intros x _. unfold hitp, p, uniform_on.
    destruct (eq_dec (f x) (f s)); simpl; [| reflexivity].
    destruct (in_b eq_dec (C ++ F) x); [rewrite Hlen; reflexivity | reflexivity]. }
  rewrite Hq_count in Hone.
  set (c := length (filter hitp all)) in *.
  assert (Hnat : (m * c = m + k)%nat).
  { apply INR_eq. rewrite mult_INR.
    apply (Rmult_eq_reg_r (/ INR (m + k))); [| apply Rinv_neq_0_compat; lra].
    rewrite Rinv_r by lra. lra. }
  destruct c as [| c']; [lia |].
  exists c'. rewrite Nat.mul_succ_r in Hnat. lia.
Qed.

(** When k is not a multiple of m, the even spread loses strictly more than
    log2 ((m + k) / m) bits. *)
Corollary nec_f_uniform_drop_strict_unless_divides :
  forall all i F,
    finite_states all ->
    permanent step cert ->
    flip_list step cert i F ->
    (0 < length F)%nat ->
    (forall j, length F <> (j * length (certified_states S cert all))%nat) ->
    entropy all (uniform_on eq_dec (certified_states S cert all ++ F))
    - entropy all (push eq_dec all (fun s => step s i) (uniform_on eq_dec (certified_states S cert all ++ F)))
      > log2 (INR (length (certified_states S cert all) + length F) / INR (length (certified_states S cert all))).
Proof.
  intros all i F Hfin Hperm HFl HFpos Hnot.
  pose proof (permanent_flip_uniform_entropy_drop S I step cert eq_dec all i F Hfin Hperm HFl HFpos) as Hge.
  cbv zeta in Hge.
  destruct (Rle_lt_or_eq_dec _ _ (Rge_le _ _ Hge)) as [Hlt | Heq]; [lra |].
  exfalso. destruct (nec_f_uniform_drop_exact_only_if_divides all i F Hfin Hperm HFl HFpos (eq_sym Heq))
    as [j Hj].
  exact (Hnot j Hj).
Qed.

(** A step that is one to one forgets nothing: the even spread over any list
    has the same entropy after it as before, so such a step drops no bits and
    the bound above is only about steps that merge. *)
Corollary nec_f_step_entropy_invariant_uniform :
  forall (all U : list S) (f : S -> S),
    NoDup all -> (forall a, In a all) ->
    (forall x y, f x = f y -> x = y) ->
    entropy all (push eq_dec all f (uniform_on eq_dec U)) = entropy all (uniform_on eq_dec U).
Proof.
  intros all U f Hnd Hall Hinj.
  apply step_entropy_invariant_if_injective; assumption.
Qed.

End Uniform.

Print Assumptions nec_f_ln_strict.
Print Assumptions nec_f_entropy_eq_log_support.
Print Assumptions nec_f_uniform_drop_exact_only_if_divides.
Print Assumptions nec_f_uniform_drop_strict_unless_divides.
Print Assumptions nec_f_step_entropy_invariant_uniform.
