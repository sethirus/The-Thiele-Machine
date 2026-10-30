(** The tolerance check as CHECK on EarnedMulti's versioned registers.
    The tolerance is fixed for this machine instance. A successful earned
    chain has the relaxed bound, not the exact Tsirelson bound. *)
From Coq Require Import List Arith Lia Bool Reals ZArith.
Import ListNotations.
From Kernel Require Import SmallChshCheck SmallChshMachine CHSHColumnCheck NecEChsh.
From Kernel Require Import UniversalCertificationCost.
Require Minimal.EarnedMulti.
Module TM := Minimal.EarnedMulti.

Definition small_chsh_witness (t : small_chsh_tally) : WitnessCounts :=
  {| wc_same_00 := small_chsh_same00 t; wc_diff_00 := small_chsh_diff00 t;
     wc_same_01 := small_chsh_same01 t; wc_diff_01 := small_chsh_diff01 t;
     wc_same_10 := small_chsh_same10 t; wc_diff_10 := small_chsh_diff10 t;
     wc_same_11 := small_chsh_same11 t; wc_diff_11 := small_chsh_diff11 t |}.

Definition small_chsh_tol_eval (p q : Z) (_ : small_chsh_prop) (v : nat) : bool :=
  nec_e_tol_check p q (small_chsh_witness (small_chsh_tally_of v)).

Theorem small_chsh_tol_zero : forall c v,
  small_chsh_tol_eval 0 1 c v = small_chsh_eval c v.
Proof.
  intros [] v. unfold small_chsh_tol_eval, small_chsh_eval.
  rewrite nec_e_tol_check_zero. reflexivity.
Qed.

(* These are operational acceptance theorems. The mathematical meaning of
   acceptance is proved separately by small_chsh_tol_flag_bound below. *)
Theorem small_chsh_tol_chain_iff : forall p q c vs,
  TM.cert (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval p q)
    4 (small_chsh_chain c) (TM.start vs)) = true <->
  nec_e_tol_check p q (small_chsh_witness (small_chsh_tally_of (vs c))) = true.
Proof.
  intros p q c vs. unfold small_chsh_chain.
  exact (TM.multi_chain_certifies_iff small_chsh_prop_eqb small_chsh_prop_eqb_eq
    (small_chsh_tol_eval p q) (fun c v => small_chsh_tol_eval p q c v = true)
    (fun _ _ => iff_refl _) small_chsh_PCHSH c vs).
Qed.

Theorem small_chsh_tol_chain_pays_three : forall p q c vs,
  nec_e_tol_check p q (small_chsh_witness (small_chsh_tally_of (vs c))) = true ->
  TM.cert (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval p q)
    4 (small_chsh_chain c) (TM.start vs)) = true /\
  TM.mu (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval p q)
    4 (small_chsh_chain c) (TM.start vs)) = 3.
Proof.
  intros p q c vs H. unfold small_chsh_chain.
  apply (TM.multi_chain_certifies small_chsh_prop_eqb small_chsh_prop_eqb_eq
    (small_chsh_tol_eval p q) (fun c v => small_chsh_tol_eval p q c v = true)
    (fun _ _ => iff_refl _)). exact H.
Qed.

Theorem small_chsh_tol_refused_forever : forall p q c vs,
  nec_e_tol_check p q (small_chsh_witness (small_chsh_tally_of (vs c))) = false ->
  forall n,
  TM.cert (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval p q)
    n (small_chsh_chain c) (TM.start vs)) = false /\
  (n >= 1 -> TM.err (TM.core_of (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval p q)
    n (small_chsh_chain c) (TM.start vs))) = true).
Proof.
  intros p q c vs H n. unfold small_chsh_chain.
  apply (TM.multi_chain_refused_forever small_chsh_prop_eqb
    (small_chsh_tol_eval p q) (fun c v => small_chsh_tol_eval p q c v = true)
    (fun _ _ => iff_refl _)). unfold small_chsh_tol_eval. congruence.
Qed.

Lemma small_chsh_tol_untouched : forall p q mid (s : @TM.state small_chsh_prop) c,
  TM.untouched small_chsh_prop_eqb (small_chsh_tol_eval p q) s mid c ->
  TM.vals (TM.core_of (TM.run small_chsh_prop_eqb (small_chsh_tol_eval p q) mid s)) c
    = TM.vals (TM.core_of s) c.
Proof.
  intros p q mid. induction mid as [| i mid IH]; intros s c H; [reflexivity |].
  simpl. rewrite IH.
  - destruct (H [] i mid eq_refl) as [_ Hv]. exact Hv.
  - intros t1 j t2 Ht. apply (H (i :: t1) j t2). rewrite Ht. reflexivity.
Qed.

Theorem small_chsh_tol_flag_bound : forall p q (s0 : @TM.state small_chsh_prop) tr,
  TM.clean_start s0 ->
  TM.cert (TM.run small_chsh_prop_eqb (small_chsh_tol_eval p q) tr s0) = true ->
  exists pre c mid1 mid2 post,
    tr = pre ++ TM.CHECK small_chsh_PCHSH c :: mid1 ++
      TM.COMMIT small_chsh_PCHSH c :: mid2 ++ TM.CERTIFY :: post /\
    let v := TM.vals (TM.core_of (TM.run small_chsh_prop_eqb (small_chsh_tol_eval p q) pre s0)) c in
    let t := small_chsh_tally_of v in
    nec_e_tol_check p q (small_chsh_witness t) = true /\
    (0 < q)%Z /\ (0 <= p)%Z /\
    (small_chsh_score t * small_chsh_score t <=
      8 * ((1 + IZR p / IZR q) * (1 + IZR p / IZR q)))%R /\
    TM.vals (TM.core_of (TM.run small_chsh_prop_eqb (small_chsh_tol_eval p q)
      (pre ++ TM.CHECK small_chsh_PCHSH c :: mid1) s0)) c = v.
Proof.
  intros p q s0 tr H0 H1.
  destruct (TM.multi_earned_certification_provenance small_chsh_prop_eqb
    small_chsh_prop_eqb_eq (small_chsh_tol_eval p q) s0 tr H0 H1)
    as [pre [pr [c [mid1 [mid2 [post [Htr [Hck [_ [_ [_ Hun]]]]]]]]]]].
  destruct pr. exists pre, c, mid1, mid2, post. split; [exact Htr |]. cbv zeta.
  unfold TM.check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
  apply andb_true_iff in Hck as [_ Hck].
  unfold small_chsh_tol_eval in Hck.
  split; [exact Hck |].
  destruct (nec_e_tol_check_sound _ _ _ Hck) as [Hq [Hp _]].
  split; [exact Hq |]. split; [exact Hp |]. split.
  - exact (nec_e_tol_check_bound _ _ _ Hck).
  - replace (pre ++ TM.CHECK small_chsh_PCHSH c :: mid1)
      with ((pre ++ [TM.CHECK small_chsh_PCHSH c]) ++ mid1)
      by (rewrite <- app_assoc; reflexivity).
    rewrite TM.multi_run_app, small_chsh_tol_untouched by exact Hun.
    rewrite TM.multi_run_snoc. simpl. rewrite TM.multi_val_check. reflexivity.
Qed.

Theorem small_chsh_tol_program_bound : forall p q n P vs,
  TM.cert (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval p q) n P (TM.start vs)) = true ->
  exists pre c rest,
    TM.trace_of small_chsh_prop_eqb (small_chsh_tol_eval p q) n P (TM.start vs) =
      pre ++ TM.CHECK small_chsh_PCHSH c :: rest /\
    let t := small_chsh_tally_of (TM.vals (TM.core_of
      (TM.run small_chsh_prop_eqb (small_chsh_tol_eval p q) pre (TM.start vs))) c) in
    (small_chsh_score t * small_chsh_score t <=
      8 * ((1 + IZR p / IZR q) * (1 + IZR p / IZR q)))%R.
Proof.
  intros p q n P vs H. rewrite TM.multi_run_prog_trace in H.
  destruct (small_chsh_tol_flag_bound p q (TM.start vs) _ (TM.multi_start_clean vs) H)
    as [pre [c [mid1 [mid2 [post [Htr [_ [_ [_ [Hb _]]]]]]]]]].
  exists pre, c, (mid1 ++ TM.COMMIT small_chsh_PCHSH c :: mid2 ++ TM.CERTIFY :: post).
  split; assumption.
Qed.

Definition small_chsh_tol_cs (p q : Z) : CertificationSystem :=
  mk_cert_system (@TM.state small_chsh_prop) (@TM.instr small_chsh_prop)
    (TM.exec small_chsh_prop_eqb (small_chsh_tol_eval p q))
    (@TM.cost small_chsh_prop) (@TM.cert small_chsh_prop)
    (TM.multi_a2 small_chsh_prop_eqb (small_chsh_tol_eval p q)).

Lemma small_chsh_tol_cs_cost : forall p q tr,
  cs_total_cost (small_chsh_tol_cs p q) tr = TM.total_cost tr.
Proof. intros p q tr. induction tr; simpl; auto. Qed.

Theorem small_chsh_tol_certified_floor : forall p q s0 tr,
  TM.clean_start s0 ->
  TM.cert (TM.run small_chsh_prop_eqb (small_chsh_tol_eval p q) tr s0) = true ->
  cs_total_cost (small_chsh_tol_cs p q) tr >= 3.
Proof.
  intros p q s0 tr H0 H1. rewrite small_chsh_tol_cs_cost.
  exact (proj1 (TM.multi_certified_run_min_cost small_chsh_prop_eqb
    small_chsh_prop_eqb_eq (small_chsh_tol_eval p q) s0 tr H0 H1)).
Qed.

Theorem small_chsh_tol_noisy_certifies :
  TM.cert (TM.run_prog small_chsh_prop_eqb (small_chsh_tol_eval 1 10)
    4 (small_chsh_chain 0)
    (TM.start (fun _ => small_chsh_code (small_chsh_mk 86 14 85 15 86 14 14 86)))) = true.
Proof.
  apply small_chsh_tol_chain_iff. rewrite small_chsh_tally_of_code.
  vm_compute. reflexivity.
Qed.

Print Assumptions small_chsh_tol_certified_floor.
Print Assumptions small_chsh_tol_noisy_certifies.
Print Assumptions small_chsh_tol_zero.
Print Assumptions small_chsh_tol_chain_iff.
Print Assumptions small_chsh_tol_chain_pays_three.
Print Assumptions small_chsh_tol_refused_forever.
Print Assumptions small_chsh_tol_flag_bound.
Print Assumptions small_chsh_tol_program_bound.
