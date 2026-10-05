
(* ================================================================= *)
(* PAY.                                                               *)
(* ================================================================= *)

(* PAY, last part (after the paid step): INC GPC, back to HEAD. *)
Theorem pu_hPAYH_post : forall o Ph s,
  subcode (o, pu_hPAYH o) (1, Ph) -> hpc s = 1 + o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    hv s' pu_T4 = hv s pu_T4 /\ pu_hframe [pu_GPC; pu_T4] s s'.
Proof.
  intros o Ph s Hsc Hpc He. unfold pu_hPAYH in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 S0 S1.
  destruct (pu_hINC_spec pu_GPC (1 + o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (2 + o) Ph s1 S1 P1 ltac:(pu_herr_tac))
    as (s2 & R2 & P2 & V2 & F2).
  assert (KT : True) by exact I.
  exists s2. split; [pu_chain |]. split; [exact P2 |].
  split; [pu_track pu_GPC KT; congruence |]. split; [pu_track pu_T4 KT; congruence |].
  pu_frame_goal.
Qed.

Lemma pu_U_PAY : subcode (pu_L_PAY, pu_hPAY pu_L_PAY) (1, U_P).
Proof. pose proof pu_U_PAYH as H. unfold pu_hPAYH in H. pu_sc_split H H1 H2. exact H1. Qed.

(* A guest PAY: the host pays 1 at its own PAY and goes back to HEAD with
   GPC one higher; nothing else moves. *)
Theorem pu_phase_pay : forall P s,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some E.PAY ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, r <> pu_GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s E.PAY Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler E.PAY) with pu_L_PAY in P1. change (pu_arg_of E.PAY) with 0 in A1.
  destruct (pu_hrun_same_sub _ _ _ _ _ R1) as (Fa1 & Ch1 & Er1 & Mu1 & Ce1).
  pose proof (pu_hPAY_pass pu_L_PAY U_P s1 pu_U_PAY P1 E1) as Hs2.
  set (s2 := hrun_prog 1 U_P s1) in *.
  assert (F2 : pu_hframe [] s1 s2)
    by (apply pu_all_same_hframe; intro d; rewrite Hs2; split; reflexivity).
  assert (P2 : hpc s2 = 1 + pu_L_PAY) by (rewrite Hs2; reflexivity).
  assert (Er2 : herr s2 = false) by (rewrite Hs2; exact E1).
  destruct (pu_hPAYH_post pu_L_PAY U_P s2 pu_U_PAYH P2 Er2) as (s3 & R3 & P3 & G3 & W3 & F3).
  destruct (pu_hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KT : True) by exact I.
  assert (AH : pu_at_head P s3).
  { unfold pu_at_head. split; [exact P3 |]. split; [pu_cc |].
    split; [pu_track pu_PROG KT; pu_cc |]. apply pu_scratch_all; pu_zero_goal KT. }
  exists s3. split.
  { apply (pu_hreach_trans s s1 s3); [apply pu_Hrun_hreach, R1 |].
    apply (pu_hreach_trans s1 s2 s3); [apply pu_hreach_one | apply pu_Hrun_hreach, R3]. }
  split; [exact AH |]. split; [pu_track pu_GPC KT; pu_cc |].
  rewrite Hs2 in Fa3, Ch3, Mu3, Ce3.
  cbn [M.core_of M.mu M.cert M.goto M.facts M.chan] in Fa3, Ch3, Mu3, Ce3.
  split; [pu_cc |]. split; [pu_cc |]. split; [lia |]. split; [pu_cc |]. split.
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ pu_scratch r /\ r <> pu_GPC) by (split; assumption). pu_track r K. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

