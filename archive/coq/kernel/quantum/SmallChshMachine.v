(** SmallChshMachine.v: the integer CHSH check as an earned check on the
    small machine.

    The machine is the one of EarnedMulti.v, unchanged: counters indexed by
    natural numbers, the instructions INC, DEC, HALT, CHECK, COMMIT and
    CERTIFY, a fact table, a commitment channel, a trap latch, a ledger and
    a certified flag. Its property language is left open there; this file
    fills it with one property, small_chsh_PCHSH.

    A CHECK reads one counter. The eight CHSH counts therefore travel in one
    counter, as a code: the list [same00; diff00; same01; diff01; same10;
    diff10; same11; diff11] under the list code of EarnedGeneric.v (0 is the
    empty list, 2^x * (2y + 1) is x followed by the list y). small_chsh_code
    writes a tally as a number, and small_chsh_tally_of reads any number
    back as a tally (missing entries read as 0); reading a code gives back
    exactly the tally that was written (small_chsh_tally_of_code).

    PCHSH holds of a counter value when its tally passes the integer check
    of SmallChshCheck.v, and its meaning is that every question pair was
    sampled and the pinned five-by-five moment matrix is symmetric and
    positive semidefinite. The two agree for every value
    (small_chsh_eval_iff).

    Headline results.
      small_chsh_flag_implies_tsirelson: from a clean start, a raised flag
        means the run contains CHECK PCHSH c, then COMMIT PCHSH c, then
        CERTIFY; the counter c held, at the CHECK, a tally that passes the
        integer check, whose pinned matrix is PSD, and whose score S obeys
        S^2 <= 8 and |S| <= 2 sqrt 2; and c still held that same value at
        the COMMIT.
      small_chsh_program_flag_implies_tsirelson: the same for any stored
        program run from a start.
      small_chsh_tally_certifies_iff: the chain CHECK, COMMIT, CERTIFY on a
        counter holding the code of a tally certifies exactly when the
        integer check passes; when it passes the run pays exactly 3, and
        when it fails no number of further steps raises the flag.
      Concrete tallies: two that pass (S = 12/5 and S = 14/5, the second
        just under 2 sqrt 2) and three that are refused forever (S = 16/5,
        above the bound; the PR box at S = 4; and the all-ones classical
        plan at S = 2, which shows the check is stricter than the bound).

    Dependencies: EarnedMulti.v and EarnedGeneric.v (Coq standard library
    only) and SmallChshCheck.v.                                               *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   fills the property language of the machine of EarnedMulti.v with the CHSH
   check and proves what a raised flag means. The machine as a
   CertificationSystem, with the floor of 3 for a certified run, lives in
   SmallChshLinks.v. *)

From Coq Require Import List Arith Lia Bool Reals Lra ZArith.
Import ListNotations.
Require Import Minimal.EarnedMulti.
Require Minimal.EarnedGeneric.
From Kernel Require Import TsirelsonFromAlgebra.
Require Import Kernel.SmallChshCheck.

(* ================================================================= *)
(* The property language.                                            *)
(* ================================================================= *)

Inductive small_chsh_prop : Type :=
| small_chsh_PCHSH.   (* the counter's tally passes the CHSH check *)

(* Equality of the one property, by cases on both sides. *)
Definition small_chsh_prop_eqb (p q : small_chsh_prop) : bool :=
  match p, q with small_chsh_PCHSH, small_chsh_PCHSH => true end.

Lemma small_chsh_prop_eqb_eq : forall p q, small_chsh_prop_eqb p q = true <-> p = q.
Proof. intros [] []. split; reflexivity. Qed.

(* A counter value read as a tally. *)
Definition small_chsh_tally_of (v : nat) : small_chsh_tally :=
  let l := Minimal.EarnedGeneric.decode v in
  small_chsh_mk (nth 0 l 0) (nth 1 l 0) (nth 2 l 0) (nth 3 l 0)
                (nth 4 l 0) (nth 5 l 0) (nth 6 l 0) (nth 7 l 0).

(* A tally written as a counter value. *)
Definition small_chsh_code (t : small_chsh_tally) : nat :=
  Minimal.EarnedGeneric.encode
    [t.(small_chsh_same00); t.(small_chsh_diff00);
     t.(small_chsh_same01); t.(small_chsh_diff01);
     t.(small_chsh_same10); t.(small_chsh_diff10);
     t.(small_chsh_same11); t.(small_chsh_diff11)].

Theorem small_chsh_tally_of_code : forall t, small_chsh_tally_of (small_chsh_code t) = t.
Proof.
  intros [a b c d e f g h]. unfold small_chsh_tally_of, small_chsh_code.
  rewrite Minimal.EarnedGeneric.decode_encode. reflexivity.
Qed.

Definition small_chsh_eval (p : small_chsh_prop) (v : nat) : bool :=
  match p with small_chsh_PCHSH => small_chsh_check (small_chsh_tally_of v) end.

Definition small_chsh_holds (p : small_chsh_prop) (v : nat) : Prop :=
  match p with small_chsh_PCHSH => small_chsh_meaning (small_chsh_tally_of v) end.

Theorem small_chsh_eval_iff : forall p v,
  small_chsh_eval p v = true <-> small_chsh_holds p v.
Proof. intros [] v. apply small_chsh_check_iff. Qed.

(* ================================================================= *)
(* The payoff: a raised flag means the Tsirelson bound.              *)
(* ================================================================= *)

(* A counter untouched through a stretch of run keeps its value. *)
Lemma small_chsh_untouched_vals : forall mid (s : @state small_chsh_prop) c,
  untouched small_chsh_prop_eqb small_chsh_eval s mid c ->
  vals (core_of (run small_chsh_prop_eqb small_chsh_eval mid s)) c
    = vals (core_of s) c.
Proof.
  induction mid as [| i mid IH]; intros s c H; [reflexivity |].
  simpl. rewrite IH.
  - destruct (H [] i mid eq_refl) as [_ Hv]. exact Hv.
  - intros t1 j t2 Ht. apply (H (i :: t1) j t2). rewrite Ht. reflexivity.
Qed.

Theorem small_chsh_flag_implies_tsirelson :
  forall (s0 : @state small_chsh_prop) (tr : list (@instr small_chsh_prop)),
  clean_start s0 ->
  cert (run small_chsh_prop_eqb small_chsh_eval tr s0) = true ->
  exists pre1 c mid1 mid2 post,
    tr = pre1 ++ CHECK small_chsh_PCHSH c :: mid1
           ++ COMMIT small_chsh_PCHSH c :: mid2 ++ CERTIFY :: post /\
    let v := vals (core_of (run small_chsh_prop_eqb small_chsh_eval pre1 s0)) c in
    let t := small_chsh_tally_of v in
    small_chsh_check t = true /\
    small_chsh_meaning t /\
    (small_chsh_score t * small_chsh_score t <= 8)%R /\
    (Rabs (small_chsh_score t) <= 2 * sqrt 2)%R /\
    vals (core_of (run small_chsh_prop_eqb small_chsh_eval
                    (pre1 ++ CHECK small_chsh_PCHSH c :: mid1) s0)) c = v.
Proof.
  intros s0 tr H0 H1.
  destruct (multi_earned_certification_provenance small_chsh_prop_eqb
              small_chsh_prop_eqb_eq small_chsh_eval s0 tr H0 H1)
    as [pre1 [p [c [mid1 [mid2 [post [Htr [Hck [_ [_ [_ Hun]]]]]]]]]]].
  destruct p.
  exists pre1, c, mid1, mid2, post. split; [exact Htr |].
  cbv zeta.
  assert (Hpass : small_chsh_check
            (small_chsh_tally_of
               (vals (core_of (run small_chsh_prop_eqb small_chsh_eval pre1 s0)) c))
          = true).
  { unfold check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
    apply andb_true_iff in Hck as [_ Hck]. exact Hck. }
  pose proof (proj1 (small_chsh_check_iff _) Hpass) as Hmean.
  destruct (small_chsh_meaning_tsirelson _ Hmean) as [Hsq Habs].
  split; [exact Hpass |]. split; [exact Hmean |].
  split; [exact Hsq |]. split; [exact Habs |].
  replace (pre1 ++ CHECK small_chsh_PCHSH c :: mid1)
    with ((pre1 ++ [CHECK small_chsh_PCHSH c]) ++ mid1)
    by (rewrite <- app_assoc; reflexivity).
  rewrite multi_run_app, small_chsh_untouched_vals by exact Hun.
  rewrite multi_run_snoc. simpl. rewrite multi_val_check. reflexivity.
Qed.

(* The same, for a stored program run from any start. *)
Theorem small_chsh_program_flag_implies_tsirelson :
  forall n (P : list (@instr small_chsh_prop)) vs,
  cert (run_prog small_chsh_prop_eqb small_chsh_eval n P (start vs)) = true ->
  exists pre1 c rest,
    trace_of small_chsh_prop_eqb small_chsh_eval n P (start vs)
      = pre1 ++ CHECK small_chsh_PCHSH c :: rest /\
    let t := small_chsh_tally_of
               (vals (core_of (run small_chsh_prop_eqb small_chsh_eval pre1 (start vs))) c) in
    small_chsh_check t = true /\
    small_chsh_meaning t /\
    (small_chsh_score t * small_chsh_score t <= 8)%R /\
    (Rabs (small_chsh_score t) <= 2 * sqrt 2)%R.
Proof.
  intros n P vs H. rewrite multi_run_prog_trace in H.
  destruct (small_chsh_flag_implies_tsirelson (start vs) _ (multi_start_clean vs) H)
    as [pre1 [c [mid1 [mid2 [post [Htr [Hc [Hm [Hs [Ha _]]]]]]]]]].
  exists pre1, c, (mid1 ++ COMMIT small_chsh_PCHSH c :: mid2 ++ CERTIFY :: post).
  split; [exact Htr |]. cbv zeta. auto.
Qed.

(* ================================================================= *)
(* The chain CHECK PCHSH, COMMIT PCHSH, CERTIFY.                     *)
(* ================================================================= *)

Definition small_chsh_chain (c : nat) : list (@instr small_chsh_prop) :=
  chain small_chsh_PCHSH c.

(* On any start, the chain certifies exactly when the tally read from
   counter c passes the integer check. *)
Theorem small_chsh_chain_certifies_iff : forall c vs,
  cert (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain c) (start vs))
    = true <->
  small_chsh_check (small_chsh_tally_of (vs c)) = true.
Proof.
  intros c vs. unfold small_chsh_chain.
  rewrite (multi_chain_certifies_iff small_chsh_prop_eqb small_chsh_prop_eqb_eq
             small_chsh_eval small_chsh_holds small_chsh_eval_iff).
  simpl. symmetry. apply small_chsh_check_iff.
Qed.

(* With the code of a tally in counter c: certified exactly when the
   integer check passes, equivalently when the pinned matrix is PSD with
   every pair sampled. *)
Theorem small_chsh_tally_certifies_iff : forall t c vs,
  vs c = small_chsh_code t ->
  (cert (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain c) (start vs))
     = true <-> small_chsh_check t = true) /\
  (small_chsh_check t = true <-> small_chsh_meaning t).
Proof.
  intros t c vs Hv. split; [| apply small_chsh_check_iff].
  rewrite small_chsh_chain_certifies_iff, Hv, small_chsh_tally_of_code. reflexivity.
Qed.

Theorem small_chsh_tally_certifies : forall t c vs,
  vs c = small_chsh_code t ->
  small_chsh_check t = true ->
  cert (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain c) (start vs))
    = true /\
  mu (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain c) (start vs))
    = 3.
Proof.
  intros t c vs Hv Hc. unfold small_chsh_chain.
  apply (multi_chain_certifies small_chsh_prop_eqb small_chsh_prop_eqb_eq
           small_chsh_eval small_chsh_holds small_chsh_eval_iff).
  simpl. rewrite Hv, small_chsh_tally_of_code. apply small_chsh_check_iff, Hc.
Qed.

Theorem small_chsh_tally_refused_forever : forall t c vs,
  vs c = small_chsh_code t ->
  small_chsh_check t = false ->
  forall n,
  cert (run_prog small_chsh_prop_eqb small_chsh_eval n (small_chsh_chain c) (start vs))
    = false /\
  (n >= 1 ->
   err (core_of (run_prog small_chsh_prop_eqb small_chsh_eval n (small_chsh_chain c)
                  (start vs))) = true).
Proof.
  intros t c vs Hv Hc n. unfold small_chsh_chain.
  apply (multi_chain_refused_forever small_chsh_prop_eqb small_chsh_eval
           small_chsh_holds small_chsh_eval_iff).
  simpl. rewrite Hv, small_chsh_tally_of_code. intro Hm.
  apply small_chsh_check_iff in Hm. congruence.
Qed.

(* ================================================================= *)
(* Concrete tallies.                                                  *)
(* ================================================================= *)

(* The start used below: every counter holds the code of the tally, and
   the chain runs on counter 0. *)
Definition small_chsh_start (t : small_chsh_tally) : @state small_chsh_prop :=
  start (fun _ => small_chsh_code t).

(* (same, diff) = (4, 1), (4, 1), (4, 1), (1, 4): correlators 3/5, 3/5,
   3/5, -3/5 and S = 12/5, above the classical 2 and below 2 sqrt 2. *)
Definition small_chsh_tally_12_5 : small_chsh_tally :=
  small_chsh_mk 4 1 4 1 4 1 1 4.

(* (17, 3) three times and (3, 17): correlators 7/10, 7/10, 7/10, -7/10
   and S = 14/5 = 2.8, the rational stand-in just under 2 sqrt 2. *)
Definition small_chsh_tally_14_5 : small_chsh_tally :=
  small_chsh_mk 17 3 17 3 17 3 3 17.

(* (9, 1) three times and (1, 9): correlators 4/5, 4/5, 4/5, -4/5 and
   S = 16/5 = 3.2, above 2 sqrt 2. *)
Definition small_chsh_tally_16_5 : small_chsh_tally :=
  small_chsh_mk 9 1 9 1 9 1 1 9.

(* The PR box: always match on the first three pairs, always differ on
   the last, S = 4. *)
Definition small_chsh_tally_pr_box : small_chsh_tally :=
  small_chsh_mk 1 0 1 0 1 0 0 1.

(* The all-ones classical plan: always match, S = 2. *)
Definition small_chsh_tally_all_ones : small_chsh_tally :=
  small_chsh_mk 1 0 1 0 1 0 1 0.

Lemma small_chsh_score_12_5 : (small_chsh_score small_chsh_tally_12_5 = 12 / 5)%R.
Proof.
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01, small_chsh_e10,
    small_chsh_e11, small_chsh_corr. simpl. field.
Qed.

Lemma small_chsh_score_14_5 : (small_chsh_score small_chsh_tally_14_5 = 14 / 5)%R.
Proof.
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01, small_chsh_e10,
    small_chsh_e11, small_chsh_corr. simpl. field.
Qed.

Lemma small_chsh_score_16_5 : (small_chsh_score small_chsh_tally_16_5 = 16 / 5)%R.
Proof.
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01, small_chsh_e10,
    small_chsh_e11, small_chsh_corr. simpl. field.
Qed.

Lemma small_chsh_score_pr_box : (small_chsh_score small_chsh_tally_pr_box = 4)%R.
Proof.
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01, small_chsh_e10,
    small_chsh_e11, small_chsh_corr. simpl. field.
Qed.

Lemma small_chsh_score_all_ones : (small_chsh_score small_chsh_tally_all_ones = 2)%R.
Proof.
  unfold small_chsh_score, CHSH_value, small_chsh_e00, small_chsh_e01, small_chsh_e10,
    small_chsh_e11, small_chsh_corr. simpl. field.
Qed.

(* S = 12/5 passes: the flag rises at cost 3, and S^2 <= 8. *)
Theorem small_chsh_demo_12_5_certifies :
  small_chsh_check small_chsh_tally_12_5 = true /\
  (small_chsh_score small_chsh_tally_12_5 = 12 / 5)%R /\
  cert (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_12_5)) = true /\
  mu (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_12_5)) = 3.
Proof.
  assert (Hc : small_chsh_check small_chsh_tally_12_5 = true) by reflexivity.
  split; [exact Hc |]. split; [exact small_chsh_score_12_5 |].
  exact (small_chsh_tally_certifies small_chsh_tally_12_5 0 (fun _ => small_chsh_code small_chsh_tally_12_5) eq_refl Hc).
Qed.

(* S = 14/5 passes too, with S^2 = 196/25 <= 8 = 200/25. *)
Theorem small_chsh_demo_14_5_certifies :
  small_chsh_check small_chsh_tally_14_5 = true /\
  (small_chsh_score small_chsh_tally_14_5 = 14 / 5)%R /\
  cert (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_14_5)) = true /\
  mu (run_prog small_chsh_prop_eqb small_chsh_eval 4 (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_14_5)) = 3.
Proof.
  assert (Hc : small_chsh_check small_chsh_tally_14_5 = true) by reflexivity.
  split; [exact Hc |]. split; [exact small_chsh_score_14_5 |].
  exact (small_chsh_tally_certifies small_chsh_tally_14_5 0 (fun _ => small_chsh_code small_chsh_tally_14_5) eq_refl Hc).
Qed.

(* S = 16/5 is above the bound (S^2 = 256/25 > 8): the check fails, the
   CHECK traps, and the flag never rises. *)
Theorem small_chsh_demo_16_5_refused_forever :
  small_chsh_check small_chsh_tally_16_5 = false /\
  (small_chsh_score small_chsh_tally_16_5 * small_chsh_score small_chsh_tally_16_5 > 8)%R /\
  forall n,
  cert (run_prog small_chsh_prop_eqb small_chsh_eval n (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_16_5)) = false.
Proof.
  assert (Hc : small_chsh_check small_chsh_tally_16_5 = false) by reflexivity.
  split; [exact Hc |]. split; [rewrite small_chsh_score_16_5; lra |].
  intro n. exact (proj1 (small_chsh_tally_refused_forever small_chsh_tally_16_5 0 (fun _ => small_chsh_code small_chsh_tally_16_5) eq_refl Hc n)).
Qed.

(* The PR box, S = 4, is refused forever. *)
Theorem small_chsh_demo_pr_box_refused_forever :
  small_chsh_check small_chsh_tally_pr_box = false /\
  (small_chsh_score small_chsh_tally_pr_box = 4)%R /\
  forall n,
  cert (run_prog small_chsh_prop_eqb small_chsh_eval n (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_pr_box)) = false.
Proof.
  assert (Hc : small_chsh_check small_chsh_tally_pr_box = false) by reflexivity.
  split; [exact Hc |]. split; [exact small_chsh_score_pr_box |].
  intro n. exact (proj1 (small_chsh_tally_refused_forever small_chsh_tally_pr_box 0 (fun _ => small_chsh_code small_chsh_tally_pr_box) eq_refl Hc n)).
Qed.

(* The all-ones classical plan, S = 2, under the bound, is refused too:
   the check is sufficient for the bound, not necessary. *)
Theorem small_chsh_demo_all_ones_refused_forever :
  small_chsh_check small_chsh_tally_all_ones = false /\
  (small_chsh_score small_chsh_tally_all_ones = 2)%R /\
  forall n,
  cert (run_prog small_chsh_prop_eqb small_chsh_eval n (small_chsh_chain 0)
          (small_chsh_start small_chsh_tally_all_ones)) = false.
Proof.
  assert (Hc : small_chsh_check small_chsh_tally_all_ones = false) by reflexivity.
  split; [exact Hc |]. split; [exact small_chsh_score_all_ones |].
  intro n. exact (proj1 (small_chsh_tally_refused_forever small_chsh_tally_all_ones 0 (fun _ => small_chsh_code small_chsh_tally_all_ones) eq_refl Hc n)).
Qed.

Print Assumptions small_chsh_tally_of_code.
Print Assumptions small_chsh_eval_iff.
Print Assumptions small_chsh_flag_implies_tsirelson.
Print Assumptions small_chsh_program_flag_implies_tsirelson.
Print Assumptions small_chsh_chain_certifies_iff.
Print Assumptions small_chsh_tally_certifies_iff.
Print Assumptions small_chsh_tally_certifies.
Print Assumptions small_chsh_tally_refused_forever.
Print Assumptions small_chsh_demo_12_5_certifies.
Print Assumptions small_chsh_demo_14_5_certifies.
Print Assumptions small_chsh_demo_16_5_refused_forever.
Print Assumptions small_chsh_demo_pr_box_refused_forever.
Print Assumptions small_chsh_demo_all_ones_refused_forever.
