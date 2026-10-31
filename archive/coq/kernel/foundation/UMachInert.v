(** UMachInert.v: on the register machines of EarnedMulti.v and
    EarnedMultiPriced.v (U's host and U_P's host, with ANY property
    language and ANY checker), the record moves cannot do computing work
    for the base.  Two runs of the same program from states with the same
    registers, versions and line, under two arbitrary checkers (and
    property-equality tests), have the same registers, versions and line
    at every step at which neither has trapped.

    So the checker, even one that evaluates a guest's step, or U_P's
    universal routine checker, or an uncomputable one, is invisible to
    the base except through the trap, which ends the run.  On these
    machines everything a run computes, it computes with INC and DEC.  *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedMulti.v and EarnedMultiPriced.v, the two machines this file is
   about: it imports only them and the Coq standard library. Their link to
   the abstract record lives in UniversalInterpreterLinks.v and
   PricedHostLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti.
Require Minimal.EarnedMultiPriced.
Module M := Minimal.EarnedMulti.
Module MP := Minimal.EarnedMultiPriced.

(* ================================================================= *)
(* EarnedMulti (U's host, any property language).                     *)
(* ================================================================= *)

Section Multi.
Context {prop : Type}.

Definition bsame (k1 k2 : @M.core prop) : Prop :=
  (forall r, M.vals k1 r = M.vals k2 r) /\ (forall r, M.vers k1 r = M.vers k2 r) /\
  M.pc k1 = M.pc k2.

Lemma err_stays : forall eq ev n Q (s : @M.state prop),
  M.err (M.core_of s) = true -> M.run_prog eq ev n Q s = s.
Proof.
  intros eq ev n Q s H. apply M.multi_run_prog_halted. unfold M.halted, M.next_instr.
  rewrite H. reflexivity.
Qed.

Lemma step_untrapped_before : forall eq ev n Q (s : @M.state prop),
  M.err (M.core_of (M.run_prog eq ev n Q s)) = false -> M.err (M.core_of s) = false.
Proof.
  intros eq ev n Q s H. destruct (M.err (M.core_of s)) eqn:E; [| reflexivity].
  rewrite err_stays in H by exact E. congruence.
Qed.

Lemma one_step : forall eq1 ev1 eq2 ev2 (i : @M.instr prop) (k1 k2 : @M.core prop),
  M.err k1 = false -> M.err k2 = false -> bsame k1 k2 ->
  M.err (M.cexec eq1 ev1 k1 i) = false -> M.err (M.cexec eq2 ev2 k2 i) = false ->
  bsame (M.cexec eq1 ev1 k1 i) (M.cexec eq2 ev2 k2 i).
Proof.
  intros eq1 ev1 eq2 ev2 i k1 k2 E1 E2 [Hv [Hw Hp]] F1 F2.
  unfold M.cexec in *. rewrite E1 in *. rewrite E2 in *.
  destruct i as [r | r j | | p r | p r |].
  - unfold M.write, M.upd, bsame. simpl. rewrite Hv, Hw, Hp.
    split; [intros x; destruct (Nat.eqb x r); auto |]. split; [intros x; destruct (Nat.eqb x r); auto | auto].
  - rewrite <- Hv. destruct (M.vals k1 r) as [| n].
    + unfold M.goto, bsame. simpl. auto.
    + unfold M.write, M.upd, bsame. simpl. rewrite Hw.
      split; [intros x; destruct (Nat.eqb x r); auto |]. split; [intros x; destruct (Nat.eqb x r); auto | auto].
  - split; [| split]; auto.
  - destruct (M.check_ok ev1 k1 p r), (M.check_ok ev2 k2 p r); simpl in F1, F2;
      try discriminate; unfold bsame; simpl; auto.
  - destruct (M.commit_ok eq1 k1 p r), (M.commit_ok eq2 k2 p r); simpl in F1, F2;
      try discriminate; unfold bsame; simpl; auto.
  - destruct (M.certify_ok k1), (M.certify_ok k2); simpl in F1, F2;
      try discriminate; unfold bsame; simpl; auto.
Qed.

Theorem checker_blind : forall eq1 ev1 eq2 ev2 n Q (s1 s2 : @M.state prop),
  bsame (M.core_of s1) (M.core_of s2) ->
  M.err (M.core_of (M.run_prog eq1 ev1 n Q s1)) = false ->
  M.err (M.core_of (M.run_prog eq2 ev2 n Q s2)) = false ->
  bsame (M.core_of (M.run_prog eq1 ev1 n Q s1)) (M.core_of (M.run_prog eq2 ev2 n Q s2)).
Proof.
  intros eq1 ev1 eq2 ev2 n. induction n as [| n IH]; intros Q s1 s2 B F1 F2; [exact B |].
  change (M.run_prog eq1 ev1 (S n) Q s1) with (M.run_prog eq1 ev1 n Q (M.step eq1 ev1 Q s1)) in *.
  change (M.run_prog eq2 ev2 (S n) Q s2) with (M.run_prog eq2 ev2 n Q (M.step eq2 ev2 Q s2)) in *.
  pose proof (step_untrapped_before eq1 ev1 n Q _ F1) as G1.
  pose proof (step_untrapped_before eq2 ev2 n Q _ F2) as G2.
  apply IH; [| exact F1 | exact F2].
  unfold M.step in *.
  assert (E1 : M.err (M.core_of s1) = false).
  { destruct (M.err (M.core_of s1)) eqn:E; [| reflexivity].
    unfold M.next_instr in G1. rewrite E in G1. simpl in G1. congruence. }
  assert (E2 : M.err (M.core_of s2) = false).
  { destruct (M.err (M.core_of s2)) eqn:E; [| reflexivity].
    unfold M.next_instr in G2. rewrite E in G2. simpl in G2. congruence. }
  assert (N : M.next_instr Q (M.core_of s1) = M.next_instr Q (M.core_of s2)).
  { unfold M.next_instr. rewrite E1, E2. destruct B as [_ [_ ->]]. reflexivity. }
  rewrite <- N in G2 |- *.
  destruct (M.next_instr Q (M.core_of s1)) as [i |]; [| exact B].
  simpl in G1, G2 |- *. apply one_step; assumption.
Qed.

End Multi.

(* ================================================================= *)
(* EarnedMultiPriced (U_P's host, any property language), with PAY.   *)
(* ================================================================= *)

Section Priced.
Context {prop : Type}.

Definition pbsame (k1 k2 : @MP.pu_core prop) : Prop :=
  (forall r, MP.vals k1 r = MP.vals k2 r) /\ (forall r, MP.vers k1 r = MP.vers k2 r) /\
  MP.pc k1 = MP.pc k2.

Lemma perr_stays : forall eq ev n Q (s : @MP.pu_state prop),
  MP.err (MP.core_of s) = true -> MP.pu_run_prog eq ev n Q s = s.
Proof.
  intros eq ev n Q s H. apply MP.pu_multi_run_prog_halted. unfold MP.pu_halted, MP.pu_next_instr.
  rewrite H. reflexivity.
Qed.

Lemma pstep_untrapped_before : forall eq ev n Q (s : @MP.pu_state prop),
  MP.err (MP.core_of (MP.pu_run_prog eq ev n Q s)) = false -> MP.err (MP.core_of s) = false.
Proof.
  intros eq ev n Q s H. destruct (MP.err (MP.core_of s)) eqn:E; [| reflexivity].
  rewrite perr_stays in H by exact E. congruence.
Qed.

Lemma pone_step : forall eq1 ev1 eq2 ev2 (i : @MP.pu_instr prop) (k1 k2 : @MP.pu_core prop),
  MP.err k1 = false -> MP.err k2 = false -> pbsame k1 k2 ->
  MP.err (MP.pu_cexec eq1 ev1 k1 i) = false -> MP.err (MP.pu_cexec eq2 ev2 k2 i) = false ->
  pbsame (MP.pu_cexec eq1 ev1 k1 i) (MP.pu_cexec eq2 ev2 k2 i).
Proof.
  intros eq1 ev1 eq2 ev2 i k1 k2 E1 E2 [Hv [Hw Hp]] F1 F2.
  unfold MP.pu_cexec in *. rewrite E1 in *. rewrite E2 in *.
  destruct i as [r | r j | | p r | p r | |].
  - unfold MP.pu_write, MP.pu_upd, pbsame. simpl. rewrite Hv, Hw, Hp.
    split; [intros x; destruct (Nat.eqb x r); auto |]. split; [intros x; destruct (Nat.eqb x r); auto | auto].
  - rewrite <- Hv. destruct (MP.vals k1 r) as [| n].
    + unfold MP.pu_goto, pbsame. simpl. auto.
    + unfold MP.pu_write, MP.pu_upd, pbsame. simpl. rewrite Hw.
      split; [intros x; destruct (Nat.eqb x r); auto |]. split; [intros x; destruct (Nat.eqb x r); auto | auto].
  - split; [| split]; auto.
  - destruct (MP.pu_check_ok ev1 k1 p r), (MP.pu_check_ok ev2 k2 p r); simpl in F1, F2;
      try discriminate; unfold pbsame; simpl; auto.
  - destruct (MP.pu_commit_ok eq1 k1 p r), (MP.pu_commit_ok eq2 k2 p r); simpl in F1, F2;
      try discriminate; unfold pbsame; simpl; auto.
  - destruct (MP.pu_certify_ok k1), (MP.pu_certify_ok k2); simpl in F1, F2;
      try discriminate; unfold pbsame; simpl; auto.
  - unfold MP.pu_goto, pbsame. simpl. auto.
Qed.

Theorem pchecker_blind : forall eq1 ev1 eq2 ev2 n Q (s1 s2 : @MP.pu_state prop),
  pbsame (MP.core_of s1) (MP.core_of s2) ->
  MP.err (MP.core_of (MP.pu_run_prog eq1 ev1 n Q s1)) = false ->
  MP.err (MP.core_of (MP.pu_run_prog eq2 ev2 n Q s2)) = false ->
  pbsame (MP.core_of (MP.pu_run_prog eq1 ev1 n Q s1)) (MP.core_of (MP.pu_run_prog eq2 ev2 n Q s2)).
Proof.
  intros eq1 ev1 eq2 ev2 n. induction n as [| n IH]; intros Q s1 s2 B F1 F2; [exact B |].
  change (MP.pu_run_prog eq1 ev1 (S n) Q s1) with (MP.pu_run_prog eq1 ev1 n Q (MP.pu_step eq1 ev1 Q s1)) in *.
  change (MP.pu_run_prog eq2 ev2 (S n) Q s2) with (MP.pu_run_prog eq2 ev2 n Q (MP.pu_step eq2 ev2 Q s2)) in *.
  pose proof (pstep_untrapped_before eq1 ev1 n Q _ F1) as G1.
  pose proof (pstep_untrapped_before eq2 ev2 n Q _ F2) as G2.
  apply IH; [| exact F1 | exact F2].
  unfold MP.pu_step in *.
  assert (E1 : MP.err (MP.core_of s1) = false).
  { destruct (MP.err (MP.core_of s1)) eqn:E; [| reflexivity].
    unfold MP.pu_next_instr in G1. rewrite E in G1. simpl in G1. congruence. }
  assert (E2 : MP.err (MP.core_of s2) = false).
  { destruct (MP.err (MP.core_of s2)) eqn:E; [| reflexivity].
    unfold MP.pu_next_instr in G2. rewrite E in G2. simpl in G2. congruence. }
  assert (N : MP.pu_next_instr Q (MP.core_of s1) = MP.pu_next_instr Q (MP.core_of s2)).
  { unfold MP.pu_next_instr. rewrite E1, E2. destruct B as [_ [_ ->]]. reflexivity. }
  rewrite <- N in G2 |- *.
  destruct (MP.pu_next_instr Q (MP.core_of s1)) as [i |]; [| exact B].
  simpl in G1, G2 |- *. apply pone_step; assumption.
Qed.

End Priced.

Print Assumptions checker_blind.
Print Assumptions pchecker_blind.
