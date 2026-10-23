From Coq Require Import List Arith Lia Bool.
Require Minimal.EarnedCore.
Import ListNotations.
Module E := Minimal.EarnedCore.

(* A concrete structural quantity the ACTUAL ledger does account for:
   appended fact records, including duplicates, not distinct truths. *)
Definition check_gain (k : E.core) (i : E.instr) : nat :=
  if E.err k then 0 else
  match i with E.CHECK p c => if E.check_ok k p c then 1 else 0 | _ => 0 end.

Lemma fact_length_one_step : forall k i,
  length (E.facts (E.cexec k i))=length (E.facts k)+check_gain k i.
Proof.
  intros k i; unfold E.cexec,check_gain; destruct (E.err k); [lia|].
  destruct i as [c|c j| |p c|p c|]; simpl.
  - rewrite E.facts_write; lia.
  - destruct (E.val k c); simpl; [lia|rewrite E.facts_write; lia].
  - lia.
  - destruct (E.check_ok k p c); simpl; lia.
  - destruct (E.commit_ok k p c); simpl; lia.
  - destruct (E.certify_ok k); simpl; lia.
Qed.
Lemma successful_check_is_priced : forall k i, check_gain k i<=E.cost i.
Proof.
  intros k i; unfold check_gain; destruct (E.err k); [lia|].
  destruct i; simpl; try lia; destruct (E.check_ok k p c); lia.
Qed.

Fixpoint passing_checks (tr : list E.instr) (s : E.state) : nat :=
  match tr with []=>0 | i::rest => check_gain (E.core_of s) i + passing_checks rest (E.exec s i) end.

Theorem actual_fact_growth_exact : forall tr s,
  length (E.facts (E.core_of (E.run tr s))) =
    length (E.facts (E.core_of s))+passing_checks tr s.
Proof.
  induction tr as [|i tr IH]; intro s; [simpl; lia|].
  change (length (E.facts (E.core_of (E.run tr (E.exec s i))))=
    length (E.facts (E.core_of s))+
    (check_gain (E.core_of s) i+passing_checks tr (E.exec s i))).
  rewrite IH; change (length (E.facts (E.cexec (E.core_of s) i))+
    passing_checks tr (E.exec s i)=length (E.facts (E.core_of s))+
    (check_gain (E.core_of s) i+passing_checks tr (E.exec s i))).
  rewrite fact_length_one_step; lia.
Qed.
Theorem passing_checks_bounded_by_actual_cost : forall tr s,
  passing_checks tr s<=E.total_cost tr.
Proof.
  induction tr as [|i tr IH]; intro s; simpl; [lia|].
  pose proof (IH (E.exec s i)); pose proof (successful_check_is_priced (E.core_of s) i); lia.
Qed.
Theorem actual_ledger_bounds_fact_growth : forall tr s,
  E.mu s+passing_checks tr s<=E.mu (E.run tr s).
Proof.
  intros tr s; rewrite E.mu_conservation_trace.
  pose proof (passing_checks_bounded_by_actual_cost tr s); lia.
Qed.
Theorem actual_ledger_bounds_table_growth : forall tr s,
  E.mu s+length (E.facts (E.core_of (E.run tr s))) <=
    E.mu (E.run tr s)+length (E.facts (E.core_of s)).
Proof.
  intros tr s; rewrite actual_fact_growth_exact.
  pose proof (actual_ledger_bounds_fact_growth tr s); lia.
Qed.
Theorem stored_program_ledger_bounds_table_growth : forall n P a b,
  length (E.facts (E.core_of (E.run_prog n P (E.start a b)))) <=
    E.mu (E.run_prog n P (E.start a b)).
Proof.
  intros n P a b; rewrite E.run_prog_trace.
  pose proof (actual_ledger_bounds_table_growth (E.trace_of n P (E.start a b)) (E.start a b)) as H.
  simpl in H; lia.
Qed.
Theorem table_growth_bound_is_attained :
  passing_checks [E.CHECK E.PZero E.CA] (E.start 0 0)=1 /\
  E.mu (E.run [E.CHECK E.PZero E.CA] (E.start 0 0))=1.
Proof. split; reflexivity. Qed.
