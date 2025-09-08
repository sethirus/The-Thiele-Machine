(* Confluence.v: Church–Rosser Confluence and μ Invariance *)

Require Import Relations.
Require Import Permutation.
Require Import Arith.
Require Import List.
Import ListNotations.

(* Import the audited step definitions from SpecSound.v *)
Require Import SpecSound.

(* "Local diamond" for the steps you actually use *)
Definition certs_independent (c1 c2 : Cert) : Prop :=
  cnf c1 <> cnf c2.

Theorem independent_steps_confluence :
  forall s c1 s1 c2 s2,
    audited_step s c1 s1 ->
    audited_step s c2 s2 ->
    certs_independent c1 c2 ->
    proof_ok c1 ->
    proof_ok c2 ->
    let s12 := step_apply s1 c2 in
    let s21 := step_apply s2 c1 in
    audited_step s1 c2 s12 /\
    audited_step s2 c1 s21 /\
    mu_of s12 = mu_of s21.
Proof.
  intros s c1 s1 c2 s2 Hstep1 Hstep2 Hindep Hok1 Hok2.
  inversion Hstep1; subst.
  inversion Hstep2; subst.
  split.
  - constructor; assumption.
  - split.
    + constructor; assumption.
    + unfold step_apply; simpl.
      destruct (mu_of s) as [m|]; destruct (mu_delta c1) as [d1|]; destruct (mu_delta c2) as [d2|]; auto.
      f_equal; ring.
Qed.