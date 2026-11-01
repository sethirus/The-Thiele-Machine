(** Napkin.v: the three-line argument and the smallest machine, machine-checked.
    Stdlib only, 0 axioms. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose.
   Same reason as MuCore.v, only more so. This file is the napkin argument and
   the smallest machine written out as theorems, and its whole value is that it imports
   nothing of mine: delete the repository and these still hold. It re-proves the
   cost floor and the non-invertible projection from scratch rather than reaching
   for AxThiele or the floor theorems in the kernel. Wiring it into the
   foundation chain would pull the kernel back in and turn "a napkin holds it"
   into "a napkin plus the kernel holds it", which is the very claim this file
   exists to make good on. So it stays standalone on the Coq standard library,
   and this note tells the gate why. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.

Record state := mk { st_mem : list nat ; st_pc : nat ; st_mu : nat ; st_cert : bool }.
Definition shadow (s : state) : (list nat * nat) := (st_mem s, st_pc s).

(* LINE 1: the smallest machine. Two states, no and yes, read as themselves; a
   reading that no move lowers and that some run raises forces a move that
   sends both states to yes. The merge is inside the smallest machine, and
   the latch, two states and that one move at price one, is it. *)
Fixpoint run2 (I : Type) (step : bool -> I -> bool) (tr : list I) (b : bool) : bool :=
  match tr with [] => b | i :: rest => run2 I step rest (step b i) end.
Lemma run2_raise : forall (I : Type) (step : bool -> I -> bool) tr b,
  run2 I step tr b = true -> b = true \/ exists i, step false i = true.
Proof.
  intros I step tr. induction tr as [| i rest IH]; intros b Hrun; simpl in Hrun.
  - left. exact Hrun.
  - destruct (IH _ Hrun) as [Hb | Hex].
    + destruct b; [left; reflexivity | right; exists i; exact Hb].
    + right. exact Hex.
Qed.
Theorem smallest_machine_merges :
  forall (I : Type) (step : bool -> I -> bool),
    (forall b i, b = true -> step b i = true) ->
    (exists tr, run2 I step tr false = true) ->
    exists i, step false i = true /\ step true i = true.
Proof.
  intros I step Hperm [tr Htr].
  destruct (run2_raise I step tr false Htr) as [H | [i Hi]]; [discriminate |].
  exists i. split; [exact Hi | apply Hperm; reflexivity].
Qed.
Definition latch_step (b : bool) (_ : unit) : bool :=
  match b with false => true | true => true end.
Definition latch_cost (_ : unit) : nat := 1.
Theorem latch_meets_definition :
  (forall b m, b = false -> latch_step b m = true -> latch_cost m >= 1) /\
  (forall b m, b = true -> latch_step b m = true) /\
  run2 unit latch_step [tt] false = true /\
  latch_step false tt = latch_step true tt.
Proof.
  split; [intros b m _ _; unfold latch_cost; lia |].
  split; [intros [] m _; reflexivity |].
  split; reflexivity.
Qed.

(* LINE 2a: enforcement requires reading the cost *)
Theorem cost_blind_admits_free_cert :
  forall (C I : Type) (icost : I -> nat) (effect : C -> I -> C)
         (flip : C -> bool) (c : C) (i_free i_paid : I),
    effect c i_free = effect c i_paid ->
    icost i_free = 0 ->
    flip (effect c i_paid) = true ->
    flip (effect c i_free) = true /\ icost i_free = 0.
Proof.
  intros C I icost effect flip c i_free i_paid Heff Hfree Hpaid.
  split. - rewrite Heff. exact Hpaid. - exact Hfree.
Qed.

(* LINE 2b: gating rule IS the substrate; non-gating forges *)
Definition enforces_A2 (step : state -> nat -> state) : Prop :=
  forall s d, st_cert s = false -> st_cert (step s d) = true -> d >= 1.
Definition gate_step (s : state) (d : nat) : state :=
  mk (st_mem s) (S (st_pc s)) (st_mu s + d) (orb (st_cert s) (Nat.leb 1 d)).
Theorem gate_step_is_substrate : enforces_A2 gate_step.
Proof.
  intros s d Hbefore Hafter. unfold gate_step in Hafter. simpl in Hafter.
  rewrite Hbefore in Hafter. simpl in Hafter.
  destruct d as [| d']. - simpl in Hafter; discriminate. - lia.
Qed.
Definition forge_step (s : state) (d : nat) : state :=
  mk (st_mem s) (S (st_pc s)) (st_mu s + d) true.
Theorem forge_step_not_substrate : ~ enforces_A2 forge_step.
Proof.
  intro H. assert (Hbad : 0 >= 1).
  { apply (H (mk [] 0 0 false) 0); reflexivity. } lia.
Qed.

(* LINE 3a: the projection is not invertible *)
Definition sA : state := gate_step (mk [] 0 0 false) 1.
Definition sB : state := mk [] 1 0 false.
Lemma shadows_agree : shadow sA = shadow sB. Proof. reflexivity. Qed.
Theorem no_mu_oracle :
  ~ exists f : (list nat * nat) -> nat, forall s, f (shadow s) = st_mu s.
Proof.
  intros [f Hf]. assert (E : st_mu sA = st_mu sB).
  { rewrite <- (Hf sA), <- (Hf sB), shadows_agree. reflexivity. }
  vm_compute in E. discriminate.
Qed.
Theorem no_cert_oracle :
  ~ exists f : (list nat * nat) -> bool, forall s, f (shadow s) = st_cert s.
Proof.
  intros [f Hf]. assert (E : st_cert sA = st_cert sB).
  { rewrite <- (Hf sA), <- (Hf sB), shadows_agree. reflexivity. }
  vm_compute in E. discriminate.
Qed.

(* LINE 3b: simulation reproduces the forbidden flip; the law forbids it *)
Theorem free_run_forges :
  exists s d, st_cert s = false /\ st_cert (forge_step s d) = true /\ d = 0.
Proof. exists (mk [] 0 0 false), 0. repeat split; reflexivity. Qed.
Theorem substrate_forbids_free_flip :
  forall s d, st_cert s = false -> st_cert (gate_step s d) = true -> d >= 1.
Proof. exact gate_step_is_substrate. Qed.

Print Assumptions smallest_machine_merges.
Print Assumptions latch_meets_definition.
Print Assumptions cost_blind_admits_free_cert.
Print Assumptions gate_step_is_substrate.
Print Assumptions forge_step_not_substrate.
Print Assumptions no_mu_oracle.
Print Assumptions no_cert_oracle.
Print Assumptions free_run_forges.
Print Assumptions substrate_forbids_free_flip.
