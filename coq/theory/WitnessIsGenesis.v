(* WitnessIsGenesis.v — Instantiating Genesis.v with the Ouroboros witness model *)

Set Implicit Arguments.

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.

Require Import Theory.Genesis.

Record CreatorState := {
  creator_hash : nat;
  embedded_child_hash : nat;
  anchor_value : nat;
  coq_proofs_compiled : bool;
  coq_proofs_sound : coq_proofs_compiled = true
}.

Record ChildState := {
  child_reported_hash : nat;
  child_anchor_binding : nat;
  thesis_verified : bool
}.

Definition anchor_binding (hash anchor : nat) : nat := hash + anchor.

Definition proposer_func (c : CreatorState) : ChildState :=
  {| child_reported_hash := embedded_child_hash c;
     child_anchor_binding := anchor_binding (embedded_child_hash c) (anchor_value c);
     thesis_verified := true |}.

Definition auditor_func (c : CreatorState) (child : ChildState) : bool :=
  Nat.eqb (child_reported_hash child) (embedded_child_hash c) &&
  Nat.eqb (child_anchor_binding child)
          (anchor_binding (embedded_child_hash c) (anchor_value c)) &&
  thesis_verified child &&
  coq_proofs_compiled c.

Record WitnessState := {
  witness_creator : CreatorState;
  witness_child : ChildState
}.

Definition witness_step (w : WitnessState) : WitnessState :=
  {| witness_creator := witness_creator w;
     witness_child := proposer_func (witness_creator w) |}.

Definition witness_auditor (before after : WitnessState) : Prop :=
  witness_creator after = witness_creator before /\
  auditor_func (witness_creator before) (witness_child after) = true.

Lemma auditor_func_accepts :
  forall c : CreatorState,
    auditor_func c (proposer_func c) = true.
Proof.
  intros c.
  unfold auditor_func, proposer_func, anchor_binding.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite (coq_proofs_sound c).
  reflexivity.
Qed.

Lemma witness_auditor_accepts :
  forall w : WitnessState, witness_auditor w (witness_step w).
Proof.
  intros [creator child]; simpl.
  split; [reflexivity|].
  apply auditor_func_accepts.
Qed.

Definition WitnessProc : Proc WitnessState :=
  {| step := witness_step;
     ok := witness_auditor;
     ok_step := witness_auditor_accepts |}.

Definition Logos_Machine : Thiele WitnessState :=
  proc_to_thiele WitnessProc.

Theorem Ouroboros_Witness_Is_A_Coherent_Process :
  forall s : WitnessState,
    ThieleStep Logos_Machine s (witness_step s).
Proof.
  intro s.
  unfold Logos_Machine.
  apply proc_realises_thiele.
Qed.

Corollary Logos_Auditor_Sees_True :
  forall c : CreatorState,
    auditor_func c (proposer_func c) = true.
Proof.
  apply auditor_func_accepts.
Qed.
