From Coq Require Import List Bool QArith Lia.
Import ListNotations.
Open Scope Q_scope.

From ThieleMachine Require Import BellInequality.
From ThieleMachine Require Import BellReceiptSemantics.
From ThieleMachine Require Import BellReceiptSoundness.
From ThieleMachine Require Import BellReceiptLocalGeneral.
From ThieleMachine Require Import ThieleMachineConcrete.

(** A small end-to-end classical bound for a *local fragment*.

    The fragment is: programs that only emit CHSH trials whose outcomes are
    produced by a deterministic local strategy (one response table for Alice,
    one for Bob), and that cover all four (x,y) settings exactly once.

    This is a deliberately minimal “receipt → trials → CHSH” theorem that is
    adversarially meaningful and does not rely on any oracle events.
*)

Definition nat_of_bit (b : Bit) : nat :=
  match b with
  | B0 => 0%nat
  | B1 => 1%nat
  end.

Definition bit_of_nat01 (n : nat) : Bit :=
  if Nat.eqb n 0 then B0 else B1.

Definition prog_of_strategy (s : Strategy) : list ThieleInstr :=
  let '(rA, rB) := s in
  let A0 := nat_of_bit (resp_eval rA B0) in
  let A1 := nat_of_bit (resp_eval rA B1) in
  let B0n := nat_of_bit (resp_eval rB B0) in
  let B1n := nat_of_bit (resp_eval rB B1) in
  [ CHSH_TRIAL 0 0 A0 B0n;
    CHSH_TRIAL 0 1 A0 B1n;
    CHSH_TRIAL 1 0 A1 B0n;
    CHSH_TRIAL 1 1 A1 B1n ].

Definition trials_from_receipts (s0 : ConcreteState) (prog : list ThieleInstr) : list Trial :=
  trials_of_concrete_receipts (concrete_receipts_of s0 prog).

Theorem local_fragment_CHSH_le_2_end_to_end :
  forall s0 strat,
    (Qabs (chsh_of_trials (trials_from_receipts s0 (prog_of_strategy strat))) <= 2#1)%Q.
Proof.
  intros s0 [rA rB].
  destruct rA as [a0 a1].
  destruct rB as [b0 b1].
  set (rA' := {| out0 := a0; out1 := a1 |}).
  set (rB' := {| out0 := b0; out1 := b1 |}).
  unfold trials_from_receipts.
  rewrite trials_of_concrete_receipts_of.
  (* Discharge the locality and coverage hypotheses by computation. *)
  apply (local_trials_CHSH_bound
            (trials_of_prog (prog_of_strategy (rA', rB')))
            rA' rB').
  { unfold rA', rB', prog_of_strategy.
    destruct a0, a1; destruct b0, b1.
    all: (vm_compute; repeat constructor; try (split; reflexivity)). }
  { intro x; intro y.
    unfold rA', rB', prog_of_strategy.
    destruct a0, a1; destruct b0, b1.
    all: (destruct x, y; vm_compute; lia). }
Qed.
