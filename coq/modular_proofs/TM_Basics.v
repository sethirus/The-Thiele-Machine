(* ================================================================= *)
(* Modular Proofs for Thiele Machine Simulation                       *)
(* ================================================================= *)
(* This directory contains granular, incremental proofs building up  *)
(* to the full simulation theorem, avoiding large axioms/admits.     *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* Basic TM Definitions and Properties                               *)
(* ----------------------------------------------------------------- *)

(* Turing Machine state: (state, tape, head position) *)
Definition TMState := (nat * list nat * nat)%type.

(* TM configuration: (current state, tape, head) *)
Definition TMConfig := TMState.

(* TM transition: state -> symbol -> (new_state, write_symbol, move) *)
Definition TMTransition := nat -> nat -> (nat * nat * nat).

(* Helper: replace nth element in list *)
Fixpoint replace_nth (l : list nat) (n : nat) (v : nat) : list nat :=
  match l, n with
  | [], _ => []
  | x :: xs, 0 => v :: xs
  | x :: xs, S n' => x :: replace_nth xs n' v
  end.

(* Simple TM step function *)
Definition tm_step (tm : TMTransition) (conf : TMConfig) : TMConfig :=
  let '(q, tape, head) := conf in
  let symbol := nth head tape 0 in
  let '(q', write, move) := tm q symbol in
  let tape' := replace_nth tape head write in
  let head' := if Nat.eqb move 0 then head else if Nat.eqb move 1 then head + 1 else head - 1 in
  (q', tape', head').

(* Run TM for n steps *)
Fixpoint tm_run_n (tm : TMTransition) (conf : TMConfig) (n : nat) : TMConfig :=
  match n with
  | 0 => conf
  | S n' => tm_run_n tm (tm_step tm conf) n'
  end.

(* Property: replace_nth preserves length *)
Lemma replace_nth_length : forall l n v, length (replace_nth l n v) = length l.
Proof.
  induction l; intros; simpl; auto.
  destruct n; simpl; auto.
Qed.

(* Get tape from config *)
Definition get_tape (conf : TMConfig) : list nat :=
  match conf with
  | (_, tape, _) => tape
  end.

(* TM step preserves tape length if head is within bounds *)
Lemma tm_step_tape_length : forall tm q tape head,
  head < length tape ->
  length (get_tape (tm_step tm (q, tape, head))) = length tape.
Proof.
  intros.
  unfold tm_step, get_tape.
  simpl.
  remember (tm q (nth head tape 0)) as trans.
  destruct trans as [[q' write] move].
  simpl.
  apply replace_nth_length.
Qed.