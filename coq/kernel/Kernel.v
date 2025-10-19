From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Record state := {
  tape : list bool;
  head : nat;
  tm_state : nat;
  mu_cost : nat
}.

Inductive direction :=
| DLeft
| DRight.

Inductive instruction :=
| T_Halt
| T_Write (b : bool)
| T_Move (d : direction)
| T_Branch (target : nat)
| H_ClaimTapeIsZero.

Definition program := list instruction.

Definition read_cell (t : list bool) (idx : nat) : bool :=
  nth idx t false.

Fixpoint set_nth (n : nat) (b : bool) (t : list bool) : list bool :=
  match n, t with
  | 0, [] => [b]
  | 0, _ :: xs => b :: xs
  | S n', [] => false :: set_nth n' b []
  | S n', x :: xs => x :: set_nth n' b xs
  end.

Definition write_cell (t : list bool) (idx : nat) (b : bool) : list bool :=
  set_nth idx b t.

Definition ensure_length (t : list bool) (idx : nat) : list bool :=
  if Nat.leb (S idx) (length t) then t
  else t ++ repeat false (Nat.sub (S idx) (length t)).

Definition move_left (t : list bool) (h : nat) : (list bool * nat) :=
  match h with
  | 0 => (false :: t, 0)
  | S h' => (t, h')
  end.

Definition move_right (t : list bool) (h : nat) : (list bool * nat) :=
  let h' := S h in
  let t' := ensure_length t h' in
  (t', h').

Definition claim_tape_zero (t : list bool) : list bool :=
  repeat false (length t).

Definition update_state (st : state) (t' : list bool) (h' : nat) (s' : nat) (mu' : nat) : state :=
  {| tape := t'; head := h'; tm_state := s'; mu_cost := mu' |}.

Definition turing_instruction (instr : instruction) : bool :=
  match instr with
  | H_ClaimTapeIsZero => false
  | _ => true
  end.

Definition program_is_turing (p : program) : Prop :=
  Forall (fun instr => turing_instruction instr = true) p.
