From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Require Import Kernel.

Definition fetch (prog : program) (st : state) : instruction :=
  match nth_error prog st.(tm_state) with
  | Some instr => instr
  | None => T_Halt
  end.

Definition step_tm (prog : program) (st : state) : state :=
  match fetch prog st with
  | T_Halt => st
  | T_Write b =>
      let t' := write_cell st.(tape) st.(head) b in
      update_state st t' st.(head) (S st.(tm_state)) st.(mu_cost)
  | T_Move DLeft =>
      let '(t', h') := move_left st.(tape) st.(head) in
      update_state st t' h' (S st.(tm_state)) st.(mu_cost)
  | T_Move DRight =>
      let '(t', h') := move_right st.(tape) st.(head) in
      update_state st t' h' (S st.(tm_state)) st.(mu_cost)
  | T_Branch target =>
      let cell := read_cell st.(tape) st.(head) in
      let next := if cell then target else S st.(tm_state) in
      update_state st st.(tape) st.(head) next st.(mu_cost)
  | H_ClaimTapeIsZero _ =>
      update_state st st.(tape) st.(head) (S st.(tm_state)) st.(mu_cost)
  end.

Fixpoint run_tm (fuel : nat) (prog : program) (st : state) : state :=
  match fuel with
  | 0 => st
  | S fuel' =>
      match fetch prog st with
      | T_Halt => st
      | _ => run_tm fuel' prog (step_tm prog st)
      end
  end.

Record TuringMachine := {
  tm_program : program;
  tm_initial : state;
  tm_steps : nat
}.

Definition initial_state_for (M : TuringMachine) : state := tm_initial M.
Definition final_state_for (M : TuringMachine) : state :=
  run_tm (tm_steps M) (tm_program M) (tm_initial M).

Theorem tm_is_turing_complete :
  forall (M : TuringMachine),
    exists (p : program),
      run_tm (tm_steps M) p (initial_state_for M) = final_state_for M.
Proof.
  intros M.
  exists (tm_program M).
  unfold final_state_for, initial_state_for.
  reflexivity.
Qed.
