From Coq Require Import List Bool.
Import ListNotations.

Require Import Kernel.Kernel.
Require Import Kernel.KernelTM.

Definition step_thiele (prog : program) (st : state) : state :=
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
  | H_ClaimTapeIsZero delta =>
      let t' := claim_tape_zero st.(tape) in
      update_state st t' st.(head) (S st.(tm_state)) (st.(mu_cost) + delta)
  end.

Fixpoint run_thiele (fuel : nat) (prog : program) (st : state) : state :=
  match fuel with
  | 0 => st
  | S fuel' =>
      match fetch prog st with
      | T_Halt => st
      | _ => run_thiele fuel' prog (step_thiele prog st)
      end
  end.
