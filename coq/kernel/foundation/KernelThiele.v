(** KernelThiele: costed toy execution for Kernel.v.

    This file gives the toy machine a second step function. Unlike
    KernelTM.step_tm, step_thiele gives H_ClaimTapeIsZero an operational effect:
    it zeros the tape and adds the instruction's delta to mu_cost.

    Unlike KernelTM.step_tm (standard TM semantics, ignores μ-cost), step_thiele
    charges delta μ-bits for H_ClaimTapeIsZero:
      update_state st t' st.(head) (S st.(tm_state)) (st.(mu_cost) + delta)
    ClaimTapeIsZero zeros the tape and increments mu_cost by delta. The delta
    parameter is an explicit model input, not a derived entropy calculation.

    Physical Landauer claims are not proved here. This is just the costed toy
    semantics that later files can compare against stronger VM models.

    To challenge this file directly, show that step_thiele does not implement
    the stated toy rule: ordinary TM instructions preserve mu_cost, while
    H_ClaimTapeIsZero zeros the tape and adds delta.

    This file does not prove that hypercomputation becomes physical.
*)

From Coq Require Import List Bool.
Import ListNotations.

From Kernel Require Import Kernel KernelTM.

(** [step_thiele] is the costed toy step function. Ordinary toy instructions preserve [mu_cost]; [H_ClaimTapeIsZero] zeros the tape and adds its supplied delta. No physical calibration or cross-layer isomorphism is claimed here. *)
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

(** [run_thiele] is a fuel-bounded total evaluator. It returns the current state at fuel zero, stops early at [T_Halt], and otherwise applies [step_thiele] before recurring on the smaller fuel value. The fuel bound is a recursion bound, not a physical energy claim. *)
Fixpoint run_thiele (fuel : nat) (prog : program) (st : state) : state :=
  match fuel with
  | 0 => st
  | S fuel' =>
      match fetch prog st with
      | T_Halt => st
      | _ => run_thiele fuel' prog (step_thiele prog st)
      end
  end.
