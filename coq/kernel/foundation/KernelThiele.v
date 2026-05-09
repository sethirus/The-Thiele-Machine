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

(**
  step_thiele: ONE STEP of Thiele Machine execution with μ-cost tracking.

  This is the costed variant of the KernelTM step function. The key difference
  from step_tm is the H_ClaimTapeIsZero branch.

  ALGORITHM: Match on fetched instruction:
  - T_Halt: No change (halted state)
  - T_Write b: Write b to current cell, advance state, μ unchanged
  - T_Move DLeft: Move head left, extend tape if needed, μ unchanged
  - T_Move DRight: Move head right, extend tape if needed, μ unchanged
  - T_Branch target: If current cell = 1, jump to target; else advance. μ unchanged.
  - H_ClaimTapeIsZero delta: Zero the entire tape, advance state, ADD delta to μ-cost.

  The critical line is (st.(mu_cost) + delta). The file does not derive delta
  from tape length or Landauer; it only records the supplied cost.

  CLAIM: step_thiele is deterministic. ∀ prog, st, there exists UNIQUE st'
  such that step_thiele prog st = st'.

  Reading: ordinary toy instructions leave mu_cost unchanged; the special
  ClaimTapeIsZero instruction pays the supplied μ cost.

  Comparison to step_tm: KernelTM.step_tm treats H_ClaimTapeIsZero as an
  advance-only placeholder. step_thiele gives that placeholder a tape effect
  and a μ charge.

  To falsify the formal rule: find prog/st where the ClaimTapeIsZero branch
  does not zero the tape or does not add delta.

  DEPENDENCIES: Requires Kernel.state, KernelTM.fetch, KernelTM.{write_cell,
  move_left, move_right, read_cell, claim_tape_zero, update_state}.

  No cross-layer isomorphism is proved in this file.
*)
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

(**
  run_thiele: Execute Thiele Machine for up to fuel steps.

  WHY: I need a TOTAL function (always terminates) for executing the Thiele
  Machine. Coq requires all functions to be provably terminating, so I use
  fuel-bounded execution instead of while-loops.

  ALGORITHM:
  - fuel = 0: Out of gas, return current state (possibly non-halted).
  - fuel > 0 AND T_Halt: Reached halt state, return immediately (early exit).
  - fuel > 0 AND other instruction: Execute step_thiele, recurse with fuel - 1.

  TERMINATION: Structural recursion on fuel (nat). Each recursive call has
  strictly smaller fuel (S fuel' < fuel), guaranteeing termination.

  CLAIM: If program halts within fuel steps, run_thiele returns halted state
  with remaining fuel unused (captured in state, not function result).

  Reading: fuel is just the recursion bound needed to make execution total in
  Coq. It is not an energy budget in this file.

  DIFFERENCE FROM run_tm: Semantically identical in control flow, but step_thiele
  charges μ-cost where step_tm doesn't. This means run_thiele accumulates
  μ-cost, run_tm ignores it.

  EXAMPLE: run_thiele 100 prog init_state executes at most 100 steps. If prog
  halts after 50 steps, returns halted state. If prog needs 150 steps, returns
  state after 100 steps (possibly non-halted).

  To falsify the formal behavior: find a finite-fuel case where run_thiele does
  not follow the fetch/step recursion above.

  DEPENDENCIES: Requires step_thiele, fetch, T_Halt.

  This file does not prove wall-clock complexity; list tape operations and
  instruction fetch have their own costs in an extracted implementation.
*)
Fixpoint run_thiele (fuel : nat) (prog : program) (st : state) : state :=
  match fuel with
  | 0 => st
  | S fuel' =>
      match fetch prog st with
      | T_Halt => st
      | _ => run_thiele fuel' prog (step_thiele prog st)
      end
  end.
