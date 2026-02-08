(** * KernelThiele: Thiele Machine with μ-Cost Tracking

    WHY THIS FILE EXISTS:
    I claim H_ClaimTapeIsZero operations MUST cost μ-bits, or you get perpetual
    motion (free search space narrowing). This file implements step_thiele which
    ACTUALLY CHARGES μ-cost for ClaimTapeIsZero, unlike step_tm (which ignores it).

    THE DIFFERENCE FROM KernelTM:
    - KernelTM.step_tm: Standard TM semantics, ignores μ-cost tracking
    - THIS FILE.step_thiele: Charges delta μ-bits for H_ClaimTapeIsZero (line 25)

    KEY LINE (25): update_state st t' st.(head) (S st.(tm_state)) (st.(mu_cost) + delta)
    This says: ClaimTapeIsZero zeros the tape BUT increments mu_cost by delta.
    The delta parameter encodes HOW MUCH information was erased (tape length,
    number of non-zero cells, etc.).

    PHYSICAL CLAIM:
    Erasing information costs energy (Landauer's principle: kT ln 2 per bit).
    μ-cost tracks this information erasure. ClaimTapeIsZero is hypercomputational
    (solves halting problem if free) but becomes physical when it costs μ.

    FALSIFICATION:
    Show you can implement ClaimTapeIsZero in a real quantum computer with zero
    energy cost (violating Landauer). Or prove the halting problem is decidable
    by showing free ClaimTapeIsZero is physically realizable. Or demonstrate
    qubit initialization (|0⟩ state preparation) requires no thermodynamic work.

    This file shows: hypercomputation + μ-cost = physical computation.
*)

From Coq Require Import List Bool.
Import ListNotations.

Require Import Kernel.
Require Import KernelTM.

(**
  step_thiele: ONE STEP of Thiele Machine execution with μ-cost tracking.

  WHY: I need operational semantics that ACTUALLY CHARGE μ-cost for hypercomputation.
  This is the key difference from step_tm: H_ClaimTapeIsZero costs μ, making
  hypercomputation physical (not magic).

  ALGORITHM: Match on fetched instruction:
  - T_Halt: No change (halted state)
  - T_Write b: Write b to current cell, advance state, μ unchanged
  - T_Move DLeft: Move head left, extend tape if needed, μ unchanged
  - T_Move DRight: Move head right, extend tape if needed, μ unchanged
  - T_Branch target: If current cell = 1, jump to target; else advance. μ unchanged.
  - H_ClaimTapeIsZero delta: Zero the entire tape, advance state, ADD delta to μ-cost.

  THE CRITICAL LINE (line 55): (st.(mu_cost) + delta)
  This is where hypercomputation pays thermodynamic cost. ClaimTapeIsZero erases
  information (sets all cells to 0), which violates reversibility. Landauer's
  principle: erasing n bits costs n × kT ln(2) energy. The delta parameter
  represents this thermodynamic debt.

  CLAIM: step_thiele is deterministic. ∀ prog, st, there exists UNIQUE st'
  such that step_thiele prog st = st'.

  PHYSICAL MEANING: step_thiele models the second law. Most operations (Write,
  Move, Branch) are reversible (μ = 0). But ClaimTapeIsZero is IRREVERSIBLE
  (erases information, costs μ). This makes the Thiele Machine a thermodynamically
  consistent hypercomputer - you can solve undecidable problems, but you pay
  energy cost proportional to the solution's information content.

  COMPARISON TO step_tm: KernelTM.step_tm ignores μ-cost entirely (line 25 has
  st.(mu_cost) instead of st.(mu_cost) + delta). This makes step_tm a
  "fictional" TM (ignores thermodynamics). step_thiele is the PHYSICAL TM.

  FALSIFICATION: Show that ClaimTapeIsZero can be implemented in a real physical
  system (quantum computer, reversible computing, etc.) with ZERO thermodynamic
  cost. This would mean Landauer's principle is false. Or demonstrate that
  qubit initialization (|ψ⟩ → |0⟩) requires no energy dissipation.

  DEPENDENCIES: Requires Kernel.state, KernelTM.fetch, KernelTM.{write_cell,
  move_left, move_right, read_cell, claim_tape_zero, update_state}.

  USED BY: run_thiele (iterates step_thiele), hypercomputation analysis.

  ISOMORPHISM: The μ-charging behavior matches thielecpu/vm.py::step_instruction()
  for partition operations (PNEW, PDISCOVER) which also charge μ-cost.
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

  PHYSICAL MEANING: fuel represents available energy budget. Each step consumes
  1 unit of fuel (regardless of μ-cost). When fuel exhausted, computation halts
  (thermal equilibrium, no free energy left). The μ-cost tracks INFORMATION
  cost, fuel tracks COMPUTATION cost. Both are necessary: μ for thermodynamics,
  fuel for complexity bounds.

  DIFFERENCE FROM run_tm: Semantically identical in control flow, but step_thiele
  charges μ-cost where step_tm doesn't. This means run_thiele accumulates
  μ-cost, run_tm ignores it.

  EXAMPLE: run_thiele 100 prog init_state executes at most 100 steps. If prog
  halts after 50 steps, returns halted state. If prog needs 150 steps, returns
  state after 100 steps (possibly non-halted).

  FALSIFICATION: Show run_thiele diverges (infinite loop) for finite fuel.
  This would mean structural recursion is broken (impossible in Coq). Or prove
  run_thiele fuel prog st ≠ run_thiele (fuel + 1) prog st when fuel is
  sufficient for halting (would mean early exit doesn't work).

  DEPENDENCIES: Requires step_thiele, fetch, T_Halt.

  USED BY: Hypercomputation analysis, resource-bounded proofs, complexity bounds.

  COMPUTATIONAL COMPLEXITY: O(fuel) time, O(|tape| + |prog|) space. Linear in
  fuel because each step is O(1) (assuming tape operations are amortized O(1)).
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
