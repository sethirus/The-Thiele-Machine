(** * Kernel: Minimal Turing Machine with μ-Cost Tracking

    WHY THIS FILE EXISTS:
    I claim the μ-cost model applies to ANY computational model, not just the
    specific VM (VMState, VMStep). To prove this, I define a minimal Turing
    machine and show it tracks μ-cost the same way.

    THE MODEL:
    - State: (tape, head_position, machine_state, mu_cost)
    - Instructions: Halt, Write(b), Move(Left/Right), Branch(target), ClaimTapeIsZero
    - Tape: infinite to the right (list bool with dynamic extension)

    TURING VS HYPERCOMPUTATION:
    - Standard Turing instructions: Write, Move, Branch, Halt (turing_instruction = true)
    - Hypercomputational instruction: ClaimTapeIsZero (turing_instruction = false)

    ClaimTapeIsZero(δ) is the key: it "magically" zeros the tape but costs δ μ-bits.
    This models algorithms that narrow the search space - they pay μ-cost proportional
    to the reduction. This is the computational form of No Free Insight.

    WHY CLAIMTAPEISZERO:
    If you could zero a tape without cost, you could reset computation state for free,
    effectively solving the halting problem (run a program, reset, try again with
    different input). By charging μ-cost, we make hypercomputational operations
    "pay their way" - they're not free magic.

    FALSIFICATION:
    Show that ClaimTapeIsZero operations in real quantum computers (e.g., qubit
    initialization, state preparation) don't have energy/time cost proportional
    to the information being erased. This would violate Landauer's principle
    (kT ln 2 per bit erased) and falsify the μ-cost model.

    Or prove the halting problem is decidable by showing you can implement
    ClaimTapeIsZero with zero cost in a physical system.

    This file is a MINIMAL EXAMPLE, not the full VM. See VMState.v and VMStep.v
    for the complete computational model.
*)

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
| H_ClaimTapeIsZero (delta : nat).

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
  | H_ClaimTapeIsZero _ => false
  | _ => true
  end.

Definition program_is_turing (p : program) : Prop :=
  Forall (fun instr => turing_instruction instr = true) p.
