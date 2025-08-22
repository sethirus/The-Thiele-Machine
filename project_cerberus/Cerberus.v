(* Cerberus.v - Minimal provably-safe kernel *)
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

(* Simple machine state *)
Record MachineState := {
  pc : nat; (* program counter *)
  mem : list nat (* flat memory cells *)
}.

(* Simple instruction set *)
Inductive Instr :=
  | Load (addr : nat)
  | Store (addr : nat) (val : nat)
  | Halt.

Definition Program := list Instr.

(* Kernel step: Fetches and executes one instruction safely.
   If PC is out of bounds, it halts (state does not change). *)
Definition kernel_step (p : Program) (st : MachineState) : MachineState :=
  match nth_error p st.(pc) with
  | None => st (* PC is out of program bounds, halt. *)
  | Some Halt => st (* Halt instruction, state does not change. *)
  | Some (Load _) => {| pc := S st.(pc); mem := st.(mem) |}
  | Some (Store _ _) => {| pc := S st.(pc); mem := st.(mem) |}
  end.

Fixpoint run_kernel_n (p : Program) (st : MachineState) (n : nat) : MachineState :=
  match n with
  | 0 => st
  | S k => run_kernel_n p (kernel_step p st) k
  end.

(* Main security theorem: The program counter never goes out of the program's bounds. *)
(* Main security theorem: The program counter never exceeds the program's bounds. *)
Theorem pc_never_exceeds_program_bounds :
  forall (p : Program) (st : MachineState) (n : nat),
    st.(pc) <= length p ->
    (run_kernel_n p st n).(pc) <= length p.
Proof.
  intros p st n H_pc_bound.
  revert st H_pc_bound.
  induction n as [|k IH]; intros st H_pc_bound.
  - (* Base Case *)
    simpl. assumption.
  - (* Inductive Step *)
    simpl.
    apply IH.
    unfold kernel_step.
    destruct (nth_error p st.(pc)) as [instr|] eqn:H_fetch.
    + (* Case 1: Fetch succeeds. This means st.pc < length p. *)
      destruct instr; simpl.
      * (* Load *)
        assert (st.(pc) < length p) as Hlt by (apply nth_error_Some; congruence).
        lia.
      * (* Store *)
        assert (st.(pc) < length p) as Hlt by (apply nth_error_Some; congruence).
        lia.
      * (* Halt *) exact H_pc_bound.
    + (* Case 2: Fetch fails. This means st.pc >= length p. *)
      (* kernel_step doesn't change st, so next state's pc is still <= length p. *)
      exact H_pc_bound.
Qed.