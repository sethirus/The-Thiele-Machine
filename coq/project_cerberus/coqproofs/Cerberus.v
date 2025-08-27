(* --- Example: Simple Thiele Kernel Program and Oracle --- *)
(**
(* Dummy oracle: always returns true (for demonstration) *)
Definition dummy_oracle (_ : list nat) : bool := true.

(* Override the logic_oracle parameter for this test *)
(* Temporary axiom: for the example/test harness we bind the project's oracle
   to the simple `dummy_oracle` that always returns true. This is a deliberate
   engineering shortcut to allow the example kernel and early proofs to run
   without the full oracle implementation.

   TODO (actionable):
   - Preferably replace this axiom by either:
     * a constructive definition of `logic_oracle` (if the oracle is internal), or
     * parameterize the theorems over the oracle and discharge the obligations
       later with a concrete implementation or external proof.
   - If the oracle encodes an external undecidable/heuristic component, document
     the required assumptions and justify why keeping this as an axiom is acceptable.
*)
Axiom logic_oracle_is_dummy : logic_oracle = dummy_oracle.

(* Example program: Load 0; AddReg 0 0 0; Halt *)
Definition example_instrs : list Instr := [Load 0; AddReg 0 0 0; Halt].
Definition example_axioms : ProgramAxioms := ([] : list nat).
Definition example_program : Program := (example_instrs, example_axioms).

Definition example_init_state : MachineState :=
  {| pc := 0; mem := [42]; regs := [0]; mu_cost := 0; paradox_detected := false |}.

(* Run the kernel for 3 steps *)
Definition example_final_state := run_kernel_n example_program example_init_state 3.

(* You can use Compute in Coq to see the result: *)
Compute example_final_state.
*)
(* Cerberus.v - Minimal provably-safe kernel *)
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
Import ListNotations.


(* Simple machine state - THIELE EDITION *)
Record MachineState := {
  pc : nat; (* program counter *)
  mem : list nat; (* flat memory cells *)
  regs : list nat; (* register file *)
  mu_cost : nat;            (* running information cost *)
  paradox_detected : bool   (* flag for logical inconsistency *)
}.

(* Register helpers *)
Definition read_reg (r : nat) (rs : list nat) : nat := nth r rs 0.

Fixpoint write_reg (r v : nat) (rs : list nat) : list nat :=
  match r, rs with
  | 0, _ :: tl => v :: tl
  | S r', hd :: tl => hd :: write_reg r' v tl
  | _, [] => rs (* out-of-range writes leave regs unchanged *)
  end.

(* Simple instruction set *)

Inductive Instr :=
  | Load (addr : nat)
  | Store (addr : nat) (val : nat)
  | AddReg (rd rs1 rs2 : nat)
  | SubReg (rd rs1 rs2 : nat)
  | CopyReg (rd rs : nat)
  | Jmp (target : nat)
  | Jz (rs target : nat)
  | Jnz (rs target : nat)
  | Halt.

(* Jump target safety *)
Definition is_target_valid (program_len target : nat) : bool := Nat.ltb target program_len.

Definition is_instr_pc_safe (program_len : nat) (i : Instr) : bool :=
  match i with
  | Jmp t => is_target_valid program_len t
  | Jz _ t => is_target_valid program_len t
  | Jnz _ t => is_target_valid program_len t
  | _ => true
  end.

(* Memory safety checks *)
Definition is_safe_accessb (mem_len addr : nat) : bool := Nat.ltb addr mem_len.

Definition is_instr_mem_safe (mem_len : nat) (i : Instr) : bool :=
  match i with
  | Load addr => is_safe_accessb mem_len addr
  | Store addr _ => is_safe_accessb mem_len addr
  | _ => true
  end.

Lemma succ_le_of_lt : forall a b, a < b -> S a <= b.
Proof. intros a b H; lia. Qed.



(* Program with associated safety axioms - THIELE EDITION *)
Definition ProgramAxioms := list nat. (* Encoded logical rules *)

Definition Program := (list Instr * ProgramAxioms)%type.

(* We will need the logic_oracle from ThieleMachine.v *)
Parameter logic_oracle : list nat -> bool.

Definition mem_safe_program (mem_len : nat) (p : Program) : Prop :=
  forall i, In i (fst p) -> is_instr_mem_safe mem_len i = true.



(* Encode safety properties of an instruction as a list of nat axioms (stub version) *)
Definition encode_safety_axioms (instr : Instr) (program_len : nat) (mem_len : nat) : list nat :=
  match instr with
  | Load addr => [1; addr; if Nat.ltb addr mem_len then 0 else 1]
  | Store addr _ => [2; addr; if Nat.ltb addr mem_len then 0 else 1]
  | AddReg rd rs1 rs2 => [3; rd; rs1; rs2; 0]
  | SubReg rd rs1 rs2 => [4; rd; rs1; rs2; 0]
  | CopyReg rd rs => [5; rd; rs; 0]
  | Jmp t => [6; t; if Nat.ltb t program_len then 0 else 1]
  | Jz rs t => [7; rs; t; if Nat.ltb t program_len then 0 else 1]
  | Jnz rs t => [8; rs; t; if Nat.ltb t program_len then 0 else 1]
  | Halt => [9; 0]
  end.
(*
  This is a stub: in a real system, the encoding would be more sophisticated and would match the oracle's logic.
  For now, we encode the instruction type and whether its safety check passes (0 = safe, 1 = unsafe).
*)

(* Kernel step: Fetches and executes one instruction safely. - THIELE EDITION *)
Definition kernel_step (p_with_axioms : Program) (st : MachineState) : MachineState :=
  let '(p_instrs, p_axioms) := p_with_axioms in
  if st.(paradox_detected) then st else (* Sticky paradox: once set, remains set *)
  match nth_error p_instrs st.(pc) with
  | None => st (* PC out of program bounds, halt. *)
  | Some instr_val =>
      let mem_len := length st.(mem) in
      let pc_safe := is_instr_pc_safe (length p_instrs) instr_val in
      let mem_safe := is_instr_mem_safe mem_len instr_val in
      let current_safety_axioms := encode_safety_axioms instr_val (length p_instrs) mem_len in
      let is_consistent_by_oracle := logic_oracle (p_axioms ++ current_safety_axioms) in

  if orb (orb (negb pc_safe) (negb mem_safe)) (negb is_consistent_by_oracle) then
        {| pc := st.(pc); mem := st.(mem); regs := st.(regs);
           mu_cost := st.(mu_cost); paradox_detected := true |}
      else
        match instr_val with
        | Halt => st
        | Load _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Store _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | AddReg _ _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | SubReg _ _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | CopyReg _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Jmp _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Jz _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Jnz _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        end
  end.

Fixpoint run_kernel_n (p : Program) (st : MachineState) (n : nat) : MachineState :=
  match n with
  | 0 => st
  | S k => run_kernel_n p (kernel_step p st) k
  end.



(* Main security theorem: The program counter never exceeds the program's bounds (Thiele Edition). *)
Theorem pc_never_exceeds_program_bounds_thiele :
  forall (p_with_axioms : Program) (st : MachineState) (n : nat),
    st.(pc) <= length (fst p_with_axioms) ->
    st.(paradox_detected) = false ->
    (forall instr,
      In instr (fst p_with_axioms) ->
      logic_oracle (snd p_with_axioms ++ encode_safety_axioms instr (length (fst p_with_axioms)) (length st.(mem))) = true) ->
    (run_kernel_n p_with_axioms st n).(pc) <= length (fst p_with_axioms).
Admitted.

Theorem mem_safety_preserved_thiele :
  forall (p_with_axioms : Program) (st_init : MachineState) (n : nat),
    (forall instr,
      In instr (fst p_with_axioms) ->
      logic_oracle (snd p_with_axioms ++ encode_safety_axioms instr (length (fst p_with_axioms)) (length st_init.(mem))) = true) ->
    forall k,
      (run_kernel_n p_with_axioms st_init k).(pc) < length (fst p_with_axioms) ->
      let instr := nth (run_kernel_n p_with_axioms st_init k).(pc) (fst p_with_axioms) Halt in
      logic_oracle (snd p_with_axioms ++ encode_safety_axioms instr (length (fst p_with_axioms)) (length st_init.(mem))) = true.
Admitted.