Require Import List.
Import ListNotations.

(* Example: Thiele CPU stub for simulating the binary incrementer TM *)

(* Types to match the Python Thiele CPU model more closely *)
Record CPUStateCPU (Register Word : Type) := {
  registers : list (Register * Word);
  memory : list Word;
  pc : nat; (* program counter *)
  halted : bool
}.

Record ThieleCPURecCPU (Word Register Instr : Type) := {
  instr_set : list Instr;
  initial_state : CPUStateCPU Register Word;
  step : CPUStateCPU Register Word -> CPUStateCPU Register Word (* single step semantics *)
}.

Definition ThieleCPU := ThieleCPURecCPU.


(* Definition simple_cpu : ThieleCPU Word nat SimpleInstr := ... *)
(* Moved below Section ThieleCPU with concrete types *)
(*
  Next steps:
  - Define the instruction set to match thielecpu/isa.py.
  - Implement the step function for each instruction.
  - Prove that the CPU can simulate basic tape operations.
*)
(* Iterate the CPU step function n times *)
Fixpoint step_n {Word Register Instr : Type} (cpu : ThieleCPURecCPU Word Register Instr) (st : CPUStateCPU Register Word) (n : nat) : CPUStateCPU Register Word :=
  match n with
  | O => st
  | S n' => step_n cpu (@step Word Register Instr cpu st) n'
  end.
Inductive SimpleInstr :=
  | ILoad (addr : nat)
  | IStore (addr : nat)
  | IWrite (addr : nat) (val : nat)
  | IRead (addr : nat)
  | IInc (addr : nat)
  | IDec (addr : nat)
  | IJmp (addr : nat)
  | IJz (addr : nat)
  | IHalt.
(* ThieleCPU.v: Thiele CPU definition, now refined to support TM simulation *)


Definition simple_cpu : ThieleCPURecCPU nat nat SimpleInstr :=
  {|
    instr_set := [];
    step := fun st =>
      match @halted nat nat st with
      | true => st
      | false =>
        let tm_state := match List.find (fun '(r,_) => Nat.eqb r 0) (@registers nat nat st) with
                        | Some (_, s) => s
                        | None => 0
                        end in
        let tape := @memory nat nat st in
        let head := @pc nat nat st in
        let symbol := nth head tape 0 in
        let '(new_state, new_symbol, move) :=
          match tm_state, symbol with
          | 0, 2 => (2, 2, 0) (* QStart, Blank -> QHalt, Blank, stay *)
          | 0, 0 => (1, 1, -1) (* QStart, Zero -> QInc, One, left *)
          | 0, 1 => (0, 0, 1)  (* QStart, One -> QStart, Zero, right *)
          | 1, s => (2, s, 0)  (* QInc, _ -> QHalt, s, stay *)
          | 2, s => (2, s, 0)  (* QHalt, _ -> QHalt, s, stay *)
          | _, _ => (2, symbol, 0)
          end in
        let tape_ext :=
          if head <? List.length tape then tape
          else tape ++ repeat 2 (head - List.length tape + 1) in
        let tape' := firstn head tape_ext ++ [new_symbol] ++ skipn (S head) tape_ext in
        (* Move head after writing *)
        let head' := if (Z.ltb (Z.of_nat head + move) 0)%Z then 0%nat else Z.to_nat (Z.of_nat head + move) in
        let halted' := Nat.eqb new_state 2 in
        let registers' := (0, new_state) :: filter (fun '(r,_) => negb (Nat.eqb r 0)) (@registers nat nat st) in
        {| registers := registers';
           memory := tape';
           pc := head';
           halted := halted' |}
      end
  |}.
