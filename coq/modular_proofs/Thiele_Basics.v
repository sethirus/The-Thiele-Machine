(* ================================================================= *)
(* Thiele Machine Basics                                             *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith.
From ThieleMachine.Modular_Proofs Require Import Encoding TM_Basics.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* Thiele Machine State and Programs                                 *)
(* ----------------------------------------------------------------- *)

(* Register indexes for the simple CPU. *)

Definition REG_PC   := 0.
Definition REG_Q    := 1.
Definition REG_HEAD := 2.
Definition REG_SYM  := 3.
Definition REG_Q'   := 4.
Definition REG_WRITE:= 5.
Definition REG_MOVE := 6.
Definition REG_ADDR := 7.
Definition REG_TEMP1:= 8.
Definition REG_TEMP2:= 9.

(* Instruction set for the CPU. *)
Inductive Instr : Type :=
  | LoadConst (rd val : nat)
  | LoadIndirect (rd ra : nat)
  | StoreIndirect (ra rv : nat)
  | CopyReg (rd rs : nat)
  | AddConst (rd val : nat)
  | AddReg (rd rs1 rs2 : nat)
  | SubReg (rd rs1 rs2 : nat)
  | Jz (rc target : nat)
  | Jnz (rc target : nat)
  | Halt.

(* Machine state: register file, memory, and cost. *)
Record State := { regs : list nat; mem : list nat; cost : nat }.

(* Program: initial memory containing the encoded program *)
Definition ThieleProgram := list nat.

(* Register and memory helpers. *)
Definition read_reg (r : nat) (st : State) : nat := nth r st.(regs) 0.
Definition write_reg (r v : nat) (st : State) : State :=
  {| regs := firstn r st.(regs) ++ [v] ++ skipn (S r) st.(regs); mem := st.(mem); cost := st.(cost) |}.

Definition read_mem (addr : nat) (st : State) : nat := nth addr st.(mem) 0.
Definition write_mem (addr v : nat) (st : State) : State :=
  {| regs := st.(regs); mem := firstn addr st.(mem) ++ [v] ++ skipn (S addr) st.(mem); cost := st.(cost) |}.

(* Cost model: each instruction has a cost in µ-bits. *)
Definition instr_cost (i : Instr) : nat :=
  match i with
  | LoadConst _ _ => 1
  | LoadIndirect _ _ => 2
  | StoreIndirect _ _ => 5  (* Higher cost for complex checks *)
  | CopyReg _ _ => 1
  | AddConst _ _ => 1
  | AddReg _ _ _ => 1
  | SubReg _ _ _ => 1
  | Jz _ _ => 1
  | Jnz _ _ => 1
  | Halt => 1
  end.

(* Encoding base used for packing instruction operands into a single word. *)
Definition ENC_BASE := 1024.

(* Encode a single instruction as four consecutive words in memory:
   [opcode; arg1; arg2; arg3]. *)
Definition encode_instr_words (i:Instr) : list nat :=
  match i with
  | LoadConst rd v      => [0; rd; v; 0]
  | LoadIndirect rd ra  => [1; rd; ra; 0]
  | StoreIndirect ra rv => [2; ra; rv; 0]
  | CopyReg rd rs       => [3; rd; rs; 0]
  | AddConst rd v       => [4; rd; v; 0]
  | AddReg rd r1 r2     => [5; rd; r1; r2]
  | SubReg rd r1 r2     => [6; rd; r1; r2]
  | Jz rc target        => [7; rc; target; 0]
  | Jnz rc target       => [8; rc; target; 0]
  | Halt                => [9; 0; 0; 0]
  end.

(* Decode an instruction from the memory image. Read four consecutive
   cells starting at PC: opcode, arg1, arg2, arg3. *)
Definition decode_instr_from_mem (mem : list nat) (pc : nat) : Instr :=
  let opcode := nth pc mem 0 in
  let arg1 := nth (pc + 1) mem 0 in
  let arg2 := nth (pc + 2) mem 0 in
  let arg3 := nth (pc + 3) mem 0 in
  match opcode with
  | 0 => LoadConst arg1 arg2
  | 1 => LoadIndirect arg1 arg2
  | 2 => StoreIndirect arg1 arg2
  | 3 => CopyReg arg1 arg2
  | 4 => AddConst arg1 arg2
  | 5 => AddReg arg1 arg2 arg3
  | 6 => SubReg arg1 arg2 arg3
  | 7 => Jz arg1 arg2
  | 8 => Jnz arg1 arg2
  | _ => Halt
  end.

(* Single instruction execution. *)
Definition step (i : Instr) (st : State) : State :=
  let pc := read_reg REG_PC st in
  let st' := write_reg REG_PC (S pc) st in
  let st'' := match i with
  | LoadConst rd v    => write_reg rd v st'
  | LoadIndirect rd ra  => write_reg rd (read_mem (read_reg ra st) st) st'
  | StoreIndirect ra rv => write_mem (read_reg ra st) (read_reg rv st) st'
  | CopyReg rd rs     => write_reg rd (read_reg rs st) st'
  | AddConst rd v     => write_reg rd (read_reg rd st + v) st'
  | AddReg rd rs1 rs2 => write_reg rd (read_reg rs1 st + read_reg rs2 st) st'
  | SubReg rd rs1 rs2 => write_reg rd (read_reg rs1 st - read_reg rs2 st) st'
  | Jz rc target      => if Nat.eqb (read_reg rc st) 0 then write_reg REG_PC target st else st'
  | Jnz rc target     => if Nat.eqb (read_reg rc st) 0 then st' else write_reg REG_PC target st
  | Halt              => st
  end in
  {| regs := st''.(regs); mem := st''.(mem); cost := st''.(cost) + instr_cost i |}.

(* Step function: execute one instruction *)
Definition thiele_step (s : State) : State :=
  step (decode_instr_from_mem s.(mem) (4 * read_reg REG_PC s)) s.

(* Run for n steps *)
Fixpoint thiele_run_n (s : State) (n : nat) : State :=
  match n with
  | 0 => s
  | S n' => thiele_run_n (thiele_step s) n'
  end.

Definition RULES_START_ADDR : nat := 100.
Definition TAPE_START_ADDR  : nat := 1000.

(* Concrete program implementing a small-step TM simulator. *)
Definition program_instrs : list Instr :=
  [ LoadConst REG_TEMP1 TAPE_START_ADDR;
    AddReg REG_ADDR REG_TEMP1 REG_HEAD;
    LoadIndirect REG_SYM REG_ADDR;
    LoadConst REG_ADDR RULES_START_ADDR;
    LoadIndirect REG_Q' REG_ADDR;
    CopyReg REG_TEMP1 REG_Q;
    SubReg REG_TEMP1 REG_TEMP1 REG_Q';
    Jz REG_TEMP1 12;
    AddConst REG_ADDR 5;
    Jnz REG_TEMP1 4;
    LoadConst REG_TEMP1 0;
    Jnz REG_TEMP1 0;
    CopyReg REG_TEMP1 REG_ADDR;
    AddConst REG_TEMP1 1;
    LoadIndirect REG_TEMP2 REG_TEMP1;
    CopyReg REG_TEMP1 REG_SYM;
    SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2;
    Jz REG_TEMP1 22;
    AddConst REG_ADDR 5;
    LoadConst REG_TEMP1 1;
    Jnz REG_TEMP1 4;
    LoadConst REG_TEMP1 0;
    CopyReg REG_TEMP1 REG_ADDR;
    AddConst REG_TEMP1 2;
    LoadIndirect REG_Q' REG_TEMP1;
    AddConst REG_TEMP1 1;
    LoadIndirect REG_WRITE REG_TEMP1;
    AddConst REG_TEMP1 1;
    LoadIndirect REG_MOVE REG_TEMP1;
    CopyReg REG_TEMP1 REG_HEAD;
    LoadConst REG_TEMP2 TAPE_START_ADDR;
    AddReg REG_ADDR REG_TEMP1 REG_TEMP2;
    StoreIndirect REG_ADDR REG_WRITE;
    CopyReg REG_TEMP1 REG_MOVE;
    Jnz REG_TEMP1 38;
    LoadConst REG_TEMP2 1;
    SubReg REG_HEAD REG_HEAD REG_TEMP2;
    Jnz REG_TEMP2 46;
    LoadConst REG_TEMP2 1;
    SubReg REG_TEMP1 REG_MOVE REG_TEMP2;
    Jnz REG_TEMP1 43;
    LoadConst REG_TEMP1 1;
    Jnz REG_TEMP1 46;
    LoadConst REG_TEMP2 1;
    AddReg REG_HEAD REG_HEAD REG_TEMP2;
    Jnz REG_TEMP2 46;
    CopyReg REG_Q REG_Q';
    LoadConst REG_TEMP1 1;
    Jnz REG_TEMP1 0
  ].

(* Encode the program *)
Definition encode_program (instrs : list Instr) : list nat :=
  flat_map encode_instr_words instrs.

Definition program : list nat := encode_program program_instrs.
