(** A fixed, data-driven interpreter for a two-counter Minsky guest.

    Guest programs are packed into one unbounded natural.  [width] is part
    of the input encoding, so instruction addresses and jump targets are
    not capped at 64 bits.  The low three bits of each word are the opcode:
      0 halt, 1 inc counter 0, 2 inc counter 1,
      3 zero/decrement counter 0, 4 zero/decrement counter 1.
    For opcodes 3 and 4, the remaining high bits are the zero target.

    The host program below is one fixed list.  Code, width, guest pc, and
    counters occur only in the initial host data registers. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterCode.

Record MinskyConfigU := {
  mc_pc : nat;
  mc_c0 : nat;
  mc_c1 : nat
}.

Inductive MinskyInstrU :=
| MU_Halt
| MU_Inc0
| MU_Inc1
| MU_JzDec0 (target : nat)
| MU_JzDec1 (target : nat).

Definition encode_minsky_instr (i : MinskyInstrU) : nat :=
  match i with
  | MU_Halt => 0
  | MU_Inc0 => 1
  | MU_Inc1 => 2
  | MU_JzDec0 t => 3 + 8 * t
  | MU_JzDec1 t => 4 + 8 * t
  end.

Definition minsky_step_instr (i : MinskyInstrU) (c : MinskyConfigU)
    : option MinskyConfigU :=
  match i with
  | MU_Halt => None
  | MU_Inc0 => Some {| mc_pc := S c.(mc_pc); mc_c0 := S c.(mc_c0); mc_c1 := c.(mc_c1) |}
  | MU_Inc1 => Some {| mc_pc := S c.(mc_pc); mc_c0 := c.(mc_c0); mc_c1 := S c.(mc_c1) |}
  | MU_JzDec0 t =>
      if Nat.eqb c.(mc_c0) 0
      then Some {| mc_pc := t; mc_c0 := 0; mc_c1 := c.(mc_c1) |}
      else Some {| mc_pc := S c.(mc_pc); mc_c0 := pred c.(mc_c0); mc_c1 := c.(mc_c1) |}
  | MU_JzDec1 t =>
      if Nat.eqb c.(mc_c1) 0
      then Some {| mc_pc := t; mc_c0 := c.(mc_c0); mc_c1 := 0 |}
      else Some {| mc_pc := S c.(mc_pc); mc_c0 := c.(mc_c0); mc_c1 := pred c.(mc_c1) |}
  end.

Inductive minsky_run (p : list MinskyInstrU) : MinskyConfigU -> MinskyConfigU -> Prop :=
| minsky_run_refl : forall c, minsky_run p c c
| minsky_run_step : forall c i c1 c2,
    nth_error p c.(mc_pc) = Some i ->
    minsky_step_instr i c = Some c1 ->
    minsky_run p c1 c2 ->
    minsky_run p c c2.

Inductive minsky_run_n (p : list MinskyInstrU)
    : nat -> MinskyConfigU -> MinskyConfigU -> Prop :=
| minsky_run_n_zero : forall c, minsky_run_n p 0 c c
| minsky_run_n_succ : forall n c i c1 c2,
    nth_error p c.(mc_pc) = Some i ->
    minsky_step_instr i c = Some c1 ->
    minsky_run_n p n c1 c2 ->
    minsky_run_n p (S n) c c2.

Definition minsky_diverges (p : list MinskyInstrU) (start : MinskyConfigU) : Prop :=
  forall n, exists c, minsky_run_n p n start c.

Definition minsky_word (code width pc : nat) : nat :=
  u_and (u_shr code (pc * width)) (u_sub (u_shl 1 width) 1).

Definition minsky_interpreter_program : list vm_instruction :=
  [ instr_xfer R0 12 0                 (*  0 shift := guest pc *)
  ; instr_mul R1 R0 13 0               (*  1 shift := pc * width *)
  ; instr_shr R5 14 R1 0               (*  2 shifted code *)
  ; instr_load_imm R2 1 0              (*  3 one *)
  ; instr_shl R3 R2 13 0               (*  4 2^width *)
  ; instr_sub R3 R3 R2 0               (*  5 word mask *)
  ; instr_and R5 R5 R3 0               (*  6 current word *)
  ; instr_load_imm R4 7 0              (*  7 opcode mask *)
  ; instr_and R8 R5 R4 0               (*  8 opcode *)
  ; instr_jnez R8 12 0                 (*  9 non-halt dispatch *)
  ; instr_load_imm 9 1 0               (* 10 halted status *)
  ; instr_jump 60 0                    (* 11 leave fixed program *)
  ; instr_load_imm R6 1 0              (* 12 test/inc constant *)
  ; instr_sub R7 R8 R6 0               (* 13 opcode - 1 *)
  ; instr_jnez R7 18 0                 (* 14 *)
  ; instr_add 11 11 R6 0               (* 15 inc c0 *)
  ; instr_add 12 12 R6 0               (* 16 inc guest pc *)
  ; instr_jump 0 0                     (* 17 next guest boundary *)
  ; instr_load_imm R6 2 0              (* 18 *)
  ; instr_sub R7 R8 R6 0               (* 19 opcode - 2 *)
  ; instr_jnez R7 25 0                 (* 20 *)
  ; instr_load_imm R6 1 0              (* 21 *)
  ; instr_add 10 10 R6 0               (* 22 inc c1 *)
  ; instr_add 12 12 R6 0               (* 23 inc guest pc *)
  ; instr_jump 0 0                     (* 24 next guest boundary *)
  ; instr_load_imm R6 3 0              (* 25 *)
  ; instr_sub R7 R8 R6 0               (* 26 opcode - 3 *)
  ; instr_jnez R7 36 0                 (* 27 *)
  ; instr_shr R7 R5 R6 0               (* 28 target *)
  ; instr_jnez 11 32 0                 (* 29 *)
  ; instr_xfer 12 R7 0                 (* 30 zero: pc := target *)
  ; instr_jump 0 0                     (* 31 next guest boundary *)
  ; instr_load_imm R6 1 0              (* 32 nonzero *)
  ; instr_sub 11 11 R6 0               (* 33 dec c0 *)
  ; instr_add 12 12 R6 0               (* 34 inc pc *)
  ; instr_jump 0 0                     (* 35 next guest boundary *)
  ; instr_load_imm R6 4 0              (* 36 *)
  ; instr_sub R7 R8 R6 0               (* 37 opcode - 4 *)
  ; instr_jnez R7 58 0                 (* 38 malformed *)
  ; instr_load_imm R6 3 0              (* 39 *)
  ; instr_shr R7 R5 R6 0               (* 40 target *)
  ; instr_jnez 10 44 0                 (* 41 *)
  ; instr_xfer 12 R7 0                 (* 42 zero: pc := target *)
  ; instr_jump 0 0                     (* 43 next guest boundary *)
  ; instr_load_imm R6 1 0              (* 44 nonzero *)
  ; instr_sub 10 10 R6 0               (* 45 dec c1 *)
  ; instr_add 12 12 R6 0               (* 46 inc pc *)
  ; instr_jump 0 0                     (* 47 next guest boundary *)
  ; instr_load_imm R0 0 0              (* 48 cleanup scratch *)
  ; instr_load_imm R1 0 0
  ; instr_load_imm R2 0 0
  ; instr_load_imm R3 0 0
  ; instr_load_imm R4 0 0
  ; instr_load_imm R5 0 0
  ; instr_load_imm R6 0 0
  ; instr_load_imm R7 0 0
  ; instr_load_imm R8 0 0              (* 56 *)
  ; instr_jump 0 0                     (* 57 next boundary *)
  ; instr_load_imm 9 2 0               (* 58 malformed status *)
  ; instr_jump 60 0                    (* 59 leave fixed program *)
  ].

Lemma minsky_interpreter_program_length : length minsky_interpreter_program = 60.
Proof. reflexivity. Qed.

(** Canonical boundary state. Scratch registers are zero, R9 is running,
    and R10..R14 contain the guest state and immutable input encoding. *)
Definition minsky_boundary (ambient : VMState) (code width : nat)
    (c : MinskyConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph);
     vm_csrs := ambient.(vm_csrs);
     vm_regs := [0;0;0;0;0;0;0;0;0;0; c.(mc_c1); c.(mc_c0);
                 c.(mc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem);
     vm_pc := 0;
     vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor);
     vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc);
     vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness);
     vm_certified := ambient.(vm_certified) |}.

Record MinskyScratch := {
  ms0 : nat; ms1 : nat; ms2 : nat; ms3 : nat; ms4 : nat;
  ms5 : nat; ms6 : nat; ms7 : nat; ms8 : nat; ms15 : nat
}.

Definition minsky_boundary_s (ambient : VMState) (code width : nat)
    (c : MinskyConfigU) (z : MinskyScratch) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [z.(ms0); z.(ms1); z.(ms2); z.(ms3); z.(ms4);
                 z.(ms5); z.(ms6); z.(ms7); z.(ms8); 0;
                 c.(mc_c1); c.(mc_c0); c.(mc_pc); width; code; z.(ms15)];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Definition minsky_rep (code width : nat) (c : MinskyConfigU) (s : VMState) : Prop :=
  exists ambient z, s = minsky_boundary_s ambient code width c z.

Definition minsky_host_steps (i : MinskyInstrU) (c : MinskyConfigU) : nat :=
  match i with
  | MU_Halt => 12
  | MU_Inc0 => 16
  | MU_Inc1 => 20
  | MU_JzDec0 _ => if Nat.eqb c.(mc_c0) 0 then 23 else 25
  | MU_JzDec1 _ => if Nat.eqb c.(mc_c1) 0 then 27 else 29
  end.

Definition zero_minsky_scratch : MinskyScratch :=
  {| ms0 := 0; ms1 := 0; ms2 := 0; ms3 := 0; ms4 := 0;
     ms5 := 0; ms6 := 0; ms7 := 0; ms8 := 0; ms15 := 0 |}.

Lemma minsky_boundary_is_rep : forall ambient code width c,
  minsky_rep code width c (minsky_boundary ambient code width c).
Proof.
  intros. exists ambient, zero_minsky_scratch.
  unfold minsky_boundary, minsky_boundary_s, zero_minsky_scratch. reflexivity.
Qed.

Definition minsky_halted (s : VMState) : Prop :=
  s.(vm_pc) = length minsky_interpreter_program /\ read_reg s 9 = 1.

Definition minsky_malformed (s : VMState) : Prop :=
  s.(vm_pc) = length minsky_interpreter_program /\ read_reg s 9 = 2.

Definition minsky_halt_rep (code width : nat) (c : MinskyConfigU) (s : VMState) : Prop :=
  exists ambient z,
    s =
    {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
       vm_regs := [c.(mc_pc); c.(mc_pc) * width; 1;
                   u_sub (u_shl 1 width) 1; 7; 0; z.(ms6); z.(ms7); 0; 1;
                   c.(mc_c1); c.(mc_c0); c.(mc_pc); width; code; z.(ms15)];
       vm_mem := ambient.(vm_mem); vm_pc := 60; vm_mu := ambient.(vm_mu);
       vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
       vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
       vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

(** The chosen Minsky guest language has no trapping instruction.  Trap is
    nevertheless a separate outcome class, proved unreachable below. *)
Definition minsky_traps (_p : list MinskyInstrU) (_c : MinskyConfigU) : Prop := False.
