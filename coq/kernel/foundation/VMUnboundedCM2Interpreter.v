(** CM2 variant: jump on successful decrement; zero falls through.
    This is the control convention of Dudenhefner, FSCD 2022, Definition 2.
    The earlier zero-branch Minsky modules are preserved with their own scope.
    https://doi.org/10.4230/LIPIcs.FSCD.2022.16 *)
(** A fixed, data-driven interpreter for a two-counter CM2 guest.

    Guest programs are packed into one unbounded natural.  [width] is part
    of the input encoding, so instruction addresses and jump targets are
    not capped at 64 bits.  The low three bits of each word are the opcode:
      0 halt, 1 inc counter 0, 2 inc counter 1,
      3 zero/decrement counter 0, 4 zero/decrement counter 1.
    For opcodes 3 and 4, the remaining high bits are the nonzero decrement target.

    The host program below is one fixed list.  Code, width, guest pc, and
    counters occur only in the initial host data registers. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterCode.

Record CM2ConfigU := {
  cc_pc : nat;
  cc_c0 : nat;
  cc_c1 : nat
}.

Inductive CM2InstrU :=
| CM2_Halt
| CM2_Inc0
| CM2_Inc1
| CM2_DecJump0 (target : nat)
| CM2_DecJump1 (target : nat).

Definition encode_cm2_instr (i : CM2InstrU) : nat :=
  match i with
  | CM2_Halt => 0
  | CM2_Inc0 => 1
  | CM2_Inc1 => 2
  | CM2_DecJump0 t => 3 + 8 * t
  | CM2_DecJump1 t => 4 + 8 * t
  end.

Definition cm2_step_instr (i : CM2InstrU) (c : CM2ConfigU)
    : option CM2ConfigU :=
  match i with
  | CM2_Halt => None
  | CM2_Inc0 => Some {| cc_pc := S c.(cc_pc); cc_c0 := S c.(cc_c0); cc_c1 := c.(cc_c1) |}
  | CM2_Inc1 => Some {| cc_pc := S c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := S c.(cc_c1) |}
  | CM2_DecJump0 t =>
      if Nat.eqb c.(cc_c0) 0
      then Some {| cc_pc := S c.(cc_pc); cc_c0 := 0; cc_c1 := c.(cc_c1) |}
      else Some {| cc_pc := t; cc_c0 := pred c.(cc_c0); cc_c1 := c.(cc_c1) |}
  | CM2_DecJump1 t =>
      if Nat.eqb c.(cc_c1) 0
      then Some {| cc_pc := S c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := 0 |}
      else Some {| cc_pc := t; cc_c0 := c.(cc_c0); cc_c1 := pred c.(cc_c1) |}
  end.

Inductive cm2_run (p : list CM2InstrU) : CM2ConfigU -> CM2ConfigU -> Prop :=
| cm2_run_refl : forall c, cm2_run p c c
| cm2_run_step : forall c i c1 c2,
    nth_error p c.(cc_pc) = Some i ->
    cm2_step_instr i c = Some c1 ->
    cm2_run p c1 c2 ->
    cm2_run p c c2.

Inductive cm2_run_n (p : list CM2InstrU)
    : nat -> CM2ConfigU -> CM2ConfigU -> Prop :=
| cm2_run_n_zero : forall c, cm2_run_n p 0 c c
| cm2_run_n_succ : forall n c i c1 c2,
    nth_error p c.(cc_pc) = Some i ->
    cm2_step_instr i c = Some c1 ->
    cm2_run_n p n c1 c2 ->
    cm2_run_n p (S n) c c2.

Definition cm2_diverges (p : list CM2InstrU) (start : CM2ConfigU) : Prop :=
  forall n, exists c, cm2_run_n p n start c.

Definition cm2_word (code width pc : nat) : nat :=
  u_and (u_shr code (pc * width)) (u_sub (u_shl 1 width) 1).

Definition cm2_interpreter_program : list vm_instruction :=
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
  ; instr_add 12 12 R2 0               (* 30 zero: next guest instruction *)
  ; instr_jump 0 0                     (* 31 next guest boundary *)
  ; instr_load_imm R6 1 0              (* 32 nonzero *)
  ; instr_sub 11 11 R6 0               (* 33 dec c0 *)
  ; instr_xfer 12 R7 0                 (* 34 nonzero: jump to target *)
  ; instr_jump 0 0                     (* 35 next guest boundary *)
  ; instr_load_imm R6 4 0              (* 36 *)
  ; instr_sub R7 R8 R6 0               (* 37 opcode - 4 *)
  ; instr_jnez R7 58 0                 (* 38 malformed *)
  ; instr_load_imm R6 3 0              (* 39 *)
  ; instr_shr R7 R5 R6 0               (* 40 target *)
  ; instr_jnez 10 44 0                 (* 41 *)
  ; instr_add 12 12 R2 0               (* 42 zero: next guest instruction *)
  ; instr_jump 0 0                     (* 43 next guest boundary *)
  ; instr_load_imm R6 1 0              (* 44 nonzero *)
  ; instr_sub 10 10 R6 0               (* 45 dec c1 *)
  ; instr_xfer 12 R7 0                 (* 46 nonzero: jump to target *)
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

Lemma cm2_interpreter_program_length : length cm2_interpreter_program = 60.
Proof. reflexivity. Qed.

(** Canonical boundary state. Scratch registers are zero, R9 is running,
    and R10..R14 contain the guest state and immutable input encoding. *)
Definition cm2_boundary (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph);
     vm_csrs := ambient.(vm_csrs);
     vm_regs := [0;0;0;0;0;0;0;0;0;0; c.(cc_c1); c.(cc_c0);
                 c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem);
     vm_pc := 0;
     vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor);
     vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc);
     vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness);
     vm_certified := ambient.(vm_certified) |}.

Record CM2Scratch := {
  ms0 : nat; ms1 : nat; ms2 : nat; ms3 : nat; ms4 : nat;
  ms5 : nat; ms6 : nat; ms7 : nat; ms8 : nat; ms15 : nat
}.

Definition cm2_boundary_s (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) (z : CM2Scratch) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [z.(ms0); z.(ms1); z.(ms2); z.(ms3); z.(ms4);
                 z.(ms5); z.(ms6); z.(ms7); z.(ms8); 0;
                 c.(cc_c1); c.(cc_c0); c.(cc_pc); width; code; z.(ms15)];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Definition cm2_rep (code width : nat) (c : CM2ConfigU) (s : VMState) : Prop :=
  exists ambient z, s = cm2_boundary_s ambient code width c z.

Definition cm2_host_steps (i : CM2InstrU) (c : CM2ConfigU) : nat :=
  match i with
  | CM2_Halt => 12
  | CM2_Inc0 => 16
  | CM2_Inc1 => 20
  | CM2_DecJump0 _ => if Nat.eqb c.(cc_c0) 0 then 23 else 25
  | CM2_DecJump1 _ => if Nat.eqb c.(cc_c1) 0 then 27 else 29
  end.

Definition zero_cm2_scratch : CM2Scratch :=
  {| ms0 := 0; ms1 := 0; ms2 := 0; ms3 := 0; ms4 := 0;
     ms5 := 0; ms6 := 0; ms7 := 0; ms8 := 0; ms15 := 0 |}.

Lemma cm2_boundary_is_rep : forall ambient code width c,
  cm2_rep code width c (cm2_boundary ambient code width c).
Proof.
  intros. exists ambient, zero_cm2_scratch.
  unfold cm2_boundary, cm2_boundary_s, zero_cm2_scratch. reflexivity.
Qed.

Definition cm2_halted (s : VMState) : Prop :=
  s.(vm_pc) = length cm2_interpreter_program /\ read_reg s 9 = 1.

Definition cm2_malformed (s : VMState) : Prop :=
  s.(vm_pc) = length cm2_interpreter_program /\ read_reg s 9 = 2.

Definition cm2_halt_rep (code width : nat) (c : CM2ConfigU) (s : VMState) : Prop :=
  exists ambient z,
    s =
    {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
       vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                   u_sub (u_shl 1 width) 1; 7; 0; z.(ms6); z.(ms7); 0; 1;
                   c.(cc_c1); c.(cc_c0); c.(cc_pc); width; code; z.(ms15)];
       vm_mem := ambient.(vm_mem); vm_pc := 60; vm_mu := ambient.(vm_mu);
       vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
       vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
       vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

(** The chosen CM2 guest language has no trapping instruction.  Trap is
    nevertheless a separate outcome class, proved unreachable below. *)
Definition cm2_traps (_p : list CM2InstrU) (_c : CM2ConfigU) : Prop := False.
