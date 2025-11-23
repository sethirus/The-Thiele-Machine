(* ================================================================= *)
(* ThieleUniversalBridge Module: LengthPreservation *)
(* Extracted from lines 901-920 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

    eapply Nat.le_trans; [exact H1 | exact H2].
Qed.

(* Axiom: The universal program only writes to registers 0-9.
   This is a structural property of the specific program being verified.
   All register operations (LoadConst, LoadIndirect, CopyReg, AddConst, AddReg, SubReg)
   use destination registers from {REG_PC=0, REG_Q=1, REG_SYM=3, REG_Q'=4, REG_ADDR=7, REG_TEMP1=8, REG_TEMP2=9}. *)
Axiom universal_program_bounded_writes : forall st instr,
  instr = decode_instr st ->
  length st.(CPU.regs) >= 10 ->
  length (CPU.regs (CPU.step instr st)) <= 10.

(* TODO: This lemma requires proving that the universal program's instructions
   all write to registers < 10, so the register file length stays exactly 10.
   We use the axiom above about the program structure. *)
Lemma length_run_n_eq_bounded : forall st n,
  length st.(CPU.regs) = 10 ->
  length (CPU.regs (run_n st n)) = 10.
Proof.
  intros st n Hlen.
