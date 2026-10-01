(** Frozen decoder, fuel-bounded evaluator, and specialization constructor. *)

From Coq Require Import List.
Import ListNotations.
From Kernel Require Import VMStep VMInstructionEncoding VMSelfGuest VMSelfRun.
From Kernel Require Import VMSelfRice VMRecursionTarget.

Definition g_reify_instruction (i : vm_instruction) : option GInstr :=
  match i with
  | instr_halt c => Some (GHalt c)
  | instr_load_imm d imm c => Some (GLoadImm d imm c)
  | instr_xfer d s c => Some (GXfer d s c)
  | instr_add d a b c => Some (GAdd d a b c)
  | instr_sub d a b c => Some (GSub d a b c)
  | instr_mul d a b c => Some (GMul d a b c)
  | instr_and d a b c => Some (GAnd d a b c)
  | instr_or d a b c => Some (GOr d a b c)
  | instr_shl d a b c => Some (GShl d a b c)
  | instr_shr d a b c => Some (GShr d a b c)
  | instr_jump t c => Some (GJump t c)
  | instr_jnez r t c => Some (GJnez r t c)
  | _ => None
  end.

Fixpoint g_reify_program (p : list vm_instruction) : option (list GInstr) :=
  match p with
  | [] => Some []
  | i :: rest =>
      match g_reify_instruction i, g_reify_program rest with
      | Some gi, Some gp => Some (gi :: gp)
      | _, _ => None
      end
  end.

Definition g_decode_program (code : nat) : option (list GInstr) :=
  g_reify_program (nat_to_program code).

Definition g_eval (fuel code input : nat) : option GConf :=
  match g_decode_program code with
  | Some p => Some (g_run fuel p (g_input input))
  | None => None
  end.

Definition g_specialize (p : list GInstr) (x : nat) : list GInstr :=
  GLoadImm 0 x 0 :: reloc 1 p.
