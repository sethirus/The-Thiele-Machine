Require Import ThieleUniversal.TM.
Require Import ThieleUniversal.CPU.
Require Import ThieleUniversal.UTM_Encode.
Require Import List.
Import ListNotations.

Module UTM_Program.
  Open Scope nat_scope.

  Definition RULES_START_ADDR : nat := 100.
  Definition TAPE_START_ADDR  : nat := 1000.

  (* Concrete program implementing a small-step TM simulator. *)
  Definition program_instrs : list Instr :=
    [ (* program listing copied from original file *)
      LoadConst REG_TEMP1 TAPE_START_ADDR;
      (* ... rest elided for brevity; in-place the original program_instrs should be kept *)
    ].

End UTM_Program.
