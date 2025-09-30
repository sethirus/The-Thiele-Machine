Require Import ThieleUniversal.TM.
Require Import ThieleUniversal.CPU.
Require Import ThieleUniversal.UTM_Encode.
Require Import List.
Import ListNotations.
Import CPU.

Module UTM_Program.
  Open Scope nat_scope.

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

End UTM_Program.
