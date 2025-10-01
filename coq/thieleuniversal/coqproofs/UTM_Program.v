Require Import TM.
Require Import CPU.
Require Import UTM_Encode.
Require Import List.
Require Import Lia.
Import ListNotations.
Import CPU.

Module UTM_Program.
  Open Scope nat_scope.

  Definition RULES_START_ADDR : nat := 100.
  Definition TAPE_START_ADDR  : nat := 1000.

  Lemma RULES_START_ADDR_le_TAPE_START_ADDR :
    RULES_START_ADDR <= TAPE_START_ADDR.
  Proof.
    unfold RULES_START_ADDR, TAPE_START_ADDR; lia.
  Qed.

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

  Lemma program_instrs_before_apply_not_store :
    forall pc,
      pc < 29 ->
      match nth pc program_instrs Halt with
      | StoreIndirect _ _ => False
      | _ => True
      end.
  Proof.
    intros pc Hpc.
    set (prefix := firstn 29 program_instrs).
    assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (vm_compute; reflexivity).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | StoreIndirect _ _ => False
                        | _ => True
                        end) (firstn 29 program_instrs)).
    { vm_compute. repeat constructor. }
    assert (Hlen : length prefix = 29) by (subst prefix; exact Hlen_raw).
    assert (Hforall :
              Forall (fun instr =>
                        match instr with
                        | StoreIndirect _ _ => False
                        | _ => True
                        end) prefix) by (subst prefix; exact Hforall_raw).
    assert (Hnth : nth pc program_instrs Halt = nth pc prefix Halt).
    { subst prefix.
      rewrite <- firstn_skipn with (n := 29) (l := program_instrs).
      rewrite List.app_nth1 by (rewrite Hlen_raw; lia).
      reflexivity.
    }
    rewrite Hnth.
    pose proof (proj1 (Forall_forall (A:=Instr)
                                      (fun instr =>
                                         match instr with
                                         | StoreIndirect _ _ => False
                                         | _ => True
                                         end)
                                      prefix) Hforall) as Hforall'.
    apply Hforall'.
    apply nth_In.
    rewrite Hlen.
    exact Hpc.
  Qed.

  Lemma program_instrs_before_apply_jump_target_lt :
    forall pc,
      pc < 29 ->
      match nth pc program_instrs Halt with
      | Jz _ target => target < 29
      | Jnz _ target => target < 29
      | _ => True
      end.
  Proof.
    intros pc Hpc.
    set (prefix := firstn 29 program_instrs).
    assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (vm_compute; reflexivity).
    assert (Hlen : length prefix = 29) by (subst prefix; exact Hlen_raw).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | Jz _ target => target < 29
                        | Jnz _ target => target < 29
                        | _ => True
                        end) (firstn 29 program_instrs)).
    { vm_compute. repeat constructor; try lia. }
    assert (Hforall :
              Forall (fun instr =>
                        match instr with
                        | Jz _ target => target < 29
                        | Jnz _ target => target < 29
                        | _ => True
                        end) prefix) by (subst prefix; exact Hforall_raw).
    assert (Hnth : nth pc program_instrs Halt = nth pc prefix Halt).
    { subst prefix.
      rewrite <- firstn_skipn with (n := 29) (l := program_instrs).
      rewrite List.app_nth1 by (rewrite Hlen_raw; lia).
      reflexivity.
    }
    rewrite Hnth.
    pose proof (proj1 (Forall_forall (A:=Instr)
                                      (fun instr =>
                                         match instr with
                                         | Jz _ target => target < 29
                                         | Jnz _ target => target < 29
                                         | _ => True
                                         end)
                                      prefix) Hforall) as Hforall'.
    apply Hforall'.
    apply nth_In.
    rewrite Hlen.
    exact Hpc.
  Qed.

  Lemma program_instrs_before_apply_pc_unchanged :
    forall pc,
      pc < 29 ->
      match nth pc program_instrs Halt with
      | Jz _ _ => True
      | Jnz _ _ => True
      | instr => CPU.pc_unchanged instr
      end.
  Proof.
    intros pc Hpc.
    set (prefix := firstn 29 program_instrs).
    assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (vm_compute; reflexivity).
    assert (Hlen : length prefix = 29) by (subst prefix; exact Hlen_raw).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | LoadConst rd val => CPU.pc_unchanged (LoadConst rd val)
                        | LoadIndirect rd ra => CPU.pc_unchanged (LoadIndirect rd ra)
                        | StoreIndirect ra rv => CPU.pc_unchanged (StoreIndirect ra rv)
                        | CopyReg rd rs => CPU.pc_unchanged (CopyReg rd rs)
                        | AddConst rd val => CPU.pc_unchanged (AddConst rd val)
                        | AddReg rd rs1 rs2 => CPU.pc_unchanged (AddReg rd rs1 rs2)
                        | SubReg rd rs1 rs2 => CPU.pc_unchanged (SubReg rd rs1 rs2)
                        | Jz _ _ => True
                        | Jnz _ _ => True
                        | Halt => CPU.pc_unchanged Halt
                        end) (firstn 29 program_instrs)).
    { vm_compute. repeat constructor; try discriminate; try lia. }
    assert (Hforall :
              Forall (fun instr =>
                        match instr with
                        | LoadConst rd val => CPU.pc_unchanged (LoadConst rd val)
                        | LoadIndirect rd ra => CPU.pc_unchanged (LoadIndirect rd ra)
                        | StoreIndirect ra rv => CPU.pc_unchanged (StoreIndirect ra rv)
                        | CopyReg rd rs => CPU.pc_unchanged (CopyReg rd rs)
                        | AddConst rd val => CPU.pc_unchanged (AddConst rd val)
                        | AddReg rd rs1 rs2 => CPU.pc_unchanged (AddReg rd rs1 rs2)
                        | SubReg rd rs1 rs2 => CPU.pc_unchanged (SubReg rd rs1 rs2)
                        | Jz _ _ => True
                        | Jnz _ _ => True
                        | Halt => CPU.pc_unchanged Halt
                        end) prefix) by (subst prefix; exact Hforall_raw).
    assert (Hnth : nth pc program_instrs Halt = nth pc prefix Halt).
    { subst prefix.
      rewrite <- firstn_skipn with (n := 29) (l := program_instrs).
      rewrite List.app_nth1 by (rewrite Hlen_raw; lia).
      reflexivity. }
    rewrite Hnth.
    pose proof (proj1 (Forall_forall (A:=Instr)
                                      (fun instr =>
                                         match instr with
                                         | LoadConst rd val => CPU.pc_unchanged (LoadConst rd val)
                                         | LoadIndirect rd ra => CPU.pc_unchanged (LoadIndirect rd ra)
                                         | StoreIndirect ra rv => CPU.pc_unchanged (StoreIndirect ra rv)
                                         | CopyReg rd rs => CPU.pc_unchanged (CopyReg rd rs)
                                         | AddConst rd val => CPU.pc_unchanged (AddConst rd val)
                                         | AddReg rd rs1 rs2 => CPU.pc_unchanged (AddReg rd rs1 rs2)
                                         | SubReg rd rs1 rs2 => CPU.pc_unchanged (SubReg rd rs1 rs2)
                                         | Jz _ _ => True
                                         | Jnz _ _ => True
                                         | Halt => CPU.pc_unchanged Halt
                                         end)
                                      prefix) Hforall) as Hforall'.
    apply Hforall'.
    apply nth_In.
    rewrite Hlen.
    exact Hpc.
  Qed.

End UTM_Program.
