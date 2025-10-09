Require Import ThieleUniversal.TM.
Require Import ThieleUniversal.CPU.
Require Import UTM_Encode.
Require Import List.
Require Import Lia.
Require Import Arith.
Import ListNotations.

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

  Lemma nth_firstn_lt : forall (A : Type) n m (l : list A) d,
    n < m -> nth n (firstn m l) d = nth n l d.
  Proof.
    intros A n m l d Hlt.
    revert n l Hlt.
    induction m as [|m IH]; intros [|n] l Hlt; simpl in *; try lia.
    - destruct l; reflexivity.
    - destruct l as [|x xs]; simpl; [reflexivity|].
      apply IH. lia.
  Qed.

  Lemma program_instrs_length_gt_48 : 48 < length program_instrs.
  Proof. cbn; lia. Qed.

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
      assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (cbn; reflexivity).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | StoreIndirect _ _ => False
                        | _ => True
                        end) (firstn 29 program_instrs)).
  { cbn. repeat constructor. }
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
      assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (cbn; reflexivity).
    assert (Hlen : length prefix = 29) by (subst prefix; exact Hlen_raw).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | Jz _ target => target < 29
                        | Jnz _ target => target < 29
                        | _ => True
                        end) (firstn 29 program_instrs)).
  { cbn. repeat constructor; try lia. }
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

  Lemma program_instrs_before_apply_reg_bound :
    forall pc,
      pc < 29 ->
      match nth pc program_instrs Halt with
      | LoadConst rd _ => rd < 10
      | LoadIndirect rd _ => rd < 10
      | CopyReg rd _ => rd < 10
      | AddConst rd _ => rd < 10
      | AddReg rd _ _ => rd < 10
      | SubReg rd _ _ => rd < 10
      | Jz rc _ => rc < 10
      | Jnz rc _ => rc < 10
      | StoreIndirect _ _ => True
      | Halt => True
      end.
  Proof.
    intros pc Hpc.
    set (prefix := firstn 29 program_instrs).
      assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (cbn; reflexivity).
    assert (Hlen : length prefix = 29) by (subst prefix; exact Hlen_raw).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | LoadConst rd _
                        | LoadIndirect rd _
                        | CopyReg rd _
                        | AddConst rd _
                        | AddReg rd _ _
                        | SubReg rd _ _ => rd < 10
                        | Jz rc _
                        | Jnz rc _ => rc < 10
                        | StoreIndirect _ _ => True
                        | Halt => True
                        end) (firstn 29 program_instrs)).
  { cbn. repeat constructor; try lia. }
    assert (Hforall :
              Forall (fun instr =>
                        match instr with
                        | LoadConst rd _
                        | LoadIndirect rd _
                        | CopyReg rd _
                        | AddConst rd _
                        | AddReg rd _ _
                        | SubReg rd _ _ => rd < 10
                        | Jz rc _
                        | Jnz rc _ => rc < 10
                        | StoreIndirect _ _ => True
                        | Halt => True
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
                                         | LoadConst rd _
                                         | LoadIndirect rd _
                                         | CopyReg rd _
                                         | AddConst rd _
                                         | AddReg rd _ _
                                         | SubReg rd _ _ => rd < 10
                                         | Jz rc _
                                         | Jnz rc _ => rc < 10
                                         | StoreIndirect _ _ => True
                                         | Halt => True
                                         end)
                                      prefix) Hforall) as Hforall'.
    apply Hforall'.
    apply nth_In.
    rewrite Hlen.
    exact Hpc.
  Qed.

  Lemma program_instrs_pc29 :
    nth 29 program_instrs Halt = CopyReg REG_TEMP1 REG_HEAD.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc7 :
    nth 7 program_instrs Halt = Jz REG_TEMP1 12.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc9 :
    nth 9 program_instrs Halt = Jnz REG_TEMP1 4.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc11 :
    nth 11 program_instrs Halt = Jnz REG_TEMP1 0.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc17 :
    nth 17 program_instrs Halt = Jz REG_TEMP1 22.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc20 :
    nth 20 program_instrs Halt = Jnz REG_TEMP1 4.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc21 :
    nth 21 program_instrs Halt = LoadConst REG_TEMP1 0.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc22 :
    nth 22 program_instrs Halt = CopyReg REG_TEMP1 REG_ADDR.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc23 :
    nth 23 program_instrs Halt = AddConst REG_TEMP1 2.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc24 :
    nth 24 program_instrs Halt = LoadIndirect REG_Q' REG_TEMP1.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc25 :
    nth 25 program_instrs Halt = AddConst REG_TEMP1 1.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc26 :
    nth 26 program_instrs Halt = LoadIndirect REG_WRITE REG_TEMP1.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc27 :
    nth 27 program_instrs Halt = AddConst REG_TEMP1 1.
  Proof. reflexivity. Qed.

  Lemma program_instrs_pc28 :
    nth 28 program_instrs Halt = LoadIndirect REG_MOVE REG_TEMP1.
  Proof. reflexivity. Qed.

  Lemma program_instrs_before_apply_pc_unchanged :
    forall pc,
      pc < 29 ->
      match nth pc program_instrs Halt with
      | Jz _ _ => True
      | Jnz _ _ => True
      | instr => pc_unchanged instr
      end.
  Proof.
    intros pc Hpc.
    set (prefix := firstn 29 program_instrs).
      assert (Hlen_raw : length (firstn 29 program_instrs) = 29) by (cbn; reflexivity).
    assert (Hlen : length prefix = 29) by (subst prefix; exact Hlen_raw).
    assert (Hforall_raw :
              Forall (fun instr =>
                        match instr with
                        | LoadConst rd val => pc_unchanged (LoadConst rd val)
                        | LoadIndirect rd ra => pc_unchanged (LoadIndirect rd ra)
                        | StoreIndirect ra rv => pc_unchanged (StoreIndirect ra rv)
                        | CopyReg rd rs => pc_unchanged (CopyReg rd rs)
                        | AddConst rd val => pc_unchanged (AddConst rd val)
                        | AddReg rd rs1 rs2 => pc_unchanged (AddReg rd rs1 rs2)
                        | SubReg rd rs1 rs2 => pc_unchanged (SubReg rd rs1 rs2)
                        | Jz _ _ => True
                        | Jnz _ _ => True
                        | Halt => pc_unchanged Halt
                        end) (firstn 29 program_instrs)).
  { cbn. repeat constructor; try discriminate; try lia. }
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
                                         | LoadConst rd val => pc_unchanged (LoadConst rd val)
                                         | LoadIndirect rd ra => pc_unchanged (LoadIndirect rd ra)
                                         | StoreIndirect ra rv => pc_unchanged (StoreIndirect ra rv)
                                         | CopyReg rd rs => pc_unchanged (CopyReg rd rs)
                                         | AddConst rd val => pc_unchanged (AddConst rd val)
                                         | AddReg rd rs1 rs2 => pc_unchanged (AddReg rd rs1 rs2)
                                         | SubReg rd rs1 rs2 => pc_unchanged (SubReg rd rs1 rs2)
                                         | Jz _ _ => True
                                         | Jnz _ _ => True
                                         | Halt => pc_unchanged Halt
                                         end)
                                      prefix) Hforall) as Hforall'.
    apply Hforall'.
    apply nth_In.
    rewrite Hlen.
    exact Hpc.
  Qed.

  Lemma program_instrs_monotonic_after_apply : forall pc,
    29 <= pc < 48 ->
    match nth pc program_instrs Halt with
    | Jz _ target => 29 <= target
    | Jnz _ target => 29 <= target
    | instr => pc_unchanged instr
    end.
  Proof.
    intros pc Hpc.
    destruct pc; try lia.
    (* pc >= 29 *)
    do 29 (destruct pc; try lia).
    (* now pc = 29 + n for n=0 to 18 *)
    (* 29: CopyReg *)
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 30: LoadConst *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 31: AddReg *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 32: StoreIndirect *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. exact I.
    (* 33: CopyReg *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 34: Jnz to 38 *)
    destruct pc; try lia.
    simpl. lia.
    (* 35: LoadConst *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 36: SubReg *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 37: Jnz to 46 *)
    destruct pc; try lia.
    simpl. lia.
    (* 38: LoadConst *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 39: SubReg *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 40: Jnz to 43 *)
    destruct pc; try lia.
    simpl. lia.
    (* 41: LoadConst *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 42: Jnz to 46 *)
    destruct pc; try lia.
    simpl. lia.
    (* 43: LoadConst *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 44: AddReg *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 45: Jnz to 46 *)
    destruct pc; try lia.
    simpl. lia.
    (* 46: CopyReg *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* 47: LoadConst *)
    destruct pc; try lia.
    simpl. unfold CPU.pc_unchanged. simpl. intros H; discriminate.
    (* pc = 48 would be next, but <48 *)
  Qed.

End UTM_Program.
