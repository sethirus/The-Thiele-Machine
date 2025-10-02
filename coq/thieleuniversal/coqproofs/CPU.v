Require Import List.
Require Import Nat.
Require Import ZArith.
Require Import TM.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

Module CPU.

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

  (* Machine state: register file and memory. *)
  Record State := { regs : list nat; mem : list nat }.

  (* Register and memory helpers. *)
  Definition read_reg (r : nat) (st : State) : nat := nth r st.(regs) 0.
  Definition write_reg (r v : nat) (st : State) : State :=
    {| regs := firstn r st.(regs) ++ [v] ++ skipn (S r) st.(regs); mem := st.(mem) |}.

  Definition read_mem (addr : nat) (st : State) : nat := nth addr st.(mem) 0.
  Definition write_mem (addr v : nat) (st : State) : State :=
    {| regs := st.(regs); mem := firstn addr st.(mem) ++ [v] ++ skipn (S addr) st.(mem) |}.

  (* Single instruction execution. *)
  Definition step (i : Instr) (st : State) : State :=
    let pc := read_reg REG_PC st in
    let st' := write_reg REG_PC (S pc) st in
    match i with
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
    end.

  (* --- Basic register lemmas for reasoning about the program counter --- *)

  Lemma read_pc_write_pc : forall v st,
    read_reg REG_PC (write_reg REG_PC v st) = v.
  Proof.
    intros v st. unfold read_reg, write_reg. simpl. reflexivity.
  Qed.

  Lemma read_pc_write_nonpc : forall rd v st,
    rd <> REG_PC -> regs st <> [] ->
    read_reg REG_PC (write_reg rd v st) = read_reg REG_PC st.
  Proof.
    intros rd v st Hneq Hlen. unfold read_reg, write_reg.
    destruct rd; simpl in *.
    - contradiction.
    - destruct (regs st) as [|a l]; [contradiction|reflexivity].
  Qed.

  Lemma read_pc_write_mem : forall addr v st,
    read_reg REG_PC (write_mem addr v st) = read_reg REG_PC st.
  Proof.
    intros addr v st. unfold read_reg, write_mem. simpl. reflexivity.
  Qed.

  (* Instructions that do not modify the program counter. *)
  Definition pc_unchanged (i:Instr) : Prop :=
    match i with
    | LoadConst rd _ | LoadIndirect rd _ | CopyReg rd _
    | AddConst rd _ | AddReg rd _ _ | SubReg rd _ _ => rd <> REG_PC
    | StoreIndirect _ _ => True
    | _ => False
    end.

  Lemma step_pc_succ : forall i st,
    pc_unchanged i ->
    read_reg REG_PC (step i st) = S (read_reg REG_PC st).
  Proof.
    intros i st Hun.
    destruct i as
      [rd v | rd ra | ra rv | rd rs | rd v | rd r1 r2 | rd r1 r2 | rc target | rc target |];
      simpl in Hun; try contradiction;
      unfold step; remember (read_reg REG_PC st) as pc; simpl.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=v); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_mem (read_reg ra st) st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - rewrite read_pc_write_mem. rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg rs st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg rd st + v); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg r1 st + read_reg r2 st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg r1 st - read_reg r2 st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
  Qed.

  (* Helper lemmas for jump instructions *)
  Lemma step_jz_true : forall rc target st,
    Nat.eqb (read_reg rc st) 0 = true ->
    read_reg REG_PC (step (Jz rc target) st) = target.
  Proof.
    intros rc target st Heq.
    unfold step. rewrite Heq. apply read_pc_write_pc.
  Qed.

  Lemma step_jz_false : forall rc target st,
    Nat.eqb (read_reg rc st) 0 = false ->
    read_reg REG_PC (step (Jz rc target) st) = S (read_reg REG_PC st).
  Proof.
    intros rc target st Heq.
    unfold step. rewrite Heq. apply read_pc_write_pc.
  Qed.

  Lemma step_jnz_true : forall rc target st,
    Nat.eqb (read_reg rc st) 0 = true ->
    read_reg REG_PC (step (Jnz rc target) st) = S (read_reg REG_PC st).
  Proof.
    intros rc target st Heq.
    unfold step. rewrite Heq. apply read_pc_write_pc.
  Qed.

  Lemma step_jnz_false : forall rc target st,
    Nat.eqb (read_reg rc st) 0 = false ->
    read_reg REG_PC (step (Jnz rc target) st) = target.
  Proof.
    intros rc target st Heq.
    unfold step. rewrite Heq. apply read_pc_write_pc.
  Qed.

End CPU.
