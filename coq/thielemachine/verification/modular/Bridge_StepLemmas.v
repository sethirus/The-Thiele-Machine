(* ================================================================= *)
(* ThieleUniversalBridge Module: StepLemmas *)
(* Extracted from lines 1201-1400 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

(* Dependencies noted for reference: Invariants *)
(* These are NOT imported to keep modules standalone for analysis *)

  intros cpu rd rs Hneq Hrd_bound Hlen.
  split.
  - apply CPU.step_pc_succ. unfold CPU.pc_unchanged. exact Hneq.
  - unfold CPU.step, CPU.read_reg, CPU.write_reg. simpl.
    unfold CPU.REG_PC in Hneq.
    assert (rd >= 1) by (destruct rd; [contradiction|lia]).
    destruct (CPU.regs cpu) as [|r0 rest]; [simpl in Hlen; lia|].
    simpl.
    rewrite app_nth2.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle.
      replace (rd - rd) with 0 by lia.
      simpl. reflexivity.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle. lia.
Qed.

(* Lemma for LoadIndirect execution *)
Lemma step_LoadIndirect : forall cpu rd ra,
  rd <> CPU.REG_PC ->
  rd < 10 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.LoadIndirect rd ra) cpu) = S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.LoadIndirect rd ra) cpu) = 
    CPU.read_mem (CPU.read_reg ra cpu) cpu.
Proof.
  intros cpu rd ra Hneq Hrd_bound Hlen.
  split.
  - apply CPU.step_pc_succ. unfold CPU.pc_unchanged. exact Hneq.
  - (* After step: PC incremented, then rd written with memory value *)
    unfold CPU.step, CPU.read_reg, CPU.write_reg, CPU.read_mem. simpl.
    unfold CPU.REG_PC in Hneq.
    assert (rd >= 1) by (destruct rd; [contradiction|lia]).
    destruct (CPU.regs cpu) as [|r0 rest]; [simpl in Hlen; lia|].
    simpl. 
    rewrite app_nth2.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle.
      replace (rd - rd) with 0 by lia.
      simpl. reflexivity.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle. lia.
Qed.

(* Lemma for StoreIndirect execution *)
Lemma step_StoreIndirect : forall cpu ra rv,
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.StoreIndirect ra rv) cpu) = S (CPU.read_reg CPU.REG_PC cpu).
Proof.
  intros cpu ra rv Hlen.
  apply CPU.step_pc_succ.
  unfold CPU.pc_unchanged. exact I.
Qed.

Lemma step_SubReg : forall cpu rd rs1 rs2,
  rd <> CPU.REG_PC ->
  rd < 10 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.SubReg rd rs1 rs2) cpu) =
    S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.SubReg rd rs1 rs2) cpu) =
    CPU.read_reg rs1 cpu - CPU.read_reg rs2 cpu.
Proof.
  intros cpu rd rs1 rs2 Hneq Hrd_bound Hlen.
  split.
  - apply CPU.step_pc_succ. unfold CPU.pc_unchanged. exact Hneq.
  - unfold CPU.step, CPU.read_reg, CPU.write_reg. simpl.
    unfold CPU.REG_PC in Hneq.
    assert (rd >= 1) by (destruct rd; [contradiction|lia]).
    destruct (CPU.regs cpu) as [|r0 rest]; [simpl in Hlen; lia|].
    simpl.
    rewrite app_nth2.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle.
      replace (rd - rd) with 0 by lia.
      simpl. reflexivity.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle. lia.
Qed.

Lemma step_AddConst : forall cpu rd v,
  rd <> CPU.REG_PC ->
  rd < 10 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.AddConst rd v) cpu) =
    S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.AddConst rd v) cpu) =
    CPU.read_reg rd cpu + v.
Proof.
  intros cpu rd v Hneq Hrd_bound Hlen.
  split.
  - apply CPU.step_pc_succ. unfold CPU.pc_unchanged. exact Hneq.
  - unfold CPU.step, CPU.read_reg, CPU.write_reg. simpl.
    unfold CPU.REG_PC in Hneq.
    assert (rd >= 1) by (destruct rd; [contradiction|lia]).
    destruct (CPU.regs cpu) as [|r0 rest]; [simpl in Hlen; lia|].
    simpl.
    rewrite app_nth2.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle.
      replace (rd - rd) with 0 by lia.
      simpl. reflexivity.
    + rewrite firstn_length. simpl.
      assert (Hle: rd <= S (length rest)) by (simpl in Hlen; lia).
      rewrite Nat.min_l by exact Hle. lia.
Qed.

(* Lemma for BranchZero (conditional) when rs = 0 *)
Lemma step_BranchZero_taken : forall cpu rs target,
  CPU.read_reg rs cpu = 0 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.Jz rs target) cpu) = target.
Proof.
  intros cpu rs target Hzero Hlen.
  apply CPU.step_jz_true.
  apply Nat.eqb_eq. exact Hzero.
Qed.

(* Lemma for BranchZero (conditional) when rs <> 0 *)
Lemma step_BranchZero_not_taken : forall cpu rs target,
  CPU.read_reg rs cpu <> 0 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.Jz rs target) cpu) = S (CPU.read_reg CPU.REG_PC cpu).
Proof.
  intros cpu rs target Hnonzero Hlen.
  apply CPU.step_jz_false.
  apply Nat.eqb_neq. exact Hnonzero.
Qed.

Lemma step_JumpNonZero_taken : forall cpu rs target,
  CPU.read_reg rs cpu <> 0 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.Jnz rs target) cpu) = target.
Proof.
  intros cpu rs target Hnz _.
  apply CPU.step_jnz_false.
  apply Nat.eqb_neq. exact Hnz.
Qed.

(* ----------------------------------------------------------------- *)
(* Symbolic Execution - Attempt at Proof 1                          *)
(* ----------------------------------------------------------------- *)

(* Try a direct proof approach using the specific instructions *)
(* This proof demonstrates the symbolic execution reasoning required.
   A complete proof would require:
   1. Full memory encoding invariants from setup_state
   2. Detailed register tracking through each instruction
   3. Proof that each instruction matches the expected one from UTM_Program
   
   The structure shows how to reason about multi-step execution. *)
Time Lemma transition_Fetch_to_FindRule_direct : forall tm conf cpu0,
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  cpu0 = setup_state tm conf ->
  CPU.read_reg CPU.REG_PC cpu0 = 0 ->
  length cpu0.(CPU.regs) = 10 ->
  decode_instr cpu0 =
    CPU.LoadConst CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR ->
  decode_instr (run1 cpu0) =
    CPU.AddReg CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD ->
  decode_instr (run_n cpu0 2) =
    CPU.LoadIndirect CPU.REG_SYM CPU.REG_ADDR ->
  exists cpu_find,
    run_n cpu0 3 = cpu_find /\
    IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu_find) /\
    CPU.read_reg CPU.REG_PC cpu_find = 3.
Proof.
  bridge_checkpoint ("transition_Fetch_to_FindRule_direct"%string).
  intros tm conf cpu0 Hinv_core Hfetch Hsetup Hpc0 Hlen
         Hdecode0 Hdecode1 Hdecode2.
  subst cpu0.
  remember (setup_state tm conf) as cpu_init eqn:Hinit.

  pose proof Hlen as Hlen_init.
  pose proof Hpc0 as Hpc0_init.
  pose proof Hdecode0 as Hdecode0_init.
  pose proof Hdecode1 as Hdecode1_init.
  pose proof Hdecode2 as Hdecode2_init.

  assert (Hrd_pc : CPU.REG_TEMP1 <> CPU.REG_PC) by (cbv; discriminate).
  assert (Hrd_bound : CPU.REG_TEMP1 < 10) by (cbv; lia).
  assert (Haddr_pc : CPU.REG_ADDR <> CPU.REG_PC) by (cbv; discriminate).
  assert (Haddr_bound : CPU.REG_ADDR < 10) by (cbv; lia).
  assert (Hsym_pc : CPU.REG_SYM <> CPU.REG_PC) by (cbv; discriminate).
  assert (Hsym_bound : CPU.REG_SYM < 10) by (cbv; lia).

  (* Step 0 → 1: LoadConst TEMP1, PC increments to 1. *)
  assert (Hpc1 : CPU.read_reg CPU.REG_PC (run1 cpu_init) = 1).
  { rewrite run1_decode, Hdecode0_init.
    destruct (step_LoadConst cpu_init CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR
               Hrd_pc Hrd_bound Hlen_init) as [Hpc _].
    now rewrite Hpc0_init in Hpc.
