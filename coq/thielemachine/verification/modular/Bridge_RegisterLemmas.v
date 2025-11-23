(* ================================================================= *)
(* ThieleUniversalBridge Module: RegisterLemmas *)
(* Extracted from lines 921-1200 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

  (* The universal program maintains exactly 10 registers using the axiom. *)
  (* First prove by induction that length <= 10 *)
  assert (Hle: length (CPU.regs (run_n st n)) <= 10).
  { revert st Hlen. induction n as [|n' IHn]; intros st Hlen.
    - (* Base case: n = 0 *)
      simpl. apply Nat.eq_le_incl. exact Hlen.
    - (* Inductive case: n = S n' *)
      simpl. (* run_n st (S n') = run_n (run1 st) n' *)
      change (run_n st (S n')) with (run_n (run1 st) n').
      (* Need: length (run_n (run1 st) n') <= 10 *)
      (* By IH, need: length (run1 st) = 10 *)
      assert (Hlen1: length (CPU.regs (run1 st)) = 10).
      { (* run1 st = CPU.step (decode_instr st) st *)
        unfold run1.
        (* Use the axiom: universal_program_bounded_writes *)
        assert (Hle_step: length (CPU.regs (CPU.step (decode_instr st) st)) <= 10).
        { apply universal_program_bounded_writes.
          - reflexivity.
          - rewrite Hlen. apply Nat.le_refl. }
        assert (Hge_step: length (CPU.regs (CPU.step (decode_instr st) st)) >= 10).
        { assert (H_ge: length (CPU.regs (CPU.step (decode_instr st) st)) >= length st.(CPU.regs)).
          { apply length_step_ge. }
          rewrite Hlen in H_ge. exact H_ge. }
        lia. }
      apply IHn. exact Hlen1. }
  (* Then prove that length >= 10 *)
  assert (Hge: length (CPU.regs (run_n st n)) >= 10).
  { assert (H_ge: length (CPU.regs (run_n st n)) >= length st.(CPU.regs)).
    { apply length_run_n_ge. }
    rewrite Hlen in H_ge. exact H_ge. }
  (* Combine both directions *)
  apply Nat.le_antisymm; [exact Hle | exact Hge].
Qed.

(* Helper: length is preserved by write_reg *)
Lemma length_write_reg : forall r v st,
  r < length st.(CPU.regs) ->
  length (CPU.write_reg r v st).(CPU.regs) = length st.(CPU.regs).
Proof.
  intros r v st Hr.
  unfold CPU.write_reg. simpl.
  (* Directly compute the length *)
  generalize dependent r. generalize dependent v.
  induction (CPU.regs st) as [|x xs IH]; intros.
  - simpl in Hr. lia.
  - destruct r; simpl.
    + simpl. reflexivity.
    + simpl. rewrite IH by (simpl in Hr; lia). reflexivity.
Qed.

(* Infrastructure lemmas for register tracking after simpl/unfold *)
(* These lemmas work on the expanded nth/firstn/skipn/app forms *)

(* Helper: nth on list built with firstn/skipn/app preserves original value for different indices *)
Lemma nth_write_diff : forall {A : Type} (l : list A) (r r' : nat) (v d : A),
  r <> r' ->
  r < length l ->
  r' < length l ->
  nth r (firstn r' l ++ [v] ++ skipn (S r') l) d = nth r l d.
Proof.
  intros A l r r' v d Hneq Hr Hr'.
  destruct (Nat.ltb r r') eqn:Hlt.
  - (* Case r < r': r is in the firstn part *)
    apply Nat.ltb_lt in Hlt.
    rewrite app_nth1.
    + apply nth_firstn_lt. exact Hlt.
    + rewrite firstn_length. rewrite Nat.min_l; [lia|lia].
  - (* Case r >= r', but r <> r', so r > r' *)
    apply Nat.ltb_nlt in Hlt.
    assert (r > r') by lia.
    (* r is beyond the firstn r' part *)
    rewrite app_nth2.
    + rewrite firstn_length. rewrite Nat.min_l; [|lia].
      (* nth (r - r') ([v] ++ skipn (S r') l) d = nth r l d *)
      destruct (r - r') as [|n] eqn:Hdiff; [lia|].
      simpl.
      (* nth n (skipn (S r') l) d = nth r l d *)
      assert (Heqr: r = S r' + n) by lia.
      rewrite Heqr.
      (* Now prove: nth n (skipn (S r') l) d = nth (S r' + n) l d *)
      clear Heqr Hdiff Hneq Hr Hr' H Hlt v r.
      generalize dependent n. generalize dependent r'.
      induction l as [|x xs IH]; intros.
      { destruct n, r'; reflexivity. }
      destruct r'; simpl.
      { destruct n; reflexivity. }
      { apply IH. }
    + rewrite firstn_length. rewrite Nat.min_l; [lia|lia].
Qed.

(* Specialized version for nat lists (most common case) *)
Lemma nth_nat_write_diff : forall (l : list nat) (r r' v : nat),
  r <> r' ->
  r < length l ->
  r' < length l ->
  nth r (firstn r' l ++ [v] ++ skipn (S r') l) 0 = nth r l 0.
Proof.
  intros. apply nth_write_diff; assumption.
Qed.

(* Specialized lemma for nested writes (common CPU.step pattern) *)
(* CPU.step typically writes PC first, then the target register *)
Lemma nth_double_write_diff : forall (l : list nat) (r r1 r2 v1 v2 : nat),
  r <> r1 ->
  r <> r2 ->
  r < length l ->
  r1 < length l ->
  r2 < length l ->
  nth r (firstn r2 (firstn r1 l ++ [v1] ++ skipn (S r1) l) ++ [v2] ++ 
         skipn (S r2) (firstn r1 l ++ [v1] ++ skipn (S r1) l)) 0 =
  nth r l 0.
Proof.
  intros l r r1 r2 v1 v2 Hneq1 Hneq2 Hr Hr1 Hr2.
  (* Apply nth_nat_write_diff for the outer write *)
  assert (Hlen_inner: length (firstn r1 l ++ [v1] ++ skipn (S r1) l) = length l).
  { repeat rewrite app_length. repeat rewrite firstn_length. repeat rewrite skipn_length.
    simpl. rewrite Nat.min_l by lia. lia. }
  rewrite nth_nat_write_diff.
  - (* Apply nth_nat_write_diff for the inner write *)
    apply nth_nat_write_diff; assumption.
  - exact Hneq2.
  - rewrite Hlen_inner. exact Hr.
  - rewrite Hlen_inner. exact Hr2.
Qed.

(* Ltac automation for register preservation goals *)
Ltac solve_reg_preservation :=
  match goal with
  | |- nth ?r (firstn ?r' _ ++ _ ++ skipn _ _) _ = nth ?r _ _ =>
    apply nth_nat_write_diff; [lia | lia | lia]
  | |- nth ?r (firstn ?r2 (firstn ?r1 _ ++ _ ++ skipn _ _) ++ _ ++ 
                skipn _ (firstn ?r1 _ ++ _ ++ skipn _ _)) _ = nth ?r _ _ =>
    apply nth_double_write_diff; [lia | lia | lia | lia | lia]
  end.

(* CPU.step PC progression for non-branching instructions *)
(* Note: This lemma requires that rd <> REG_PC for all register-writing instructions.
   This is a constraint on the instruction encoding that should be enforced by the
   instruction decoder or compiler. The UTM program in UTM_Program.v satisfies this. *)
Lemma step_pc_increment : forall cpu instr,
  CPU.pc_unchanged instr ->
  CPU.read_reg CPU.REG_PC (CPU.step instr cpu) = S (CPU.read_reg CPU.REG_PC cpu).
Proof.
  intros cpu instr Hpc_unch.
  apply CPU.step_pc_succ.
  exact Hpc_unch.
Qed.

(* ----------------------------------------------------------------- *)
(* Instruction Decoding Lemmas                                       *)
(* ----------------------------------------------------------------- *)

(* Import the actual UTM program from archive *)
(* The program starts at PC=0 with these instructions:
   PC=0: LoadConst REG_TEMP1 TAPE_START_ADDR  (Fetch phase)
   PC=1: AddReg REG_ADDR REG_TEMP1 REG_HEAD
   PC=2: LoadIndirect REG_SYM REG_ADDR
   PC=3: LoadConst REG_ADDR RULES_START_ADDR  (FindRule phase starts)
   ...
*)

(* Lemmas about what instructions are at specific PCs *)
Lemma instr_at_pc_0 : 
  nth 0 UTM_Program.program_instrs CPU.Halt = 
  CPU.LoadConst CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR.
Proof.
  unfold UTM_Program.program_instrs. simpl. reflexivity.
Qed.

Lemma instr_at_pc_1 :
  nth 1 UTM_Program.program_instrs CPU.Halt =
  CPU.AddReg CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD.
Proof.
  unfold UTM_Program.program_instrs. simpl. reflexivity.
Qed.

Lemma instr_at_pc_2 :
  nth 2 UTM_Program.program_instrs CPU.Halt =
  CPU.LoadIndirect CPU.REG_SYM CPU.REG_ADDR.
Proof.
  unfold UTM_Program.program_instrs. simpl. reflexivity.
Qed.

Lemma instr_at_pc_3 :
  nth 3 UTM_Program.program_instrs CPU.Halt =
  CPU.LoadConst CPU.REG_ADDR UTM_Program.RULES_START_ADDR.
Proof.
  unfold UTM_Program.program_instrs. simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Simplified Proof Attempt - Proof 1 Foundation                    *)
(* ----------------------------------------------------------------- *)

(* First, let's try to prove a simplified version where we just show
   the structure without full symbolic execution *)

Lemma transition_Fetch_to_FindRule_structure : forall tm conf cpu0,
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  exists cpu_find, run_n cpu0 3 = cpu_find.
Proof.
  intros tm conf cpu0 Hinv Hfetch.
  (* This is trivially true - running for 3 steps produces some state *)
  exists (run_n cpu0 3).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* CPU Step Execution Lemmas                                         *)
(* ----------------------------------------------------------------- *)

(* Lemma for LoadConst execution - use existing CPU lemmas *)
Lemma step_LoadConst : forall cpu rd v,
  rd <> CPU.REG_PC ->
  rd < 10 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.LoadConst rd v) cpu) = S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.LoadConst rd v) cpu) = v.
Proof.
  intros cpu rd v Hneq Hrd_bound Hlen.
  split.
  - apply CPU.step_pc_succ. unfold CPU.pc_unchanged. exact Hneq.
  - (* After step: PC incremented, then rd written with v *)
    unfold CPU.step, CPU.read_reg, CPU.write_reg. simpl.
    (* Goal is to show: nth rd (firstn rd (S (nth 0 regs 0) :: skipn 1 regs) ++ [v] ++ skipn rd (skipn 1 regs)) 0 = v *)
    (* This simplifies because rd >= 1 (since rd <> 0) *)
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

(* Lemma for AddReg execution *)
Lemma step_AddReg : forall cpu rd rs1 rs2,
  rd <> CPU.REG_PC ->
  rd < 10 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.AddReg rd rs1 rs2) cpu) = S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.AddReg rd rs1 rs2) cpu) = 
    CPU.read_reg rs1 cpu + CPU.read_reg rs2 cpu.
Proof.
  intros cpu rd rs1 rs2 Hneq Hrd_bound Hlen.
  split.
  - apply CPU.step_pc_succ. unfold CPU.pc_unchanged. exact Hneq.
  - (* After step: PC incremented, then rd written with sum *)
    unfold CPU.step, CPU.read_reg, CPU.write_reg. simpl.
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

Lemma step_CopyReg : forall cpu rd rs,
  rd <> CPU.REG_PC ->
  rd < 10 ->
  length cpu.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.CopyReg rd rs) cpu) =
    S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.CopyReg rd rs) cpu) =
    CPU.read_reg rs cpu.
Proof.
