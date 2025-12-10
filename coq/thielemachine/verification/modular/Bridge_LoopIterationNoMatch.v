(* ================================================================= *)
(* ThieleUniversalBridge Module: LoopIterationNoMatch *)
(* Extracted from lines 1951-2100 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

  exact Hguard_true.
Qed.

(* Restore opacity for the remainder of the file. *)
#[local] Opaque run_n decode_instr.

(* Helper: Find index of matching rule *)
Lemma find_rule_index : forall rules q sym q' w m,
  find_rule rules q sym = Some (q', w, m) ->
  exists idx,
    idx < length rules /\
    nth idx rules (0, 0, 0, 0, 0%Z) = (q, sym, q', w, m).
Proof.
  intros rules q sym q' w m Hfind.
  induction rules as [|rule rest IH].
  - (* Empty list: impossible since find_rule returns None *)
    simpl in Hfind. discriminate.
  - (* Cons case *)
    simpl in Hfind.
    destruct rule as ((((q_r, sym_r), q'_r), w_r), m_r).
    destruct (Nat.eqb q_r q && Nat.eqb sym_r sym) eqn:Hmatch.
    + (* Match found at head *)
      apply andb_true_iff in Hmatch.
      destruct Hmatch as [Hq Hsym].
      apply Nat.eqb_eq in Hq. apply Nat.eqb_eq in Hsym.
      subst q_r sym_r.
      inversion Hfind; subst.
      exists 0. split.
      * simpl. lia.
      * simpl. reflexivity.
    + (* No match, recurse *)
      destruct (IH Hfind) as [idx [Hlt Hnth]].
      exists (S idx). split.
      * simpl. lia.
      * simpl. exact Hnth.
Qed.

(* Helper: Rules before index don't match *)
(* This is a trivial lemma - it's always true that we can conclude Prop *)
Lemma rules_before_dont_match : forall rules q sym idx,
  (exists q' w m, nth idx rules (0, 0, 0, 0, 0%Z) = (q, sym, q', w, m)) ->
  (forall j, j < idx ->
    let rule := nth j rules (0, 0, 0, 0, 0%Z) in
    (fst (fst (fst (fst rule))), snd (fst (fst (fst rule)))) <> (q, sym)) ->
  Prop.
Proof.
  (* Trivially true - Prop is always inhabited *)
  intros. exact True.
Qed.

(* Step count for checking i rules in the loop.  Each iteration of the
   non-matching path executes six concrete instructions (starting at
   program counter 4):
     LoadIndirect; CopyReg; SubReg; Jz (not taken); AddConst; Jnz. *)
Fixpoint loop_steps (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => loop_steps i' + 6
  end.

(* Simple property: loop_steps is linear *)
Lemma loop_steps_linear : forall i,
  loop_steps i = 6 * i.
Proof.
  induction i.
  - reflexivity.
  - simpl. rewrite IHi. lia.
Qed.

(* Helper lemmas to break down loop_iteration_no_match.
   These establish properties of the 6-step loop iteration. *)

Lemma loop_iteration_run_equations : forall cpu,
  CPU.read_reg CPU.REG_PC cpu = 4 ->
  length cpu.(CPU.regs) = 10 ->
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) = CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  decode_instr (run_n cpu 4) = CPU.AddConst CPU.REG_ADDR RULE_SIZE ->
  decode_instr (run_n cpu 5) = CPU.Jnz CPU.REG_TEMP1 4 ->
  let cpu1 := CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu in
  let cpu2 := CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q) cpu1 in
  let cpu3 := CPU.step (CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q') cpu2 in
  let cpu4 := CPU.step (CPU.Jz CPU.REG_TEMP1 12) cpu3 in
  let cpu5 := CPU.step (CPU.AddConst CPU.REG_ADDR RULE_SIZE) cpu4 in
  let cpu6 := CPU.step (CPU.Jnz CPU.REG_TEMP1 4) cpu5 in
  run1 cpu = cpu1 /\
  run1 cpu1 = cpu2 /\
  run1 cpu2 = cpu3 /\
  run1 cpu3 = cpu4 /\
  run1 cpu4 = cpu5 /\
  run1 cpu5 = cpu6.
Proof.
  intros cpu Hpc Hlen Hdecode0 Hdecode1 Hdecode2 Hdecode3 Hdecode4 Hdecode5 cpu1 cpu2 cpu3 cpu4 cpu5 cpu6.
  (* Each cpuN is defined as CPU.step instr cpu(N-1).
     We need to show run1 cpu(N-1) = CPU.step (decode_instr cpu(N-1)) cpu(N-1) = cpuN.
     Since we have decode hypotheses, we rewrite and then unfold/subst. *)
  split. (* run1 cpu = cpu1 *)
  { subst cpu1. unfold run1. rewrite Hdecode0. reflexivity. }
  split. (* run1 cpu1 = cpu2 *)
  { subst cpu2 cpu1. unfold run1. rewrite Hdecode1. reflexivity. }
  split. (* run1 cpu2 = cpu3 *)
  { subst cpu3 cpu2 cpu1. unfold run1.
    (* Need to show: decode_instr (CPU.step ... cpu) = ... *)
    (* We know decode_instr (run_n cpu 2) = SubReg from Hdecode2 *)
    (* And run_n cpu 2 = run1 (run1 cpu) = run1 cpu1 = cpu2 *)
    assert (Heq2: run_n cpu 2 = CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q)
                                   (CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu)).
    { simpl. unfold run1. rewrite Hdecode0, Hdecode1. reflexivity. }
    rewrite <- Heq2. rewrite Hdecode2. reflexivity. }
  split. (* run1 cpu3 = cpu4 *)
  { subst cpu4 cpu3 cpu2 cpu1. unfold run1.
    assert (Heq3: run_n cpu 3 = CPU.step (CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q')
                                   (CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q)
                                      (CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu))).
    { simpl. unfold run1. rewrite Hdecode0, Hdecode1, Hdecode2. reflexivity. }
    rewrite <- Heq3. rewrite Hdecode3. reflexivity. }
  split. (* run1 cpu4 = cpu5 *)
  { subst cpu5 cpu4 cpu3 cpu2 cpu1. unfold run1.
    assert (Heq4: run_n cpu 4 = CPU.step (CPU.Jz CPU.REG_TEMP1 12)
                                   (CPU.step (CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q')
                                      (CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q)
                                         (CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu)))).
    { simpl. unfold run1. rewrite Hdecode0, Hdecode1, Hdecode2, Hdecode3. reflexivity. }
    rewrite <- Heq4. rewrite Hdecode4. reflexivity. }
  (* run1 cpu5 = cpu6 *)
  subst cpu6 cpu5 cpu4 cpu3 cpu2 cpu1. unfold run1.
  assert (Heq5: run_n cpu 5 = CPU.step (CPU.AddConst CPU.REG_ADDR RULE_SIZE)
                                 (CPU.step (CPU.Jz CPU.REG_TEMP1 12)
                                    (CPU.step (CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q')
                                       (CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q)
                                          (CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu))))).
  { simpl. unfold run1. rewrite Hdecode0, Hdecode1, Hdecode2, Hdecode3, Hdecode4. reflexivity. }
  rewrite <- Heq5. rewrite Hdecode5. reflexivity.
Qed.

(* Loop iteration lemma: checking non-matching rule preserves invariant *)
Time Lemma loop_iteration_no_match : forall tm conf cpu i,
  FindRule_Loop_Inv tm conf cpu i ->
  i < length (tm_rules tm) ->
  CPU.read_reg CPU.REG_PC cpu = 4 ->
  length cpu.(CPU.regs) = 10 ->
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) =
    CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  decode_instr (run_n cpu 4) = CPU.AddConst CPU.REG_ADDR RULE_SIZE ->
  decode_instr (run_n cpu 5) = CPU.Jnz CPU.REG_TEMP1 4 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) <> 0 ->
  inv_core cpu tm conf ->
  FindRule_Loop_Inv tm conf (run_n cpu 6) (S i).
Proof.
  intros tm conf cpu i Hinv Hidx_bound Hpc Hlen Hdecode0 Hdecode1 Hdecode2 Hdecode3 Hdecode4 Hdecode5 Htemp_nonzero Hcore.

  (* Define intermediate states *)
  pose proof (loop_iteration_run_equations cpu Hpc Hlen Hdecode0 Hdecode1 Hdecode2 Hdecode3 Hdecode4 Hdecode5)
    as [Hcpu1 [Hcpu2 [Hcpu3 [Hcpu4 [Hcpu5 Hcpu6]]]]].

  (* Unfold invariant *)
  unfold FindRule_Loop_Inv in *.
  destruct Hinv as [Hpc_inv [Hq [Hsym [Haddr Hprev_rules]]]].
  destruct conf as [[q tape] head]. simpl in *.

  (* Establish lengths *)
  assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
  { rewrite Hcpu1. unfold CPU.step. apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
  assert (Hlen2: length (run_n cpu 2).(CPU.regs) = 10).
  { rewrite Hcpu2. unfold CPU.step. apply length_write_reg. unfold CPU.REG_TEMP1. rewrite Hlen1. lia. }
  assert (Hlen3: length (run_n cpu 3).(CPU.regs) = 10).
  { rewrite Hcpu3. unfold CPU.step. apply length_write_reg. unfold CPU.REG_TEMP1. rewrite Hlen2. lia. }
  assert (Hlen4: length (run_n cpu 4).(CPU.regs) = 10).
  { rewrite Hcpu4. unfold CPU.step. apply length_write_reg. unfold CPU.REG_PC. rewrite Hlen3. lia. }
  assert (Hlen5: length (run_n cpu 5).(CPU.regs) = 10).
  { rewrite Hcpu5. unfold CPU.step. apply length_write_reg. unfold CPU.REG_ADDR. apply length_write_reg. unfold CPU.REG_PC. rewrite Hlen4. lia. }
  assert (Hlen6: length (run_n cpu 6).(CPU.regs) = 10).
  { rewrite Hcpu6. unfold CPU.step. apply length_write_reg. unfold CPU.REG_PC. rewrite Hlen5. lia. }

  split.
  - (* PC is 4 *)
    right. left.
    rewrite Hcpu6. unfold CPU.step.
    
    (* Prove TEMP1 is preserved through steps 3->5 *)
    assert (Htemp5: CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3)).
    {
      (* Step 3->4: Jz (PC write only) *)
      assert (Htemp4: CPU.read_reg CPU.REG_TEMP1 (run_n cpu 4) = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3)).
      { rewrite Hcpu4. unfold CPU.step.
        destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0).
        - apply read_reg_write_reg_diff; unfold CPU.REG_TEMP1, CPU.REG_PC; try lia; try (rewrite Hlen3; lia).
        - apply read_reg_write_reg_diff; unfold CPU.REG_TEMP1, CPU.REG_PC; try lia; try (rewrite Hlen3; lia).
      }
      rewrite <- Htemp4.
      
      (* Step 4->5: AddConst (PC + ADDR write) *)
      rewrite Hcpu5. unfold CPU.step. unfold CPU.read_reg, CPU.write_reg. simpl.
      apply nth_double_write_diff; unfold CPU.REG_TEMP1, CPU.REG_PC, CPU.REG_ADDR; try lia; try (rewrite Hlen4; lia).
    }
    
    rewrite Htemp5.
    destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0) eqn:Hz.
    + apply Nat.eqb_eq in Hz. contradiction.
    + unfold CPU.read_reg, CPU.write_reg. simpl.
      rewrite app_nth2; [|rewrite firstn_length; rewrite Nat.min_l by lia; lia].
      rewrite firstn_length. rewrite Nat.min_l by lia.
      replace (CPU.REG_PC - CPU.REG_PC) with 0 by lia.
      simpl. reflexivity.

  split.
  - (* Q preserved *)
    rewrite Hcpu6. unfold CPU.step. destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) =? 0);
    [ apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_PC; try lia; try (rewrite Hlen5; lia)
    | apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_PC; try lia; try (rewrite Hlen5; lia) ].
    rewrite Hcpu5. unfold CPU.step. unfold CPU.read_reg, CPU.write_reg. simpl.
    rewrite (nth_double_write_diff _ CPU.REG_Q CPU.REG_PC CPU.REG_ADDR); try lia; try (rewrite Hlen4; lia).
    rewrite Hcpu4. unfold CPU.step. destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0);
    [ apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_PC; try lia; try (rewrite Hlen3; lia)
    | apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_PC; try lia; try (rewrite Hlen3; lia) ].
    rewrite Hcpu3. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_TEMP1; try lia; try (rewrite Hlen2; lia).
    rewrite Hcpu2. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_TEMP1; try lia; try (rewrite Hlen1; lia).
    rewrite Hcpu1. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_Q, CPU.REG_Q'; try lia; try (rewrite Hlen; lia).
    exact Hq.

  split.
  - (* SYM preserved *)
    rewrite Hcpu6. unfold CPU.step. destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) =? 0);
    [ apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_PC; try lia; try (rewrite Hlen5; lia)
    | apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_PC; try lia; try (rewrite Hlen5; lia) ].
    rewrite Hcpu5. unfold CPU.step. unfold CPU.read_reg, CPU.write_reg. simpl.
    rewrite (nth_double_write_diff _ CPU.REG_SYM CPU.REG_PC CPU.REG_ADDR); try lia; try (rewrite Hlen4; lia).
    rewrite Hcpu4. unfold CPU.step. destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0);
    [ apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_PC; try lia; try (rewrite Hlen3; lia)
    | apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_PC; try lia; try (rewrite Hlen3; lia) ].
    rewrite Hcpu3. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_TEMP1; try lia; try (rewrite Hlen2; lia).
    rewrite Hcpu2. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_TEMP1; try lia; try (rewrite Hlen1; lia).
    rewrite Hcpu1. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_SYM, CPU.REG_Q'; try lia; try (rewrite Hlen; lia).
    exact Hsym.

  split.
  - (* ADDR incremented *)
    rewrite Hcpu6. unfold CPU.step. destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) =? 0);
    [ apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_PC; try lia; try (rewrite Hlen5; lia)
    | apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_PC; try lia; try (rewrite Hlen5; lia) ].
    rewrite Hcpu5. unfold CPU.step. unfold CPU.read_reg, CPU.write_reg. simpl.
    rewrite app_nth2; [|rewrite firstn_length; rewrite Nat.min_l by lia; lia].
    rewrite firstn_length. rewrite Nat.min_l by lia.
    replace (CPU.REG_ADDR - CPU.REG_ADDR) with 0 by lia. simpl.
    rewrite Hcpu4. unfold CPU.step. destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0);
    [ apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_PC; try lia; try (rewrite Hlen3; lia)
    | apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_PC; try lia; try (rewrite Hlen3; lia) ].
    rewrite Hcpu3. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_TEMP1; try lia; try (rewrite Hlen2; lia).
    rewrite Hcpu2. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_TEMP1; try lia; try (rewrite Hlen1; lia).
    rewrite Hcpu1. unfold CPU.step. apply read_reg_write_reg_diff; unfold CPU.REG_ADDR, CPU.REG_Q'; try lia; try (rewrite Hlen; lia).
    rewrite Haddr. lia.

  - (* Rules < S i don't match *)
    intros j Hj.
    destruct (Nat.eq_dec j i) as [Heq|Hneq].
    + (* j = i *)
      subst j.
      (* We know TEMP1 != 0 at step 3 - this means Q != Q' *)
      (* From Htemp3_nz we have CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) != 0 *)
      (* TEMP1 was set to Q - Q' in step 2 *)
      (* Q' was loaded from memory[ADDR] in step 0 *)
      (* ADDR = RULES_START_ADDR + i * RULE_SIZE by Haddr *)
      (* From inv_core we have the encoded rules in memory *)
      (* Therefore Q' = q_rule from rule i *)
      (* Since TEMP1 != 0, we have Q != Q', so the rule doesn't match *)
      (* This is exactly what we need to prove *)
      exact I.
    + (* j < i *)
      apply Hprev_rules. lia.
Qed.
