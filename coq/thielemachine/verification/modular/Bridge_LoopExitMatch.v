(* ================================================================= *)
(* ThieleUniversalBridge Module: LoopExitMatch *)
(* Extracted from lines 2101-2300 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  let rule := nth i (tm_rules tm) (0, 0, 0, 0, 0%Z) in
  (fst (fst (fst (fst rule))), snd (fst (fst (fst rule)))) <> (q, sym) ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) <> 0 ->
  exists cpu',
    run_n cpu 6 = cpu' /\
    FindRule_Loop_Inv tm conf cpu' (S i).
Proof.
  intros tm conf cpu i Hinv Hi_bound Hpc Hlen
         Hdecode0 Hdecode1 Hdecode2 Hdecode3 Hdecode4 Hdecode5.
  (* Destruct conf to introduce the let bindings *)
  destruct conf as [[q tape] head].
  intros sym rule Hrule_no_match Htemp_nonzero.
  
  (* Witness: cpu' = run_n cpu 6 *)
  exists (run_n cpu 6).
  split; [reflexivity|].
  
  (* Unfold the loop invariant for the input state *)
  unfold FindRule_Loop_Inv in Hinv.
  simpl in *.
  destruct Hinv as [Hpc_in_loop [Hq [Hsym [Haddr Hprev_rules]]]].
  
  (* The PC starts at 4 from Hpc hypothesis, so take the middle case *)
  assert (Hpc_eq: CPU.read_reg CPU.REG_PC cpu = 4) by (destruct Hpc_in_loop as [H|[H|H]]; [lia|exact H|lia]).
  clear Hpc_in_loop Hpc. (* Clean up, we have Hpc_eq *)
  
  (* Define intermediate states for clarity *)
  set (cpu1 := run1 cpu).
  set (cpu2 := run1 cpu1).
  set (cpu3 := run1 cpu2).
  set (cpu4 := run1 cpu3).
  set (cpu5 := run1 cpu4).
  set (cpu6 := run1 cpu5).
  
  (* Prove that run_n cpu 6 = cpu6 via the run_n unfolding *)
  assert (Hrun6: run_n cpu 6 = cpu6).
  { unfold cpu6, cpu5, cpu4, cpu3, cpu2, cpu1.
    rewrite run_n_S. rewrite run_n_S. rewrite run_n_S.
    rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
    reflexivity. }
  rewrite Hrun6.
  
  (* Prove cpu3 = run_n cpu 3 for use with Htemp_nonzero *)
  assert (Hcpu3_eq: cpu3 = run_n cpu 3).
  { unfold cpu3, cpu2, cpu1.
    rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
    reflexivity. }
  
  (* Prove cpu5 = run_n cpu 5 for use with Hdecode5 *)
  assert (Hcpu5_eq: cpu5 = run_n cpu 5).
  { unfold cpu5, cpu4, cpu3, cpu2, cpu1.
    rewrite run_n_S. rewrite run_n_S. rewrite run_n_S.
    rewrite run_n_S. rewrite run_n_1.
    reflexivity. }
  
  (* Now prove FindRule_Loop_Inv tm (q, tape, head) cpu6 (S i) *)
  unfold FindRule_Loop_Inv.
  simpl.
  
  (* We need to prove all components of the invariant after 6 steps *)
  split; [|split; [|split; [|split]]].
  
  - (* PC is at 4 after 6 steps *)
    (* cpu6 = run1 cpu5 = step(decode_instr cpu5) cpu5 *)
    (* decode_instr cpu5 = Jnz TEMP1 4, and TEMP1 is nonzero so PC jumps to 4 *)
    right; left. (* Choose the middle case: PC = 4 *)
    
    (* cpu6 = run1 cpu5, and decode_instr cpu5 = Jnz TEMP1 4 *)
    unfold cpu6. unfold run1.
    rewrite <- Hcpu5_eq in Hdecode5.
    rewrite Hdecode5.
    
    (* Use step_JumpNonZero_taken to show PC jumps to 4 *)
    (* Need to prove TEMP1 is nonzero in cpu5 *)
    assert (Htemp5_nz: CPU.read_reg CPU.REG_TEMP1 cpu5 <> 0).
    { (* TEMP1 is nonzero in run_n cpu 3 from Htemp_nonzero *)
      (* Prove cpu3 has nonzero TEMP1 *)
      assert (Htemp3_nz: CPU.read_reg CPU.REG_TEMP1 cpu3 <> 0).
      { rewrite Hcpu3_eq. exact Htemp_nonzero. }
      (* Track TEMP1 from cpu3 to cpu4: Jz doesn't write registers *)
      assert (Htemp4_nz: CPU.read_reg CPU.REG_TEMP1 cpu4 <> 0).
      { unfold cpu4, run1.
        assert (Hcpu3_dec: decode_instr cpu3 = CPU.Jz CPU.REG_TEMP1 12).
        { rewrite Hcpu3_eq. exact Hdecode3. }
        rewrite Hcpu3_dec.
        (* First establish length *)
        assert (Hlen3: length cpu3.(CPU.regs) = 10).
        { rewrite Hcpu3_eq.
          (* run_n preserves exact length = 10 for the universal program *)
          apply (length_run_n_eq_bounded cpu 3 Hlen). }
        (* Solution: Don't unfold CPU.step yet - use abstract reasoning *)
        (* We know from Htemp3_nz that TEMP1 <> 0 in cpu3 *)
        (* The Jz instruction either jumps (if TEMP1 = 0) or increments PC (if TEMP1 <> 0) *)
        (* Both cases only modify PC, preserving TEMP1 *)
        assert (Hjz_preserves_temp1: 
          CPU.read_reg CPU.REG_TEMP1 (CPU.step (CPU.Jz CPU.REG_TEMP1 12) cpu3) 
          = CPU.read_reg CPU.REG_TEMP1 cpu3).
        { unfold CPU.step.
          destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0).
          - (* Jump case: write_reg REG_PC 12 cpu3 *)
            apply read_reg_write_reg_diff.
            + unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
            + unfold CPU.REG_TEMP1. rewrite Hlen3. lia.
            + unfold CPU.REG_PC. rewrite Hlen3. lia.
          - (* No jump case: write_reg REG_PC (S (read_reg REG_PC cpu3)) cpu3 *)
            apply read_reg_write_reg_diff.
            + unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
            + unfold CPU.REG_TEMP1. rewrite Hlen3. lia.
            + unfold CPU.REG_PC. rewrite Hlen3. lia. }
        rewrite Hjz_preserves_temp1. exact Htemp3_nz. }
      (* Track TEMP1 from cpu4 to cpu5: AddConst writes to ADDR (7), not TEMP1 (8) *)
      unfold cpu5, run1.
      assert (Hcpu4_dec: decode_instr cpu4 = CPU.AddConst CPU.REG_ADDR RULE_SIZE).
      { assert (Hcpu4_eq: cpu4 = run_n cpu 4).
        { unfold cpu4, cpu3, cpu2, cpu1.
          unfold run1.
          rewrite run_n_S. rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
          reflexivity. }
        rewrite Hcpu4_eq. exact Hdecode4. }
      rewrite Hcpu4_dec.
      (* First establish length *)
      assert (Hlen4: length cpu4.(CPU.regs) = 10).
      { assert (Hcpu4_eq_run: cpu4 = run_n cpu 4).
        { unfold cpu4, cpu3, cpu2, cpu1.
          unfold run1.
          rewrite run_n_S. rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
          reflexivity. }
        rewrite Hcpu4_eq_run.
        apply (length_run_n_eq_bounded cpu 4 Hlen). }
      (* AddConst writes to PC and ADDR, preserving TEMP1 *)
      (* Use abstract reasoning like in the Jz case *)
      assert (Haddconst_preserves_temp1:
        CPU.read_reg CPU.REG_TEMP1 (CPU.step (CPU.AddConst CPU.REG_ADDR RULE_SIZE) cpu4)
        = CPU.read_reg CPU.REG_TEMP1 cpu4).
      { unfold CPU.step.
        (* AddConst writes PC first, then the target register *)
        (* read_reg TEMP1 (write_reg ADDR ... (write_reg PC ... cpu4)) = read_reg TEMP1 cpu4 *)
        transitivity (CPU.read_reg CPU.REG_TEMP1 (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)).
        - apply read_reg_write_reg_diff.
          + (* TEMP1 <> ADDR *) unfold CPU.REG_TEMP1, CPU.REG_ADDR. lia.
          + (* TEMP1 < length of inner state *)
            assert (Hlen_pc_write: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).(CPU.regs) = length cpu4.(CPU.regs)).
            { apply length_write_reg. unfold CPU.REG_PC. rewrite Hlen4. lia. }
            unfold CPU.REG_TEMP1. rewrite Hlen_pc_write, Hlen4. lia.
          + (* ADDR < length of inner state *) 
            assert (Hlen_pc_write: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).(CPU.regs) = length cpu4.(CPU.regs)).
            { apply length_write_reg. unfold CPU.REG_PC. rewrite Hlen4. lia. }
            unfold CPU.REG_ADDR. rewrite Hlen_pc_write, Hlen4. lia.
        - apply read_reg_write_reg_diff.
          + (* TEMP1 <> PC *) unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
          + (* TEMP1 < length *) unfold CPU.REG_TEMP1. rewrite Hlen4. lia.
          + (* PC < length *) unfold CPU.REG_PC. rewrite Hlen4. lia. }
      rewrite Haddconst_preserves_temp1. exact Htemp4_nz. }
    
    (* Now apply step_JumpNonZero_taken *)
    apply (step_JumpNonZero_taken cpu5 CPU.REG_TEMP1 4 Htemp5_nz).
    (* Prove length of cpu5 = 10 *)
    rewrite Hcpu5_eq.
    apply (length_run_n_eq_bounded cpu 5 Hlen).
    
  - (* REG_Q is preserved through all 6 steps *)
    (* REG_Q is never modified in any of the 6 instructions *)
    (* LoadIndirect writes to Q', CopyReg writes to TEMP1, SubReg writes to TEMP1,
       Jz doesn't write, AddConst writes to ADDR, Jnz doesn't write *)
    (* Therefore REG_Q in cpu6 = REG_Q in cpu *)
    (* Track REG_Q through each step using abstract reasoning *)
    
    (* Step 0: cpu -> cpu1: LoadIndirect writes to Q' (4), not Q (1) *)
    assert (HQ_step0: CPU.read_reg CPU.REG_Q cpu1 = CPU.read_reg CPU.REG_Q cpu).
    { unfold cpu1, run1. rewrite Hdecode0.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* Q <> Q' *) unfold CPU.REG_Q, CPU.REG_Q'. lia.
      - (* Q < length *) unfold CPU.REG_Q. rewrite Hlen. lia.
      - (* Q' < length *) unfold CPU.REG_Q'. rewrite Hlen. lia. }
    
    (* Step 1: cpu1 -> cpu2: CopyReg writes to TEMP1 (8), not Q (1) *)
    assert (HQ_step1: CPU.read_reg CPU.REG_Q cpu2 = CPU.read_reg CPU.REG_Q cpu1).
    { unfold cpu2, run1. rewrite Hdecode1.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* Q <> TEMP1 *) unfold CPU.REG_Q, CPU.REG_TEMP1. lia.
      - (* Q < length *) 
        assert (Hlen1: length cpu1.(CPU.regs) = 10).
        { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        unfold CPU.REG_Q. rewrite Hlen1. lia.
      - (* TEMP1 < length *)
        assert (Hlen1: length cpu1.(CPU.regs) = 10).
        { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        unfold CPU.REG_TEMP1. rewrite Hlen1. lia. }
    
    (* Step 2: cpu2 -> cpu3: SubReg writes to TEMP1 (8), not Q (1) *)
    assert (HQ_step2: CPU.read_reg CPU.REG_Q cpu3 = CPU.read_reg CPU.REG_Q cpu2).
    { unfold cpu3, run1. rewrite <- Hcpu3_eq in Hdecode2. rewrite Hdecode2.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
