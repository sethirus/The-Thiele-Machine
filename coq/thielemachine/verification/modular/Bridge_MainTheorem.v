(* ================================================================= *)
(* ThieleUniversalBridge Module: MainTheorem *)
(* Extracted from lines 2301-2876 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

      - (* Q <> TEMP1 *) unfold CPU.REG_Q, CPU.REG_TEMP1. lia.
      - (* Q < length *)
        assert (Hlen2: length cpu2.(CPU.regs) = 10).
        { unfold cpu2, run1. rewrite Hdecode1. unfold CPU.step.
          apply length_write_reg.
          + unfold CPU.REG_TEMP1.
            assert (Hlen1: length cpu1.(CPU.regs) = 10).
            { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
              apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
            rewrite Hlen1. lia. }
        unfold CPU.REG_Q. rewrite Hlen2. lia.
      - (* TEMP1 < length *)
        assert (Hlen2: length cpu2.(CPU.regs) = 10).
        { unfold cpu2, run1. rewrite Hdecode1. unfold CPU.step.
          apply length_write_reg.
          + unfold CPU.REG_TEMP1.
            assert (Hlen1: length cpu1.(CPU.regs) = 10).
            { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
              apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
            rewrite Hlen1. lia. }
        unfold CPU.REG_TEMP1. rewrite Hlen2. lia. }
    
    (* Step 3: cpu3 -> cpu4: Jz only writes PC (0), not Q (1) *)
    assert (HQ_step3: CPU.read_reg CPU.REG_Q cpu4 = CPU.read_reg CPU.REG_Q cpu3).
    { unfold cpu4, run1. rewrite Hcpu3_eq. rewrite Hdecode3.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0).
      - (* Jump case: write PC *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_Q, CPU.REG_PC. lia.
        + unfold CPU.REG_Q. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
      - (* No jump case: write PC *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_Q, CPU.REG_PC. lia.
        + unfold CPU.REG_Q. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen). }
    
    (* Step 4: cpu4 -> cpu5: AddConst writes PC (0) and ADDR (7), not Q (1) *)
    assert (HQ_step4: CPU.read_reg CPU.REG_Q cpu5 = CPU.read_reg CPU.REG_Q cpu4).
    { unfold cpu5, run1.
      assert (Hcpu4_eq: cpu4 = run_n cpu 4).
      { unfold cpu4, cpu3, cpu2, cpu1. unfold run1.
        rewrite run_n_S. rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
        reflexivity. }
      rewrite Hcpu4_eq. rewrite Hdecode4.
      unfold CPU.step.
      (* AddConst writes PC then ADDR *)
      transitivity (CPU.read_reg CPU.REG_Q (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)).
      - (* Q preserved through ADDR write *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_Q, CPU.REG_ADDR. lia.
        + unfold CPU.REG_Q.
          assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).(CPU.regs) = length cpu4.(CPU.regs)).
          { apply length_write_reg. unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
          rewrite Hlen_pc, Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
        + unfold CPU.REG_ADDR.
          assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).(CPU.regs) = length cpu4.(CPU.regs)).
          { apply length_write_reg. unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
          rewrite Hlen_pc, Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
      - (* Q preserved through PC write *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_Q, CPU.REG_PC. lia.
        + unfold CPU.REG_Q. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
    
    (* Step 5: cpu5 -> cpu6: Jnz only writes PC (0), not Q (1) *)
    assert (HQ_step5: CPU.read_reg CPU.REG_Q cpu6 = CPU.read_reg CPU.REG_Q cpu5).
    { unfold cpu6, run1. rewrite <- Hcpu5_eq in Hdecode5. rewrite Hdecode5.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu5 =? 0).
      - (* No jump case: write PC *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_Q, CPU.REG_PC. lia.
        + unfold CPU.REG_Q. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
      - (* Jump case: write PC *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_Q, CPU.REG_PC. lia.
        + unfold CPU.REG_Q. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen). }
    
    (* Chain the equalities *)
    rewrite HQ_step5, HQ_step4, HQ_step3, HQ_step2, HQ_step1, HQ_step0.
    exact Hq.
    
  - (* REG_SYM is preserved through all 6 steps *)
    (* REG_SYM is never modified in any of the 6 instructions *)
    (* Prove by tracking REG_SYM through each step *)
    
    (* Step 0: cpu -> cpu1 (LoadIndirect REG_Q' REG_ADDR) - writes to REG_Q' (4), not REG_SYM (3) *)
    assert (HSYM_step0: CPU.read_reg CPU.REG_SYM cpu1 = CPU.read_reg CPU.REG_SYM cpu).
    { unfold cpu1, run1. rewrite Hdecode0.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* REG_SYM != REG_Q' *) unfold CPU.REG_SYM, CPU.REG_Q'. lia.
      - (* REG_SYM < length *) unfold CPU.REG_SYM. rewrite Hlen. lia.
      - (* REG_Q' < length *) unfold CPU.REG_Q'. rewrite Hlen. lia. }
    
    (* Step 1: cpu1 -> cpu2 (CopyReg REG_TEMP1 REG_Q) - writes to REG_TEMP1 (8), not REG_SYM (3) *)
    assert (HSYM_step1: CPU.read_reg CPU.REG_SYM cpu2 = CPU.read_reg CPU.REG_SYM cpu1).
    { unfold cpu2, run1. rewrite Hdecode1.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* REG_SYM != REG_TEMP1 *) unfold CPU.REG_SYM, CPU.REG_TEMP1. lia.
      - (* REG_SYM < length *)
        assert (Hlen1: length cpu1.(CPU.regs) = 10).
        { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        unfold CPU.REG_SYM. rewrite Hlen1. lia.
      - (* REG_TEMP1 < length *)
        assert (Hlen1: length cpu1.(CPU.regs) = 10).
        { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        unfold CPU.REG_TEMP1. rewrite Hlen1. lia. }
    
    (* Step 2: cpu2 -> cpu3 (SubReg REG_TEMP1 REG_TEMP1 REG_Q) - writes to REG_TEMP1 (8), not REG_SYM (3) *)
    assert (HSYM_step2: CPU.read_reg CPU.REG_SYM cpu3 = CPU.read_reg CPU.REG_SYM cpu2).
    { unfold cpu3, run1. rewrite <- Hcpu3_eq in Hdecode2. rewrite Hdecode2.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* REG_SYM != REG_TEMP1 *) unfold CPU.REG_SYM, CPU.REG_TEMP1. lia.
      - (* REG_SYM < length *)
        assert (Hlen2: length cpu2.(CPU.regs) = 10).
        { unfold cpu2, run1. rewrite Hdecode1. unfold CPU.step.
          apply length_write_reg.
          + unfold CPU.REG_TEMP1.
            assert (Hlen1: length cpu1.(CPU.regs) = 10).
            { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
              apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
            rewrite Hlen1. lia. }
        unfold CPU.REG_SYM. rewrite Hlen2. lia.
      - (* REG_TEMP1 < length *)
        assert (Hlen2: length cpu2.(CPU.regs) = 10).
        { unfold cpu2, run1. rewrite Hdecode1. unfold CPU.step.
          apply length_write_reg.
          + unfold CPU.REG_TEMP1.
            assert (Hlen1: length cpu1.(CPU.regs) = 10).
            { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
              apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
            rewrite Hlen1. lia. }
        unfold CPU.REG_TEMP1. rewrite Hlen2. lia. }
    
    (* Step 3: cpu3 -> cpu4 (Jz REG_TEMP1 12) - only writes PC (0), not REG_SYM (3) *)
    assert (HSYM_step3: CPU.read_reg CPU.REG_SYM cpu4 = CPU.read_reg CPU.REG_SYM cpu3).
    { unfold cpu4, run1. rewrite Hcpu3_eq. rewrite Hdecode3.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0).
      - (* Jump taken case *)
        apply read_reg_write_reg_diff.
        + (* REG_SYM != REG_PC *) unfold CPU.REG_SYM, CPU.REG_PC. lia.
        + (* REG_SYM < length *) unfold CPU.REG_SYM. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
        + (* REG_PC < length *) unfold CPU.REG_PC. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
      - (* Jump not taken case *)
        apply read_reg_write_reg_diff.
        + (* REG_SYM != REG_PC *) unfold CPU.REG_SYM, CPU.REG_PC. lia.
        + (* REG_SYM < length *) unfold CPU.REG_SYM. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
        + (* REG_PC < length *) unfold CPU.REG_PC. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen). }
    
    (* Step 4: cpu4 -> cpu5 (AddConst REG_ADDR RULE_SIZE) - writes PC (0) and REG_ADDR (7), not REG_SYM (3) *)
    assert (HSYM_step4: CPU.read_reg CPU.REG_SYM cpu5 = CPU.read_reg CPU.REG_SYM cpu4).
    { unfold cpu5, run1.
      assert (Hcpu4_eq: cpu4 = run_n cpu 4).
      { unfold cpu4, cpu3, cpu2, cpu1. unfold run1.
        rewrite run_n_S. rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
        reflexivity. }
      rewrite Hcpu4_eq. rewrite Hdecode4.
      unfold CPU.step.
      (* AddConst writes PC then ADDR *)
      transitivity (CPU.read_reg CPU.REG_SYM (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)).
      - (* REG_SYM preserved through ADDR write *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_SYM, CPU.REG_ADDR. lia.
        + unfold CPU.REG_SYM.
          assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).(CPU.regs) = length cpu4.(CPU.regs)).
          { apply length_write_reg. unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
          rewrite Hlen_pc, Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
        + unfold CPU.REG_ADDR.
          assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).(CPU.regs) = length cpu4.(CPU.regs)).
          { apply length_write_reg. unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
          rewrite Hlen_pc, Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
      - (* REG_SYM preserved through PC write *)
        apply read_reg_write_reg_diff.
        + unfold CPU.REG_SYM, CPU.REG_PC. lia.
        + unfold CPU.REG_SYM. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
    
    (* Step 5: cpu5 -> cpu6 (Jnz REG_TEMP1 4) - only writes PC (0), not REG_SYM (3) *)
    assert (HSYM_step5: CPU.read_reg CPU.REG_SYM cpu6 = CPU.read_reg CPU.REG_SYM cpu5).
    { unfold cpu6, run1. rewrite Hdecode5.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu5 =? 0).
      - (* Jump not taken case *)
        apply read_reg_write_reg_diff.
        + (* REG_SYM != REG_PC *) unfold CPU.REG_SYM, CPU.REG_PC. lia.
        + (* REG_SYM < length *) unfold CPU.REG_SYM. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
        + (* REG_PC < length *) unfold CPU.REG_PC. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
      - (* Jump taken case *)
        apply read_reg_write_reg_diff.
        + (* REG_SYM != REG_PC *) unfold CPU.REG_SYM, CPU.REG_PC. lia.
        + (* REG_SYM < length *) unfold CPU.REG_SYM. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
        + (* REG_PC < length *) unfold CPU.REG_PC. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen). }
    
    (* Chain all equalities *)
    rewrite HSYM_step5, HSYM_step4, HSYM_step3, HSYM_step2, HSYM_step1, HSYM_step0.
    exact Hsym.
    
  - (* REG_ADDR is incremented by RULE_SIZE *)
    (* Step 4 (cpu4->cpu5) executes AddConst REG_ADDR RULE_SIZE *)
    (* Steps 0-3 don't modify ADDR, step 5 doesn't modify ADDR *)
    (* Need to prove: CPU.read_reg CPU.REG_ADDR cpu6 = RULES_START_ADDR + (S i) * RULE_SIZE *)
    (* We know: CPU.read_reg CPU.REG_ADDR cpu = RULES_START_ADDR + i * RULE_SIZE *)
    
    (* Step 0: cpu -> cpu1 (LoadIndirect writes to Q', not ADDR) *)
    assert (Haddr1: CPU.read_reg CPU.REG_ADDR cpu1 = CPU.read_reg CPU.REG_ADDR cpu).
    { unfold cpu1, run1. rewrite Hdecode0.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* ADDR ≠ Q' *) unfold CPU.REG_ADDR, CPU.REG_Q'. lia.
      - (* ADDR < length *) unfold CPU.REG_ADDR. rewrite Hlen. lia.
      - (* Q' < length *) unfold CPU.REG_Q'. rewrite Hlen. lia. }
    
    (* Step 1: cpu1 -> cpu2 (CopyReg writes to TEMP1, not ADDR) *)
    assert (Haddr2: CPU.read_reg CPU.REG_ADDR cpu2 = CPU.read_reg CPU.REG_ADDR cpu1).
    { unfold cpu2, run1. rewrite Hdecode1.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* ADDR ≠ TEMP1 *) unfold CPU.REG_ADDR, CPU.REG_TEMP1. lia.
      - (* ADDR < length *)
        assert (Hlen1: length cpu1.(CPU.regs) = 10).
        { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        unfold CPU.REG_ADDR. rewrite Hlen1. lia.
      - (* TEMP1 < length *)
        assert (Hlen1: length cpu1.(CPU.regs) = 10).
        { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        unfold CPU.REG_TEMP1. rewrite Hlen1. lia. }
    
    (* Step 2: cpu2 -> cpu3 (SubReg writes to TEMP1, not ADDR) *)
    assert (Haddr3: CPU.read_reg CPU.REG_ADDR cpu3 = CPU.read_reg CPU.REG_ADDR cpu2).
    { unfold cpu3, run1. rewrite <- Hcpu3_eq in Hdecode2. rewrite Hdecode2.
      unfold CPU.step.
      apply read_reg_write_reg_diff.
      - (* ADDR ≠ TEMP1 *) unfold CPU.REG_ADDR, CPU.REG_TEMP1. lia.
      - (* ADDR < length *)
        assert (Hlen2: length cpu2.(CPU.regs) = 10).
        { unfold cpu2, run1. rewrite Hdecode1. unfold CPU.step.
          apply length_write_reg.
          + unfold CPU.REG_TEMP1.
            assert (Hlen1: length cpu1.(CPU.regs) = 10).
            { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
              apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
            rewrite Hlen1. lia. }
        unfold CPU.REG_ADDR. rewrite Hlen2. lia.
      - (* TEMP1 < length *)
        assert (Hlen2: length cpu2.(CPU.regs) = 10).
        { unfold cpu2, run1. rewrite Hdecode1. unfold CPU.step.
          apply length_write_reg.
          + unfold CPU.REG_TEMP1.
            assert (Hlen1: length cpu1.(CPU.regs) = 10).
            { unfold cpu1, run1. rewrite Hdecode0. unfold CPU.step.
              apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
            rewrite Hlen1. lia. }
        unfold CPU.REG_TEMP1. rewrite Hlen2. lia. }
    
    (* Step 3: cpu3 -> cpu4 (Jz writes only to PC, not ADDR) *)
    assert (Haddr4: CPU.read_reg CPU.REG_ADDR cpu4 = CPU.read_reg CPU.REG_ADDR cpu3).
    { unfold cpu4, run1. rewrite Hcpu3_eq. rewrite Hdecode3.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0).
      - (* Jump taken *) apply read_reg_write_reg_diff.
        + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
        + unfold CPU.REG_ADDR. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
      - (* Jump not taken *) apply read_reg_write_reg_diff.
        + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
        + unfold CPU.REG_ADDR. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu3_eq. apply (length_run_n_eq_bounded cpu 3 Hlen). }
    
    (* Step 4: cpu4 -> cpu5 (AddConst ADDR RULE_SIZE increments ADDR) *)
    assert (Haddr5: CPU.read_reg CPU.REG_ADDR cpu5 = CPU.read_reg CPU.REG_ADDR cpu4 + RULE_SIZE).
    { unfold cpu5, run1.
      assert (Hcpu4_eq: cpu4 = run_n cpu 4).
      { unfold cpu4, cpu3, cpu2, cpu1. unfold run1.
        rewrite run_n_S. rewrite run_n_S. rewrite run_n_S. rewrite run_n_1.
        reflexivity. }
      rewrite Hcpu4_eq. rewrite Hdecode4.
      unfold CPU.step.
      transitivity (CPU.read_reg CPU.REG_ADDR 
                      (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4))).
      - (* ADDR write sets ADDR to old_value + RULE_SIZE *)
        unfold CPU.read_reg, CPU.write_reg. simpl.
        rewrite app_nth2.
        + rewrite firstn_length. rewrite Nat.min_l by lia.
          replace (CPU.REG_ADDR - CPU.REG_ADDR) with 0 by lia.
          simpl. reflexivity.
        + rewrite firstn_length. rewrite Nat.min_l by lia. lia.
      - (* ADDR preserved through PC write *)
        rewrite read_reg_write_reg_diff.
        + rewrite <- Hcpu4_eq. reflexivity.
        + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
        + unfold CPU.REG_ADDR. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
    
    (* Step 5: cpu5 -> cpu6 (Jnz writes only to PC, not ADDR) *)
    assert (Haddr6: CPU.read_reg CPU.REG_ADDR cpu6 = CPU.read_reg CPU.REG_ADDR cpu5).
    { unfold cpu6, run1. rewrite <- Hcpu5_eq in Hdecode5. rewrite Hdecode5.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu5 =? 0).
      - (* Jump not taken *) apply read_reg_write_reg_diff.
        + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
        + unfold CPU.REG_ADDR. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
      - (* Jump taken *) apply read_reg_write_reg_diff.
        + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
        + unfold CPU.REG_ADDR. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen).
        + unfold CPU.REG_PC. rewrite Hcpu5_eq. apply (length_run_n_eq_bounded cpu 5 Hlen). }
    
    (* Chain the equalities and use arithmetic *)
    rewrite Haddr6, Haddr5, Haddr4, Haddr3, Haddr2, Haddr1.
    rewrite Haddr.
    (* Now we have: RULES_START_ADDR + i * RULE_SIZE + RULE_SIZE = RULES_START_ADDR + S i * RULE_SIZE *)
    lia.
    
  - (* All rules j < S i don't match *)
    intros j Hj.
    destruct (Nat.eq_dec j i) as [Heq|Hneq].
    + (* j = i: use Hrule_no_match *)
      subst j.
      exact Hrule_no_match.
    + (* j < i: use Hprev_rules *)
      apply Hprev_rules.
      lia.
Qed.

(*
   Loop exit lemma (partial): when a matching rule is found the loop
   takes the branch into the rule payload at PC=12.  We only establish
   the first control-flow jump here; loading the rule payload and
   executing the ApplyRule block is proved separately.
 *)
Time Lemma loop_exit_match : forall tm conf cpu idx,
  FindRule_Loop_Inv tm conf cpu idx ->
  idx < length (tm_rules tm) ->
  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  length cpu.(CPU.regs) = 10 ->
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) =
    CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) = 0 ->
  exists cpu_branch,
    run_n cpu 4 = cpu_branch /\
    CPU.read_reg CPU.REG_PC cpu_branch = 12 /\
    CPU.read_reg CPU.REG_Q cpu_branch = q /\
    CPU.read_reg CPU.REG_SYM cpu_branch = sym /\
    CPU.read_reg CPU.REG_ADDR cpu_branch =
      RULES_START_ADDR + idx * RULE_SIZE.
Proof.
  intros tm conf cpu idx Hinv Hidx_bound Hlen Hdecode0 Hdecode1 Hdecode2 Hdecode3 Htemp_zero.
  destruct conf as [[q tape] head]. simpl in *.
  
  (* Witness: cpu_branch = run_n cpu 4 *)
  exists (run_n cpu 4).
  
  (* Unfold the invariant to get register values *)
  unfold FindRule_Loop_Inv in Hinv. simpl in Hinv.
  destruct Hinv as [Hpc_in_loop [Hq [Hsym [Haddr Hprev_rules]]]].
  
  split; [reflexivity|].
  
  (* Need to prove all register values after 4 steps *)
  split.
  - (* PC = 12 after step 3->4 *)
    (* Step 3->4 is Jz TEMP1 12, and TEMP1 = 0, so jumps to 12 *)
    change (run_n cpu 4) with (run1 (run_n cpu 3)).
    unfold run1. rewrite Hdecode3.
    unfold CPU.step.
    rewrite Htemp_zero.
    simpl. (* Jz with condition true writes PC to 12 *)
    unfold CPU.read_reg, CPU.write_reg. simpl.
    rewrite app_nth2.
    + rewrite firstn_length. rewrite Nat.min_l by lia.
      replace (CPU.REG_PC - CPU.REG_PC) with 0 by lia.
      simpl. reflexivity.
    + rewrite firstn_length. rewrite Nat.min_l by lia.
      unfold CPU.REG_PC. lia.
  
  split.
  - (* REG_Q preserved through steps 0-3 *)
    (* Step 0: LoadIndirect writes to Q', not Q *)
    assert (Hq1: CPU.read_reg CPU.REG_Q (run1 cpu) = CPU.read_reg CPU.REG_Q cpu).
    { unfold run1. rewrite Hdecode0. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_Q, CPU.REG_Q'. lia.
      - unfold CPU.REG_Q. rewrite Hlen. lia.
      - unfold CPU.REG_Q'. rewrite Hlen. lia. }
    
    (* Step 1: CopyReg reads from Q, writes to TEMP1 *)
    assert (Hq2: CPU.read_reg CPU.REG_Q (run_n cpu 2) = CPU.read_reg CPU.REG_Q (run1 cpu)).
    { change (run_n cpu 2) with (run1 (run1 cpu)).
      unfold run1 at 1. rewrite Hdecode1. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_Q, CPU.REG_TEMP1. lia.
      - unfold CPU.REG_Q.
        assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
        { unfold run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        rewrite Hlen1. lia.
      - unfold CPU.REG_TEMP1.
        assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
        { unfold run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        rewrite Hlen1. lia. }
    
    (* Step 2: SubReg writes to TEMP1, not Q *)
    assert (Hq3: CPU.read_reg CPU.REG_Q (run_n cpu 3) = CPU.read_reg CPU.REG_Q (run_n cpu 2)).
    { change (run_n cpu 3) with (run1 (run_n cpu 2)).
      unfold run1. rewrite Hdecode2. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_Q, CPU.REG_TEMP1. lia.
      - unfold CPU.REG_Q. apply (length_run_n_eq_bounded cpu 2 Hlen).
      - unfold CPU.REG_TEMP1. apply (length_run_n_eq_bounded cpu 2 Hlen). }
    
    (* Step 3: Jz writes only to PC, not Q *)
    assert (Hq4: CPU.read_reg CPU.REG_Q (run_n cpu 4) = CPU.read_reg CPU.REG_Q (run_n cpu 3)).
    { change (run_n cpu 4) with (run1 (run_n cpu 3)).
      unfold run1. rewrite Hdecode3. unfold CPU.step.
      rewrite Htemp_zero. simpl.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_Q, CPU.REG_PC. lia.
      - unfold CPU.REG_Q. apply (length_run_n_eq_bounded cpu 3 Hlen).
      - unfold CPU.REG_PC. apply (length_run_n_eq_bounded cpu 3 Hlen). }
    
    (* Chain all equalities *)
    rewrite Hq4, Hq3, Hq2, Hq1. exact Hq.
  
  split.
  - (* REG_SYM preserved through steps 0-3 *)
    (* Similar to Q, SYM is not written by any of the instructions *)
    assert (Hsym1: CPU.read_reg CPU.REG_SYM (run1 cpu) = CPU.read_reg CPU.REG_SYM cpu).
    { unfold run1. rewrite Hdecode0. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_SYM, CPU.REG_Q'. lia.
      - unfold CPU.REG_SYM. rewrite Hlen. lia.
      - unfold CPU.REG_Q'. rewrite Hlen. lia. }
    
    assert (Hsym2: CPU.read_reg CPU.REG_SYM (run_n cpu 2) = CPU.read_reg CPU.REG_SYM (run1 cpu)).
    { change (run_n cpu 2) with (run1 (run1 cpu)).
      unfold run1 at 1. rewrite Hdecode1. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_SYM, CPU.REG_TEMP1. lia.
      - unfold CPU.REG_SYM.
        assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
        { unfold run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        rewrite Hlen1. lia.
      - unfold CPU.REG_TEMP1.
        assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
        { unfold run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        rewrite Hlen1. lia. }
    
    assert (Hsym3: CPU.read_reg CPU.REG_SYM (run_n cpu 3) = CPU.read_reg CPU.REG_SYM (run_n cpu 2)).
    { change (run_n cpu 3) with (run1 (run_n cpu 2)).
      unfold run1. rewrite Hdecode2. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_SYM, CPU.REG_TEMP1. lia.
      - unfold CPU.REG_SYM. apply (length_run_n_eq_bounded cpu 2 Hlen).
      - unfold CPU.REG_TEMP1. apply (length_run_n_eq_bounded cpu 2 Hlen). }
    
    assert (Hsym4: CPU.read_reg CPU.REG_SYM (run_n cpu 4) = CPU.read_reg CPU.REG_SYM (run_n cpu 3)).
    { change (run_n cpu 4) with (run1 (run_n cpu 3)).
      unfold run1. rewrite Hdecode3. unfold CPU.step.
      rewrite Htemp_zero. simpl.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_SYM, CPU.REG_PC. lia.
      - unfold CPU.REG_SYM. apply (length_run_n_eq_bounded cpu 3 Hlen).
      - unfold CPU.REG_PC. apply (length_run_n_eq_bounded cpu 3 Hlen). }
    
    rewrite Hsym4, Hsym3, Hsym2, Hsym1. exact Hsym.
  
  - (* REG_ADDR preserved through steps 0-3 *)
    (* Similar pattern: ADDR is not written until step 4, which we don't execute *)
    assert (Haddr1: CPU.read_reg CPU.REG_ADDR (run1 cpu) = CPU.read_reg CPU.REG_ADDR cpu).
    { unfold run1. rewrite Hdecode0. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_ADDR, CPU.REG_Q'. lia.
      - unfold CPU.REG_ADDR. rewrite Hlen. lia.
      - unfold CPU.REG_Q'. rewrite Hlen. lia. }
    
    assert (Haddr2: CPU.read_reg CPU.REG_ADDR (run_n cpu 2) = CPU.read_reg CPU.REG_ADDR (run1 cpu)).
    { change (run_n cpu 2) with (run1 (run1 cpu)).
      unfold run1 at 1. rewrite Hdecode1. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_ADDR, CPU.REG_TEMP1. lia.
      - unfold CPU.REG_ADDR.
        assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
        { unfold run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        rewrite Hlen1. lia.
      - unfold CPU.REG_TEMP1.
        assert (Hlen1: length (run1 cpu).(CPU.regs) = 10).
        { unfold run1. rewrite Hdecode0. unfold CPU.step.
          apply length_write_reg. unfold CPU.REG_Q'. rewrite Hlen. lia. }
        rewrite Hlen1. lia. }
    
    assert (Haddr3: CPU.read_reg CPU.REG_ADDR (run_n cpu 3) = CPU.read_reg CPU.REG_ADDR (run_n cpu 2)).
    { change (run_n cpu 3) with (run1 (run_n cpu 2)).
      unfold run1. rewrite Hdecode2. unfold CPU.step.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_ADDR, CPU.REG_TEMP1. lia.
      - unfold CPU.REG_ADDR. apply (length_run_n_eq_bounded cpu 2 Hlen).
      - unfold CPU.REG_TEMP1. apply (length_run_n_eq_bounded cpu 2 Hlen). }
    
    assert (Haddr4: CPU.read_reg CPU.REG_ADDR (run_n cpu 4) = CPU.read_reg CPU.REG_ADDR (run_n cpu 3)).
    { change (run_n cpu 4) with (run1 (run_n cpu 3)).
      unfold run1. rewrite Hdecode3. unfold CPU.step.
      rewrite Htemp_zero. simpl.
      apply read_reg_write_reg_diff.
      - unfold CPU.REG_ADDR, CPU.REG_PC. lia.
      - unfold CPU.REG_ADDR. apply (length_run_n_eq_bounded cpu 3 Hlen).
      - unfold CPU.REG_PC. apply (length_run_n_eq_bounded cpu 3 Hlen). }
    
    rewrite Haddr4, Haddr3, Haddr2, Haddr1. exact Haddr.
Qed.

(* Main loop theorem: compose iteration lemmas *)
Time Lemma transition_FindRule_to_ApplyRule (tm : TM) (conf : TMConfig) (cpu_find : CPU.State)
  (q' write : nat) (move : Z) :
  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  FindRule_Loop_Inv tm conf cpu_find 0 ->
  length cpu_find.(CPU.regs) = 10 ->
  CPU.read_reg CPU.REG_PC cpu_find = 4 ->
  decode_instr cpu_find = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu_find) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu_find 2) =
    CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu_find 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu_find 3) = 0 ->
  CPU.read_reg CPU.REG_ADDR cpu_find = RULES_START_ADDR ->
  nth 0 (tm_rules tm) (0, 0, 0, 0, 0%Z) = (q, sym, q', write, move) ->
  exists cpu_apply,
    run_n cpu_find 4 = cpu_apply /\
    CPU.read_reg CPU.REG_PC cpu_apply = 12.
Proof.
  intros tm conf cpu_find q' write move Hinv Hlen Hpc Hdecode0 Hdecode1 Hdecode2 Hdecode3 Htemp_zero Haddr_init Hrule_match.
  destruct conf as [[q tape] head]. simpl in *.
  
  (* Apply loop_exit_match with idx = 0 *)
  assert (Hidx_bound: 0 < length (tm_rules tm)).
  { (* The rule exists since we have Hrule_match *)
    destruct (tm_rules tm) as [|r rs] eqn:Hrules.
    - (* Empty list - contradiction *)
      simpl in Hrule_match. discriminate Hrule_match.
    - simpl. lia. }
  
  (* Update the invariant to use idx = 0 *)
  assert (Hinv0: FindRule_Loop_Inv tm (q, tape, head) cpu_find 0).
  { exact Hinv. }
  
  (* Apply loop_exit_match *)
  destruct (loop_exit_match tm (q, tape, head) cpu_find 0 Hinv0 Hidx_bound Hlen
             Hdecode0 Hdecode1 Hdecode2 Hdecode3 Htemp_zero)
    as [cpu_branch [Hcpu_branch [Hpc_branch [Hq_branch [Hsym_branch Haddr_branch]]]]].
  
  (* Witness cpu_apply = cpu_branch *)
  exists cpu_branch.
  split.
  - exact Hcpu_branch.
  - exact Hpc_branch.
Qed.
