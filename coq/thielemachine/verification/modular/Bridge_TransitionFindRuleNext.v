(* ================================================================= *)
(* ThieleUniversalBridge Module: TransitionFindRuleNext *)
(* Extracted from lines 1651-1950 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

  assert (Hlen4 : length (CPU.regs (run_n cpu 4)) >= 10).
  { apply (transition_FindRule_step2b_len4 cpu Hlen3). }

  assert (Htemp5_val : CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5)
                       = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3)).
  { apply (transition_FindRule_step2b_temp5 cpu Hdec4 Htemp4 Hlen4). }

  (* Final step: TEMP1 is non-zero at step 5, so Jnz goes to 4 *)
  assert (Htemp5 : CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) =? 0 = false).
  { rewrite Htemp5_val, Htemp_nonzero. reflexivity. }

  (* Convert run_n cpu 6 to single step form *)
  change (run_n cpu 6) with (run1 (run_n cpu 5)).
  rewrite run1_decode, Hdec5.
  apply CPU.step_jnz_false.
  exact Htemp5.
Qed.


(* Checkpoints for transition_FindRule_Next_step3b *)
Lemma transition_FindRule_step3b_len_cpu : forall cpu0,
  length cpu0.(CPU.regs) = 10 ->
  let cpu := run_n cpu0 3 in
  length (CPU.regs cpu) >= 10.
Proof.
  intros cpu0 Hlen0 cpu.
  subst cpu.
  eapply Nat.le_trans; [|apply length_run_n_ge].
  rewrite Hlen0. apply Nat.le_refl.
Qed.

Lemma transition_FindRule_step3b_len3 : forall cpu,
  length (CPU.regs cpu) >= 10 ->
  length (CPU.regs (run_n (run_n cpu 3) 3)) >= 10.
Proof.
  intros cpu Hlen_cpu.
  eapply Nat.le_trans; [|apply length_run_n_ge].
  eapply Nat.le_trans; [exact Hlen_cpu|apply length_run_n_ge].
Qed.

Lemma transition_FindRule_step3b_len4 : forall cpu,
  length (CPU.regs cpu) >= 10 ->
  length (CPU.regs (run_n (run_n cpu 3) 4)) >= 10.
Proof.
  intros cpu Hlen_cpu.
  eapply Nat.le_trans; [|apply length_run_n_ge].
  eapply Nat.le_trans; [exact Hlen_cpu|apply length_run_n_ge].
Qed.

Lemma transition_FindRule_step3b_len5 : forall cpu,
  length (CPU.regs cpu) >= 10 ->
  length (CPU.regs (run_n (run_n cpu 3) 5)) >= 10.
Proof.
  intros cpu Hlen_cpu.
  eapply Nat.le_trans; [|apply length_run_n_ge].
  eapply Nat.le_trans; [exact Hlen_cpu|apply length_run_n_ge].
Qed.

Lemma transition_FindRule_Next_step3b : forall cpu0,
  length cpu0.(CPU.regs) = 10 ->
  let cpu := run_n cpu0 3 in
  (* Provide explicit decode_instr results as hypotheses *)
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) = CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  decode_instr (run_n cpu 4) = CPU.AddConst CPU.REG_ADDR RULE_SIZE ->
  decode_instr (run_n cpu 5) = CPU.Jnz CPU.REG_TEMP1 4 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0 = false ->
  CPU.read_reg CPU.REG_ADDR (run_n cpu 6) =
    CPU.read_reg CPU.REG_ADDR cpu + RULE_SIZE.
Proof.
  intros cpu0 Hlen0 cpu Hdec0 Hdec1 Hdec2 Hdec3 Hdec4 Hdec5 Htemp_nonzero.

  (* Use sealed checkpoints - simplified to admit due to complexity *)
  assert (Hlen_cpu : length (CPU.regs cpu) >= 10).
  { apply (transition_FindRule_step3b_len_cpu cpu0 Hlen0). }

  assert (Hlen3 : length (CPU.regs (run_n cpu 3)) >= 10).
  { apply (transition_FindRule_step3b_len3 cpu Hlen_cpu). }

  assert (Hlen4 : length (CPU.regs (run_n cpu 4)) >= 10).
  { apply (transition_FindRule_step3b_len4 cpu Hlen_cpu). }

  assert (Hlen5 : length (CPU.regs (run_n cpu 5)) >= 10).
  { apply (transition_FindRule_step3b_len5 cpu Hlen_cpu). }

  (* Step 3 → 4: Jz with nonzero guard leaves ADDR unchanged. *)
  assert (Haddr4 : CPU.read_reg CPU.REG_ADDR (run_n cpu 4)
                   = CPU.read_reg CPU.REG_ADDR (run_n cpu 3)).
  { (* run_n cpu 4 = run1 (run_n cpu 3) *)
    change (run_n cpu 4) with (run1 (run_n cpu 3)).
    rewrite run1_decode, Hdec3.
    (* Jz only writes PC, ADDR is preserved *)
    unfold CPU.step.
    destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0).
    - (* Jump taken: write_reg PC 12 *)
      apply read_reg_write_reg_diff.
      + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
      + unfold CPU.REG_ADDR. lia.
      + unfold CPU.REG_PC. lia.
    - (* Jump not taken: write_reg PC (S ...) *)
      apply read_reg_write_reg_diff.
      + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
      + unfold CPU.REG_ADDR. lia.
      + unfold CPU.REG_PC. lia. }

  (* Step 4 → 5: AddConst bumps ADDR by RULE_SIZE. *)
  assert (Haddr5 : CPU.read_reg CPU.REG_ADDR (run_n cpu 5)
                   = CPU.read_reg CPU.REG_ADDR (run_n cpu 3) + RULE_SIZE).
  { (* run_n cpu 5 = run1 (run_n cpu 4) *)
    change (run_n cpu 5) with (run1 (run_n cpu 4)).
    rewrite run1_decode, Hdec4.
    (* AddConst ADDR RULE_SIZE adds RULE_SIZE to ADDR *)
    unfold CPU.step.
    (* After PC write, then ADDR write *)
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
      + (* Use Haddr4 *)
        rewrite Haddr4. reflexivity.
      + unfold CPU.REG_ADDR, CPU.REG_PC. lia.
      + unfold CPU.REG_ADDR. lia.
      + unfold CPU.REG_PC. lia. }

  (* Guard remains non-zero through Jnz. *)
  assert (Htemp5_val : CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5)
                        = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3)).
  { (* Track TEMP1 from step 3 through 4 and 5 *)
    (* Step 3→4: Jz preserves TEMP1 *)
    assert (Htemp4: CPU.read_reg CPU.REG_TEMP1 (run_n cpu 4) 
                    = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3)).
    { change (run_n cpu 4) with (run1 (run_n cpu 3)).
      rewrite run1_decode, Hdec3.
      unfold CPU.step.
      destruct (CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0).
      - apply read_reg_write_reg_diff.
        + unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
        + unfold CPU.REG_TEMP1. lia.
        + unfold CPU.REG_PC. lia.
      - apply read_reg_write_reg_diff.
        + unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
        + unfold CPU.REG_TEMP1. lia.
        + unfold CPU.REG_PC. lia. }
    (* Step 4→5: AddConst ADDR preserves TEMP1 *)
    change (run_n cpu 5) with (run1 (run_n cpu 4)).
    rewrite run1_decode, Hdec4.
    unfold CPU.step.
    transitivity (CPU.read_reg CPU.REG_TEMP1 
                    (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4))).
    - apply read_reg_write_reg_diff.
      + unfold CPU.REG_TEMP1, CPU.REG_ADDR. lia.
      + unfold CPU.REG_TEMP1.
        assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4)).(CPU.regs) 
                         = length (run_n cpu 4).(CPU.regs)).
        { apply length_write_reg. unfold CPU.REG_PC. lia. }
        rewrite Hlen_pc. lia.
      + unfold CPU.REG_ADDR.
        assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4)).(CPU.regs) 
                         = length (run_n cpu 4).(CPU.regs)).
        { apply length_write_reg. unfold CPU.REG_PC. lia. }
        rewrite Hlen_pc. lia.
    - rewrite read_reg_write_reg_diff.
      + exact Htemp4.
      + unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
      + unfold CPU.REG_TEMP1. lia.
      + unfold CPU.REG_PC. lia. }

  assert (Htemp5 : CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) =? 0 = false).
  { rewrite Htemp5_val, Htemp_nonzero. reflexivity. }

  (* Final Jnz step leaves ADDR untouched. *)
  change (run_n cpu 6) with (run1 (run_n cpu 5)).
  rewrite run1_decode, Hdec5.
  unfold CPU.step.
  set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 5))) (run_n cpu 5)).
  rewrite Htemp5.
  (* Jnz with nonzero guard writes PC to target 4, ADDR is preserved *)
  rewrite read_reg_write_reg_diff.
  - (* Apply Haddr5 *)
    exact Haddr5.
  - (* ADDR ≠ PC *) unfold CPU.REG_ADDR, CPU.REG_PC. lia.
  - (* ADDR < length *) unfold CPU.REG_ADDR. lia.
  - (* PC < length *) unfold CPU.REG_PC. lia.
Qed.


(* Helper lemma for transition_FindRule_Found *)
Lemma transition_FindRule_Found_step : forall cpu0,
  let cpu := run_n cpu0 3 in
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) = CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0 = true ->
  CPU.read_reg CPU.REG_PC (run_n cpu 4) = 12.
Proof.
  intros cpu0 cpu Hdec0 Hdec1 Hdec2 Hdec3 Htemp_zero.
  
  (* Convert run_n cpu 4 to a form we can work with *)
  change (run_n cpu 4) with (run1 (run1 (run1 (run1 cpu)))).
  
  (* Similarly for run_n cpu 3 *)
  assert (E3: run_n cpu 3 = run1 (run1 (run1 cpu))).
  { reflexivity. }
  
  (* Rewrite to use run_n cpu 3 *)
  rewrite <- E3.
  
  (* Apply run1_decode *)
  rewrite run1_decode.
  
  (* Apply Hdec3 *)
  rewrite Hdec3.
  
  (* Now goal is: read_reg PC (step (Jz TEMP1 12) (run_n cpu 3)) = 12 *)
  (* Use CPU.step_jz_true directly - it expects =? 0 = true *)
  apply CPU.step_jz_true.
  exact Htemp_zero.
Qed.

Time Lemma transition_FindRule_Next (tm : TM) (conf : TMConfig) :
  let cpu := findrule_entry_state tm conf in
  (* Add explicit decode_instr hypotheses to avoid vm_compute *)
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) = CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  decode_instr (run_n cpu 4) = CPU.AddConst CPU.REG_ADDR RULE_SIZE ->
  decode_instr (run_n cpu 5) = CPU.Jnz CPU.REG_TEMP1 4 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) <> 0 ->
  exists cpu',
    run_n cpu 6 = cpu' /\
    CPU.read_reg CPU.REG_PC cpu' = 4 /\
    CPU.read_reg CPU.REG_ADDR cpu' = CPU.read_reg CPU.REG_ADDR cpu + RULE_SIZE.
Proof.
  bridge_checkpoint ("transition_FindRule_Next"%string).
  intros cpu Hdec0 Hdec1 Hdec2 Hdec3 Hdec4 Hdec5 Htemp.
  subst cpu. unfold findrule_entry_state.
  set (cpu0 := setup_state tm conf).
  assert (Hlen0 : length cpu0.(CPU.regs) = 10).
  { subst cpu0. apply setup_state_regs_length. }
  Local Opaque CPU.read_mem.

  (* The guard is known to be non-zero at the Jz. *)
  assert (Hguard_false : CPU.read_reg CPU.REG_TEMP1 (run_n (run_n cpu0 3) 3) =? 0 = false).
  { apply Nat.eqb_neq.
    rewrite <- run_n_add.
    exact Htemp. }

  bridge_checkpoint ("transition_FindRule_Next_done"%string).
  exists (run_n (run_n cpu0 3) 6).
  split; [reflexivity|].
  split.
  - (* Use helper lemma to avoid OOM *)
    apply (transition_FindRule_Next_step2b cpu0 Hlen0 Hdec0 Hdec1 Hdec2 Hdec3 Hdec4 Hdec5).
    exact Hguard_false.
  - (* Use helper lemma to avoid OOM *)
    apply (transition_FindRule_Next_step3b cpu0 Hlen0 Hdec0 Hdec1 Hdec2 Hdec3 Hdec4 Hdec5).
    exact Hguard_false.
Qed.

(* Concrete computation for the matching path: the temporary register is zero,
   so the Jz is taken and control jumps to the Found block at PC=12. *)
Time Lemma transition_FindRule_Found (tm : TM) (conf : TMConfig) :
  let cpu := findrule_entry_state tm conf in
  (* Add explicit decode_instr hypotheses to avoid vm_compute *)
  decode_instr cpu = CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR ->
  decode_instr (run1 cpu) = CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q ->
  decode_instr (run_n cpu 2) = CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ->
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) = 0 ->
  exists cpu',
    run_n cpu 4 = cpu' /\
    CPU.read_reg CPU.REG_PC cpu' = 12.
Proof.
  bridge_checkpoint ("transition_FindRule_Found"%string).
  intros cpu Hdec0 Hdec1 Hdec2 Hdec3 Htemp.
  subst cpu. unfold findrule_entry_state.
  set (cpu0 := setup_state tm conf).
  Local Opaque CPU.read_mem.

  assert (Hguard_true : CPU.read_reg CPU.REG_TEMP1 (run_n (run_n cpu0 3) 3) =? 0 = true).
  { apply Nat.eqb_eq.
    rewrite <- run_n_add.
    exact Htemp. }

  bridge_checkpoint ("transition_FindRule_Found_done"%string).
  exists (run_n (run_n cpu0 3) 4).
  split; [reflexivity|].
  (* Use helper lemma to avoid OOM *)
  apply (transition_FindRule_Found_step cpu0 Hdec0 Hdec1 Hdec2 Hdec3).
