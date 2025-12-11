(* ThieleUniversalBridge Module: TransitionFetch *)
(* Extracted from lines 1401-1650 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

  }
  assert (Hlen1 : length (CPU.regs (run1 cpu_init)) = 10).
  { rewrite run1_decode, Hdecode0_init.
    unfold CPU.step.
    set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu_init)) cpu_init).
    assert (Hlen_pc : length (CPU.regs st_pc) = 10).
    { subst st_pc. rewrite length_write_reg by (rewrite Hlen_init; cbv; lia). exact Hlen_init. }
    set (st_reg := CPU.write_reg CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR st_pc).
    assert (Hlen_reg : length (CPU.regs st_reg) = 10).
    { subst st_reg. rewrite length_write_reg by (rewrite Hlen_pc; cbv; lia). exact Hlen_pc. }
    exact Hlen_reg.
  }

  (* Step 1 → 2: AddReg ADDR := TEMP1 + HEAD, PC increments to 2. *)
  assert (Hpc2 : CPU.read_reg CPU.REG_PC (run1 (run1 cpu_init)) = 2).
  { rewrite run1_decode, Hdecode1_init.
    destruct (step_AddReg (run1 cpu_init) CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD
               Haddr_pc Haddr_bound Hlen1) as [Hpc _].
    replace (CPU.read_reg CPU.REG_PC (run1 cpu_init)) with 1 in Hpc by exact Hpc1.
    lia.
  }
  assert (Hlen2 : length (CPU.regs (run1 (run1 cpu_init))) = 10).
  { rewrite run1_decode, Hdecode1_init.
    unfold CPU.step.
    set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run1 cpu_init))) (run1 cpu_init)).
    assert (Hlen_pc : length (CPU.regs st_pc) = 10).
    { subst st_pc. rewrite length_write_reg by (rewrite Hlen1; cbv; lia). exact Hlen1. }
    set (st_reg := CPU.write_reg CPU.REG_ADDR (CPU.read_reg CPU.REG_TEMP1 (run1 cpu_init) + CPU.read_reg CPU.REG_HEAD (run1 cpu_init)) st_pc).
    assert (Hlen_reg : length (CPU.regs st_reg) = 10).
    { subst st_reg. rewrite length_write_reg by (rewrite Hlen_pc; cbv; lia). exact Hlen_pc. }
    exact Hlen_reg.
  }

  (* Step 2 → 3: LoadIndirect SYM := mem[ADDR], PC increments to 3. *)
  assert (Hpc3 : CPU.read_reg CPU.REG_PC (run1 (run1 (run1 cpu_init))) = 3).
  { pose proof Hdecode2_init as Hdecode2_run1.
    rewrite (run_n_S cpu_init 1) in Hdecode2_run1.
    rewrite run_n_1 in Hdecode2_run1.
    rewrite run1_decode, Hdecode2_run1.
    destruct (step_LoadIndirect (run1 (run1 cpu_init)) CPU.REG_SYM CPU.REG_ADDR
               Hsym_pc Hsym_bound Hlen2) as [Hpc _].
    replace (CPU.read_reg CPU.REG_PC (run1 (run1 cpu_init))) with 2 in Hpc by exact Hpc2.
    lia.
  }

  exists (run_n cpu_init 3).
  split; [reflexivity|].
  split.
  - unfold IS_FindRule_Start.
    rewrite run_n_unfold_3.
    exact Hpc3.
  - rewrite run_n_unfold_3.
    exact Hpc3.
Qed.

(* Now we need to show PC advances correctly *)
(* This requires knowing what instructions are at PC=0, 1, 2 *)

(* ----------------------------------------------------------------- *)
(* Transition Lemmas                                                 *)
(* ----------------------------------------------------------------- *)

Time Lemma transition_Fetch_to_FindRule (tm : TM) (conf : TMConfig) (cpu0 : CPU.State) :
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  cpu0 = setup_state tm conf ->
  length cpu0.(CPU.regs) = 10 ->
  decode_instr cpu0 =
    CPU.LoadConst CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR ->
  decode_instr (run1 cpu0) =
    CPU.AddReg CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD ->
  decode_instr (run_n cpu0 2) =
    CPU.LoadIndirect CPU.REG_SYM CPU.REG_ADDR ->
  exists cpu_find, run_n cpu0 3 = cpu_find /\ IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu_find).
Proof.
  bridge_checkpoint ("transition_Fetch_to_FindRule"%string).
  intros Hinv Hfetch Hsetup Hlen Hdecode0 Hdecode1 Hdecode2.

  destruct (transition_Fetch_to_FindRule_direct tm conf cpu0
              Hinv Hfetch Hsetup Hfetch Hlen Hdecode0 Hdecode1 Hdecode2)
    as [cpu_find [Hrun [Hstart _]]].
  exists cpu_find.
  split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Loop Reasoning Infrastructure - Week 2 of Roadmap                 *)
(* ----------------------------------------------------------------- *)

(* Constants for rule encoding *)
Definition RULES_START_ADDR : nat := UTM_Program.RULES_START_ADDR.
Definition RULE_SIZE : nat := 5. (* (q_old, sym_old, q_new, write, move) *)

(* Loop invariant for FindRule loop *)
Definition FindRule_Loop_Inv (tm : TM) (conf : TMConfig)
                            (cpu : CPU.State) (i : nat) : Prop :=
  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  (* PC is in the loop *)
  (CPU.read_reg CPU.REG_PC cpu = 3 \/ 
   CPU.read_reg CPU.REG_PC cpu = 4 \/
   CPU.read_reg CPU.REG_PC cpu = 5) /\
  (* State and symbol registers match current config *)
  CPU.read_reg CPU.REG_Q cpu = q /\
  CPU.read_reg CPU.REG_SYM cpu = sym /\
  (* Address pointer points to rule i *)
  CPU.read_reg CPU.REG_ADDR cpu = RULES_START_ADDR + i * RULE_SIZE /\
  (* All rules checked so far didn't match *)
  (forall j, j < i ->
    let rule := nth j (tm_rules tm) (0, 0, 0, 0, 0%Z) in
    (fst (fst (fst (fst rule))), snd (fst (fst (fst rule)))) <> (q, sym)).

(* A reflective view of the loop entry state produced by the fetch block. *)
Definition findrule_entry_state (tm : TM) (conf : TMConfig) : CPU.State :=
  run_n (setup_state tm conf) 3.

(* Reopen the small-step interpreter locally for the short FindRule traces and
   re-opaque it after the concrete 6- and 4-step lemmas below. *)
#[local] Transparent run_n decode_instr.

(* Helper lemmas to break down transition_FindRule_Next into smaller chunks.
   This prevents OOM by forcing Coq to seal proof terms at each checkpoint.
   Strategy: Use explicit decode_instr hypotheses and rewrite, NOT vm_compute. *)

(* Sealed helper lemmas to prevent term explosion - Strategy 2: Checkpoint Method *)

(* Checkpoint 1: Length preservation through run_n *)
Lemma transition_FindRule_step2b_len_cpu : forall cpu0,
  length cpu0.(CPU.regs) = 10 ->
  let cpu := run_n cpu0 3 in
  length (CPU.regs cpu) >= 10.
Proof.
  intros cpu0 Hlen0 cpu.
  subst cpu.
  eapply Nat.le_trans; [|apply length_run_n_ge].
  rewrite Hlen0. apply Nat.le_refl.
Qed.

(* Checkpoint 2: Length at step 3 *)
Lemma transition_FindRule_step2b_len3 : forall cpu,
  length (CPU.regs cpu) >= 10 ->
  length (CPU.regs (run_n cpu 3)) >= 10.
Proof.
  intros cpu Hlen_cpu.
  eapply Nat.le_trans; [|apply length_run_n_ge]. exact Hlen_cpu.
Qed.

(* Checkpoint 3: TEMP1 preserved through Jz step 3->4 *)
Lemma transition_FindRule_step2b_temp4 : forall cpu,
  decode_instr (run_n cpu 3) = CPU.Jz CPU.REG_TEMP1 12 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) =? 0 = false ->
  length (CPU.regs (run_n cpu 3)) >= 10 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 4) = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3).
Proof.
  intros cpu Hdec3 Htemp_nonzero Hlen3.
  abstract (
    change (run_n cpu 4) with (run1 (run_n cpu 3));
    rewrite run1_decode, Hdec3;
    unfold CPU.step;
    rewrite Htemp_nonzero;
    apply read_reg_write_reg_diff;
    [ unfold CPU.REG_TEMP1, CPU.REG_PC; discriminate
    | unfold CPU.REG_TEMP1; lia
    | unfold CPU.REG_PC; lia ]
  ).
Qed.

(* Checkpoint 4: Length at step 4 *)
Lemma transition_FindRule_step2b_len4 : forall cpu,
  length (CPU.regs (run_n cpu 3)) >= 10 ->
  length (CPU.regs (run_n cpu 4)) >= 10.
Proof.
  intros cpu Hlen3.
  eapply Nat.le_trans; [exact Hlen3|].
  assert (H: length (CPU.regs (run_n cpu 3)) <= length (CPU.regs (run_n cpu 4))).
  { change (run_n cpu 4) with (run1 (run_n cpu 3)).
    unfold run1. apply length_step_ge. }
  exact H.
Qed.

(* Checkpoint 5: TEMP1 preserved through AddConst step 4->5 *)
Lemma transition_FindRule_step2b_temp5 : forall cpu,
  decode_instr (run_n cpu 4) = CPU.AddConst CPU.REG_ADDR RULE_SIZE ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 4) = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) ->
  length (CPU.regs (run_n cpu 4)) >= 10 ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 5) = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3).
Proof.
  intros cpu Hdec4 Htemp4 Hlen4.
  (* run_n cpu 5 = run1 (run_n cpu 4) = CPU.step (decode_instr (run_n cpu 4)) (run_n cpu 4) *)
  change (run_n cpu 5) with (run1 (run_n cpu 4)).
  rewrite run1_decode, Hdec4.
  (* Now goal is: read_reg TEMP1 (CPU.step (AddConst ADDR RULE_SIZE) (run_n cpu 4)) 
                  = read_reg TEMP1 (run_n cpu 3) *)
  (* CPU.step (AddConst rd v) st first writes PC, then writes rd *)
  unfold CPU.step.
  (* After unfolding: write_reg ADDR (read_reg ADDR (run_n cpu 4) + RULE_SIZE) 
                      (write_reg PC (S (read_reg PC (run_n cpu 4))) (run_n cpu 4)) *)
  (* TEMP1 is preserved through PC write (TEMP1 ≠ PC) *)
  transitivity (CPU.read_reg CPU.REG_TEMP1 
                  (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4))).
  - (* TEMP1 preserved through ADDR write *)
    apply read_reg_write_reg_diff.
    + (* TEMP1 ≠ ADDR *) unfold CPU.REG_TEMP1, CPU.REG_ADDR. lia.
    + (* TEMP1 < length *)
      unfold CPU.REG_TEMP1.
      assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4)).(CPU.regs) 
                       = length (run_n cpu 4).(CPU.regs)).
      { apply length_write_reg. unfold CPU.REG_PC. lia. }
      rewrite Hlen_pc. lia.
    + (* ADDR < length *)
      unfold CPU.REG_ADDR.
      assert (Hlen_pc: length (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC (run_n cpu 4))) (run_n cpu 4)).(CPU.regs) 
                       = length (run_n cpu 4).(CPU.regs)).
      { apply length_write_reg. unfold CPU.REG_PC. lia. }
      rewrite Hlen_pc. lia.
  - (* TEMP1 preserved through PC write *)
    rewrite read_reg_write_reg_diff.
    + (* Conclude with Htemp4 *)
      exact Htemp4.
    + (* TEMP1 ≠ PC *) unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
    + (* TEMP1 < length *) unfold CPU.REG_TEMP1. lia.
    + (* PC < length *) unfold CPU.REG_PC. lia.
Qed.

Lemma transition_FindRule_Next_step2b : forall cpu0,
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
  CPU.read_reg CPU.REG_PC (run_n cpu 6) = 4.
Proof.
  intros cpu0 Hlen0 cpu Hdec0 Hdec1 Hdec2 Hdec3 Hdec4 Hdec5 Htemp_nonzero.

  (* Use sealed checkpoints to prevent term explosion *)
  assert (Hlen_cpu : length (CPU.regs cpu) >= 10).
  { apply (transition_FindRule_step2b_len_cpu cpu0 Hlen0). }

  assert (Hlen3 : length (CPU.regs (run_n cpu 3)) >= 10).
  { apply (transition_FindRule_step2b_len3 cpu Hlen_cpu). }

  assert (Htemp4 : CPU.read_reg CPU.REG_TEMP1 (run_n cpu 4)
                   = CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3)).
  { apply (transition_FindRule_step2b_temp4 cpu Hdec3 Htemp_nonzero Hlen3). }
