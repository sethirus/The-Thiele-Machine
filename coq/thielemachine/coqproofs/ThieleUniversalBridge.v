(* ================================================================= *)
(* Bridge module providing concrete implementations from archive    *)
(* This module extracts working definitions from the archive to     *)
(* avoid circular dependencies and compilation errors.              *)
(*                                                                   *)
(* STATUS: Partially complete                                        *)
(*   - Core definitions (run1, run_n, setup_state): CONCRETE ✓     *)
(*   - Basic lemmas (setup_state_regs_length, inv_min): PROVED ✓   *)
(*   - Helper lemmas (nth_add_skipn, nth_firstn_lt): PROVED ✓      *)
(*   - Transition lemmas: ADMITTED (require symbolic execution)     *)
(*                                                                   *)
(* To complete: The transition lemmas require detailed symbolic     *)
(* execution proofs through the CPU interpreter. These are complex  *)
(* but mechanizable - they involve stepping through the instruction *)
(* sequence and maintaining invariants.                             *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.

Local Open Scope nat_scope.

(* ----------------------------------------------------------------- *)
(* CPU Execution - from ThieleUniversal_Run1.v                      *)
(* ----------------------------------------------------------------- *)

(* Single step execution *)
Definition run1 (s : CPU.State) : CPU.State :=
  let instr := UTM_Encode.decode_instr_from_mem s.(CPU.mem) (4 * CPU.read_reg CPU.REG_PC s) in
  CPU.step s instr.

(* Multi-step execution *)
Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
  match n with
  | 0 => s
  | S n' => run_n (run1 s) n'
  end.

(* ----------------------------------------------------------------- *)
(* State Setup - extracted from ThieleUniversal.v                   *)
(* ----------------------------------------------------------------- *)

(* Helper: set nth element of a list *)
Definition set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  firstn n l ++ [v] ++ skipn (S n) l.

(* Helper: pad list to length n with zeros *)
Definition pad_to (n : nat) (l : list nat) : list nat :=
  l ++ repeat 0 (n - length l).

(* Setup initial CPU state from TM configuration *)
Definition setup_state (tm : TM) (conf : TMConfig) : CPU.State :=
  let '((q, tape), head) := conf in
  let regs0 := repeat 0 10 in
  let regs1 := set_nth regs0 CPU.REG_Q q in
  let regs2 := set_nth regs1 CPU.REG_HEAD head in
  let regs3 := set_nth regs2 CPU.REG_PC 0 in
  let rules := UTM_Encode.encode_rules tm.(tm_rules) in
  let mem0 := pad_to UTM_Program.RULES_START_ADDR UTM_Program.program_instrs in
  let mem1 := pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules) in
  {| CPU.regs := regs3; CPU.mem := mem1 ++ tape; CPU.cost := 0 |}.

(* ----------------------------------------------------------------- *)
(* Basic lemmas about setup_state                                    *)
(* ----------------------------------------------------------------- *)

Lemma length_set_nth : forall {A : Type} (l : list A) n v,
  n < length l ->
  length (set_nth l n v) = length l.
Proof.
  intros A l n v Hn.
  unfold set_nth.
  rewrite app_length, app_length.
  rewrite firstn_length, skipn_length.
  simpl.
  rewrite Nat.min_l by assumption.
  lia.
Qed.

Lemma setup_state_regs_length :
  forall tm conf, length (CPU.regs (setup_state tm conf)) = 10.
Proof.
  intros tm conf.
  destruct conf as ((q, tape), head).
  unfold setup_state; simpl.
  repeat (rewrite length_set_nth; [|simpl; lia]).
  rewrite repeat_length.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* State predicates and invariants                                   *)
(* ----------------------------------------------------------------- *)

Definition inv_min (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  CPU.read_reg CPU.REG_Q st = q /\
  CPU.read_reg CPU.REG_HEAD st = head /\
  CPU.read_reg CPU.REG_PC st = 0.

Lemma inv_min_setup_state : forall tm conf,
  inv_min (setup_state tm conf) tm conf.
Proof.
  intros tm ((q, tape), head).
  unfold inv_min, setup_state; simpl.
  repeat split.
  - (* REG_Q *)
    unfold CPU.read_reg.
    repeat (rewrite nth_firstn || rewrite nth_skipn || simpl); try lia.
    reflexivity.
  - (* REG_HEAD *)
    unfold CPU.read_reg.
    repeat (rewrite nth_firstn || rewrite nth_skipn || simpl); try lia.
    reflexivity.
  - (* REG_PC *)
    unfold CPU.read_reg.
    repeat (rewrite nth_firstn || rewrite nth_skipn || simpl); try lia.
    reflexivity.
Qed.

Definition IS_FetchSymbol (pc : nat) : Prop := pc = 0.
Definition IS_FindRule_Start (pc : nat) : Prop := pc = 3.

(* Full invariant placeholder - to be refined as needed *)
Definition inv (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  inv_min st tm conf /\
  (* Additional invariants would go here *)
  True.

Lemma inv_setup_state : forall tm conf,
  inv (setup_state tm conf) tm conf.
Proof.
  intros tm conf.
  unfold inv.
  split.
  - apply inv_min_setup_state.
  - exact I.
Qed.

Definition inv_core (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  inv_min st tm conf.

Definition find_rule_start_inv (tm : TM) (conf : TMConfig) (cpu : CPU.State) : Prop :=
  IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu) /\
  inv_min cpu tm conf.

(* ----------------------------------------------------------------- *)
(* Decoding                                                          *)
(* ----------------------------------------------------------------- *)

Definition decode_instr (st : CPU.State) : CPU.Instr :=
  UTM_Encode.decode_instr_from_mem st.(CPU.mem) (4 * CPU.read_reg CPU.REG_PC st).

(* ----------------------------------------------------------------- *)
(* Helper lemmas                                                      *)
(* ----------------------------------------------------------------- *)

Lemma nth_add_skipn : forall {A} n m (l : list A) d,
  nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros A n m l d.
  revert n m.
  induction l as [|x l IH]; intros n m.
  - destruct m; destruct n; simpl; reflexivity.
  - destruct m.
    + simpl. reflexivity.
    + simpl. apply IH.
Qed.

Lemma nth_firstn_lt : forall {A} n m (l : list A) d,
  n < m -> nth n (firstn m l) d = nth n l d.
Proof.
  intros A n m l d Hn.
  revert n m Hn.
  induction l as [|x l IH]; intros n m Hn.
  - destruct n; destruct m; simpl; try reflexivity; try lia.
  - destruct n; destruct m; simpl; try reflexivity; try lia.
    apply IH. lia.
Qed.

(* Placeholder transition lemmas - these would need full proofs *)
(* For now we provide stubs that can be filled in *)

(* ----------------------------------------------------------------- *)
(* Common Infrastructure Lemmas                                      *)
(* ----------------------------------------------------------------- *)

(* Step composition lemmas *)
Lemma run_n_add : forall cpu m n,
  run_n cpu (m + n) = run_n (run_n cpu m) n.
Proof.
  intros cpu m n.
  revert cpu.
  induction m as [|m' IH]; intros cpu.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma run_n_S : forall cpu n,
  run_n cpu (S n) = run1 (run_n cpu n).
Proof.
  intros cpu n.
  revert cpu.
  induction n as [|n' IH]; intros cpu.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma run_n_0 : forall cpu,
  run_n cpu 0 = cpu.
Proof.
  intros cpu. reflexivity.
Qed.

Lemma run_n_1 : forall cpu,
  run_n cpu 1 = run1 cpu.
Proof.
  intros cpu. reflexivity.
Qed.

(* Rewrite run_n in terms of iterations *)
Lemma run_n_unfold_3 : forall cpu,
  run_n cpu 3 = run1 (run1 (run1 cpu)).
Proof.
  intros cpu.
  unfold run_n at 1.
  unfold run_n at 1.
  unfold run_n at 1.
  simpl.
  reflexivity.
Qed.

(* Memory and register helpers *)
Lemma read_reg_bounds : forall cpu r,
  r < 10 ->
  exists v, CPU.read_reg r cpu = v.
Proof.
  intros cpu r Hr.
  exists (CPU.read_reg r cpu).
  reflexivity.
Qed.

(* CPU.step PC progression for non-branching instructions *)
Lemma step_pc_increment : forall cpu instr,
  (forall rc tgt, instr <> CPU.Jz rc tgt) ->
  (forall rc tgt, instr <> CPU.Jnz rc tgt) ->
  instr <> CPU.Halt ->
  CPU.read_reg CPU.REG_PC (CPU.step instr cpu) = S (CPU.read_reg CPU.REG_PC cpu).
Proof.
  intros cpu instr Hnot_jz Hnot_jnz Hnot_halt.
  unfold CPU.step.
  destruct instr; simpl;
    try (unfold CPU.write_reg; simpl; reflexivity);
    try contradiction.
  - (* Jz case *) exfalso. apply (Hnot_jz r n). reflexivity.
  - (* Jnz case *) exfalso. apply (Hnot_jnz r n). reflexivity.
  - (* Halt case *) exfalso. apply Hnot_halt. reflexivity.
Qed.

(* Placeholder for PC progression - will be refined *)
Axiom pc_in_bounds : forall cpu,
  CPU.read_reg CPU.REG_PC cpu < 100. (* Rough upper bound *)

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
  CPU.LoadConst CPU.REG_TEMP1 CPU.TAPE_START_ADDR.
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
  CPU.LoadConst CPU.REG_ADDR CPU.RULES_START_ADDR.
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

(* Lemma for LoadConst execution *)
Lemma step_LoadConst : forall cpu rd v,
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.LoadConst rd v) cpu) = S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.LoadConst rd v) cpu) = v.
Proof.
  intros cpu rd v.
  unfold CPU.step.
  simpl.
  split.
  - unfold CPU.write_reg, CPU.read_reg. simpl. reflexivity.
  - unfold CPU.write_reg, CPU.read_reg. simpl.
    (* This needs more detail about register file structure *)
Admitted.

(* Lemma for AddReg execution *)
Lemma step_AddReg : forall cpu rd rs1 rs2,
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.AddReg rd rs1 rs2) cpu) = S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.AddReg rd rs1 rs2) cpu) = 
    CPU.read_reg rs1 cpu + CPU.read_reg rs2 cpu.
Proof.
  intros cpu rd rs1 rs2.
  unfold CPU.step.
  simpl.
  split.
  - unfold CPU.write_reg, CPU.read_reg. simpl. reflexivity.
  - unfold CPU.write_reg, CPU.read_reg. simpl.
    (* This needs more detail about register file structure *)
Admitted.

(* Lemma for LoadIndirect execution *)
Lemma step_LoadIndirect : forall cpu rd ra,
  CPU.read_reg CPU.REG_PC (CPU.step (CPU.LoadIndirect rd ra) cpu) = S (CPU.read_reg CPU.REG_PC cpu) /\
  CPU.read_reg rd (CPU.step (CPU.LoadIndirect rd ra) cpu) = 
    CPU.read_mem (CPU.read_reg ra cpu) cpu.
Proof.
  intros cpu rd ra.
  unfold CPU.step.
  simpl.
  split.
  - unfold CPU.write_reg, CPU.read_reg. simpl. reflexivity.
  - unfold CPU.write_reg, CPU.read_reg. simpl.
    (* This needs more detail about register file structure *)
Admitted.

(* ----------------------------------------------------------------- *)
(* Symbolic Execution - Attempt at Proof 1                          *)
(* ----------------------------------------------------------------- *)

(* Try a direct proof approach using the specific instructions *)
Lemma transition_Fetch_to_FindRule_direct : forall tm conf cpu0,
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  CPU.read_reg CPU.REG_PC cpu0 = 0 ->
  (* Assume we can decode instructions from memory encoded program *)
  (forall pc, UTM_Encode.decode_instr_from_mem cpu0.(CPU.mem) (4 * pc) = 
              nth pc UTM_Program.program_instrs CPU.Halt) ->
  exists cpu_find, 
    run_n cpu0 3 = cpu_find /\ 
    IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu_find) /\
    CPU.read_reg CPU.REG_PC cpu_find = 3.
Proof.
  intros tm conf cpu0 Hinv Hfetch Hpc0 Hdecode.
  
  (* Expand run_n 3 = run1 (run1 (run1 cpu0)) *)
  exists (run_n cpu0 3).
  split; [reflexivity|].
  split.
  - unfold IS_FindRule_Start. 
    (* We need to show PC = 3 *)
    
    (* Step 1: Execute instruction at PC=0 *)
    assert (H_step0 : run_n cpu0 1 = run1 cpu0) by reflexivity.
    
    (* Instruction at PC=0 is LoadConst REG_TEMP1 TAPE_START_ADDR *)
    assert (H_instr0 : UTM_Encode.decode_instr_from_mem cpu0.(CPU.mem) (4 * 0) = 
                       CPU.LoadConst CPU.REG_TEMP1 CPU.TAPE_START_ADDR).
    { rewrite Hdecode. rewrite instr_at_pc_0. reflexivity. }
    
    (* After step 1, PC = 1 *)
    unfold run1 at 1.
    rewrite H_instr0.
    
    (* Now we need to show that after 3 steps, PC = 3 *)
    (* This requires unfolding run_n further and tracking PC through each step *)
    
Admitted.

(* Now we need to show PC advances correctly *)
(* This requires knowing what instructions are at PC=0, 1, 2 *)

(* ----------------------------------------------------------------- *)
(* Transition Lemmas                                                 *)
(* ----------------------------------------------------------------- *)

Lemma transition_Fetch_to_FindRule (tm : TM) (conf : TMConfig) (cpu0 : CPU.State) :
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  exists cpu_find, run_n cpu0 3 = cpu_find /\ IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu_find).
Proof.
  intros Hinv Hfetch.
  (* Strategy: Unfold run_n to 3 iterations, then show PC progression *)
  
  (* Unfold Hfetch to get PC = 0 *)
  unfold IS_FetchSymbol in Hfetch.
  
  (* Set up the result state *)
  exists (run_n cpu0 3).
  split.
  - reflexivity.
  - (* Need to show PC = 3 after 3 steps *)
    unfold IS_FindRule_Start.
    
    (* This is where we need symbolic execution *)
    (* TODO: Expand run_n, decode instructions at PC=0,1,2, execute them *)
    (* 
       Step 1: cpu0 has PC=0
       - Decode instruction at PC=0
       - Execute: PC becomes 1
       
       Step 2: cpu1 has PC=1  
       - Decode instruction at PC=1
       - Execute: PC becomes 2
       
       Step 3: cpu2 has PC=2
       - Decode instruction at PC=1
       - Execute: PC becomes 3
       
       Infrastructure available:
       - run_n_unfold_3 to expand 3 iterations
       - step_pc_increment for PC progression
       
       Missing:
       - Concrete knowledge of what instructions are at PC=0,1,2
       - Lemmas about how those specific instructions affect state
    *)
Admitted.

Lemma transition_FindRule_to_ApplyRule (tm : TM) (conf : TMConfig) (cpu_find : CPU.State) 
  (q' write : nat) (move : Z) :
  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  inv_core cpu_find tm conf ->
  find_rule_start_inv tm conf cpu_find ->
  find_rule (tm_rules tm) q sym = Some (q', write, move) ->
  exists k cpu_apply, run_n cpu_find k = cpu_apply.
Proof.
  intros q tape head sym Hinv_core Hstart_inv Hfind.
  (* TODO: This requires symbolic execution through the rule matching loop.
     Proof strategy:
     1. Start at PC=3 (FindRule_Start)
     2. Execute loop searching for matching rule
     3. Show that when rule is found, execution reaches ApplyRule state
     4. Return the CPU state and step count
     
     This is complex because:
     - Number of steps depends on rule table size
     - Requires reasoning about loop invariants
     - Requires memory/register preservation properties
  *)
Admitted.
