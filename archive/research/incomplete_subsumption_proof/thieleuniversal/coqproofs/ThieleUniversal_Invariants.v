Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Require Import CPU.
Require Import UTM_Rules.
Require Import UTM_Encode.
Require Import UTM_Program.
Require Import UTM_CoreLemmas.
Require Import ZCPULemmas.
Require Import ThieleUniversal_Program.
Require Import ThieleUniversal_Run1.

Import ListNotations.

(* Strengthened invariant relating CPU state to TM configuration. *)
Definition inv (st : State) (tm : TM) (conf : TMConfig) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_HEAD st = head /\
  read_reg REG_PC st = 0 /\
  tape_window_ok st tape /\
  firstn (length program) st.(mem) = program /\
  firstn (length (encode_rules tm.(tm_rules)))
        (skipn RULES_START_ADDR st.(mem)) = encode_rules tm.(tm_rules).

(* Core invariant used after the program counter has advanced beyond
   the fetch entry point.  This drops the PC constraint while retaining
   the data- and memory-layout facts needed by the symbolic execution
   lemmas. *)
Definition inv_core (st : State) (tm : TM) (conf : TMConfig) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_HEAD st = head /\
  tape_window_ok st tape /\
  firstn (length program) st.(mem) = program /\
  firstn (length (encode_rules tm.(tm_rules)))
        (skipn RULES_START_ADDR st.(mem)) = encode_rules tm.(tm_rules).

Lemma inv_implies_inv_core :
  forall st tm conf,
    inv st tm conf -> inv_core st tm conf.
Proof.
  intros st tm conf Hinv.
  destruct conf as ((q, tape), head).
  unfold inv in Hinv.
  unfold inv_core.
  destruct Hinv as [Hq [Hhead [_ [Htape [Hprog Hrules]]]]].
  repeat split; assumption.
Qed.

(* Strong invariant implies the tape window predicate. *)
Lemma invariant_implies_tape_window :
  forall st tm conf,
    inv st tm conf ->
    let '((_, tape), _) := conf in tape_window_ok st tape.
Proof.
  intros st tm conf Hinv.
  destruct conf as ((q0, tape), head0).
  unfold inv in Hinv.
  destruct Hinv as (_ & _ & _ & Htape & _ & _).
  exact Htape.
Qed.

(* Minimal invariant capturing only the register relations. *)
Definition inv_min (st : State) (tm : TM) (conf : TMConfig) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_HEAD st = head /\
  read_reg REG_PC st = 0.

(* Minimal invariant holds for the setup state. *)
Lemma inv_min_setup_state :
  forall tm conf, inv_min (setup_state tm conf) tm conf.
Proof.
  intros tm conf.
  destruct conf as ((q, tape), head).
  unfold inv_min, setup_state; cbn.
  repeat split; reflexivity.
Qed.

(* Strong invariant implies the minimal one. *)
Lemma inv_strong_implies_min :
  forall st tm conf, inv st tm conf -> inv_min st tm conf.
Proof.
  intros st tm conf Hinv.
  destruct conf as ((q, tape), head).
  unfold inv in Hinv.
  destruct Hinv as (HQ & HHEAD & HPC & _ & _ & _).
  unfold inv_min; repeat split; assumption.
Qed.

Lemma run_n_mem_preserved_from_inv : forall tm conf st k,
  inv st tm conf ->
  (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
  (run_n st k).(mem) = st.(mem).
Proof.
  intros tm conf st k Hinv Hpc.
  destruct conf as ((q, tape), head).
  unfold inv in Hinv.
  destruct Hinv as (_ & _ & _ & _ & Hprog & _).
  apply run_n_mem_preserved_until_apply; assumption.
Qed.

Lemma rule_table_preserved_until_apply : forall tm conf st k,
  inv st tm conf ->
  (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
  firstn (length (encode_rules tm.(tm_rules)))
        (skipn RULES_START_ADDR (mem (run_n st k))) =
  encode_rules tm.(tm_rules).
Proof.
  intros tm conf st k Hinv Hpc_lt.
  pose proof (run_n_mem_preserved_from_inv tm conf st k Hinv Hpc_lt) as Hmem.
  destruct conf as ((q, tape), head).
  unfold inv in Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ Hr]]]]].
  rewrite Hmem.
  exact Hr.
Qed.

Lemma inv_init : forall tm conf,
  length program <= RULES_START_ADDR ->
  length (encode_rules tm.(tm_rules)) <= TAPE_START_ADDR - RULES_START_ADDR ->
  inv (setup_state tm conf) tm conf.
Proof.
  intros tm conf Hprog Hrules.
  unfold inv.
  destruct conf as ((q, tape), head).
  split.
  { unfold setup_state; cbn [read_reg set_nth repeat]; reflexivity. }
  split.
  { unfold setup_state; cbn [read_reg set_nth repeat]; reflexivity. }
  split.
  { unfold setup_state; cbn [read_reg set_nth repeat]; reflexivity. }
  split.
  { change (tape_window_ok (setup_state tm ((q, tape), head)) tape).
    apply tape_window_ok_setup_state; assumption. }
  split.
  { unfold setup_state; cbn [mem].
    set (rules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0 : length mem0 = RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; assumption).
    pose proof RULES_START_ADDR_le_TAPE_START_ADDR as Haddr.
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite length_app, Hmem0.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)) by lia.
      apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to TAPE_START_ADDR (mem0 ++ rules)) = TAPE_START_ADDR)
      by (apply length_pad_to_ge; assumption).
    subst mem1.
    rewrite firstn_app_le by (rewrite Hmem1_len; lia).
    rewrite (firstn_pad_to_le (mem0 ++ rules) TAPE_START_ADDR (length program)) by (rewrite length_app, Hmem0; lia).
    rewrite firstn_app_le by (rewrite Hmem0; lia).
    subst mem0; apply firstn_pad_to; assumption. }
  { unfold setup_state; cbn [mem].
    set (rules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0 : length mem0 = RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; assumption).
    pose proof RULES_START_ADDR_le_TAPE_START_ADDR as Haddr.
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite length_app, Hmem0.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)) by lia.
      apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to TAPE_START_ADDR (mem0 ++ rules)) = TAPE_START_ADDR)
      by (apply length_pad_to_ge; assumption).
    subst mem1.
    rewrite skipn_app_le by (rewrite Hmem1_len; lia).
    rewrite (skipn_pad_to_split (mem0 ++ rules) TAPE_START_ADDR RULES_START_ADDR) by (rewrite length_app, Hmem0; lia).
    rewrite skipn_app_le by (rewrite Hmem0; lia).
    rewrite <- Hmem0.
    rewrite skipn_all.
    simpl.
    rewrite app_nil_l.
    rewrite <- app_assoc.
    rewrite firstn_app_le by lia.
    apply firstn_all_length. }
Qed.

(* ---------- Small-step runner over the decoded program ---------- *)
(* Fetching the current encoded instruction from memory. *)
Lemma fetch_current_instr : forall s,
  nth (read_reg REG_PC s) (CPU.mem s) 0 =
  read_mem (read_reg REG_PC s) s.
Proof. reflexivity. Qed.

Lemma run_n_mem_preserved_if_no_store : forall s n,
  (forall k, k < n ->
    match decode_instr (run_n s k) with
    | StoreIndirect _ _ => False
    | _ => True
    end) ->
  (run_n s n).(mem) = s.(mem).
Proof.
  intros s n.
  revert s.
  induction n as [|n IH]; intros s Hsafe.
  - reflexivity.
  - rewrite run_n_succ.
    assert (Hhead : match decode_instr (run_n s 0) with
                    | StoreIndirect _ _ => False
                    | _ => True
                    end).
    { apply Hsafe. lia. }
    simpl in Hhead.
    assert (Hmem1 : (run1 s).(mem) = s.(mem)).
    { apply run1_mem_preserved_if_no_store. exact Hhead. }
    assert (Htail : forall k, k < n ->
      match decode_instr (run_n (run1 s) k) with
      | StoreIndirect _ _ => False
      | _ => True
      end).
    { intros k Hk.
      specialize (Hsafe (S k)).
      assert (HS : S k < S n) by lia.
      specialize (Hsafe HS).
      rewrite run_n_succ in Hsafe.
      exact Hsafe.
    }
    specialize (IH (run1 s)).
    specialize (IH Htail).
    rewrite IH.
    exact Hmem1.
Qed.

(* After fetching a tape symbol, control jumps to the rule-search loop. *)
Lemma transition_Fetch_to_FindRule :
  forall tm conf st,
    inv st tm conf ->
    IS_FetchSymbol (read_reg REG_PC st) ->
    exists st',
      st' = run_n st 3 /\
      IS_FindRule_Start (read_reg REG_PC st').
Proof.
  intros tm conf st Hinv HPC.
  destruct conf as ((q, tape), head).
  destruct Hinv as [HQ [HHEAD [HPC0 [Htape [Hprog Hr]]]]].
  unfold IS_FetchSymbol in HPC.
  inversion HPC0. clear HPC0.
  set (steps := S (S (S (read_reg REG_PC st)))).
  exists (run_n st steps); split.
  { subst steps. rewrite H0. reflexivity. }
  subst steps.
  rewrite H0.
  unfold IS_FindRule_Start.
  (* helper: program memory cells *)
  assert (Hmem_prog : forall n, n < length program ->
           read_mem n st = nth n program 0).
  { intros n Hlt.
    unfold read_mem.
    rewrite <- Hprog.
    rewrite nth_firstn_lt; [reflexivity|assumption]. }
  assert (Hlen_prog : length program > 11) by apply program_length_gt_11.
  assert (Hnth0 : nth 0 (mem st) 0 = 0).
  { pose proof (Hmem_prog 0 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_0 in Hm.
    exact Hm. }
  assert (Hnth1 : nth 1 (mem st) 0 = REG_TEMP1).
  { pose proof (Hmem_prog 1 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_1 in Hm.
    exact Hm. }
  assert (Hnth2 : nth 2 (mem st) 0 = TAPE_START_ADDR).
  { pose proof (Hmem_prog 2 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_2 in Hm.
    exact Hm. }
  assert (Hnth3 : nth 3 (mem st) 0 = 0).
  { pose proof (Hmem_prog 3 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_3 in Hm.
    exact Hm. }
  assert (Hnth4 : nth 4 (mem st) 0 = 5).
  { pose proof (Hmem_prog 4 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_4 in Hm.
    exact Hm. }
  assert (Hnth5 : nth 5 (mem st) 0 = REG_ADDR).
  { pose proof (Hmem_prog 5 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_5 in Hm.
    exact Hm. }
  assert (Hnth6 : nth 6 (mem st) 0 = REG_TEMP1).
  { pose proof (Hmem_prog 6 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_6 in Hm.
    exact Hm. }
  assert (Hnth7 : nth 7 (mem st) 0 = REG_HEAD).
  { pose proof (Hmem_prog 7 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_7 in Hm.
    exact Hm. }
  assert (Hnth8 : nth 8 (mem st) 0 = 1).
  { pose proof (Hmem_prog 8 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_8 in Hm.
    exact Hm. }
  assert (Hnth9 : nth 9 (mem st) 0 = REG_SYM).
  { pose proof (Hmem_prog 9 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_9 in Hm.
    exact Hm. }
  assert (Hnth10 : nth 10 (mem st) 0 = REG_ADDR).
  { pose proof (Hmem_prog 10 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_10 in Hm.
    exact Hm. }
  assert (Hnth11 : nth 11 (mem st) 0 = 0).
  { pose proof (Hmem_prog 11 ltac:(lia)) as Hm.
    unfold read_mem in Hm.
    change st.(mem) with (mem st) in Hm.
    rewrite program_word_11 in Hm.
    exact Hm. }
  (* decode first instruction using the state-based decoder *)
  assert (Hdec0 : decode_instr st = LoadConst REG_TEMP1 TAPE_START_ADDR).
  { unfold decode_instr.
    rewrite H0.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth0, Hnth1, Hnth2.
    cbn.
    reflexivity. }
  assert (Hmem_run1 : (run1 st).(mem) = st.(mem)).
  { unfold run1; rewrite Hdec0; unfold step; simpl. reflexivity. }
  assert (Hdec1_mem : decode_instr_from_mem st.(mem) 4 =
                      AddReg REG_ADDR REG_TEMP1 REG_HEAD).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth4.
    cbn.
    rewrite Hnth5.
    cbn.
    rewrite Hnth6.
    cbn.
    rewrite Hnth7.
    cbn.
    reflexivity. }
  assert (Hpc1_succ : read_reg REG_PC (run1 st) = S (read_reg REG_PC st)).
  { apply run1_pc_succ.
    rewrite Hdec0; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc1 : read_reg REG_PC (run1 st) = 1).
  { rewrite Hpc1_succ, H0. reflexivity. }
  (* decode second instruction *)
  assert (Hdec1 : decode_instr (run1 st) = AddReg REG_ADDR REG_TEMP1 REG_HEAD).
  { unfold decode_instr.
    rewrite Hpc1.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run1.
    change st.(mem) with (mem st) in Hm.
    exact Hdec1_mem. }
  assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
  { apply run1_mem_preserved_if_no_store.
    rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
       rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
Proof.
  intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
  destruct conf as ((q, tape), head).
  (* Proof starts here. *)
  destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
  assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
  destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
  assert (Hinv_full : inv st tm ((q, tape), head)).
  { unfold inv; repeat split; assumption. }
  assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
  assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
  { pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
    assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
    pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
    rewrite Hdecode_prog.
    rewrite Hpc_4.
    rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
    reflexivity.
  }
  set (st1 := run1 st).
  assert (Hpc_st1 : read_reg REG_PC st1 = 5).
  { subst st1.
    assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
    { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
    pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
    rewrite Hpc_4 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  }
  assert (Hlen_st1 : length (regs st1) = 10).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = 10).
    { subst st_pc.
      apply length_regs_write_reg_10; [exact Hlen_st|].
      rewrite Hlen_st. unfold REG_PC. lia. }
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; unfold REG_Q'; lia).
    apply length_regs_write_reg_10; [exact Hlen_pc|].
    exact Hq'_bound_pc.
  }
  assert (Haddr_bound : REG_ADDR < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr_reg.
    unfold RULES_START_ADDR.
    lia.
  }
  assert (Hpc_bound : REG_PC < length (regs st)).
  { apply read_reg_nonzero_implies_in_bounds.
    rewrite Hpc_4.
    discriminate.
  }
  assert (Hq_bound : REG_Q < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q; lia).
  assert (Hq'_bound : REG_Q' < length (regs st))
    by (rewrite Hlen_st; unfold REG_Q'; lia).
  assert (Hsym_bound : REG_SYM < length (regs st))
    by (rewrite Hlen_st; unfold REG_SYM; lia).
  assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_PC. lia. }
  assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_ADDR. lia. }
  assert (Hq_bound_st1 : REG_Q < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q. lia. }
  assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_Q'. lia. }
  assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
  assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
  { rewrite Hlen_st1. unfold REG_SYM. lia. }
  assert (Hst1_q : read_reg REG_Q st1 = q).
  { subst st1.
    unfold run1.
    rewrite Hdecode_pc4.
    cbn [CPU.step read_reg write_reg read_mem].
    set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
    assert (Hlen_pc : length (regs st_pc) = length (regs st)).
    { subst st_pc.
      apply length_regs_write_reg.
      exact Hpc_bound.
    }
    assert (Hq_bound_pc : REG_Q < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq_bound).
    assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
      by (rewrite Hlen_pc; exact Hq'_bound).
    assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
    assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
    assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
    { subst st_pc.
      apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
    }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
  assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
  { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
  assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                      LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    change st.(mem) with (mem st).
    rewrite Hnth8.
    cbn.
    rewrite Hnth9.
    cbn.
    rewrite Hnth10.
    cbn.
    reflexivity. }
  assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
  { apply run1_pc_succ.
    rewrite Hdec1; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
  { rewrite Hpc2_succ, Hpc1. reflexivity. }
  (* decode third instruction *)
  assert (Hdec2 : decode_instr (run1 (run1 st)) =
                  LoadIndirect REG_SYM REG_ADDR).
  { unfold decode_instr.
    rewrite Hpc2.
    cbn [read_reg].
    unfold decode_instr_from_mem.
    cbn [Nat.mul Nat.add].
    rewrite Hmem_run2.
    change st.(mem) with (mem st) in Hm.
    exact Hdec2_mem. }
  assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                       S (read_reg REG_PC (run1 (run1 st)))).
  { apply run1_pc_succ.
    rewrite Hdec2; simpl.
    intros Hneq; inversion Hneq. }
  assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
  { rewrite Hpc2 in Hpc3_succ.
    simpl in Hpc3_succ.
    exact Hpc3_succ. }
  unfold IS_FindRule_Start.
  cbn [run_n].
  exact Hpc3.
Qed.

(* State immediately after the fetch phase and before entering the loop. *)
Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR /\
  read_reg REG_PC st = 3.

(* Loop invariant for the rule-search phase. After checking [i] rules the
   address register advances by 5*i while the state and symbol registers
   remain fixed and control jumps back to program counter 4. *)
Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
           (st:State) (i:nat) : Prop :=
  let '((q, tape), head) := conf in
  read_reg REG_Q st = q /\
  read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
  read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
  read_reg REG_PC st = 4.

Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
  find_rule_start_inv tm conf st ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_start_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  read_reg REG_PC st < 29.
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ Hpc]]].
  subst.
  lia.
Qed.

Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
  find_rule_loop_inv tm conf st i ->
  REG_ADDR < length (regs st).
Proof.
  intros tm conf st i Hinv.
  destruct conf as ((q, tape), head).
  unfold find_rule_loop_inv in Hinv.
  destruct Hinv as [_ [_ [Haddr _]]].
  apply read_reg_nonzero_implies_in_bounds.
  rewrite Haddr.
  unfold RULES_START_ADDR.
  lia.
Qed.

Definition rule_table_q_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        q_rule <= q
    end.

Definition rule_table_symbol_monotone (tm : TM) : Prop :=
  forall i q sym res,
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        q_rule = q ->
        find_rule (skipn i (tm_rules tm)) q sym = Some res ->
        sym_rule <= sym
    end.

Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv_core st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
Proof.
  intros tm conf st i component_offset Hcore Hi.
  destruct conf as ((q, tape), head).
  simpl in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hr]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    unfold read_mem.
    rewrite nth_add_skipn.
    pose proof Hr as Hnth_raw.
    pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                              (skipn RULES_START_ADDR st.(mem)) 0 Hk)
      as Hfirstn.
    rewrite <- Hfirstn.
    pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
    exact Hnth.
  }
  destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
  repeat split; intros Hc;
    pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
      assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
        by (rewrite length_UTM_Encode_encode_rules; lia);
    specialize (Haddr Hlen);
    replace (RULES_START_ADDR + i * 5 + component_offset)
      with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
    subst component_offset;
    rewrite Haddr;
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia;
    rewrite Hr_i; reflexivity.
Qed.

Lemma find_rule_skipn_replace :
  forall rules i q sym default tail,
    skipn i rules = default :: tail ->
    find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
Proof.
  intros rules i q sym default tail Hsplit.
  rewrite Hsplit.
  reflexivity.
Qed.

Lemma find_rule_skipn_succ :
  forall rules i q sym,
    find_rule
      match rules with
      | [] => []
      | _ :: l => skipn i l
      end q sym =
    find_rule (skipn (S i) rules) q sym.
Proof.
  intros rules i q sym.
  destruct rules; reflexivity.
Qed.

Lemma find_rule_cons_mismatch :
  forall q_rule sym_rule q_next w_next m_next tail q sym,
    andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
    find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
    find_rule tail q sym.
Proof.
  intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
  simpl.
  rewrite Hmatch.
  reflexivity.
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head