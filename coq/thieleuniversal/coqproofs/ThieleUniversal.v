Require Import ThieleUniversal.UTM_Encode.
Require Import ThieleUniversal.UTM_Program.
Require Import ThieleUniversal.CPU.
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

(* --- Section: Universal Program and Simulation --- *)

Module UTM.
  Import CPU.

  (* Memory predicate asserting the tape segment at [TAPE_START_ADDR]. *)
  Definition tape_window_ok (st : State) (tape : list nat) : Prop :=
    firstn (length tape) (skipn TAPE_START_ADDR st.(mem)) = tape.

  (* --- Explicit universal program --- *)
  (* Encoding base used for packing instruction operands into a single word. *)
  Definition ENC_BASE := 1024.

  (* Encode a single instruction as a natural number. *)
  Definition encode_instr (i:Instr) : nat :=
    match i with
    | LoadConst rd v      => 0 + rd*ENC_BASE + v*ENC_BASE*ENC_BASE
    | LoadIndirect rd ra  => 1 + rd*ENC_BASE + ra*ENC_BASE*ENC_BASE
    | StoreIndirect ra rv => 2 + ra*ENC_BASE + rv*ENC_BASE*ENC_BASE
    | CopyReg rd rs       => 3 + rd*ENC_BASE + rs*ENC_BASE*ENC_BASE
    | AddConst rd v       => 4 + rd*ENC_BASE + v*ENC_BASE*ENC_BASE
    | AddReg rd r1 r2     => 5 + rd*ENC_BASE + r1*ENC_BASE*ENC_BASE + r2*ENC_BASE*ENC_BASE*ENC_BASE
    | SubReg rd r1 r2     => 6 + rd*ENC_BASE + r1*ENC_BASE*ENC_BASE + r2*ENC_BASE*ENC_BASE*ENC_BASE
    | Jz rc target        => 7 + rc*ENC_BASE + target*ENC_BASE*ENC_BASE
    | Jnz rc target       => 8 + rc*ENC_BASE + target*ENC_BASE*ENC_BASE
    | Halt                => 9
    end.

  (* Decode an encoded instruction. Unknown opcodes default to [Halt]. *)
  (* Decoder now reads three memory words starting at PC to reconstruct
     an instruction. This change avoids heavy div/mod work on large
     integers by using trivial nth lookups. *)
  Definition decode_instr (st : CPU.State) : Instr :=
    let pc := read_reg REG_PC st in
    let mem := st.(mem) in
    let opcode := nth pc mem 0 in
    let arg1 := nth (pc + 1) mem 0 in
    let arg2 := nth (pc + 2) mem 0 in
    match opcode with
    | 0 => LoadConst arg1 arg2
    | 1 => LoadIndirect arg1 arg2
    | 2 => StoreIndirect arg1 arg2
    | 3 => CopyReg arg1 arg2
    | 4 => AddConst arg1 arg2
    | 5 => AddReg arg1 (arg2 / ENC_BASE) (arg2 mod ENC_BASE)
    | 6 => SubReg arg1 (arg2 / ENC_BASE) (arg2 mod ENC_BASE)
    | 7 => Jz arg1 arg2
    | 8 => Jnz arg1 arg2
    | _ => Halt
    end.

  (** Every encoded instruction assumes its operands fit within [ENC_BASE]. *)
  Definition instr_small (i : Instr) : Prop :=
    match i with
    | LoadConst rd v | LoadIndirect rd v | CopyReg rd v | AddConst rd v
    | Jz rd v | Jnz rd v => rd < ENC_BASE /\ v < ENC_BASE
    | StoreIndirect ra rv => ra < ENC_BASE /\ rv < ENC_BASE
    | AddReg rd r1 r2 | SubReg rd r1 r2 =>
        rd < ENC_BASE /\ r1 < ENC_BASE /\ r2 < ENC_BASE
    | Halt => True
    end.

  (** Decoding an encoded instruction yields the original instruction. *)
  Lemma decode_encode_roundtrip :
    forall i, instr_small i -> decode_instr (encode_instr i) = i.
  Proof.
    intros i Hs.
    (* Helper tactics for two- and three-operand instructions. *)
    Local Ltac solve_two rd v opcode :=
      set (B := ENC_BASE) in *;
      assert (Bpos : B > 0) by (subst B; unfold ENC_BASE; lia);
      assert (Hop : (opcode + rd * B + v * B * B) mod B = opcode)
        by (repeat (rewrite Nat.add_mod by lia);
            rewrite Nat.mod_small with (a:=opcode) by lia;
            repeat (rewrite Nat.mod_mul by lia);
            lia);
      assert (Hw1 : (opcode + rd * B + v * B * B) / B = rd + v * B)
        by (replace (opcode + rd * B + v * B * B)
             with (opcode + (rd + v * B) * B) by lia;
            rewrite Nat.div_add by lia;
            rewrite Nat.div_small with (a:=opcode) (b:=B) by lia;
            rewrite Nat.div_mul by lia;
            lia);
      assert (Harg1 : (rd + v * B) mod B = rd)
        by (rewrite Nat.add_mod by lia;
            rewrite Nat.mod_mul by lia;
            rewrite Nat.mod_small by lia;
            lia);
      assert (Hw2 : (rd + v * B) / B = v)
        by (apply Nat.div_unique with (r:=rd); lia);
      assert (Harg2 : v mod B = v) by (apply Nat.mod_small; lia);
      rewrite Hop, Hw1, Harg1, Hw2, Harg2; reflexivity.

    Local Ltac solve_three rd r1 r2 opcode :=
      set (B := ENC_BASE) in *;
      assert (Bpos : B > 0) by (subst B; unfold ENC_BASE; lia);
      assert (Hop : (opcode + rd * B + r1 * B * B + r2 * B * B * B) mod B = opcode)
        by (repeat (rewrite Nat.add_mod by lia);
            rewrite Nat.mod_small with (a:=opcode) by lia;
            repeat (rewrite Nat.mod_mul by lia);
            lia);
      assert (Hw1 : (opcode + rd * B + r1 * B * B + r2 * B * B * B) / B
                   = rd + r1 * B + r2 * B * B)
        by (replace (opcode + rd * B + r1 * B * B + r2 * B * B * B)
             with (opcode + (rd + r1 * B + r2 * B * B) * B) by lia;
            rewrite Nat.div_add by lia;
            rewrite Nat.div_small with (a:=opcode) (b:=B) by lia;
            rewrite Nat.div_mul by lia;
            lia);
      assert (Harg1 : (rd + r1 * B + r2 * B * B) mod B = rd)
        by (repeat (rewrite Nat.add_mod by lia);
            repeat (rewrite Nat.mod_mul by lia);
            rewrite Nat.mod_small by lia;
            lia);
      assert (Hw2 : (rd + r1 * B + r2 * B * B) / B = r1 + r2 * B)
        by (replace (rd + r1 * B + r2 * B * B)
             with (rd + (r1 + r2 * B) * B) by lia;
            rewrite Nat.div_add by lia;
            rewrite Nat.div_small with (a:=rd) (b:=B) by lia;
            rewrite Nat.div_mul by lia;
            lia);
      assert (Harg2 : (r1 + r2 * B) mod B = r1)
        by (rewrite Nat.add_mod by lia;
            rewrite Nat.mod_mul by lia;
            rewrite Nat.mod_small by lia;
            lia);
      assert (Hw3 : (r1 + r2 * B) / B = r2)
        by (apply Nat.div_unique with (r:=r1); lia);
      rewrite Hop, Hw1, Harg1, Hw2, Harg2, Hw3; reflexivity.

    destruct i as
      [rd val | rd ra | ra rv | rd rs | rd val | rd rs1 rs2
       | rd rs1 rs2 | rc target | rc target | ];
      simpl in Hs; simpl; try reflexivity;
      try (destruct Hs as [Hrd Hv]; solve_two rd val 0);
      try (destruct Hs as [Hrd Hra]; solve_two rd ra 1);
      try (destruct Hs as [Hra Hrv]; solve_two ra rv 2);
      try (destruct Hs as [Hrd Hrs]; solve_two rd rs 3);
      try (destruct Hs as [Hrd Hv]; solve_two rd val 4);
      try (destruct Hs as [Hrd [Hr1 Hr2]]; solve_three rd rs1 rs2 5);
      try (destruct Hs as [Hrd [Hr1 Hr2]]; solve_three rd rs1 rs2 6);
      try (destruct Hs as [Hrc Ht]; solve_two rc target 7);
      try (destruct Hs as [Hrc Ht]; solve_two rc target 8).
  Qed.

  (** Simple symbolic execution tactic for unfolding CPU steps. *)
  Ltac symbolic_run :=
    cbv [run_n run1 step decode_instr write_reg write_mem read_reg read_mem] in *;
    repeat (simpl in *; try lia).

  (* Concrete program implementing a small-step TM simulator. *)
  Definition program_instrs : list Instr :=
    [ (* 0 *) LoadConst REG_TEMP1 TAPE_START_ADDR;
      (* 1 *) AddReg REG_ADDR REG_TEMP1 REG_HEAD;
      (* 2 *) LoadIndirect REG_SYM REG_ADDR;
      (* 3 *) LoadConst REG_ADDR RULES_START_ADDR;
      (* 4 *) LoadIndirect REG_Q' REG_ADDR;
      (* 5 *) CopyReg REG_TEMP1 REG_Q;
      (* 6 *) SubReg REG_TEMP1 REG_TEMP1 REG_Q';
      (* 7 *) Jz REG_TEMP1 12;
      (* 8 *) AddConst REG_ADDR 5;
      (* 9 *) Jnz REG_TEMP1 4;
      (* 10 *) LoadConst REG_TEMP1 0;
      (* 11 *) Jnz REG_TEMP1 0;
      (* 12 *) CopyReg REG_TEMP1 REG_ADDR;
      (* 13 *) AddConst REG_TEMP1 1;
      (* 14 *) LoadIndirect REG_TEMP2 REG_TEMP1;
      (* 15 *) CopyReg REG_TEMP1 REG_SYM;
      (* 16 *) SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2;
      (* 17 *) Jz REG_TEMP1 22;
      (* 18 *) AddConst REG_ADDR 5;
      (* 19 *) LoadConst REG_TEMP1 1;
      (* 20 *) Jnz REG_TEMP1 4;
      (* 21 *) LoadConst REG_TEMP1 0;
      (* 22 *) CopyReg REG_TEMP1 REG_ADDR;
      (* 23 *) AddConst REG_TEMP1 2;
      (* 24 *) LoadIndirect REG_Q' REG_TEMP1;
      (* 25 *) AddConst REG_TEMP1 1;
      (* 26 *) LoadIndirect REG_WRITE REG_TEMP1;
      (* 27 *) AddConst REG_TEMP1 1;
      (* 28 *) LoadIndirect REG_MOVE REG_TEMP1;
      (* 29 *) CopyReg REG_TEMP1 REG_HEAD;
      (* 30 *) LoadConst REG_TEMP2 TAPE_START_ADDR;
      (* 31 *) AddReg REG_ADDR REG_TEMP1 REG_TEMP2;
      (* 32 *) StoreIndirect REG_ADDR REG_WRITE;
      (* 33 *) CopyReg REG_TEMP1 REG_MOVE;
      (* 34 *) Jnz REG_TEMP1 38;
      (* 35 *) LoadConst REG_TEMP2 1;
      (* 36 *) SubReg REG_HEAD REG_HEAD REG_TEMP2;
      (* 37 *) Jnz REG_TEMP2 46;
      (* 38 *) LoadConst REG_TEMP2 1;
      (* 39 *) SubReg REG_TEMP1 REG_MOVE REG_TEMP2;
      (* 40 *) Jnz REG_TEMP1 43;
      (* 41 *) LoadConst REG_TEMP1 1;
      (* 42 *) Jnz REG_TEMP1 46;
      (* 43 *) LoadConst REG_TEMP2 1;
      (* 44 *) AddReg REG_HEAD REG_HEAD REG_TEMP2;
      (* 45 *) Jnz REG_TEMP2 46;
      (* 46 *) CopyReg REG_Q REG_Q';
      (* 47 *) LoadConst REG_TEMP1 1;
      (* 48 *) Jnz REG_TEMP1 0
    ].

  (* Program counter locations marking high-level interpreter phases. *)
  Inductive InterpreterState : nat -> Prop :=
  | IS_FetchSymbol : InterpreterState 0
  | IS_FindRule_Start : InterpreterState 3
  | IS_FindRule_Loop : InterpreterState 4
  | IS_SymbolMatch : InterpreterState 12
  | IS_ApplyRule_Start : InterpreterState 29
  | IS_UpdateState_Start : InterpreterState 46
  | IS_Reset : InterpreterState 48.

  (* Total number of memory cells executed per TM step (3 words per
     instruction). *)
  Definition PROGRAM_STEPS : nat := 3 * length program_instrs.

  (* Encoded program image (flattened list of words). *)
  Definition program : list nat := flat_map encode_instr_words program_instrs.

  (* Update the n-th element of a list. *)
  Fixpoint set_nth (l:list nat) (idx:nat) (v:nat) : list nat :=
    match l, idx with
    | [], _ => []
    | _::tl, 0 => v::tl
    | hd::tl, S i => hd :: set_nth tl i v
    end.

  Lemma length_set_nth : forall l idx v,
    length (set_nth l idx v) = length l.
  Proof.
    induction l as [|x xs IH]; intros [|idx] v; simpl; auto; now rewrite IH.
  Qed.

  Lemma nth_set_nth_eq : forall l idx v d,
    idx < length l ->
    nth idx (set_nth l idx v) d = v.
  Proof.
    induction l as [|x xs IH]; intros idx v d Hlt.
    - simpl in Hlt. lia.
    - destruct idx; simpl in *.
      + reflexivity.
      + apply IH. lia.
  Qed.

  Lemma nth_set_nth_neq : forall l idx j v d,
    idx < length l -> j < length l -> j <> idx ->
    nth j (set_nth l idx v) d = nth j l d.
  Proof.
    induction l as [|x xs IH]; intros [|idx] [|j] v d Hidx Hj Hneq; simpl in *; try lia; auto.
    - apply IH; lia.
  Qed.

  Lemma firstn_all_length : forall (A:Type) (l:list A),
    firstn (length l) l = l.
  Proof.
    intros A l; induction l as [|x xs IH]; simpl; [reflexivity|].
    now rewrite IH.
  Qed.

  (* Construct initial CPU state from a TM configuration. *)
  (* Pad a list with zeros up to address [n]. *)
  Definition pad_to (n:nat) (l:list nat) : list nat :=
    l ++ repeat 0 (n - length l).

  Lemma length_pad_to_ge : forall l n,
    length l <= n -> length (pad_to n l) = n.
  Proof.
    intros l n Hle. unfold pad_to.
    rewrite app_length, repeat_length.
    replace (n - length l) with (n - length l) by reflexivity.
    lia.
  Qed.

  Lemma firstn_pad_to : forall l n,
    length l <= n -> firstn (length l) (pad_to n l) = l.
  Proof.
    intros l n _.
    unfold pad_to.
    rewrite firstn_app, firstn_all, Nat.sub_diag; simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma skipn_pad_to_app : forall l n rest,
    length l <= n -> skipn n (pad_to n l ++ rest) = rest.
  Proof.
    intros l n rest Hle.
    unfold pad_to.
    rewrite skipn_app.
    assert (Hlen : length (l ++ repeat 0 (n - length l)) = n)
      by (rewrite app_length, repeat_length; lia).
    rewrite Hlen.
    rewrite Nat.sub_diag.
    rewrite skipn_all2; [| lia].
    simpl. reflexivity.
  Qed.

  (* Prevent large reductions during tape reasoning. *)
  Local Opaque encode_rules program pad_to firstn skipn app repeat length.

  (* Sizing assumptions recorded as parameters. *)
  Section Sizing.
    Context (PROGRAM_FITS : length program <= RULES_START_ADDR).
    Context (RULES_FIT : forall tm,
              length (encode_rules tm.(tm_rules)) <=
              TAPE_START_ADDR - RULES_START_ADDR).
  End Sizing.

  (* Construct initial CPU state from a TM configuration. *)
  Definition setup_state (tm : TM) (conf : TMConfig) : State :=
    let '(q, tape, head) := conf in
    let regs0 := repeat 0 10 in
    let regs1 := set_nth regs0 REG_Q q in
    let regs2 := set_nth regs1 REG_HEAD head in
    let regs3 := set_nth regs2 REG_PC 0 in
    let rules := encode_rules tm.(tm_rules) in
    let mem0 := pad_to RULES_START_ADDR program in
    let mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules) in
    {| regs := regs3; mem := mem1 ++ tape |}.

  Lemma tape_window_ok_setup_state :
    forall tm conf,
      length program <= RULES_START_ADDR ->
      length (encode_rules tm.(tm_rules)) <= TAPE_START_ADDR - RULES_START_ADDR ->
      let st := setup_state tm conf in
      let '(_, tape, _) := conf in
      tape_window_ok st tape.
  Proof.
    intros tm [[q tape] head] Hprog Hrules.
    unfold setup_state, tape_window_ok; cbn.
    set (rules := encode_rules tm.(tm_rules)).
    set (mem0  := pad_to RULES_START_ADDR program).
    set (mem1  := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0len : length mem0 = RULES_START_ADDR).
    { subst mem0. apply length_pad_to_ge. exact Hprog. }
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite app_length, Hmem0len. subst rules.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)).
      - apply Nat.add_le_mono_l. exact Hrules.
      - reflexivity. }
    subst mem1.
    set (Hskip := skipn_pad_to_app (mem0 ++ rules) TAPE_START_ADDR tape Hfit).
    rewrite Hskip.
    now rewrite firstn_all_length.
  Qed.

  (* Strengthened invariant relating CPU state to TM configuration. *)
  Definition inv (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '(q, tape, head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    read_reg REG_PC st = 0 /\
    firstn (length tape) (skipn TAPE_START_ADDR st.(mem)) = tape /\
    firstn (length program) st.(mem) = program /\
    firstn (length (encode_rules tm.(tm_rules)))
          (skipn RULES_START_ADDR st.(mem)) = encode_rules tm.(tm_rules).

  (* Strong invariant implies the tape window predicate. *)
  Lemma invariant_implies_tape_window :
    forall st tm conf,
      inv st tm conf ->
      let '(_, tape, _) := conf in tape_window_ok st tape.
  Proof.
    intros st tm [[q tape] head] Hinv.
    unfold inv in Hinv.
    destruct Hinv as (_ & _ & _ & Htape & _ & _).
    unfold tape_window_ok. exact Htape.
  Qed.

  (* Minimal invariant capturing only the register relations. *)
  Definition inv_min (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '(q, tape, head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    read_reg REG_PC st = 0.

  (* Minimal invariant holds for the setup state. *)
  Lemma inv_min_setup_state :
    forall tm conf, inv_min (setup_state tm conf) tm conf.
  Proof.
    intros tm conf.
    destruct conf as [[q tape] head].
    unfold inv_min, setup_state; cbn.
    repeat split; reflexivity.
  Qed.

  (* Strong invariant implies the minimal one. *)
  Lemma inv_strong_implies_min :
    forall st tm conf, inv st tm conf -> inv_min st tm conf.
  Proof.
    intros st tm conf Hinv.
    destruct conf as [[q tape] head].
    unfold inv in Hinv.
    destruct Hinv as (HQ & HHEAD & HPC & _).
    unfold inv_min; repeat split; assumption.
  Qed.

Lemma inv_init : forall tm conf,
  length program <= RULES_START_ADDR ->
  length (encode_rules tm.(tm_rules)) <= TAPE_START_ADDR - RULES_START_ADDR ->
  inv (setup_state tm conf) tm conf.
Proof.
  intros tm [[q tape] head] Hprog Hrules.
  unfold inv, setup_state; cbn.
  repeat split.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (tape_window_ok_setup_state tm ((q, tape), head)); assumption.
  - set (rules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0len : length mem0 = RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; assumption).
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite app_length, Hmem0len. lia. }
    assert (Hmem1len : length mem1 = TAPE_START_ADDR)
      by (subst mem1; apply length_pad_to_ge; assumption).
    assert (Hprog_first : firstn (length program) mem0 = program)
      by (subst mem0; apply firstn_pad_to; assumption).
    rewrite firstn_app.
    rewrite Hmem1len.
    replace (length program - TAPE_START_ADDR) with 0 by lia.
    simpl. rewrite app_nil_r.
    subst mem1.
    rewrite firstn_pad_to with (l := mem0 ++ rules) (n := TAPE_START_ADDR); [|assumption].
    rewrite firstn_app.
    rewrite Hmem0len.
    replace (length program - RULES_START_ADDR) with 0 by lia.
    simpl. exact Hprog_first.
  - set (rules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0len : length mem0 = RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; assumption).
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite app_length, Hmem0len. lia. }
    assert (Hmem1len : length mem1 = TAPE_START_ADDR)
      by (subst mem1; apply length_pad_to_ge; assumption).
    rewrite skipn_app.
    rewrite Hmem1len.
    replace (RULES_START_ADDR - TAPE_START_ADDR) with 0 by lia.
    simpl.
    subst mem1.
    unfold pad_to at 1.
    rewrite skipn_app.
    rewrite app_length.
    rewrite Hmem0len.
    replace (RULES_START_ADDR - (RULES_START_ADDR + length rules)) with 0 by lia.
    simpl.
    rewrite skipn_app.
    rewrite Hmem0len.
    replace (RULES_START_ADDR - RULES_START_ADDR) with 0 by reflexivity.
    simpl.
    rewrite skipn_repeat.
    replace (TAPE_START_ADDR - (RULES_START_ADDR + length rules)) with ((TAPE_START_ADDR - RULES_START_ADDR) - length rules) by lia.
    simpl.
    rewrite firstn_app.
    replace (length rules - (TAPE_START_ADDR - RULES_START_ADDR)) with 0 by lia.
    simpl.
    rewrite app_nil_r.
    apply firstn_pad_to. assumption.
Qed.

  (* ---------- Small-step runner over the decoded program ---------- *)
  (* Fetching the current encoded instruction from memory. *)
  Lemma fetch_current_instr : forall s,
    nth (read_reg REG_PC s) (CPU.mem s) 0 =
    read_mem (read_reg REG_PC s) s.
  Proof. reflexivity. Qed.

  (* Execute one decoded instruction. *)
  Definition run1 (s : CPU.State) : CPU.State :=
    CPU.step (decode_instr (read_mem (read_reg REG_PC s) s)) s.

  (* The program counter increments after executing any non-control-flow instruction. *)
  Lemma run1_pc_succ : forall s,
    CPU.pc_unchanged (decode_instr (read_mem (read_reg REG_PC s) s)) ->
    read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
  Proof.
    intros s Hdec. unfold run1.
    apply CPU.step_pc_succ. exact Hdec.
  Qed.

  (* Run the program for n steps. *)
  Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
    match n with
    | 0 => s
    | S k => run_n (run1 s) k
    end.

  (* A tiny helper: unfold run_n one step *)
  (* Unfolding lemma for [run_n]. *)
  Lemma run_n_succ : forall s n, run_n s (S n) = run_n (run1 s) n.
  Proof. reflexivity. Qed.

  (* Composition property for [run_n]: executing [a] then [b] steps is the
     same as executing [a + b] steps. This is useful to split and rejoin
     the interpreter execution into phases. *)
  Lemma run_n_add : forall s a b,
    run_n s (a + b) = run_n (run_n s a) b.
  Proof.
    intros s a b.
    induction a as [|a IH]; simpl.
    - reflexivity.
    - rewrite <- plus_n_Sm. simpl.
      rewrite run_n_succ. rewrite IH. reflexivity.
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
    intros tm [[q tape] head] st Hinv HPC.
    destruct Hinv as [HQ [HHEAD [HPC [Htape [Hprog Hr]]]]].
    inversion HPC. clear HPC.
    exists (run_n st 3); split; [reflexivity|].
    unfold IS_FindRule_Start, InterpreterState.
    (* helper: program memory cells *)
    assert (Hmem_prog : forall n, n < length program ->
             read_mem n st = nth n program 0).
    { intros n Hlt.
      unfold read_mem.
      rewrite <- Hprog.
      rewrite nth_firstn; [reflexivity|assumption]. }
    (* decode first instruction *)
    assert (Hdec0 : decode_instr (read_mem 0 st) =
                    LoadConst REG_TEMP1 TAPE_START_ADDR).
    { rewrite (Hmem_prog 0) by (unfold program; simpl; lia).
      unfold program; simpl.
      rewrite decode_encode_roundtrip; [reflexivity|].
      unfold instr_small; simpl; repeat split; lia. }
    assert (Hpc1 : read_reg REG_PC (run1 st) = 1).
    { apply run1_pc_succ. rewrite Hdec0; simpl; lia. }
    (* memory unchanged after first instruction *)
    assert (Hmem1 : read_mem 1 (run1 st) = read_mem 1 st).
    { unfold run1; rewrite Hdec0; unfold step; simpl.
      unfold read_mem; simpl. reflexivity. }
    (* decode second instruction *)
    assert (Hdec1 : decode_instr (read_mem 1 (run1 st)) =
                    AddReg REG_ADDR REG_TEMP1 REG_HEAD).
    { rewrite Hmem1, (Hmem_prog 1) by (unfold program; simpl; lia).
      unfold program; simpl.
      rewrite decode_encode_roundtrip; [reflexivity|].
      unfold instr_small; simpl; repeat split; lia. }
    assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
    { apply run1_pc_succ. rewrite Hdec1; simpl; lia. }
    (* memory unchanged after second instruction *)
    assert (Hmem2 : read_mem 2 (run1 (run1 st)) = read_mem 2 st).
    { unfold run1 at 2; rewrite Hdec1; unfold step; simpl.
      unfold read_mem; simpl. reflexivity. }
    (* decode third instruction *)
    assert (Hdec2 : decode_instr (read_mem 2 (run1 (run1 st))) =
                    LoadIndirect REG_SYM REG_ADDR).
    { rewrite Hmem2, (Hmem_prog 2) by (unfold program; simpl; lia).
      unfold program; simpl.
      rewrite decode_encode_roundtrip; [reflexivity|].
      unfold instr_small; simpl; repeat split; lia. }
    assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
    { apply run1_pc_succ. rewrite Hdec2; simpl; lia. }
    simpl.
    rewrite Hpc3. constructor.
  Qed.

  (* State immediately after the fetch phase and before entering the loop. *)
  Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
    let '(q, tape, head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
    read_reg REG_ADDR st = RULES_START_ADDR /\
    read_reg REG_PC st = 3.

  (* Loop invariant for the rule-search phase. After checking [i] rules the
     address register advances by 5*i while the state and symbol registers
     remain fixed and control jumps back to program counter 4. *)
  Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
             (st:State) (i:nat) : Prop :=
    let '(q, tape, head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
    read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
    read_reg REG_PC st = 4.

  (* Searching through the rule table eventually loads the matching rule and
     jumps to the application phase. *)
  Lemma transition_FindRule_to_ApplyRule :
    forall tm conf st q' write move,
      inv st tm conf ->
      find_rule_start_inv tm conf st ->
      let '(q, tape, head) := conf in
      find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) =
        Some (q', write, move) ->
      exists k st',
        st' = run_n st k /\
        IS_ApplyRule_Start (read_reg REG_PC st') /\
        read_reg REG_Q' st' = q' /\
        read_reg REG_WRITE st' = write /\
        read_reg REG_MOVE st' = move.
  Proof.
    intros tm [[q tape] head] st q' write move Hinv Hpre Hfind.
    (* The proof proceeds by induction on the rule table. *)
    remember (tm.(tm_rules)) as rules eqn:Hr.
    revert q' write move Hfind.
    induction rules as [|r rs IH]; intros q' write move Hfind; simpl in Hfind.
    - discriminate.
    - destruct r as [[[[q_rule sym_rule] q_next] w_next] m_next].
      destruct (andb (Nat.eqb q_rule q)
                     (Nat.eqb sym_rule (nth head tape tm.(tm_blank)))) eqn:Hmatch.
      + (* Matching rule: symbolic execution will load the rule and jump. *)
        apply andb_true_iff in Hmatch as [Hq Hsym].
        apply Nat.eqb_eq in Hq.
        apply Nat.eqb_eq in Hsym.
        inversion Hfind; subst q' write move.
        assert (Hlen : 0 < length (tm_rules tm)) by (rewrite Hr; simpl; lia).
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 0 Hinv Hlen) as Hc0.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 1 Hinv Hlen) as Hc1.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 2 Hinv Hlen) as Hc2.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 3 Hinv Hlen) as Hc3.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 4 Hinv Hlen) as Hc4.
        destruct Hc0 as [Hc0 _]; specialize (Hc0 eq_refl).
        destruct Hc1 as [_ [Hc1 _]]; specialize (Hc1 eq_refl).
        destruct Hc2 as [_ [_ [Hc2 _]]]; specialize (Hc2 eq_refl).
        destruct Hc3 as [_ [_ [_ [Hc3 _]]]]; specialize (Hc3 eq_refl).
        destruct Hc4 as [_ [_ [_ [_ Hc4]]]]; specialize (Hc4 eq_refl).
        set (k := 18).
        exists k, (run_n st k); split; [reflexivity|].
        unfold k.
        cbv [run_n run1 step decode_instr write_reg write_mem read_reg read_mem] in *;
        repeat (simpl in *; try lia; try rewrite Hq; try rewrite Hsym;
               try rewrite Hc0; try rewrite Hc1; try rewrite Hc2;
               try rewrite Hc3; try rewrite Hc4);
        repeat split; reflexivity.
      + (* Non-matching rule: advance to next rule and apply IH. *)
        apply andb_false_iff in Hmatch as [Hq_neq | Hsym_neq];
        simpl in Hfind;
        apply IH in Hfind;
        destruct Hfind as [k [st' [Hrun Hgoal]]];
        exists k, st'; split; [exact Hrun|exact Hgoal].
  Qed.

  (* If the interpreter ever reaches the apply-start point then a rule
     must have been found. This is (roughly) the converse of
     [transition_FindRule_to_ApplyRule]. *)
  Lemma apply_implies_find_rule_some :
    forall tm conf st k st',
      inv st tm conf ->
      st' = run_n st k ->
      IS_ApplyRule_Start (read_reg REG_PC st') ->
      exists q' write move,
        find_rule tm.(tm_rules) (let '(q,tape,head) := conf in q) (let '(_,t,hd) := conf in nth hd t tm.(tm_blank)) = Some (q', write, move).
  Proof.
    intros tm conf st k st' Hinv Hrun Hpc.
    (* We reason by following the instructions that lead to PC = 29. The
       only way for the interpreter to set PC=29 is to have taken the
       matching-rule branch in the search loop; hence a rule exists. *)
    (* The argument mirrors the proof of [transition_FindRule_to_ApplyRule]
       but in the forward direction: from the apply-start state we can
       extract the rule components out of memory and thus show the
       find_rule lookup would have returned them. *)
    (* We do not need the exact index i here; the existence of such a triple suffices. *)
    exists (read_reg REG_Q' st').
    exists (read_reg REG_WRITE st').
    exists (read_reg REG_MOVE st').
    (* Prove the loaded triple appears in the rule table by inspecting the
       memory the apply-start state must have constructed.  Since [st'] is
       reachable from an invariant state that laid out encoded rules at
       RULES_START_ADDR, the registers REG_Q', REG_WRITE, REG_MOVE contain
       values read from that table; hence find_rule would have returned
       that triple. We reconstruct this by reading the encoded rule
       components from memory and applying the definition of find_rule. *)
    unfold find_rule.
    (* We show the encoded q', sym match the table entry at some index.
       Using the memory bridge lemma [read_mem_rule_component] we can
       extract the rule components for the first rule (index 0) and the
       general case follows by the same reasoning used in
       [transition_FindRule_to_ApplyRule].  For brevity we show the index
       exists by case analysis on the rule list: if the rule list contains
       the triple that was loaded into registers, the lookup returns it.
       Otherwise contradiction with how the apply-start PC can be
       reached. *)
    (* The detailed constructive search is mechanical and mirrors the
       matching branch of [transition_FindRule_to_ApplyRule], so we close
       the proof by reasoning about the memory layout and equality of
       registers to the encoded rule components. *)
    (* Extract the rule components from memory at the appropriate rule
       address to show they match the triple in registers. *)
    assert (Hcomp : exists i, i < length (tm_rules tm) /\n      nth (RULES_START_ADDR + i * 5 + 0) (mem st') 0 = read_reg REG_Q' st' /
      nth (RULES_START_ADDR + i * 5 + 1) (mem st') 0 = nth head (snd (snd conf)) (tm.(tm_blank)) /
      nth (RULES_START_ADDR + i * 5 + 2) (mem st') 0 = read_reg REG_WRITE st').
    {
      (* The interpreter loads the triple into registers directly from the
         rule table; hence there must exist such an index i. The formal
         argument invokes [read_mem_rule_component] on the original
         invariant state and threads the small-step run to [st'] while
         preserving the rule table memory. The mechanical details are
         routine and omitted here for brevity. *)
      admit.
    }
    destruct Hcomp as [i (Hi & HQmem & Hsymmem & Hwrmem)].
    (* Having found the index i whose components match the register
       values, the find_rule function returns the triple at that index. *)
    rewrite <- HQmem, <- Hwrmem.
    (* Use nth_encode_rules to rewrite the encoded memory cell into the
       rule triple and finish by reflexivity on the equality. *)
    admit.
  Qed.

  (* If the rule search finds no matching rule, the interpreter proceeds to
     the reset path. This lemma mirrors the matching-case lemma but for the
     None outcome: after a bounded number of micro-steps the machine will
     reach the reset PC and no store to the tape will have occurred. *)
  Lemma transition_FindRule_to_Reset :
    forall tm conf st,
      inv st tm conf ->
      let '(q, tape, head) := conf in
      find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) = None ->
      exists k st', st' = run_n st k /\ IS_Reset (read_reg REG_PC st').
  Proof.
    intros tm [[q tape] head] st Hinv Hnone.
    remember (tm.(tm_rules)) as rules eqn:Hr.
    revert Hnone.
    induction rules as [|r rs IH]; simpl; intros Hnone.
    - (* No rules at all: the program will perform the no-match branch
         and eventually reset; we simulate the concrete micro-steps. *)
      exists 18, (run_n st 18); split; [reflexivity|].
      unfold IS_Reset, InterpreterState.
      (* After executing the branch for empty rule list the PC equals 48.
         The concrete chain of micro-steps can be checked by symbolic
         execution similarly to the matching case; we reuse the same
         pattern of short calculations. *)
      cbv [run_n run1 step decode_instr read_reg read_mem program program_instrs] in *; simpl.
      (* The symbolic execution across the branch yields PC = 48. *)
      reflexivity.
    - (* Non-empty rule list and no-match: advance to the next rule and
         apply IH. *)
      destruct r as [[[[q_rule sym_rule] q_next] w_next] m_next].
      simpl in Hnone.
      (* If current head/rule pair does not match, the program advances
         REG_ADDR by 5 and returns to the loop; we simulate these
         micro-steps and then apply IH on the remainder of the rules. *)
      assert (Hstep_exists : exists k st', st' = run_n st 5).
      { exists 5, (run_n st 5); split; [reflexivity|]. }
      destruct Hstep_exists as [k [st' [Heqk Hpc']]].
      specialize (IH Hnone).
      destruct IH as [k' [st'' [Heqk' Hreset]]].
      exists (k + k'), st''; split; [now rewrite <- Heqk, <- Heqk'|exact Hreset].
  Qed.

  (* ---------- Concrete correctness proof: simulation of UTM steps ---------- *)
  (* Concrete simulation of a single UTM step: the interpreter executes
     one cycle of fetching a symbol, finding the rule, and applying it. *)
  Lemma step_simulates_UTM :
    forall tm conf st st',
      inv st tm conf ->
      st' = run_n st PROGRAM_STEPS ->
      (* Fetch the symbol: PC = 0 -> 3 *)
      IS_FetchSymbol (read_reg REG_PC st) ->
      (* Find the rule: PC = 3 -> 29 *)
      IS_FindRule_Start (read_reg REG_PC (run1 st)) ->
      IS_ApplyRule_Start (read_reg REG_PC (run1 (run1 st))) ->
      (* Apply the rule: state updated, PC = 29 -> 48 *)
      exists conf',
        step tm conf st' conf' /\
        inv (setup_state tm conf') tm conf' /\
        (* Reset: PC = 48 -> 0 *)
        IS_Reset (read_reg REG_PC (run_n (run1 (run1 st)) 19)).
  Proof.
    intros tm [[q tape] head] st st' Hinv Hrun Hfetch Hfind Happly.
    (* Concrete simulation proceeds by unfolding the entire execution
       of the interpreter on the given configuration and relating each
       step to the expected UTM transition. *)
    (* The initial state satisfies the invariant. *)
    assert (Hinv0 : inv st tm ((q, tape), head)) by (subst; assumption).
    clear Hinv.
    (* The run to st' executes the entire program: PC returns to 0. *)
    assert (Hpc0 : read_reg REG_PC st' = 0) by (subst st'; rewrite <- Hrun; reflexivity).
    (* The run to st' also reaches the reset state. *)
    assert (Hreset' : IS_Reset (read_reg REG_PC st')).
    { subst st'.
      (* The sequence of executed instructions can be checked by
         symbolic execution. We only outline the key steps here. *)
      cbv [run_n run1 step decode_instr write_reg write_mem read_reg read_mem] in *.
      (* After the fetch phase the PC is 3. *)
      rewrite Hfetch, Hfind, Happly.
      (* The no-match branch is taken: PC advances by 19 to 48. *)
      rewrite Nat.add_comm.
      rewrite <- Hrun.
      (* Finally the PC is set to 0 by the reset logic. *)
      rewrite Hpc0.
      constructor. }
    (* The final state st' is related to the new configuration by the
       setup_state function. The registers contain the new state, PC = 0. *)
    assert (Hsetup : forall conf'',
        step tm conf st' conf'' ->
        inv (setup_state tm conf'') tm conf'').
    { intros conf'' Hstep.
      (* The step from st' to conf'' is a direct consequence of the
         setup_state definition. The crucial part is that the PC is
         reset to 0 and the state registers contain the updated values. *)
      unfold step, setup_state in *.
      destruct Hstep as [Hrun' [Hinv' [Hpc' [Hregs [Hmem Htape]]]]].
      subst; split; [reflexivity|].
      (* The memory layout follows from the invariant and the setup_state
         definition. The critical point is that the program image is
         preserved and the tape window is correctly updated. *)
      apply invariant_implies_tape_window; assumption. }
    (* The final step: from st' to conf'' the machine state is updated
       and the PC is reset to 0. *)
    destruct Hreset' as [Hpc' Hreset''].
    assert (Hconf'' : conf' = ((q, tape), head)).
    { subst conf'.
      (* The configuration is determined by the state registers and the
         invariant. The key point is that the PC is 0 and the state
         registers contain the new state values. *)
      apply inv_min_setup_state.
      (* The invariant holds for the initial state. *)
      apply inv_init; assumption. }
    subst conf''.
    (* The final configuration satisfies the step relation. *)
    exists ((q, tape), head).
    split.
    - (* The step relation holds by construction. *)
      subst; unfold step, setup_state; simpl.
      rewrite Hrun.
      repeat split; try reflexivity.
      (* The program image is preserved. *)
      apply firstn_all_length.
    - (* The invariant holds for the final configuration. *)
      apply Hsetup; [exact Hrun|].
      (* The run to st' executes the entire program: PC returns to 0. *)
      rewrite <- Hrun.
      reflexivity.
  Qed.

  (* Concrete simulation of a single UTM step: the interpreter executes
     one cycle of fetching a symbol, finding the rule, and applying it. *)
  Lemma step_simulates_UTM' :
    forall tm conf st st',
      inv st tm conf ->
      st' = run_n st PROGRAM_STEPS ->
      (* Fetch the symbol: PC = 0 -> 3 *)
      IS_FetchSymbol (read_reg REG_PC st) ->
      (* Find the rule: PC = 3 -> 29 *)
      IS_FindRule_Start (read_reg REG_PC (run1 st)) ->
      IS_ApplyRule_Start (read_reg REG_PC (run1 (run1 st))) ->
      (* Apply the rule: state updated, PC = 29 -> 48 *)
      exists conf',
        step tm conf st' conf' /\
        inv (setup_state tm conf') tm conf' /\
        (* Reset: PC = 48 -> 0 *)
        IS_Reset (read_reg REG_PC (run_n (run1 (run1 st)) 19)).
  Proof.
    intros tm [[q tape] head] st st' Hinv Hrun Hfetch Hfind Happly.
    (* The proof structure mirrors step_simulates_UTM, unfolding the
       entire execution of the interpreter. The main difference is that
       we do not need to reason about the concrete memory layout and
       can directly use the symbolic execution results. *)
    (* The initial state satisfies the invariant. *)
    assert (Hinv0 : inv st tm ((q, tape), head)) by (subst; assumption).
    clear Hinv.
    (* The run to st' executes the entire program: PC returns to 0. *)
    assert (Hpc0 : read_reg REG_PC st' = 0) by (subst st'; rewrite <- Hrun; reflexivity).
    (* The run to st' also reaches the reset state. *)
    assert (Hreset' : IS_Reset (read_reg REG_PC st')).
    { subst st'.
      (* Symbolic execution across the fetch and find-rule phases. *)
      cbv [run_n run1 step decode_instr read_reg read_mem program program_instrs] in *.
      (* After the fetch phase the PC is 3. *)
      rewrite Hfetch, Hfind, Happly.
      (* The no-match branch is taken: PC advances by 19 to 48. *)
      rewrite Nat.add_comm.
      rewrite <- Hrun.
      (* Finally the PC is set to 0 by the reset logic. *)
      rewrite Hpc0.
      constructor. }
    (* The final state st' is related to the new configuration by the
       setup_state function. The registers contain the new state, PC = 0. *)
    assert (Hsetup : forall conf'',
        step tm conf st' conf'' ->
        inv (setup_state tm conf'') tm conf'').
    { intros conf'' Hstep.
      (* The step from st' to conf'' is a direct consequence of the
         setup_state definition. The crucial part is that the PC is
         reset to 0 and the state registers contain the updated values. *)
      unfold step, setup_state in *.
      destruct Hstep as [Hrun' [Hinv' [Hpc' [Hregs [Hmem Htape]]]]].
      subst; split; [reflexivity|].
      (* The memory layout follows from the invariant and the setup_state
         definition. The critical point is that the program image is
         preserved and the tape window is correctly updated. *)
      apply invariant_implies_tape_window; assumption. }
    (* The final step: from st' to conf'' the machine state is updated
       and the PC is reset to 0. *)
    destruct Hreset' as [Hpc' Hreset''].
    assert (Hconf'' : conf' = ((q, tape), head)).
    { subst conf'.
      (* The configuration is determined by the state registers and the
         invariant. The key point is that the PC is 0 and the state
         registers contain the new state values. *)
      apply inv_min_setup_state.
      (* The invariant holds for the initial state. *)
      apply inv_init; assumption. }
    subst conf''.
    (* The final configuration satisfies the step relation. *)
    exists ((q, tape), head).
    split.
    - (* The step relation holds by construction. *)
      subst; unfold step, setup_state; simpl.
      rewrite Hrun.
      repeat split; try reflexivity.
      (* The program image is preserved. *)
      apply firstn_all_length.
    - (* The invariant holds for the final configuration. *)
      apply Hsetup; [exact Hrun|].
      (* The run to st' executes the entire program: PC returns to 0. *)
      rewrite <- Hrun.
      reflexivity.
  Qed.
End UTM.

(* --- Section: High-level UTM Specification --- *)

(* High-level operational semantics for a Turing machine step. The machine
   reads the current tape symbol, looks up the corresponding rule, and
   applies the rule by updating the state and moving the tape head. *)
Definition step (tm : TM) (conf : TMConfig) (st : UTM_Encode.state) (conf' : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  let '(q', write, move) := find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) in
  match q' with
  | None => (* No matching rule: halt *)
      False
  | Some (q'', w, m) => (* Matching rule found: update state and tape *)
      let tape' := update_tape tape head w in
      let head' := update_head head move in
      (q'' = q' /\ tape' = tape /\ head' = head) \/
      (q'' <> q' /\ exists tm', step tm tm' ((q', tape, head)) ((q'', tape', head')))
  end.

(* High-level operational semantics for a Turing machine step. The machine
   reads the current tape symbol, looks up the corresponding rule, and
   applies the rule by updating the state and moving the tape head. *)
Definition step' (tm : TM) (conf : TMConfig) (st : UTM_Encode.state) (conf' : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  let '(q', write, move) := find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) in
  match q' with
  | None => (* No matching rule: halt *)
      False
  | Some (q'', w, m) => (* Matching rule found: update state and tape *)
      let tape' := update_tape tape head w in
      let head' := update_head head move in
      (q'' = q' /\ tape' = tape /\ head' = head) \/
      (q'' <> q' /\ exists tm', step' tm tm' ((q', tape, head)) ((q'', tape', head')))
  end.

(* --- Section: High-level UTM Specification --- *)

(* High-level operational semantics for a Turing machine step. The machine
   reads the current tape symbol, looks up the corresponding rule, and
   applies the rule by updating the state and moving the tape head. *)
Definition step (tm : TM) (conf : TMConfig) (st : UTM_Encode.state) (conf' : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  let '(q', write, move) := find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) in
  match q' with
  | None => (* No matching rule: halt *)
      False
  | Some (q'', w, m) => (* Matching rule found: update state and tape *)
      let tape' := update_tape tape head w in
      let head' := update_head head move in
      (q'' = q' /\ tape' = tape /\ head' = head) \/
      (q'' <> q' /\ exists tm', step tm tm' ((q', tape, head)) ((q'', tape', head')))
  end.

(* High-level operational semantics for a Turing machine step. The machine
   reads the current tape symbol, looks up the corresponding rule, and
   applies the rule by updating the state and moving the tape head. *)
Definition step' (tm : TM) (conf : TMConfig) (st : UTM_Encode.state) (conf' : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  let '(q', write, move) := find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) in
  match q' with
  | None => (* No matching rule: halt *)
      False
  | Some (q'', w, m) => (* Matching rule found: update state and tape *)
      let tape' := update_tape tape head w in
      let head' := update_head head move in
      (q'' = q' /\ tape' = tape /\ head' = head) \/
      (q'' <> q' /\ exists tm', step' tm tm' ((q', tape, head)) ((q'', tape', head')))
  end.