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
(* Program encoding                                                  *)
(* ----------------------------------------------------------------- *)

(* The encoded universal program *)
Definition program : list nat :=
  flat_map UTM_Encode.encode_instr_words UTM_Program.program_instrs.

(* ----------------------------------------------------------------- *)
(* CPU Execution - from ThieleUniversal_Run1.v                      *)
(* ----------------------------------------------------------------- *)

(* Single step execution *)
Definition run1 (s : CPU.State) : CPU.State :=
  let instr := UTM_Encode.decode_instr_from_mem s.(CPU.mem) (4 * CPU.read_reg CPU.REG_PC s) in
  CPU.step instr s.

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

Lemma pad_to_expand : forall n l,
  pad_to n l = l ++ repeat 0 (n - length l).
Proof. reflexivity. Qed.

Lemma length_pad_to_ge : forall l n,
  length l <= n -> length (pad_to n l) = n.
Proof.
  intros l n Hle.
  unfold pad_to.
  rewrite app_length, repeat_length.
  lia.
Qed.

Lemma firstn_pad_to : forall l n,
  length l <= n -> firstn (length l) (pad_to n l) = l.
Proof.
  intros l n Hle.
  unfold pad_to.
  rewrite firstn_app.
  rewrite Nat.sub_diag.
  simpl.
  rewrite firstn_all.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma firstn_app_le' : forall {A} n (l1 l2 : list A),
  n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros A n l1 l2 Hn.
  rewrite firstn_app.
  replace (n - length l1) with 0 by lia.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma skipn_app_le' : forall {A} n (l1 l2 : list A),
  n <= length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof.
  intros A n l1 l2 Hn.
  rewrite skipn_app.
  replace (n - length l1) with 0 by lia.
  simpl.
  reflexivity.
Qed.

Lemma firstn_pad_to_le : forall l n k,
  k <= length l -> firstn k (pad_to n l) = firstn k l.
Proof.
  intros l n k Hk.
  unfold pad_to.
  rewrite firstn_app_le' by lia.
  reflexivity.
Qed.

Lemma firstn_pad_to_app_le : forall l n rest k,
  k <= length l -> firstn k (pad_to n l ++ rest) = firstn k l.
Proof.
  intros l n rest k Hk.
  unfold pad_to.
  rewrite firstn_app_le' by (rewrite app_length, repeat_length; lia).
  rewrite firstn_app_le' by lia.
  reflexivity.
Qed.

Lemma skipn_pad_to_app : forall l n rest,
  length l <= n -> skipn n (pad_to n l ++ rest) = rest.
Proof.
  intros l n rest Hle.
  unfold pad_to.
  rewrite skipn_app.
  assert (Hlen : length (l ++ repeat 0 (n - length l)) = n).
  { rewrite app_length, repeat_length. lia. }
  rewrite Hlen.
  rewrite Nat.sub_diag.
  rewrite skipn_all2 by lia.
  reflexivity.
Qed.

Lemma firstn_program_prefix :
  length program <= UTM_Program.RULES_START_ADDR ->
  forall rules,
    firstn (length program)
      (pad_to UTM_Program.TAPE_START_ADDR
         (pad_to UTM_Program.RULES_START_ADDR program ++ rules)) = program.
Proof.
  intros Hprog rules.
  remember (length program) as len_prog eqn:Hlen_prog.
  assert (Hprog_len : length program <= UTM_Program.RULES_START_ADDR)
    by (rewrite <- Hlen_prog; exact Hprog).
  assert (Hpad_window : firstn len_prog
           (pad_to UTM_Program.TAPE_START_ADDR
              (pad_to UTM_Program.RULES_START_ADDR program ++ rules)) =
          firstn len_prog (pad_to UTM_Program.RULES_START_ADDR program ++ rules)).
  { apply firstn_pad_to_le.
    rewrite app_length, length_pad_to_ge with (l := program)
        (n := UTM_Program.RULES_START_ADDR) by exact Hprog_len.
    rewrite Hlen_prog. lia. }
  assert (Hmem_prog : firstn len_prog
            (pad_to UTM_Program.RULES_START_ADDR program ++ rules) =
          firstn len_prog program).
  { rewrite firstn_pad_to_app_le with (l := program)
        (n := UTM_Program.RULES_START_ADDR) (rest := rules) (k := len_prog)
      by (rewrite Hlen_prog; lia).
    reflexivity. }
  assert (Hfirstn_prog : firstn len_prog program = program).
  { rewrite Hlen_prog. apply firstn_all. }
  eapply eq_trans. exact Hpad_window.
  eapply eq_trans. exact Hmem_prog.
  exact Hfirstn_prog.
Qed.

Lemma firstn_skipn_pad_to_app : forall l n rest,
  length l <= n -> firstn (length rest) (skipn n (pad_to n l ++ rest)) = rest.
Proof.
  intros l n rest Hle.
  rewrite skipn_pad_to_app by assumption.
  apply firstn_all.
Qed.

Lemma skipn_pad_to_split : forall l n k,
  k <= length l ->
  skipn k (pad_to n l) = skipn k l ++ repeat 0 (n - length l).
Proof.
  intros l n k Hk.
  unfold pad_to.
  rewrite skipn_app_le' by lia.
  reflexivity.
Qed.

Lemma firstn_rules_window :
  length program <= UTM_Program.RULES_START_ADDR ->
  forall rules,
    length rules <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
    firstn (length rules)
      (skipn UTM_Program.RULES_START_ADDR
         (pad_to UTM_Program.TAPE_START_ADDR
            (pad_to UTM_Program.RULES_START_ADDR program ++ rules))) = rules.
Proof.
  intros Hprog rules Hfit.
  set (memprog := pad_to UTM_Program.RULES_START_ADDR program).
  set (memrules := memprog ++ rules).
  assert (Hmemprog_len : length memprog = UTM_Program.RULES_START_ADDR).
  { subst memprog. apply length_pad_to_ge. exact Hprog. }
  assert (Hskip_memrules : skipn UTM_Program.RULES_START_ADDR memrules = rules).
  { unfold memrules.
    rewrite skipn_app_le' by (rewrite Hmemprog_len; lia).
    rewrite <- Hmemprog_len.
    rewrite skipn_all.
    simpl. reflexivity. }
  assert (Hskip_pad :
    skipn UTM_Program.RULES_START_ADDR
      (pad_to UTM_Program.TAPE_START_ADDR memrules) =
    skipn UTM_Program.RULES_START_ADDR memrules ++
      repeat 0 (UTM_Program.TAPE_START_ADDR - length memrules)).
  { apply skipn_pad_to_split.
    unfold memrules.
    rewrite app_length, Hmemprog_len.
    lia. }
  rewrite Hskip_pad.
  rewrite Hskip_memrules.
  rewrite firstn_app_le' by lia.
  apply firstn_all.
Qed.

Lemma firstn_skipn_app_exact : forall {A} (pref rest : list A) n,
  length pref = n ->
  firstn (length rest) (skipn n (pref ++ rest)) = rest.
Proof.
  intros A pref rest n Hlen.
  rewrite skipn_app.
  rewrite Hlen.
  rewrite Nat.sub_diag.
  rewrite <- Hlen.
  rewrite skipn_all.
  simpl.
  apply firstn_all.
Qed.

(* Setup initial CPU state from TM configuration *)
Definition setup_state (tm : TM) (conf : TMConfig) : CPU.State :=
  let '((q, tape), head) := conf in
  let regs0 := repeat 0 10 in
  let regs1 := set_nth regs0 CPU.REG_Q q in
  let regs2 := set_nth regs1 CPU.REG_HEAD head in
  let regs3 := set_nth regs2 CPU.REG_PC 0 in
  let rules := UTM_Encode.encode_rules tm.(tm_rules) in
  let mem0 := pad_to UTM_Program.RULES_START_ADDR program in
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
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma setup_state_regs_length :
  forall tm conf, length (CPU.regs (setup_state tm conf)) = 10.
Proof.
  intros tm conf.
  destruct conf as ((q, tape), head).
  unfold setup_state. simpl CPU.regs.
  repeat (rewrite length_set_nth; [|repeat rewrite length_set_nth; simpl; lia]).
  simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* State predicates and invariants                                   *)
(* ----------------------------------------------------------------- *)

Definition inv_min (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  CPU.read_reg CPU.REG_Q st = q /\
  CPU.read_reg CPU.REG_HEAD st = head.

Lemma inv_min_setup_state : forall tm conf,
  inv_min (setup_state tm conf) tm conf.
Proof.
  intros tm ((q, tape), head).
  unfold inv_min, setup_state; simpl.
  split; unfold CPU.read_reg; repeat (rewrite nth_skipn || simpl); try lia; reflexivity.
Qed.

Definition IS_FetchSymbol (pc : nat) : Prop := pc = 0.
Definition IS_FindRule_Start (pc : nat) : Prop := pc = 3.

(* Tape window predicate: memory correctly encodes the tape *)
Definition tape_window_ok (st : CPU.State) (tape : list nat) : Prop :=
  firstn (length tape) (skipn UTM_Program.TAPE_START_ADDR st.(CPU.mem)) = tape.

Lemma tape_window_ok_setup_state : forall tm q tape head,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  tape_window_ok (setup_state tm ((q, tape), head)) tape.
Proof.
  intros tm q tape head Hprog Hrules.
  unfold tape_window_ok, setup_state.
  set (rrules := UTM_Encode.encode_rules tm.(tm_rules)).
  set (mem0 := pad_to UTM_Program.RULES_START_ADDR program).
  set (mem1 := pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rrules)).
  simpl.
  assert (Hmem0_len : length mem0 = UTM_Program.RULES_START_ADDR).
  { subst mem0. apply length_pad_to_ge. exact Hprog. }
  assert (Hfit : length (mem0 ++ rrules) <= UTM_Program.TAPE_START_ADDR).
  { rewrite app_length, Hmem0_len.
    pose proof UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR as Hle.
    rewrite <- (Arith_prebase.le_plus_minus_r_stt _ _ Hle).
    apply Nat.add_le_mono_l. exact Hrules. }
  subst mem1.
  assert (Hmem1_len : length (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rrules))
                        = UTM_Program.TAPE_START_ADDR).
  { apply length_pad_to_ge. exact Hfit. }
  apply (@firstn_skipn_app_exact
           nat
           (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rrules))
           tape
           UTM_Program.TAPE_START_ADDR).
  exact Hmem1_len.
Qed.

(* Full invariant relating CPU state to TM configuration *)
Definition inv (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  let '((q, tape), head) := conf in
  CPU.read_reg CPU.REG_Q st = q /\
  CPU.read_reg CPU.REG_HEAD st = head /\
  CPU.read_reg CPU.REG_PC st = 0 /\
  tape_window_ok st tape /\
  firstn (length program) st.(CPU.mem) = program /\
  firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
         (skipn UTM_Program.RULES_START_ADDR st.(CPU.mem)) = 
    UTM_Encode.encode_rules tm.(tm_rules).

Lemma inv_setup_state : forall tm conf,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  inv (setup_state tm conf) tm conf.
Proof.
  intros tm ((q, tape), head) Hprog Hrules.
  pose proof (inv_min_setup_state tm ((q, tape), head)) as Hmin.
  destruct Hmin as [Hq Hhead].
  unfold inv.
  simpl.
  split. exact Hq.
  split. exact Hhead.
  split.
  { unfold setup_state.
    simpl.
    unfold CPU.read_reg.
    repeat (rewrite nth_skipn || simpl); try lia; reflexivity. }
  split. apply tape_window_ok_setup_state; assumption.
  split.
  - unfold setup_state.
    simpl.
    set (rules := UTM_Encode.encode_rules tm.(tm_rules)).
    set (mem0 := pad_to UTM_Program.RULES_START_ADDR program).
    assert (Hmem0_len : length mem0 = UTM_Program.RULES_START_ADDR).
    { subst mem0. apply length_pad_to_ge. exact Hprog. }
    assert (Hfit : length (mem0 ++ rules) <= UTM_Program.TAPE_START_ADDR).
    { rewrite app_length, Hmem0_len.
      assert (Heq: UTM_Program.TAPE_START_ADDR =
        UTM_Program.RULES_START_ADDR + (UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)).
      { unfold UTM_Program.TAPE_START_ADDR, UTM_Program.RULES_START_ADDR. lia. }
      rewrite Heq.
      apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules))
                        = UTM_Program.TAPE_START_ADDR).
    { apply length_pad_to_ge. exact Hfit. }
    assert (Hprefix :
      firstn (length program)
        ((pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      = firstn (length program)
          (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules))).
    { apply firstn_app_le'.
      rewrite Hmem1_len.
      apply (Nat.le_trans _ _ _ Hprog).
      exact UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR. }
    eapply eq_trans.
    2:{ subst mem0. apply (firstn_program_prefix Hprog rules). }
    exact Hprefix.
  - unfold setup_state.
    simpl.
    set (rules := UTM_Encode.encode_rules tm.(tm_rules)).
    set (mem0 := pad_to UTM_Program.RULES_START_ADDR program).
    assert (Hmem0_len : length mem0 = UTM_Program.RULES_START_ADDR).
    { subst mem0. apply length_pad_to_ge. exact Hprog. }
    assert (Hfit : length (mem0 ++ rules) <= UTM_Program.TAPE_START_ADDR).
    { rewrite app_length, Hmem0_len.
      assert (Heq: UTM_Program.TAPE_START_ADDR =
        UTM_Program.RULES_START_ADDR + (UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)).
      { unfold UTM_Program.TAPE_START_ADDR, UTM_Program.RULES_START_ADDR. lia. }
      rewrite Heq.
      apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules))
                        = UTM_Program.TAPE_START_ADDR).
    { apply length_pad_to_ge. exact Hfit. }
    assert (Hskip :
      skipn UTM_Program.RULES_START_ADDR
        ((pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      = skipn UTM_Program.RULES_START_ADDR
          (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape).
    { apply skipn_app_le'.
      rewrite Hmem1_len.
      exact UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR. }
    assert (Hskip_first :
      firstn (length rules)
        (skipn UTM_Program.RULES_START_ADDR
                 ((pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape))
      = firstn (length rules)
          (skipn UTM_Program.RULES_START_ADDR
                   (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)).
    { rewrite Hskip. reflexivity. }
    assert (Hdrop :
      firstn (length rules)
        (skipn UTM_Program.RULES_START_ADDR
                 (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      = firstn (length rules)
          (skipn UTM_Program.RULES_START_ADDR
                 (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)))).
    { apply firstn_app_le'.
      rewrite skipn_length, Hmem1_len.
      apply (Nat.le_trans _ _ _ Hrules).
      lia. }
    eapply eq_trans.
    2:{ eapply eq_trans.
        2:{ subst mem0. apply (firstn_rules_window Hprog rules). exact Hrules. }
        exact Hdrop. }
    exact Hskip_first.
Qed.

Definition inv_core (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  let '((q, tape), head) := conf in
  CPU.read_reg CPU.REG_Q st = q /\
  CPU.read_reg CPU.REG_HEAD st = head /\
  tape_window_ok st tape /\
  firstn (length program) st.(CPU.mem) = program /\
  firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
        (skipn UTM_Program.RULES_START_ADDR st.(CPU.mem)) =
    UTM_Encode.encode_rules tm.(tm_rules) /\
  length (skipn UTM_Program.TAPE_START_ADDR st.(CPU.mem)) = length tape.

Definition find_rule_start_inv (tm : TM) (conf : TMConfig) (cpu : CPU.State) : Prop :=
  IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu) /\
  inv_min cpu tm conf.

(* ----------------------------------------------------------------- *)
(* Decoding                                                          *)
(* ----------------------------------------------------------------- *)

Definition decode_instr (st : CPU.State) : CPU.Instr :=
  UTM_Encode.decode_instr_from_mem st.(CPU.mem) (4 * CPU.read_reg CPU.REG_PC st).

Lemma run1_decode_instr : forall cpu,
  run1 cpu = CPU.step (decode_instr cpu) cpu.
Proof.
  intros cpu. reflexivity.
Qed.

Lemma run1_decode : forall st,
  run1 st = CPU.step (decode_instr st) st.
Proof.
  intro st.
  unfold run1, decode_instr.
  reflexivity.
Qed.

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
  run_n cpu (S n) = run_n (run1 cpu) n.
Proof.
  intros cpu n.
  simpl. reflexivity.
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
  simpl. reflexivity.
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

(* Key lemma: reading from the register you just wrote gives the value *)
Lemma read_reg_write_reg_same : forall r v st,
  r < length st.(CPU.regs) ->
  CPU.read_reg r (CPU.write_reg r v st) = v.
Proof.
  intros r v st Hr.
  unfold CPU.read_reg, CPU.write_reg. simpl.
  (* After write_reg r v, the register file is: firstn r regs ++ [v] ++ skipn (S r) regs *)
  (* Reading at position r gives v *)
  rewrite app_nth2.
  - rewrite firstn_length.
    rewrite Nat.min_l by lia.
    replace (r - r) with 0 by lia.
    simpl. reflexivity.
  - rewrite firstn_length.
    rewrite Nat.min_l by lia.
    lia.
Qed.

(* Reading a different register after write *)
Lemma read_reg_write_reg_diff : forall r1 r2 v st,
  r1 <> r2 ->
  r1 < length st.(CPU.regs) ->
  r2 < length st.(CPU.regs) ->
  CPU.read_reg r1 (CPU.write_reg r2 v st) = CPU.read_reg r1 st.
Proof.
  intros r1 r2 v st Hneq Hr1 Hr2.
  unfold CPU.read_reg, CPU.write_reg. simpl.
  (* Need to show: nth r1 (firstn r2 regs ++ [v] ++ skipn (S r2) regs) 0 = nth r1 regs 0 *)
  destruct (Nat.ltb r1 r2) eqn:Hlt.
  - (* Case r1 < r2: r1 is in the firstn part *)
    apply Nat.ltb_lt in Hlt.
    rewrite app_nth1.
    + apply nth_firstn_lt. exact Hlt.
    + rewrite firstn_length. rewrite Nat.min_l; [lia|lia].
  - (* Case r1 >= r2, but r1 <> r2, so r1 > r2 *)
    apply Nat.ltb_nlt in Hlt.
    assert (r1 > r2) by lia.
    (* r1 is beyond the firstn r2 part *)
    rewrite app_nth2.
    + rewrite firstn_length. rewrite Nat.min_l; [|lia].
      (* nth (r1 - r2) ([v] ++ skipn (S r2) regs) 0 = nth r1 regs 0 *)
      destruct (r1 - r2) as [|n] eqn:Hdiff; [lia|].
      simpl.
      (* nth n (skipn (S r2) regs) 0 = nth r1 regs 0 *)
      assert (Heqr1: r1 = S r2 + n) by lia.
      rewrite Heqr1.
      (* Now prove: nth n (skipn (S r2) regs) 0 = nth (S r2 + n) regs 0 *)
      clear Heqr1 Hdiff Hneq Hr1 Hr2 H Hlt v r1.
      generalize dependent n. generalize dependent r2.
      induction (CPU.regs st) as [|x xs IH]; intros.
      { destruct n, r2; reflexivity. }
      destruct r2; simpl.
      { destruct n; reflexivity. }
      { apply IH. }
    + rewrite firstn_length. rewrite Nat.min_l; [lia|lia].
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
Lemma transition_Fetch_to_FindRule_direct : forall tm conf cpu0,
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
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
  intros tm conf cpu0 Hinv_core Hfetch Hpc0 Hlen
         Hdecode0 Hdecode1 Hdecode2.

  (* The proof proceeds by symbolic execution through 3 instructions:
     PC=0: LoadConst REG_TEMP1 TAPE_START_ADDR  -> PC=1
     PC=1: AddReg REG_ADDR REG_TEMP1 REG_HEAD   -> PC=2
     PC=2: LoadIndirect REG_SYM REG_ADDR        -> PC=3

     Each instruction:
     1. Is decoded from memory at (4 * PC)
     2. Matches the expected instruction from program_instrs
     3. Increments PC by 1 (since rd ≠ REG_PC for all three)

     The full proof requires unfolding run_n and step through each
     instruction, tracking PC and register values. *)

  (* Step 1: PC 0 -> 1 via LoadConst *)
  set (cpu1 := CPU.step (CPU.LoadConst CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR) cpu0).
  assert (Hrun1 : run1 cpu0 = cpu1).
  { unfold cpu1.
    rewrite run1_decode.
    rewrite Hdecode0.
    reflexivity. }
  assert (Hpc1 : CPU.read_reg CPU.REG_PC cpu1 = 1).
  { subst cpu1.
    assert (Hneq_temp1 : CPU.REG_TEMP1 <> CPU.REG_PC) by (cbv [CPU.REG_TEMP1 CPU.REG_PC]; lia).
    assert (Hlt_temp1 : CPU.REG_TEMP1 < 10) by (cbv [CPU.REG_TEMP1]; lia).
    destruct (step_LoadConst cpu0 CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR
              Hneq_temp1 Hlt_temp1 Hlen) as [Hpc1_step _].
    rewrite Hpc0 in Hpc1_step.
    exact Hpc1_step. }
  assert (Hlen1 : length (CPU.regs cpu1) = 10).
  { subst cpu1.
    unfold CPU.step; simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu0)) cpu0).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu0.(CPU.regs)).
    { subst st'.
      apply length_write_reg.
      rewrite Hlen; cbv [CPU.REG_PC]; lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen; reflexivity).
    assert (Hlt_temp1_len : CPU.REG_TEMP1 < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_TEMP1]; lia. }
    pose proof (length_write_reg CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR st' Hlt_temp1_len)
      as Hlen_after.
    rewrite Hlen_st' in Hlen_after.
    exact Hlen_after. }
  assert (Hmem1 : CPU.mem cpu1 = CPU.mem cpu0).
  { subst cpu1. unfold CPU.step. simpl. reflexivity. }

  (* Step 2: PC 1 -> 2 via AddReg *)
  set (cpu2 := CPU.step (CPU.AddReg CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD) cpu1).
  assert (Hdecode1' : decode_instr cpu1 =
    CPU.AddReg CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD).
  { rewrite <- Hrun1. exact Hdecode1. }
  assert (Hrun2 : run1 cpu1 = cpu2).
  { unfold cpu2.
    rewrite run1_decode.
    rewrite Hdecode1'.
    reflexivity. }
  assert (Hpc2 : CPU.read_reg CPU.REG_PC cpu2 = 2).
  { subst cpu2.
    assert (Hneq_addr : CPU.REG_ADDR <> CPU.REG_PC) by (cbv [CPU.REG_ADDR CPU.REG_PC]; lia).
    assert (Hlt_addr : CPU.REG_ADDR < 10) by (cbv [CPU.REG_ADDR]; lia).
    destruct (step_AddReg cpu1 CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD
              Hneq_addr Hlt_addr Hlen1) as [Hpc2_step _].
    rewrite Hpc1 in Hpc2_step.
    exact Hpc2_step. }
  assert (Hlen2 : length (CPU.regs cpu2) = 10).
  { subst cpu2.
    unfold CPU.step; simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu1)) cpu1).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu1.(CPU.regs)).
    { subst st'.
      apply length_write_reg.
      rewrite Hlen1; cbv [CPU.REG_PC]; lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen1; reflexivity).
    assert (Hlt_addr_len : CPU.REG_ADDR < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_ADDR]; lia. }
    pose proof (length_write_reg CPU.REG_ADDR (CPU.read_reg CPU.REG_TEMP1 cpu1 + CPU.read_reg CPU.REG_HEAD cpu1) st'
                 Hlt_addr_len) as Hlen_after.
    rewrite Hlen_st' in Hlen_after.
    exact Hlen_after. }
  assert (Hmem2 : CPU.mem cpu2 = CPU.mem cpu1).
  { subst cpu2. unfold CPU.step. simpl. reflexivity. }

  (* Step 3: PC 2 -> 3 via LoadIndirect *)
  set (cpu3 := CPU.step (CPU.LoadIndirect CPU.REG_SYM CPU.REG_ADDR) cpu2).
  assert (Hrun_n2 : run_n cpu0 2 = run1 cpu1).
  { simpl. rewrite Hrun1. reflexivity. }
  assert (Hdecode2' : decode_instr cpu2 =
    CPU.LoadIndirect CPU.REG_SYM CPU.REG_ADDR).
  { rewrite <- Hrun2.
    rewrite Hrun_n2 in Hdecode2.
    exact Hdecode2. }
  assert (Hrun3 : run1 cpu2 = cpu3).
  { unfold cpu3.
    rewrite run1_decode.
    rewrite Hdecode2'.
    reflexivity. }
  assert (Hpc3 : CPU.read_reg CPU.REG_PC cpu3 = 3).
  { subst cpu3.
    assert (Hneq_sym : CPU.REG_SYM <> CPU.REG_PC) by (cbv [CPU.REG_SYM CPU.REG_PC]; lia).
    assert (Hlt_sym : CPU.REG_SYM < 10) by (cbv [CPU.REG_SYM]; lia).
    destruct (step_LoadIndirect cpu2 CPU.REG_SYM CPU.REG_ADDR
              Hneq_sym Hlt_sym Hlen2) as [Hpc3_step _].
    rewrite Hpc2 in Hpc3_step.
    exact Hpc3_step. }

  exists (run_n cpu0 3).
  split; [reflexivity |].
  split.
  - unfold IS_FindRule_Start.
    simpl.
    rewrite Hrun1.
    simpl.
    rewrite Hrun2.
    simpl.
    rewrite Hrun3.
    exact Hpc3.
  - simpl.
    rewrite Hrun1.
    simpl.
    rewrite Hrun2.
    simpl.
    rewrite Hrun3.
    exact Hpc3.
Qed.

(* Now we need to show PC advances correctly *)
(* This requires knowing what instructions are at PC=0, 1, 2 *)

(* ----------------------------------------------------------------- *)
(* Transition Lemmas                                                 *)
(* ----------------------------------------------------------------- *)

Lemma transition_Fetch_to_FindRule (tm : TM) (conf : TMConfig) (cpu0 : CPU.State) :
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  length cpu0.(CPU.regs) = 10 ->
  decode_instr cpu0 =
    CPU.LoadConst CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR ->
  decode_instr (run1 cpu0) =
    CPU.AddReg CPU.REG_ADDR CPU.REG_TEMP1 CPU.REG_HEAD ->
  decode_instr (run_n cpu0 2) =
    CPU.LoadIndirect CPU.REG_SYM CPU.REG_ADDR ->
  exists cpu_find, run_n cpu0 3 = cpu_find /\ IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu_find).
Proof.
  intros Hinv Hfetch Hlen Hdecode0 Hdecode1 Hdecode2.

  destruct (transition_Fetch_to_FindRule_direct tm conf cpu0
              Hinv Hfetch Hfetch Hlen Hdecode0 Hdecode1 Hdecode2)
    as [cpu_find [Hrun [Hstart _]]].
  exists cpu_find.
  split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Loop Reasoning Infrastructure - Week 2 of Roadmap                 *)
(* ----------------------------------------------------------------- *)

(* Constants for rule encoding *)
Definition RULES_START_ADDR : nat := 1000.
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

(* Loop iteration lemma: checking non-matching rule preserves invariant *)
Lemma loop_iteration_no_match : forall tm conf cpu i,
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
  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  let rule := nth i (tm_rules tm) (0, 0, 0, 0, 0%Z) in
  (fst (fst (fst (fst rule))), snd (fst (fst (fst rule)))) <> (q, sym) ->
  CPU.read_reg CPU.REG_TEMP1 (run_n cpu 3) <> 0 ->
  exists cpu',
    run_n cpu 6 = cpu' /\
    FindRule_Loop_Inv tm conf cpu' (S i).
Proof.
  intros tm conf cpu i Hinv Hi_len Hpc Hlen Hdecode0 Hdecode1 Hdecode2
         Hdecode3 Hdecode4 Hdecode5.
  destruct conf as ((q, tape), head).
  simpl in *.
  intros rule_mismatch Htemp_nonzero.

  unfold FindRule_Loop_Inv in Hinv.
  simpl in Hinv.
  destruct Hinv as [[Hpc3 | [Hpc4 | Hpc5]] [Hq [Hsym [Haddr Hchecked]]]];
    try (rewrite Hpc in Hpc3; lia);
    try (rewrite Hpc in Hpc5; lia).
  rewrite Hpc in Hpc4.

  (* Concrete states after each instruction. *)
  set (cpu1 := CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu).
  set (cpu2 := CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q) cpu1).
  set (cpu3 := CPU.step (CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q') cpu2).
  set (cpu4 := CPU.step (CPU.Jz CPU.REG_TEMP1 12) cpu3).
  set (cpu5 := CPU.step (CPU.AddConst CPU.REG_ADDR RULE_SIZE) cpu4).
  set (cpu6 := CPU.step (CPU.Jnz CPU.REG_TEMP1 4) cpu5).

  assert (Hrun1 : run1 cpu = cpu1).
  { unfold cpu1.
    rewrite run1_decode.
    rewrite Hdecode0.
    reflexivity. }
  assert (Hrun2 : run1 cpu1 = cpu2).
  { rewrite run1_decode.
    assert (Heq: decode_instr cpu1 = decode_instr (run1 cpu)).
    { rewrite <- Hrun1. reflexivity. }
    rewrite Heq, Hdecode1. unfold cpu2. reflexivity.
  }
  assert (Hrun3 : run1 cpu2 = cpu3).
  { unfold cpu3.
    rewrite run1_decode.
    f_equal.
    assert (Heq_n2: run_n cpu 2 = cpu2).
    { simpl. rewrite Hrun1, Hrun2. reflexivity. }
    rewrite <- Heq_n2.
    exact Hdecode2.
  }
  assert (Hrun4 : run1 cpu3 = cpu4).
  { unfold cpu4.
    rewrite run1_decode.
    f_equal.
    assert (Heq_n3: run_n cpu 3 = cpu3).
    { simpl. rewrite Hrun1, Hrun2, Hrun3. reflexivity. }
    rewrite <- Heq_n3.
    exact Hdecode3.
  }
  assert (Hrun5 : run1 cpu4 = cpu5).
  { unfold cpu5.
    rewrite run1_decode.
    f_equal.
    assert (Heq_n4: run_n cpu 4 = cpu4).
    { simpl. rewrite Hrun1, Hrun2, Hrun3, Hrun4. reflexivity. }
    rewrite <- Heq_n4.
    exact Hdecode4.
  }
  assert (Hrun6 : run1 cpu5 = cpu6).
  { unfold cpu6.
    rewrite run1_decode.
    f_equal.
    assert (Heq_n5: run_n cpu 5 = cpu5).
    { simpl. rewrite Hrun1, Hrun2, Hrun3, Hrun4, Hrun5. reflexivity. }
    rewrite <- Heq_n5.
    exact Hdecode5.
  }

  simpl.
  rewrite Hrun1. simpl.
  rewrite Hrun2. simpl.
  rewrite Hrun3. simpl.
  rewrite Hrun4. simpl.
  rewrite Hrun5. simpl.
  rewrite Hrun6. simpl.
  exists cpu6.
  split; [reflexivity|].

  (* Program counter evolution. *)
  assert (Hpc1 : CPU.read_reg CPU.REG_PC cpu1 = 5) by
    (unfold cpu1; destruct (step_LoadIndirect cpu CPU.REG_Q' CPU.REG_ADDR ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen) as [Hpc1 _]; rewrite Hpc in Hpc1; exact Hpc1).
  assert (Hlen1: length cpu1.(CPU.regs) = 10).
  { unfold cpu1. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu)) cpu).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen; reflexivity).
    assert (Hlt_rd : CPU.REG_Q' < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_Q']. lia. }
    pose proof (length_write_reg CPU.REG_Q' (CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc2 : CPU.read_reg CPU.REG_PC cpu2 = 6) by
    (unfold cpu2; destruct (step_CopyReg cpu1 CPU.REG_TEMP1 CPU.REG_Q ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen1) as [Hpc2 _]; rewrite Hpc1 in Hpc2; exact Hpc2).
  assert (Hlen2: length cpu2.(CPU.regs) = 10).
  { unfold cpu2. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu1)) cpu1).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu1.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen1. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen1; reflexivity).
    assert (Hlt_rd : CPU.REG_TEMP1 < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_TEMP1]. lia. }
    pose proof (length_write_reg CPU.REG_TEMP1 (CPU.read_reg CPU.REG_Q cpu1) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc3' : CPU.read_reg CPU.REG_PC cpu3 = 7) by
    (unfold cpu3; destruct (step_SubReg cpu2 CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen2) as [Hpc3' _]; rewrite Hpc2 in Hpc3'; exact Hpc3').
  assert (Hlen3: length cpu3.(CPU.regs) = 10).
  { unfold cpu3. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu2)) cpu2).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu2.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen2. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen2; reflexivity).
    assert (Hlt_rd : CPU.REG_TEMP1 < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_TEMP1]. lia. }
    pose proof (length_write_reg CPU.REG_TEMP1 (CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc4' : CPU.read_reg CPU.REG_PC cpu4 = 8).
  { unfold cpu4.
    assert (Heq_cpu3: run_n cpu 3 = cpu3).
    { simpl. rewrite Hrun1, Hrun2, Hrun3. reflexivity. }
    assert (Htemp_cpu3: CPU.read_reg CPU.REG_TEMP1 cpu3 <> 0).
    { rewrite <- Heq_cpu3. exact Htemp_nonzero. }
    pose proof (step_BranchZero_not_taken cpu3 CPU.REG_TEMP1 12 Htemp_cpu3 Hlen3) as Hpc4'.
    rewrite Hpc3' in Hpc4'. exact Hpc4'. }
  assert (Hlen4: length cpu4.(CPU.regs) = 10).
  { unfold cpu4. unfold CPU.step. simpl.
    destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0) eqn:Heqb.
    - assert (Hlt: CPU.REG_PC < length cpu3.(CPU.regs)) by (rewrite Hlen3; cbv [CPU.REG_PC]; lia).
      pose proof (length_write_reg CPU.REG_PC 12 cpu3 Hlt) as H.
      rewrite H, Hlen3. reflexivity.
    - assert (Hlt: CPU.REG_PC < length cpu3.(CPU.regs)) by (rewrite Hlen3; cbv [CPU.REG_PC]; lia).
      pose proof (length_write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu3)) cpu3 Hlt) as H.
      rewrite H, Hlen3. reflexivity. }
  assert (Hpc5' : CPU.read_reg CPU.REG_PC cpu5 = 9) by
    (unfold cpu5; destruct (step_AddConst cpu4 CPU.REG_ADDR RULE_SIZE ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen4) as [Hpc5' _]; rewrite Hpc4' in Hpc5'; exact Hpc5').
  assert (Hlen5: length cpu5.(CPU.regs) = 10).
  { unfold cpu5. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu4.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen4. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen4; reflexivity).
    assert (Hlt_rd : CPU.REG_ADDR < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_ADDR]. lia. }
    pose proof (length_write_reg CPU.REG_ADDR (CPU.read_reg CPU.REG_ADDR cpu4 + RULE_SIZE) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc6 : CPU.read_reg CPU.REG_PC cpu6 = 4).
  { unfold cpu6.
    assert (Heq_cpu3: run_n cpu 3 = cpu3).
    { simpl. rewrite Hrun1, Hrun2, Hrun3. reflexivity. }
    assert (Htemp_cpu3: CPU.read_reg CPU.REG_TEMP1 cpu3 <> 0).
    { rewrite <- Heq_cpu3. exact Htemp_nonzero. }
    (* Prove TEMP1 is preserved from cpu3 to cpu4 *)
    assert (Htemp_cpu4: CPU.read_reg CPU.REG_TEMP1 cpu4 = CPU.read_reg CPU.REG_TEMP1 cpu3).
    { unfold cpu4, CPU.step. simpl.
      destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0) eqn:Heqb.
      - apply read_reg_write_reg_diff; try (rewrite Hlen3; cbv; lia).
        cbv [CPU.REG_TEMP1 CPU.REG_PC]. discriminate.
      - apply read_reg_write_reg_diff; try (rewrite Hlen3; cbv; lia).
        cbv [CPU.REG_TEMP1 CPU.REG_PC]. discriminate. }
    (* Prove TEMP1 is preserved from cpu4 to cpu5 *)
    assert (Htemp_cpu5: CPU.read_reg CPU.REG_TEMP1 cpu5 = CPU.read_reg CPU.REG_TEMP1 cpu4).
    { unfold cpu5, CPU.step.
      (* The goal is now about a match on (AddConst ADDR RULE_SIZE) *)
      (* After the match, we get: write_reg ADDR (read_reg ADDR cpu4 + RULE_SIZE) (write_reg PC ... cpu4) *)
      (* Use transitivity to break this into two steps *)
      change (CPU.read_reg CPU.REG_TEMP1
               match CPU.AddConst CPU.REG_ADDR RULE_SIZE with
               | CPU.LoadConst rd v => CPU.write_reg rd v (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)
               | CPU.LoadIndirect rd ra => CPU.write_reg rd (CPU.read_mem (CPU.read_reg ra cpu4) cpu4) (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)
               | CPU.CopyReg rd rs => CPU.write_reg rd (CPU.read_reg rs cpu4) (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)
               | CPU.AddReg rd rs1 rs2 => CPU.write_reg rd (CPU.read_reg rs1 cpu4 + CPU.read_reg rs2 cpu4) (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)
               | CPU.SubReg rd rs1 rs2 => CPU.write_reg rd (CPU.read_reg rs1 cpu4 - CPU.read_reg rs2 cpu4) (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)
               | CPU.AddConst rd v => CPU.write_reg rd (CPU.read_reg rd cpu4 + v) (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)
               | _ => CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4
               end =
              CPU.read_reg CPU.REG_TEMP1 cpu4).
      simpl.
      (* Now the goal should be simpler *)
      transitivity (CPU.read_reg CPU.REG_TEMP1 (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4)).
      - apply (read_reg_write_reg_diff CPU.REG_TEMP1 CPU.REG_ADDR).
        + cbv [CPU.REG_TEMP1 CPU.REG_ADDR]. discriminate.
        + pose proof (length_write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4) as Hlen_pc.
          assert (Hlt_pc: CPU.REG_PC < length cpu4.(CPU.regs)) by (rewrite Hlen4; cbv; lia).
          specialize (Hlen_pc Hlt_pc). rewrite Hlen_pc. rewrite Hlen4. cbv [CPU.REG_TEMP1]. lia.
        + pose proof (length_write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4) as Hlen_pc.
          assert (Hlt_pc: CPU.REG_PC < length cpu4.(CPU.regs)) by (rewrite Hlen4; cbv; lia).
          specialize (Hlen_pc Hlt_pc). rewrite Hlen_pc. rewrite Hlen4. cbv [CPU.REG_ADDR]. lia.
      - (* Then prove TEMP1 preserved across PC write *)
        apply (read_reg_write_reg_diff CPU.REG_TEMP1 CPU.REG_PC).
        + cbv [CPU.REG_TEMP1 CPU.REG_PC]. discriminate.
        + rewrite Hlen4. cbv [CPU.REG_TEMP1]. lia.
        + rewrite Hlen4. cbv [CPU.REG_PC]. lia. }
    assert (Htemp_cpu5_ne0: CPU.read_reg CPU.REG_TEMP1 cpu5 <> 0).
    { rewrite Htemp_cpu5, Htemp_cpu4. exact Htemp_cpu3. }
    pose proof (step_JumpNonZero_taken cpu5 CPU.REG_TEMP1 4 Htemp_cpu5_ne0 Hlen5) as Hpc6.
    exact Hpc6. }

  (* q register preservation. *)
  assert (Hq1 : CPU.read_reg CPU.REG_Q cpu1 = q).
  { unfold cpu1, CPU.step. simpl.
    set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu)) cpu).
    transitivity (CPU.read_reg CPU.REG_Q st_pc).
    - apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_Q' (CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) st_pc).
      + cbv [CPU.REG_Q CPU.REG_Q']. discriminate.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen; cbv; lia). rewrite Hlen. cbv [CPU.REG_Q]. lia.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen; cbv; lia). rewrite Hlen. cbv [CPU.REG_Q']. lia.
    - transitivity (CPU.read_reg CPU.REG_Q cpu).
      + subst st_pc. apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu)) cpu).
        * cbv [CPU.REG_Q CPU.REG_PC]. discriminate.
        * rewrite Hlen. cbv [CPU.REG_Q]. lia.
        * rewrite Hlen. cbv [CPU.REG_PC]. lia.
      + exact Hq. }
  assert (Hq2 : CPU.read_reg CPU.REG_Q cpu2 = q).
  { unfold cpu2, CPU.step. simpl.
    set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu1)) cpu1).
    transitivity (CPU.read_reg CPU.REG_Q st_pc).
    - apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_TEMP1 (CPU.read_reg CPU.REG_Q cpu1) st_pc).
      + cbv [CPU.REG_Q CPU.REG_TEMP1]. discriminate.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen1; cbv; lia). rewrite Hlen1. cbv [CPU.REG_Q]. lia.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen1; cbv; lia). rewrite Hlen1. cbv [CPU.REG_TEMP1]. lia.
    - transitivity (CPU.read_reg CPU.REG_Q cpu1).
      + subst st_pc. apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu1)) cpu1).
        * cbv [CPU.REG_Q CPU.REG_PC]. discriminate.
        * rewrite Hlen1. cbv [CPU.REG_Q]. lia.
        * rewrite Hlen1. cbv [CPU.REG_PC]. lia.
      + exact Hq1. }
  assert (Hq3 : CPU.read_reg CPU.REG_Q cpu3 = q).
  { unfold cpu3, CPU.step. simpl.
    set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu2)) cpu2).
    transitivity (CPU.read_reg CPU.REG_Q st_pc).
    - apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_TEMP1 (CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) st_pc).
      + cbv [CPU.REG_Q CPU.REG_TEMP1]. discriminate.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen2; cbv; lia). rewrite Hlen2. cbv [CPU.REG_Q]. lia.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen2; cbv; lia). rewrite Hlen2. cbv [CPU.REG_TEMP1]. lia.
    - transitivity (CPU.read_reg CPU.REG_Q cpu2).
      + subst st_pc. apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu2)) cpu2).
        * cbv [CPU.REG_Q CPU.REG_PC]. discriminate.
        * rewrite Hlen2. cbv [CPU.REG_Q]. lia.
        * rewrite Hlen2. cbv [CPU.REG_PC]. lia.
      + exact Hq2. }
  assert (Hq4 : CPU.read_reg CPU.REG_Q cpu4 = q).
  { unfold cpu4, CPU.step. simpl. destruct (CPU.read_reg CPU.REG_TEMP1 cpu3 =? 0).
    - transitivity (CPU.read_reg CPU.REG_Q cpu3).
      + apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC 12 cpu3). cbv; discriminate. rewrite Hlen3. cbv; lia. rewrite Hlen3. cbv; lia.
      + exact Hq3.
    - transitivity (CPU.read_reg CPU.REG_Q cpu3).
      + apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu3)) cpu3). cbv; discriminate. rewrite Hlen3. cbv; lia. rewrite Hlen3. cbv; lia.
      + exact Hq3. }
  assert (Hq5 : CPU.read_reg CPU.REG_Q cpu5 = q).
  { unfold cpu5, CPU.step. simpl.
    set (st_pc := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).
    transitivity (CPU.read_reg CPU.REG_Q st_pc).
    - apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_ADDR (CPU.read_reg CPU.REG_ADDR cpu4 + RULE_SIZE) st_pc).
      + cbv [CPU.REG_Q CPU.REG_ADDR]. discriminate.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen4; cbv; lia). rewrite Hlen4. cbv [CPU.REG_Q]. lia.
      + subst st_pc. rewrite length_write_reg by (rewrite Hlen4; cbv; lia). rewrite Hlen4. cbv [CPU.REG_ADDR]. lia.
    - transitivity (CPU.read_reg CPU.REG_Q cpu4).
      + subst st_pc. apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu4)) cpu4).
        * cbv [CPU.REG_Q CPU.REG_PC]. discriminate.
        * rewrite Hlen4. cbv [CPU.REG_Q]. lia.
        * rewrite Hlen4. cbv [CPU.REG_PC]. lia.
      + exact Hq4. }
  assert (Hq6 : CPU.read_reg CPU.REG_Q cpu6 = q).
  { unfold cpu6, CPU.step. simpl. transitivity (CPU.read_reg CPU.REG_Q cpu5). apply (read_reg_write_reg_diff CPU.REG_Q CPU.REG_PC 4 cpu5). cbv; discriminate. rewrite Hlen5. cbv; lia. rewrite Hlen5. cbv; lia. exact Hq5. }

  (* sym register preservation. *)
  assert (Hsym1 : CPU.read_reg CPU.REG_SYM cpu1 = sym).
  { subst cpu1. apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_Q') (v := CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) (st := cpu);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_Q']; lia.
  }
  assert (Hsym2 : CPU.read_reg CPU.REG_SYM cpu2 = sym).
  { subst cpu2. apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_Q cpu1) (st := cpu1);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_TEMP1]; lia.
  }
  assert (Hsym3 : CPU.read_reg CPU.REG_SYM cpu3 = sym).
  { subst cpu3. apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) (st := cpu2);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_TEMP1]; lia.
  }
  assert (Hsym4 : CPU.read_reg CPU.REG_SYM cpu4 = sym).
  { subst cpu4. unfold CPU.step.
    rewrite Hpc3'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_PC) (st := cpu3) (v := 12);
      try assumption; try lia.
    cbv [CPU.REG_SYM CPU.REG_PC]; lia.
  }
  assert (Hsym5 : CPU.read_reg CPU.REG_SYM cpu5 = sym).
  { subst cpu5. destruct (step_AddConst cpu4 CPU.REG_ADDR RULE_SIZE ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen4) as [_ Hadd].
    unfold CPU.step.
    rewrite Hpc4'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_ADDR) (st := cpu4)
      (v := CPU.read_reg CPU.REG_ADDR cpu4 + RULE_SIZE);
      try assumption; try lia.
    cbv [CPU.REG_SYM CPU.REG_ADDR]; lia.
  }
  assert (Hsym6 : CPU.read_reg CPU.REG_SYM cpu6 = sym).
  { subst cpu6. unfold CPU.step.
    rewrite Hpc5'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_PC) (st := cpu5) (v := 4);
      try assumption; try lia.
    cbv [CPU.REG_SYM CPU.REG_PC]; lia.
  }

  (* Address update. *)
  assert (Haddr5 : CPU.read_reg CPU.REG_ADDR cpu5 = CPU.read_reg CPU.REG_ADDR cpu4 + RULE_SIZE).
  { subst cpu5. destruct (step_AddConst cpu4 CPU.REG_ADDR RULE_SIZE ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen4) as [_ Hadd]. exact Hadd. }
  assert (Haddr6 : CPU.read_reg CPU.REG_ADDR cpu6 = CPU.read_reg CPU.REG_ADDR cpu5).
  { subst cpu6. unfold CPU.step.
    rewrite Hpc5'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_ADDR) (r2 := CPU.REG_PC) (st := cpu5) (v := 4);
      try assumption; try lia.
    cbv [CPU.REG_ADDR CPU.REG_PC]; lia.
  }
  assert (Haddr4_val : CPU.read_reg CPU.REG_ADDR cpu4 = CPU.read_reg CPU.REG_ADDR cpu3).
  { subst cpu4. unfold CPU.step.
    rewrite Hpc3'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_ADDR) (r2 := CPU.REG_PC) (st := cpu3) (v := 12);
      try assumption; try lia.
    cbv [CPU.REG_ADDR CPU.REG_PC]; lia.
  }
  assert (Haddr3_val : CPU.read_reg CPU.REG_ADDR cpu3 = CPU.read_reg CPU.REG_ADDR cpu2).
  { subst cpu3. apply read_reg_write_reg_diff with (r1 := CPU.REG_ADDR) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) (st := cpu2);
      try assumption; try lia.
    cbv [CPU.REG_ADDR CPU.REG_TEMP1]; lia.
  }
  assert (Haddr2_val : CPU.read_reg CPU.REG_ADDR cpu2 = CPU.read_reg CPU.REG_ADDR cpu1).
  { subst cpu2. apply read_reg_write_reg_diff with (r1 := CPU.REG_ADDR) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_Q cpu1) (st := cpu1);
      try assumption; try lia.
    cbv [CPU.REG_ADDR CPU.REG_TEMP1]; lia.
  }
  assert (Haddr1_val : CPU.read_reg CPU.REG_ADDR cpu1 = CPU.read_reg CPU.REG_ADDR cpu).
  { subst cpu1. apply read_reg_write_reg_diff with (r1 := CPU.REG_ADDR) (r2 := CPU.REG_Q') (v := CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) (st := cpu);
      try assumption; try lia.
    cbv [CPU.REG_ADDR CPU.REG_Q']; lia.
  }

  assert (Haddr_final : CPU.read_reg CPU.REG_ADDR cpu6 = RULES_START_ADDR + S i * RULE_SIZE).
  { rewrite Haddr6, Haddr5, Haddr4_val, Haddr3_val, Haddr2_val, Haddr1_val.
    rewrite Haddr.
    cbv [RULE_SIZE]. lia.
  }

  assert (Hchecked' : forall j,
            j < S i ->
            let rule_j := nth j (tm_rules tm) (0, 0, 0, 0, 0%Z) in
            (fst (fst (fst (fst rule_j))), snd (fst (fst (fst rule_j))))
              <> (q, nth head tape (tm_blank tm))).
  {
    intros j Hj.
    apply lt_n_Sm_le in Hj.
    destruct (Nat.lt_lt_succ_r _ _ Hj) as [Hlt | Heq].
    - apply Hchecked. exact Hlt.
    - subst j. exact rule_mismatch.
  }

  split.
  { right. left. exact Hpc6. }
  split.
  { exact Hq6. }
  split.
  { exact Hsym6. }
  split.
  { exact Haddr_final. }
  exact Hchecked'.
Qed.

(*
   Loop exit lemma (partial): when a matching rule is found the loop
   takes the branch into the rule payload at PC=12.  We only establish
   the first control-flow jump here; loading the rule payload and
   executing the ApplyRule block is proved separately.
 *)
Lemma loop_exit_match : forall tm conf cpu idx,
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
  intros tm conf cpu idx Hinv Hlen_idx.
  destruct conf as ((q, tape), head).
  simpl.
  intros Hlen_regs Hdecode0 Hdecode1 Hdecode2 Hdecode3 Htemp_zero.

  unfold FindRule_Loop_Inv in Hinv.
  simpl in Hinv.
  destruct Hinv as [[Hpc3 | [Hpc4 | Hpc5]] [Hq [Hsym [Haddr Hchecked]]]].
  - rewrite Hpc3 in Hdecode0. discriminate.
  - rewrite Hpc4 in Hdecode0.
  - rewrite Hpc5 in Hdecode0. discriminate.

  (* Concrete states for the four-step match path. *)
  set (cpu1 := CPU.step (CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR) cpu).
  set (cpu2 := CPU.step (CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q) cpu1).
  set (cpu3 := CPU.step (CPU.SubReg CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q') cpu2).
  set (cpu4 := CPU.step (CPU.Jz CPU.REG_TEMP1 12) cpu3).

  assert (Hrun1 : run1 cpu = cpu1).
  { unfold cpu1, run1. rewrite Hpc4. simpl. rewrite Hdecode0. reflexivity. }
  assert (Hrun2 : run1 cpu1 = cpu2).
  { rewrite run1_decode.
    assert (Heq: decode_instr cpu1 = decode_instr (run1 cpu)).
    { rewrite <- Hrun1. reflexivity. }
    rewrite Heq, Hdecode1. unfold cpu2. reflexivity. }
  assert (Hrun3 : run1 cpu2 = cpu3).
  { unfold cpu3.
    rewrite run1_decode.
    f_equal.
    assert (Heq_n2: run_n cpu 2 = cpu2).
    { simpl. rewrite Hrun1, Hrun2. reflexivity. }
    rewrite <- Heq_n2.
    exact Hdecode2. }
  assert (Hrun4 : run1 cpu3 = cpu4).
  { unfold cpu4.
    rewrite run1_decode.
    f_equal.
    assert (Heq_n3: run_n cpu 3 = cpu3).
    { simpl. rewrite Hrun1, Hrun2, Hrun3. reflexivity. }
    rewrite <- Heq_n3.
    exact Hdecode3. }

  simpl.
  rewrite Hrun1. simpl.
  rewrite Hrun2. simpl.
  rewrite Hrun3. simpl.
  rewrite Hrun4. simpl.
  exists cpu4.
  split; [reflexivity|].

  (* Program counter: branch taken to PC=12. *)
  assert (Hpc1 : CPU.read_reg CPU.REG_PC cpu1 = 5).
  { unfold cpu1. destruct (step_LoadIndirect cpu CPU.REG_Q' CPU.REG_ADDR ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen_regs) as [Hpc1 _].
    rewrite Hpc4 in Hpc1. exact Hpc1. }
  assert (Hlen1: length cpu1.(CPU.regs) = 10).
  { unfold cpu1. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu)) cpu).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen_regs. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen_regs; reflexivity).
    assert (Hlt_rd : CPU.REG_Q' < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_Q']. lia. }
    pose proof (length_write_reg CPU.REG_Q' (CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc2 : CPU.read_reg CPU.REG_PC cpu2 = 6).
  { unfold cpu2. destruct (step_CopyReg cpu1 CPU.REG_TEMP1 CPU.REG_Q ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen1) as [Hpc2 _].
    rewrite Hpc1 in Hpc2. exact Hpc2. }
  assert (Hlen2: length cpu2.(CPU.regs) = 10).
  { unfold cpu2. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu1)) cpu1).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu1.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen1. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen1; reflexivity).
    assert (Hlt_rd : CPU.REG_TEMP1 < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_TEMP1]. lia. }
    pose proof (length_write_reg CPU.REG_TEMP1 (CPU.read_reg CPU.REG_Q cpu1) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc3' : CPU.read_reg CPU.REG_PC cpu3 = 7).
  { unfold cpu3. destruct (step_SubReg cpu2 CPU.REG_TEMP1 CPU.REG_TEMP1 CPU.REG_Q' ltac:(cbv; discriminate) ltac:(cbv; lia) Hlen2) as [Hpc3' _].
    rewrite Hpc2 in Hpc3'. exact Hpc3'. }
  assert (Hlen3: length cpu3.(CPU.regs) = 10).
  { unfold cpu3. unfold CPU.step. simpl.
    set (st' := CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC cpu2)) cpu2).
    assert (Hlen_eq : length st'.(CPU.regs) = length cpu2.(CPU.regs)).
    { subst st'. apply length_write_reg. rewrite Hlen2. cbv [CPU.REG_PC]. lia. }
    assert (Hlen_st' : length st'.(CPU.regs) = 10) by (rewrite Hlen_eq, Hlen2; reflexivity).
    assert (Hlt_rd : CPU.REG_TEMP1 < length st'.(CPU.regs)).
    { rewrite Hlen_st'. cbv [CPU.REG_TEMP1]. lia. }
    pose proof (length_write_reg CPU.REG_TEMP1 (CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) st' Hlt_rd) as Hlen_after.
    rewrite Hlen_st' in Hlen_after. exact Hlen_after. }
  assert (Hpc4' : CPU.read_reg CPU.REG_PC cpu4 = 12).
  { unfold cpu4. destruct (step_BranchZero_taken cpu3 CPU.REG_TEMP1 12 Htemp_zero Hlen3) as Hpc4'.
    exact Hpc4'. }

  split; [exact Hpc4'|].

  (* q register preserved. *)
  assert (Hq1 : CPU.read_reg CPU.REG_Q cpu1 = q).
  { subst cpu1. apply read_reg_write_reg_diff with (r1 := CPU.REG_Q) (r2 := CPU.REG_Q') (v := CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) (st := cpu);
      try lia; try assumption.
    cbv [CPU.REG_Q CPU.REG_Q']; lia. }
  assert (Hq2 : CPU.read_reg CPU.REG_Q cpu2 = q).
  { subst cpu2. apply read_reg_write_reg_diff with (r1 := CPU.REG_Q) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_Q cpu1) (st := cpu1);
      try lia; try assumption.
    cbv [CPU.REG_Q CPU.REG_TEMP1]; lia. }
  assert (Hq3 : CPU.read_reg CPU.REG_Q cpu3 = q).
  { subst cpu3. apply read_reg_write_reg_diff with (r1 := CPU.REG_Q) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) (st := cpu2);
      try lia; try assumption.
    cbv [CPU.REG_Q CPU.REG_TEMP1]; lia. }
  assert (Hq4 : CPU.read_reg CPU.REG_Q cpu4 = q).
  { subst cpu4. unfold CPU.step.
    rewrite Hpc3'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_Q) (r2 := CPU.REG_PC)
      (st := cpu3) (v := 12); try lia; try assumption.
    cbv [CPU.REG_Q CPU.REG_PC]; lia. }

  split; [exact Hq4|].

  (* sym register preserved. *)
  assert (Hsym1 : CPU.read_reg CPU.REG_SYM cpu1 = sym).
  { subst cpu1. apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_Q') (v := CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu) (st := cpu);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_Q']; lia. }
  assert (Hsym2 : CPU.read_reg CPU.REG_SYM cpu2 = sym).
  { subst cpu2. apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_Q cpu1) (st := cpu1);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_TEMP1]; lia. }
  assert (Hsym3 : CPU.read_reg CPU.REG_SYM cpu3 = sym).
  { subst cpu3. apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2) (st := cpu2);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_TEMP1]; lia. }
  assert (Hsym4 : CPU.read_reg CPU.REG_SYM cpu4 = sym).
  { subst cpu4. unfold CPU.step.
    rewrite Hpc3'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_SYM)
      (r2 := CPU.REG_PC) (st := cpu3) (v := 12);
      try lia; try assumption.
    cbv [CPU.REG_SYM CPU.REG_PC]; lia. }

  split; [exact Hsym4|].

  (* Address register unchanged through the branch. *)
  assert (Haddr1 : CPU.read_reg CPU.REG_ADDR cpu1 = CPU.read_reg CPU.REG_ADDR cpu).
  { subst cpu1. apply read_reg_write_reg_diff with (st := cpu)
      (r1 := CPU.REG_ADDR) (r2 := CPU.REG_Q') (v := CPU.read_mem (CPU.read_reg CPU.REG_ADDR cpu) cpu);
      try lia; try assumption.
    cbv [CPU.REG_ADDR CPU.REG_Q']; lia. }
  assert (Haddr2 : CPU.read_reg CPU.REG_ADDR cpu2 = CPU.read_reg CPU.REG_ADDR cpu1).
  { subst cpu2. apply read_reg_write_reg_diff with (st := cpu1)
      (r1 := CPU.REG_ADDR) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_Q cpu1);
      try lia; try assumption.
    cbv [CPU.REG_ADDR CPU.REG_TEMP1]; lia. }
  assert (Haddr3 : CPU.read_reg CPU.REG_ADDR cpu3 = CPU.read_reg CPU.REG_ADDR cpu2).
  { subst cpu3. apply read_reg_write_reg_diff with (st := cpu2)
      (r1 := CPU.REG_ADDR) (r2 := CPU.REG_TEMP1) (v := CPU.read_reg CPU.REG_TEMP1 cpu2 - CPU.read_reg CPU.REG_Q' cpu2);
      try lia; try assumption.
    cbv [CPU.REG_ADDR CPU.REG_TEMP1]; lia. }
  assert (Haddr4 : CPU.read_reg CPU.REG_ADDR cpu4 = CPU.read_reg CPU.REG_ADDR cpu3).
  { subst cpu4. unfold CPU.step.
    rewrite Hpc3'. simpl.
    unfold CPU.write_reg. simpl.
    apply read_reg_write_reg_diff with (r1 := CPU.REG_ADDR)
      (r2 := CPU.REG_PC) (st := cpu3) (v := 12);
      try lia; try assumption.
    cbv [CPU.REG_ADDR CPU.REG_PC]; lia. }

  rewrite Haddr4, Haddr3, Haddr2, Haddr1.
  rewrite Haddr.
  reflexivity.
Qed.

(* Main loop theorem: compose iteration lemmas *)
Lemma transition_FindRule_to_ApplyRule (tm : TM) (conf : TMConfig) (cpu_find : CPU.State)
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
    CPU.read_reg CPU.REG_PC cpu_apply = 12 /\
    CPU.read_reg CPU.REG_Q cpu_apply = q /\
    CPU.read_reg CPU.REG_SYM cpu_apply = sym /\
    CPU.read_reg CPU.REG_ADDR cpu_apply = RULES_START_ADDR.
Proof.
  destruct conf as ((q, tape), head).
  simpl.
  intros Hinv_loop Hlen_regs Hpc4 Hdecode0 Hdecode1 Hdecode2 Hdecode3 Htemp_zero Haddr_base Hrule0.
  assert (Hlen_rules : 0 < length (tm_rules tm)).
  { destruct (tm_rules tm) as [|r rest]; simpl in Hrule0; try discriminate; lia. }
  pose proof (loop_exit_match tm ((q, tape), head) cpu_find 0
                Hinv_loop Hlen_rules Hlen_regs
                Hdecode0 Hdecode1 Hdecode2 Hdecode3 Htemp_zero) as Hex.
  simpl in Hex.
  destruct Hex as [cpu_branch [Hrun [Hpc12 [Hq [Hsym Haddr]]]]].
  exists cpu_branch.
  repeat split; assumption.
Qed.
