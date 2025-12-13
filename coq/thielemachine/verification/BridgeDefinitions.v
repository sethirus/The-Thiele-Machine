
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
(* NOTE: Relocated under thielemachine/verification to quarantine   *)
(* the instruction-level replay from the default `make core` flow.  *)
(* Use `make -C coq bridge` (or `verification`) to exercise this    *)
(* artifact without blocking the audited tier.                      *)
(*                                                                   *)
(* To complete: The transition lemmas require detailed symbolic     *)
(* execution proofs through the CPU interpreter. These are complex  *)
(* but mechanizable - they involve stepping through the instruction *)
(* sequence and maintaining invariants.                             *)
(* ================================================================= *)

Set Warnings "-deprecated".

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode UTM_CoreLemmas.
Import ListNotations.

Local Open Scope nat_scope.
Local Notation length := List.length.

(* Bring in bridge core helpers (list_eqb, state_eqb, etc.) *)
Require Import ThieleMachine.modular.Bridge_BridgeCore.

(* Instrumentation helpers to locate long-running proofs during timed bridge
   builds.  The [Time] vernac modifier is applied to the key loop lemmas, and
   [bridge_checkpoint] marks entry into their proofs so a timed build can
   report the last completed milestone before hitting a timeout. *)
Ltac bridge_checkpoint msg :=
  let s := eval compute in msg in idtac "[bridge]" s.

(* ----------------------------------------------------------------- *)
(* Program encoding                                                  *)
(* ----------------------------------------------------------------- *)

(* The encoded universal program *)
Definition program : list nat :=
  flat_map UTM_Encode.encode_instr_words UTM_Program.program_instrs.

(* Compute the concrete program length once so decoding bounds can reuse it
   without re-running a large reduction. *)
Definition program_len : nat := Eval vm_compute in List.length program.

Lemma program_length_eq : List.length program = program_len.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* CPU Execution - from ThieleUniversal_Run1.v                      *)
(* ----------------------------------------------------------------- *)

(* Decode the instruction at the current program counter. *)
Definition decode_instr (st : CPU.State) : CPU.Instr :=
  UTM_Encode.decode_instr_from_mem st.(CPU.mem) (4 * CPU.read_reg CPU.REG_PC st).

(* Single step execution *)
Definition run1 (s : CPU.State) : CPU.State :=
  CPU.step (decode_instr s) s.

(* Multi-step execution *)
Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
  match n with
  | 0 => s
  | S n' => run_n (run1 s) n'
  end.

Lemma list_eqb_refl {A} (eqb : A -> A -> bool) (eqb_refl : forall x, eqb x x = true) :
  forall l, list_eqb eqb l l = true.
Proof.
  induction l as [|x t IH]; simpl; rewrite ?eqb_refl, ?IH; reflexivity.
Qed.

Definition state_eqb (s1 s2 : CPU.State) : bool :=
  Nat.eqb s1.(CPU.cost) s2.(CPU.cost)
    && list_eqb Nat.eqb s1.(CPU.regs) s2.(CPU.regs)
    && list_eqb Nat.eqb s1.(CPU.mem) s2.(CPU.mem).

Lemma state_eqb_refl : forall s, state_eqb s s = true.
Proof.
  intro s. destruct s as [r m c].
  simpl.
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split.
    + apply Nat.eqb_refl.
    + apply list_eqb_refl. intros x. apply Nat.eqb_refl.
  - apply list_eqb_refl. intros x. apply Nat.eqb_refl.
Qed.

Lemma state_eqb_true_iff : forall s1 s2, state_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2; split; intro H.
  - destruct s1 as [r1 m1 c1], s2 as [r2 m2 c2]; simpl in H.
    apply Bool.andb_true_iff in H as [Hcost_reg Hmem].
    apply Bool.andb_true_iff in Hcost_reg as [Hcost Hregs].
    apply Nat.eqb_eq in Hcost.
    apply (list_eqb_spec Nat.eqb Nat.eqb_eq) in Hregs.
    apply (list_eqb_spec Nat.eqb Nat.eqb_eq) in Hmem.
    simpl in Hcost, Hregs, Hmem.
    subst c2 r2 m2. reflexivity.
  - rewrite H. destruct s2 as [r m c].
    apply state_eqb_refl.
  Qed.

Definition check_transition (start_state end_state : CPU.State) (steps : nat) : bool :=
  state_eqb (run_n start_state steps) end_state.

Lemma check_transition_sound : forall s1 s2 n,
  check_transition s1 s2 n = true -> run_n s1 n = s2.
Proof.
  unfold check_transition.
  intros s1 s2 n H.
  apply state_eqb_true_iff in H; assumption.
Qed.

Ltac vm_run_n :=
  match goal with
  | |- run_n ?s ?n = ?t =>
      apply (check_transition_sound s t n);
      vm_compute; reflexivity
  end.

(* Symbolic steppers for small, concrete prefixes.  These avoid the
   `vm_compute`/`native_compute` path when the starting state is still
   symbolic, but the program being fetched is concrete. *)
Ltac step_symbolic :=
  cbv [run1 CPU.step UTM_Encode.decode_instr_from_mem] in *;
  simpl.

(* ----------------------------------------------------------------- *)
(* State Setup - extracted from ThieleUniversal.v                   *)
(* ----------------------------------------------------------------- *)

(* Helper: set nth element of a list *)
Definition set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  firstn n l ++ [v] ++ skipn (S n) l.

Lemma nth_set_nth_same : forall {A} (l : list A) n v d,
  n < length l ->
  nth n (set_nth l n v) d = v.
Proof.
  intros A l n v d Hn.
  unfold set_nth.
  rewrite app_nth2.
  - rewrite firstn_length, Nat.min_l by lia.
    replace (n - n) with 0 by lia.
    simpl. reflexivity.
  - rewrite firstn_length, Nat.min_l by lia.
    lia.
Qed.

Lemma nth_set_nth_diff : forall {A} (l : list A) n m v d,
  n <> m ->
  n < length l ->
  m < length l ->
  nth n (set_nth l m v) d = nth n l d.
Proof.
  intros A l n m v d Hneq Hn Hm.
  unfold set_nth.
  destruct (Nat.ltb n m) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    rewrite app_nth1.
    + apply nth_firstn_lt. exact Hlt.
    + rewrite firstn_length, Nat.min_l by lia.
      lia.
  - apply Nat.ltb_nlt in Hlt.
    assert (n > m) by lia.
    rewrite app_nth2.
    + rewrite firstn_length, Nat.min_l by lia.
      destruct (n - m) as [|k] eqn:Hdiff; [lia|].
      simpl.
      assert (Hn': n = S m + k) by lia.
      rewrite Hn'.
      clear Hn' Hdiff Hneq Hn Hm H Hlt.
      generalize dependent k. generalize dependent m.
      induction l as [|x xs IH]; intros.
      { destruct k, m; reflexivity. }
      destruct m; simpl.
      { destruct k; reflexivity. }
      { apply IH. }
    + rewrite firstn_length, Nat.min_l by lia.
      lia.
Qed.

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

Lemma length_pad_to_ge_base : forall l n,
  length (pad_to n l) >= length l.
Proof.
  intros l n.
  unfold pad_to.
  rewrite app_length, repeat_length.
  lia.
Qed.

Lemma length_pad_to_ge_n : forall l n,
  n <= length (pad_to n l).
Proof.
  intros l n.
  unfold pad_to.
  rewrite app_length, repeat_length.
  destruct (le_dec n (length l)) as [Hnl | Hln].
  - pose proof (Nat.sub_0_le n (length l)) as Hsub0.
    (* From Hnl: n <= length l, we get n - length l = 0. *)
    assert (n - length l = 0) as Hsub by (apply Nat.sub_0_le; exact Hnl).
    rewrite Hsub.
    lia.
  - assert (length l <= n) as Hle by lia.
    rewrite Nat.add_comm.
    rewrite Nat.sub_add by exact Hle.
    lia.
Qed.

Lemma nth_app_lt : forall {A} (l1 l2 : list A) n d,
  n < length l1 -> nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  intros A l1 l2 n d Hlt.
  revert n Hlt.
  induction l1 as [|x l1 IH]; intros [|n] Hlt; simpl in *; try lia; auto.
  apply IH. lia.
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

(* Padding preserves existing elements below the original length. *)
Lemma nth_pad_to_lt : forall (l : list nat) n d k,
  n < length l ->
  nth n (pad_to k l) d = nth n l d.
Proof.
  intros l n d k Hlt.
  unfold pad_to.
  apply nth_app_lt; lia.
Qed.

(* Avoid expanding large padded memories during later proofs. *)
#[local] Opaque pad_to repeat.

(* Setup initial CPU state from TM configuration *)
Definition setup_state (tm : TM) (conf : TMConfig) : CPU.State :=
  let '((q, tape), head) := conf in
  let regs0 := repeat 0 10 in
  let regs1 := set_nth regs0 CPU.REG_Q q in
    let regs2 := set_nth regs1 CPU.REG_HEAD head in
    let regs3 := set_nth regs2 CPU.REG_PC 0 in
    (* Initialize temporary registers used by the program view: ensure the
      starting state matches the expectations of inv_full (TEMP1 and ADDR).
      This sets up a register environment consistent with the decoding
      semantics and later invariants. *)
    let regs4 := set_nth regs3 CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR in
    let regs5 := set_nth regs4 CPU.REG_ADDR (UTM_Program.TAPE_START_ADDR + head) in
  (* Align the CPU tape image with [TM.tm_step]'s defaulting behavior:
     the TM reads [nth head tape tm_blank] even when [head] is out of bounds.
     The CPU performs a concrete memory read at address [TAPE_START_ADDR+head],
     so we pad the stored tape so that cell exists and equals [tm_blank].
     This preserves [tape_window_ok] for the original tape prefix. *)
  let tape_ext :=
    if Nat.ltb head (length tape) then tape
    else tape ++ repeat tm.(tm_blank) (S head - length tape) in
  let rules := UTM_Encode.encode_rules tm.(tm_rules) in
  let mem0 := pad_to UTM_Program.RULES_START_ADDR program in
  let mem1 := pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules) in
  {| CPU.regs := regs5; CPU.mem := mem1 ++ tape_ext; CPU.cost := 0 |}.

(* Don't make these opaque yet - we need them for foundational lemmas *)

(* ----------------------------------------------------------------- *)
(* Program layout shortcuts                                          *)
(* ----------------------------------------------------------------- *)

(* Tactic to discharge fixed program-length bounds when decoding. *)
Ltac calc_bounds :=
  rewrite program_length_eq;
  unfold program_len;
  simpl;
  lia.

(* The concrete program lives at the front of memory; when the PC stays within
   the program bounds we can read directly from the static [program] list and
   ignore the symbolic rules/tape suffix. *)
Lemma program_memory_lookup : forall tm conf n,
  n < length program ->
  nth n (CPU.mem (setup_state tm conf)) 0 = nth n program 0.
Proof.
  intros tm conf n Hn.
  destruct conf as ((q, tape), head).
  unfold setup_state; simpl.
  set (rules := UTM_Encode.encode_rules tm.(tm_rules)).
  set (mem0 := pad_to UTM_Program.RULES_START_ADDR program).
  set (mem1 := pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)).
  set (tape_ext :=
    if head <? length tape then tape
    else tape ++ repeat tm.(tm_blank) (S head - length tape)).
  assert (Hmem0_len : n < length mem0).
  { subst mem0. eapply Nat.lt_le_trans; [exact Hn|]. apply length_pad_to_ge_base. }
  assert (Hmem1_len : n < length mem1).
  { subst mem1.
    eapply Nat.lt_le_trans; [| apply length_pad_to_ge_base ].
    eapply Nat.lt_le_trans; [exact Hmem0_len|].
    rewrite app_length; lia.
  }
  subst mem1.
  eapply eq_trans.
  { apply (@nth_app_lt nat (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) tape_ext n 0).
    exact Hmem1_len. }
  eapply eq_trans.
  { apply (nth_pad_to_lt (mem0 ++ rules) n 0 UTM_Program.TAPE_START_ADDR).
    rewrite app_length. lia. }
  rewrite nth_app_lt by lia.
  subst mem0.
  rewrite (nth_pad_to_lt program n 0 UTM_Program.RULES_START_ADDR) by exact Hn.
  reflexivity.
Qed.

(* If a state already exposes the concrete program prefix, we can reuse that
   fact to read directly from [program] without re-running the padding
   expansions.  This lets later steps avoid reopening [setup_state]. *)

Lemma decode_program_at_pc : forall tm conf pc,
  4 * pc + 3 < length program ->
  UTM_Encode.decode_instr_from_mem (CPU.mem (setup_state tm conf)) (4 * pc) =
  UTM_Encode.decode_instr_from_mem program (4 * pc).
Proof.
  intros tm conf pc Hbound.
  unfold UTM_Encode.decode_instr_from_mem.
  repeat rewrite program_memory_lookup; try lia.
  reflexivity.
Qed.

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

Lemma tape_window_ok_intro : forall st tape,
  firstn (length tape) (skipn UTM_Program.TAPE_START_ADDR st.(CPU.mem)) = tape ->
  tape_window_ok st tape.
Proof.
  intros. exact H.
Qed.

#[global] Opaque tape_window_ok.

(* ----------------------------------------------------------------- *)
(* Memory layout helper lemmas for setup_state                       *)
(* ----------------------------------------------------------------- *)

Lemma setup_state_mem_structure : forall tm conf,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  let rules := UTM_Encode.encode_rules tm.(tm_rules) in
  let tape := snd (fst conf) in
  let head := snd conf in
  let tape_ext :=
    if Nat.ltb head (length tape) then tape
    else tape ++ repeat tm.(tm_blank) (S head - length tape) in
  CPU.mem (setup_state tm conf) =
    pad_to UTM_Program.TAPE_START_ADDR
      (pad_to UTM_Program.RULES_START_ADDR program ++ rules) ++ tape_ext.
Proof.
  intros tm ((q, tape), head) Hprog Hrules.
  unfold setup_state. simpl.
  reflexivity.
Qed.

(* Make this lemma transparent/computable for rewriting *)
#[global] Hint Rewrite setup_state_mem_structure using (lia) : setup_state_db.

Lemma setup_state_tape_region : forall tm conf,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  let tape := snd (fst conf) in
  let head := snd conf in
  let tape_ext :=
    if Nat.ltb head (length tape) then tape
    else tape ++ repeat tm.(tm_blank) (S head - length tape) in
  skipn UTM_Program.TAPE_START_ADDR (CPU.mem (setup_state tm conf)) = tape_ext.
Proof.
  intros tm ((q, tape), head) Hprog Hrules.
  erewrite setup_state_mem_structure by eassumption.
  assert (Hinner : length (pad_to UTM_Program.RULES_START_ADDR program ++ UTM_Encode.encode_rules (tm_rules tm)) <= UTM_Program.TAPE_START_ADDR).
  { rewrite app_length.
    rewrite length_pad_to_ge by exact Hprog.
    unfold UTM_Program.RULES_START_ADDR, UTM_Program.TAPE_START_ADDR in *.
    lia. }
  rewrite skipn_pad_to_app by exact Hinner.
  apply skipn_O.
Qed.

Lemma tape_window_ok_setup_state : forall tm q tape head,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  tape_window_ok (setup_state tm ((q, tape), head)) tape.
Proof.
  intros tm q tape head Hprog Hrules.
  apply tape_window_ok_intro.
  rewrite (setup_state_tape_region tm ((q, tape), head) Hprog Hrules).
  simpl.
  destruct (Nat.ltb head (length tape)) eqn:Hlt.
  - rewrite firstn_all. reflexivity.
  - apply Nat.ltb_ge in Hlt.
    rewrite firstn_app_le' by lia.
    apply firstn_all.
Qed.

(* Helper lemmas for setup_state register access *)

Lemma setup_state_reg_q : forall tm q tape head,
  CPU.read_reg CPU.REG_Q (setup_state tm ((q, tape), head)) = q.
Proof.
  intros. unfold setup_state, CPU.read_reg, CPU.REG_Q. simpl.
  reflexivity.
Qed.

Lemma setup_state_reg_head : forall tm q tape head,
  CPU.read_reg CPU.REG_HEAD (setup_state tm ((q, tape), head)) = head.
Proof.
  intros. unfold setup_state, CPU.read_reg, CPU.REG_HEAD. simpl.
  reflexivity.
Qed.

Lemma setup_state_reg_pc : forall tm q tape head,
  CPU.read_reg CPU.REG_PC (setup_state tm ((q, tape), head)) = 0.
Proof.
  intros. unfold setup_state, CPU.read_reg, CPU.REG_PC. simpl.
  reflexivity.
Qed.

Lemma setup_state_reg_temp1 : forall tm q tape head,
  CPU.read_reg CPU.REG_TEMP1 (setup_state tm ((q, tape), head)) = UTM_Program.TAPE_START_ADDR.
Proof.
  intros. unfold setup_state, CPU.read_reg, CPU.REG_TEMP1. simpl.
  reflexivity.
Qed.

Lemma setup_state_reg_addr : forall tm q tape head,
  CPU.read_reg CPU.REG_ADDR (setup_state tm ((q, tape), head)) = UTM_Program.TAPE_START_ADDR + head.
Proof.
  intros. unfold setup_state, CPU.read_reg, CPU.REG_ADDR. simpl.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Bunker buster: fast proof for setup_state_program_prefix           *)
(* ----------------------------------------------------------------- *)

Ltac bunker_buster_setup_state_program_prefix :=
  intros tm q tape head Hprog Hrules;
  pose proof (setup_state_mem_structure tm ((q, tape), head) Hprog Hrules) as Hmem;
  rewrite Hmem;
  (* `setup_state_mem_structure` uses `let` bindings for `rules`/`tape`; reduce them. *)
  cbn [fst snd] in *;
  (* Drop the tape suffix: only the padded program/rules prefix matters. *)
  set (rules := UTM_Encode.encode_rules tm.(tm_rules)) in *;
  set (tape_ext :=
         if head <? length tape then tape
         else tape ++ repeat tm.(tm_blank) (S head - length tape)) in *;
    rewrite (firstn_app_le'
         (length program)
         (pad_to UTM_Program.TAPE_START_ADDR
      (pad_to UTM_Program.RULES_START_ADDR program ++ rules))
         tape_ext);
  [ exact (firstn_program_prefix Hprog rules)
  | (* Show the prefix is at least as long as the program. *)
      assert (Hinner_len : length program <= length (pad_to UTM_Program.RULES_START_ADDR program ++ rules))
        by (pose proof (length_pad_to_ge program UTM_Program.RULES_START_ADDR Hprog) as Hpad;
            rewrite app_length;
            lia);
      pose proof
        (length_pad_to_ge_base (pad_to UTM_Program.RULES_START_ADDR program ++ rules)
           UTM_Program.TAPE_START_ADDR) as Hge;
      lia ].

Lemma setup_state_program_prefix : forall tm q tape head,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  firstn (length program) (CPU.mem (setup_state tm ((q, tape), head))) = program.
Proof.
  bunker_buster_setup_state_program_prefix.
Qed.

Lemma setup_state_rules_window : forall tm q tape head,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
         (skipn UTM_Program.RULES_START_ADDR (CPU.mem (setup_state tm ((q, tape), head)))) =
    UTM_Encode.encode_rules tm.(tm_rules).
Proof.
  intros tm q tape head Hprog Hrules.
  assert (Hmem := setup_state_mem_structure tm ((q, tape), head) Hprog Hrules).
  rewrite Hmem.
  cbn [fst snd] in *.
  set (rules := UTM_Encode.encode_rules (tm_rules tm)).
  set (prefix :=
         pad_to UTM_Program.TAPE_START_ADDR
           (pad_to UTM_Program.RULES_START_ADDR program ++ rules)).
  set (tape_ext :=
         if head <? length tape then tape
         else tape ++ repeat tm.(tm_blank) (S head - length tape)).
  change
    (firstn (length rules)
       (skipn UTM_Program.RULES_START_ADDR (prefix ++ tape_ext)) = rules).
  rewrite skipn_app_le'.
  - rewrite firstn_app_le'.
    + subst prefix rules.
      apply firstn_rules_window; assumption.
    + rewrite skipn_length.
      subst prefix.
      pose proof
        (length_pad_to_ge_n
           (pad_to UTM_Program.RULES_START_ADDR program ++
            UTM_Encode.encode_rules (tm_rules tm))
           UTM_Program.TAPE_START_ADDR) as Hge.
      (* Hrules: length rules <= TAPE_START_ADDR - RULES_START_ADDR *)
      eapply Nat.le_trans.
      * subst rules. exact Hrules.
      * apply Nat.sub_le_mono_r. exact Hge.
  - subst prefix.
    eapply Nat.le_trans.
    + apply UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR.
    + apply length_pad_to_ge_n.
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

(* Full invariant relating CPU state to TM configuration *)
Definition inv_full (st : CPU.State) (tm : TM) (conf : TMConfig) : Prop :=
  let '((q, tape), head) := conf in
  CPU.read_reg CPU.REG_Q st = q /\
  CPU.read_reg CPU.REG_HEAD st = head /\
  CPU.read_reg CPU.REG_PC st = 0 /\
  tape_window_ok st tape /\
  firstn (length program) st.(CPU.mem) = program /\
  firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
         (skipn UTM_Program.RULES_START_ADDR st.(CPU.mem)) =
    UTM_Encode.encode_rules tm.(tm_rules) /\
  (* Additional invariants for execution *)
  CPU.read_reg CPU.REG_TEMP1 st = UTM_Program.TAPE_START_ADDR /\
  CPU.read_reg CPU.REG_ADDR st = UTM_Program.TAPE_START_ADDR + head.

Lemma inv_full_setup_state : forall tm conf,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  inv_full (setup_state tm conf) tm conf.
Proof.
  intros tm ((q, tape), head) Hprog Hrules.
  unfold inv_full. simpl.
  split.
  - exact (setup_state_reg_q tm q tape head).
  - split.
    + exact (setup_state_reg_head tm q tape head).
    + split.
      * exact (setup_state_reg_pc tm q tape head).
      * split.
        { exact (tape_window_ok_setup_state tm q tape head Hprog Hrules). }
        split.
        { exact (setup_state_program_prefix tm q tape head Hprog Hrules). }
        split.
        { exact (setup_state_rules_window tm q tape head Hprog Hrules). }
        split.
        { exact (setup_state_reg_temp1 tm q tape head). }
        { exact (setup_state_reg_addr tm q tape head). }
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

(* Specialised small-stepper for states whose memory prefix is the encoded
   program.  When explicit decoder hypotheses are available, rewrite with them
   instead of unfolding the program prefix; this keeps small goal states during
   timed builds. *)
Ltac step_fast :=
  unfold run1, CPU.step;
  (* Prefer explicit decoder hypotheses over unfolding the concrete program, so
     small symbolic goals avoid expensive [calc_bounds] calls. *)
  first
    [ match goal with
      | H : decode_instr ?s = _ |- context [decode_instr ?s] => rewrite H
      end
    (* If no hypothesis is available, compute the decoder result directly
       instead of triggering [calc_bounds] on the program prefix.  This keeps
       timed bridge builds from spending most of their budget in the fallback
       bound solver when stepping through short concrete traces. *)
    | lazymatch goal with
      | |- context [decode_instr ?s] =>
          let inst := eval vm_compute in (decode_instr s) in
          change (decode_instr s) with inst
      end
    | try rewrite decode_program_at_pc by calc_bounds ];
  cbn [CPU.read_reg CPU.mem CPU.regs CPU.cost];
  simpl.

Ltac step_n n :=
  lazymatch n with
  | 0 => cbn [run_n] in *
  | S ?n' =>
      cbn [run_n] in *;
      step_fast;
      step_n n'
  end.

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

(* Prevent large proof terms from repeatedly unfolding the small-step
   interpreter.  The structural lemmas above expose the only rewrites we
   rely on, so the operational definitions can remain opaque during the
   heavy FindRule proofs. *)
#[local] Opaque run_n decode_instr.

(* Make key definitions opaque to prevent expensive unfolding during proofs.
   This stops the unifier from expanding massive symbolic lists. *)
#[global] Opaque program.
#[global] Opaque pad_to.

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

(*Writing to a register never shrinks the register file. *)
Lemma length_write_reg_ge : forall r v st,
  length (CPU.write_reg r v st).(CPU.regs) >= length st.(CPU.regs).
Proof.
  intros r v st.
  unfold CPU.write_reg. simpl.
  (* After unfolding: firstn r (CPU.regs st) ++ [v] ++ skipn (S r) (CPU.regs st) *)
  set (regs := CPU.regs st).
  assert (Hlen: forall (l : list nat) n m,
    length (firstn n l ++ m :: skipn (S n) l) >= length l).
  { intros l. induction l as [|x xs IHxs]; intros n m.
    - destruct n; simpl; lia.
    - destruct n; simpl.
      + lia.
      + simpl in IHxs. specialize (IHxs n m). simpl. lia. }
  apply (Hlen regs r v).
Qed.

(* Stepping cannot shorten the register file. *)
Lemma length_step_ge : forall instr st,
  length (CPU.regs (CPU.step instr st)) >= length st.(CPU.regs).
Proof.
  intros instr st.
  unfold CPU.step.
  remember (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC st)) st) as st_pc eqn:Heq_st_pc.
  assert (Hlen_pc : length (CPU.regs st_pc) >= length st.(CPU.regs)).
  { subst st_pc. apply length_write_reg_ge. }
  clear Heq_st_pc.
  destruct instr; simpl.
  - (* LoadConst *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* LoadIndirect *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* StoreIndirect *) unfold CPU.write_mem; simpl; assumption.
  - (* CopyReg *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* AddConst *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* AddReg *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* SubReg *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* Jz: if zero, write_reg to st; otherwise st_pc *)
    destruct (Nat.eqb (CPU.read_reg rc st) 0).
    + apply length_write_reg_ge.
    + assumption.
  - (* Jnz: if zero, st_pc; otherwise write_reg to st *)
    destruct (Nat.eqb (CPU.read_reg rc st) 0).
    + assumption.
    + apply length_write_reg_ge.
  - (* Halt: returns st unchanged *)
    apply Nat.le_refl.
Qed.

(* Multi-step execution preserves or grows the register file length. *)
Lemma length_run_n_ge : forall st n,
  length (CPU.regs (run_n st n)) >= length st.(CPU.regs).
Proof.
  intros st n.
  revert st. (* Generalize st before induction so IH is universal *)
  induction n as [|n' IHn]; intros st.
  - (* Base case: n = 0 *)
    simpl. apply Nat.le_refl.
  - (* Inductive case: n = S n' *)
    simpl. (* run_n st (S n') = run_n (run1 st) n' *)
    (* IHn : forall st', length (run_n st' n') >= length st' *)
    (* Need: length (run_n (run1 st) n') >= length st *)
    assert (H1: length (CPU.regs (run1 st)) >= length (CPU.regs st)).
    { unfold run1. apply length_step_ge. }
    assert (H2: length (CPU.regs (run_n (run1 st) n')) >= length (CPU.regs (run1 st))).
    { apply IHn. }
    eapply Nat.le_trans; [exact H1 | exact H2].
Qed.

(* Axiom: The universal program only writes to registers 0-9.
   This is a structural property of the specific program being verified.
   All register operations (LoadConst, LoadIndirect, CopyReg, AddConst, AddReg, SubReg)
   use destination registers from {REG_PC=0, REG_Q=1, REG_SYM=3, REG_Q'=4, REG_ADDR=7, REG_TEMP1=8, REG_TEMP2=9}. *)


(* NOTE: This structural property (universal program only writes regs 0-9)
   is validated by Python VM tests in tests/test_utm_program_validation.py
   rather than formally proven in Coq due to the proof size/complexity.
   The axiom is safe because:
   1. All register operations in the program use fixed destination registers
   2. The destination set {0,1,3,4,7,8,9} ⊂ {0..9}
   3. Python VM execution confirms this property holds for all instructions *)


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

Lemma instr_at_pc_4 :
  nth 4 UTM_Program.program_instrs CPU.Halt =
  CPU.LoadIndirect CPU.REG_Q' CPU.REG_ADDR.
Proof.
  unfold UTM_Program.program_instrs. simpl. reflexivity.
Qed.

Lemma instr_at_pc_5 :
  nth 5 UTM_Program.program_instrs CPU.Halt =
  CPU.CopyReg CPU.REG_TEMP1 CPU.REG_Q.
Proof.
  unfold UTM_Program.program_instrs. simpl. reflexivity.
Qed.


Lemma check_transition_compose : forall s1 s2 s3 n1 n2,
  check_transition s1 s2 n1 = true ->
  check_transition s2 s3 n2 = true ->
  check_transition s1 s3 (n1 + n2) = true.
Proof.
  unfold check_transition. intros s1 s2 s3 n1 n2 H1 H2.
  apply state_eqb_true_iff in H1.
  apply state_eqb_true_iff in H2.
  rewrite run_n_add. rewrite H1. rewrite H2.
  apply state_eqb_refl.
Qed.

(* NOTE:
   The universal program [UTM_Program.program_instrs] is a looping interpreter.
   A single [tm_step] is not performed in a fixed constant number of CPU
   instructions for arbitrary machines/rule-sets.

   What we *do* prove here (admit-free) is the foundational isomorphism between
   a TM configuration and the CPU state produced by [setup_state]. *)

Theorem cpu_tm_isomorphism : forall tm conf,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  let st := setup_state tm conf in
  CPU.read_reg CPU.REG_Q st = fst (fst conf) /\
  CPU.read_reg CPU.REG_HEAD st = snd conf /\
  tape_window_ok st (snd (fst conf)).
Proof.
  intros tm conf Hprog Hrules.
  cbn.
  pose proof (inv_full_setup_state tm conf Hprog Hrules) as Hinv.
  destruct conf as [[q tape] head].
  unfold inv_full in Hinv. simpl in Hinv.
  destruct Hinv as (Hq & Hhead & _Hpc & Htape & _Hprog' & _Hrules' & _Htemp1 & _Haddr).
  exact (conj Hq (conj Hhead Htape)).
Qed.
