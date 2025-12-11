(* ThieleUniversalBridge Module: SetupState *)
(* Extracted from lines 351-530 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

(* Dependencies noted for reference: Invariants *)
(* These are NOT imported to keep modules standalone for analysis *)

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
  let regs4 := set_nth regs3 CPU.REG_TEMP1 UTM_Program.TAPE_START_ADDR in
  let regs5 := set_nth regs4 CPU.REG_ADDR (UTM_Program.TAPE_START_ADDR + head) in
  let rules := UTM_Encode.encode_rules tm.(tm_rules) in
  let mem0 := pad_to UTM_Program.RULES_START_ADDR program in
  let mem1 := pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules) in
  {| CPU.regs := regs5; CPU.mem := mem1 ++ tape; CPU.cost := 0 |}.

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
  { apply (@nth_app_lt nat (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) tape n 0).
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
  { rewrite app_length. rewrite Hmem0_len.
    pose proof UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR as Hle.
    lia. }
  subst mem1.
  assert (Hmem1_len : length (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rrules))
                        = UTM_Program.TAPE_START_ADDR).
  { apply length_pad_to_ge. exact Hfit. }
  rewrite (firstn_skipn_app_exact (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rrules)) tape UTM_Program.TAPE_START_ADDR Hmem1_len).
Qed.

