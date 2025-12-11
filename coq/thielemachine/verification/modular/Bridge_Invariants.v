(* ThieleUniversalBridge Module: Invariants *)
(* Extracted from lines 531-700 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

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
  - unfold setup_state; simpl.
    set (rules := UTM_Encode.encode_rules tm.(tm_rules)).
    set (mem0 := pad_to UTM_Program.RULES_START_ADDR program).
    assert (Hmem0_len : length mem0 = UTM_Program.RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; exact Hprog).
    assert (Hfit : length (mem0 ++ rules) <= UTM_Program.TAPE_START_ADDR).
    { rewrite app_length, Hmem0_len.
      assert (Heq : UTM_Program.TAPE_START_ADDR =
        UTM_Program.RULES_START_ADDR + (UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR))
        by (unfold UTM_Program.TAPE_START_ADDR, UTM_Program.RULES_START_ADDR; lia).
      rewrite Heq. apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules))
                        = UTM_Program.TAPE_START_ADDR)
      by (apply length_pad_to_ge; exact Hfit).
    assert (Hprefix :
      firstn (length program)
        ((pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      = firstn (length program)
          (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)))
      by (apply firstn_app_le'; rewrite Hmem1_len;
          apply (Nat.le_trans _ _ _ Hprog); exact UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR).
    eapply eq_trans; [exact Hprefix|].
    subst mem0. apply (firstn_program_prefix Hprog rules).
  - unfold setup_state; simpl.
    set (rules := UTM_Encode.encode_rules tm.(tm_rules)).
    set (mem0 := pad_to UTM_Program.RULES_START_ADDR program).
    assert (Hmem0_len : length mem0 = UTM_Program.RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; exact Hprog).
    assert (Hfit : length (mem0 ++ rules) <= UTM_Program.TAPE_START_ADDR).
    { rewrite app_length, Hmem0_len.
      assert (Heq : UTM_Program.TAPE_START_ADDR =
        UTM_Program.RULES_START_ADDR + (UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR))
        by (unfold UTM_Program.TAPE_START_ADDR, UTM_Program.RULES_START_ADDR; lia).
      rewrite Heq. apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules))
                        = UTM_Program.TAPE_START_ADDR)
      by (apply length_pad_to_ge; exact Hfit).
    assert (Hskip :
      skipn UTM_Program.RULES_START_ADDR
        ((pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      = skipn UTM_Program.RULES_START_ADDR
          (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      by (apply skipn_app_le'; rewrite Hmem1_len; exact UTM_Program.RULES_START_ADDR_le_TAPE_START_ADDR).
    assert (Hskip_first :
      firstn (length rules)
        (skipn UTM_Program.RULES_START_ADDR
                 ((pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape))
      = firstn (length rules)
          (skipn UTM_Program.RULES_START_ADDR
                   (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape))
      by (rewrite Hskip; reflexivity).
    assert (Hdrop :
      firstn (length rules)
        (skipn UTM_Program.RULES_START_ADDR
                 (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) ++ tape)
      = firstn (length rules)
          (skipn UTM_Program.RULES_START_ADDR
                 (pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules))))
      by (apply firstn_app_le'; rewrite skipn_length, Hmem1_len;
          apply (Nat.le_trans _ _ _ Hrules); lia).
    eapply eq_trans; [exact Hskip_first|].
    eapply eq_trans; [exact Hdrop|].
    subst mem0. apply (firstn_rules_window Hprog rules). exact Hrules.
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

