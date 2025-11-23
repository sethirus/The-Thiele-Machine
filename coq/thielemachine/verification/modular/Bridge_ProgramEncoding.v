(* ================================================================= *)
(* ThieleUniversalBridge Module: ProgramEncoding *)
(* Extracted from lines 201-350 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

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
