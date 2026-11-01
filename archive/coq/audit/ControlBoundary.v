(* Formalizes the fixed-rule obstruction discussed on the monograph's page. *)
From Coq Require Import List Arith Lia.
Import ListNotations.
Require Minimal.ThieleComplete Minimal.LiftMacro Minimal.CompleteHost.
Module T := Minimal.ThieleComplete.
Module L := Minimal.LiftMacro.
Module H := Minimal.CompleteHost.

Section OneRule.
Variable M : T.machine.
Variable f : T.m_state M -> T.m_state M.
Hypothesis one_rule : forall s i, T.m_step M s i = f s.

Lemma word_is_iteration : forall w s,
  T.run M w s = H.iter f (length w) s.
Proof.
  induction w as [|i w IH]; intro s; [reflexivity|].
  cbn; rewrite IH, one_rule.
  symmetry; apply H.iter_succ_from.
Qed.

Theorem fixed_words_commute : forall w v s,
  T.run M v (T.run M w s) = T.run M w (T.run M v s).
Proof.
  intros; rewrite !word_is_iteration, <-!H.iter_add, Nat.add_comm; reflexivity.
Qed.

Theorem one_rule_has_no_fixed_word_simulation : ~ inhabited (L.sim_base M).
Proof.
  intros [B].
  set (s := L.sb_load B 0 0).
  set (i := T.CINC T.RA).
  set (j := T.CDEC T.RA 5).
  assert (Hl : L.sb_live B s) by apply L.sb_load_live.
  assert (Hw : L.sb_window B s = (1,(0,0))) by apply L.sb_load_window.
  destruct (L.sb_sim B s i Hl) as [Wi Li].
  destruct (L.sb_sim B s j Hl) as [Wj Lj].
  destruct (L.sb_sim B (T.run M (L.sb_compile B i) s) j Li) as [Wij _].
  destruct (L.sb_sim B (T.run M (L.sb_compile B j) s) i Lj) as [Wji _].
  rewrite Wi,Hw in Wij; rewrite Wj,Hw in Wji.
  rewrite fixed_words_commute in Wij.
  rewrite Wji in Wij.
  unfold i,j in Wij; cbn in Wij; discriminate.
Qed.
End OneRule.

Print Assumptions word_is_iteration.
Print Assumptions fixed_words_commute.
Print Assumptions one_rule_has_no_fixed_word_simulation.
