(** TCDeps.v: which clauses of Thiele-complete each consequence
    really uses. Each theorem below restates a result of
    minimal/ThieleComplete.v / ThieleCompleteWindow.v with ONLY the named
    sub-clauses as hypotheses and re-proves it. If a clause were needed,
    the proof would not go through. Sub-clause names:
      a1 compiled moves are KBase      a2 loads are clean
      a3 base moves record-blind       a4 record permanent
      b1 clean -> record down          b2 earned chain on every raise
      b3 checker soundness             b4 meaning kept while unchanged
      c1 cost = record_move            c2 ledger adds cost
      d  non-vacuity about a claim                                         *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.ThieleCompleteWindow.

Section Deps.
Variable M : machine.
Variable I : thiele_interface M.

Definition a1 := forall i, ti_kind I (ub_compile (ti_base I) i) = KBase.
Definition a2 := forall a b, ti_clean I (load I a b).
Definition a3 := forall s m, ti_kind I m = KBase -> m_record M (m_step M s m) = m_record M s.
Definition a4 := forall s m, m_record M s = true -> m_record M (m_step M s m) = true.
Definition b1 := forall s, ti_clean I s -> m_record M s = false.
Definition b2 := forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true -> earned_chain I s0 tr.
Definition b3 := forall s c, ti_check I s c = true -> ti_meaning I c s.
Definition b4 := forall c s s', ti_same I c s s' -> ti_meaning I c s -> ti_meaning I c s'.
Definition c1 := forall m, m_cost M m = record_move I m.
Definition c2 := forall s m, ti_ledger I (m_step M s m) = ti_ledger I s + m_cost M m.
Definition d := non_vacuity_clause I.

Lemma clauses_split : thiele_complete_with I <->
  a1 /\ a2 /\ a3 /\ a4 /\ b1 /\ b2 /\ b3 /\ b4 /\ c1 /\ c2 /\ d.
Proof.
  unfold thiele_complete_with, universal_base_clause, earned_record_clause, exact_toll_clause.
  unfold a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, d. tauto.
Qed.

(* tc-consequences (1), toll half: a3 + c1. *)
Theorem dep_toll : a3 -> c1 -> obeys_toll M.
Proof.
  intros H3 Hc s m H0 H1. rewrite Hc. unfold record_move.
  destruct (ti_kind I m) eqn:Hk; try lia. rewrite (H3 s m Hk) in H1. congruence.
Qed.

(* tc-consequences (3), count half: b2 ONLY (no price clause). *)
Theorem dep_three_moves : b2 -> forall s0 tr, ti_clean I s0 ->
  m_record M (run M tr s0) = true -> record_moves I tr >= 3.
Proof.
  intros Hch s0 tr H0 H1.
  destruct (Hch s0 tr H0 H1)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [Hk1 [Hk2 [Hk3 _]]]]]]]]]]]].
  rewrite Htr. repeat (rewrite record_moves_app; simpl).
  unfold record_move. rewrite Hk1, Hk2, Hk3. lia.
Qed.

(* tc-consequences (3), ledger half: b2 + c1 + c2. *)
Theorem dep_three_ledger : b2 -> c1 -> c2 -> forall s0 tr, ti_clean I s0 ->
  m_record M (run M tr s0) = true -> ti_ledger I (run M tr s0) >= ti_ledger I s0 + 3.
Proof.
  intros Hch Hc Hl s0 tr H0 H1.
  pose proof (dep_three_moves Hch s0 tr H0 H1).
  rewrite (ledger_counts_record_moves M I (conj Hc Hl)). lia.
Qed.

(* committed_claim_holds: b2 + b3 + b4. *)
Theorem dep_committed : b2 -> b3 -> b4 -> forall s0 tr, ti_clean I s0 ->
  m_record M (run M tr s0) = true ->
  exists pre c chk mid1 cmt rest,
    tr = pre ++ chk :: mid1 ++ cmt :: rest /\
    ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\
    ti_meaning I c (run M pre s0) /\ ti_meaning I c (run M (pre ++ chk :: mid1) s0).
Proof.
  intros Hchain Hsound Hresp s0 tr H0 H1.
  destruct (Hchain s0 tr H0 H1)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post
         [Htr [Hk1 [Hk2 [_ [Hck [Hsame _]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, (mid2 ++ crt :: post).
  split; [exact Htr |]. split; [exact Hk1 |]. split; [exact Hk2 |].
  assert (Hm : ti_meaning I c (run M pre s0)) by (apply Hsound; exact Hck).
  split; [exact Hm |].
  apply (Hresp c (run M pre s0)); [apply (Hsame mid1 []); rewrite app_nil_r; reflexivity
                                  | exact Hm].
Qed.

(* check_can_fail: b3 + d. *)
Theorem dep_check_can_fail : b3 -> d ->
  exists a b chk c, ti_kind I chk = KCheck c /\
    ti_check I (load I a b) c = false /\ ~ ti_meaning I c (load I a b).
Proof.
  intros Hsound Hnv.
  destruct Hnv as [c [chk [_ [_ [Hk1 [_ [_ [_ [_ [a [b Hno]]]]]]]]]]].
  exists a, b, chk, c. split; [exact Hk1 |]. split; [| exact Hno].
  destruct (ti_check I (load I a b) c) eqn:E; [| reflexivity].
  exfalso. apply Hno, Hsound, E.
Qed.

(* some_run_certifies: a2 + d. *)
Theorem dep_some_run : a2 -> d ->
  exists a b tr, ti_clean I (load I a b) /\ m_record M (run M tr (load I a b)) = true.
Proof.
  intros Hclean Hnv.
  destruct Hnv as [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hyes]] _]]]]]]]]].
  exists a, b, [chk; cmt; crt]. split; [apply Hclean |]. apply Hiff, Hyes.
Qed.

(* only_certify_raises: a4 + b2. *)
Theorem dep_only_certify : a4 -> b2 -> forall s0 tr m, ti_clean I s0 ->
  m_record M (run M tr s0) = false -> m_record M (m_step M (run M tr s0) m) = true ->
  ti_kind I m = KCertify.
Proof.
  intros Hperm Hchain s0 tr m H0 Hdown Hup.
  assert (Hstay : forall l s, m_record M s = true -> m_record M (run M l s) = true)
    by (induction l; intros; simpl; auto).
  assert (Hrun : m_record M (run M (tr ++ [m]) s0) = true) by (rewrite run_app; exact Hup).
  destruct (Hchain s0 (tr ++ [m]) H0 Hrun)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post
         [Htr [_ [_ [Hk3 [_ [_ [Hbefore Hafter]]]]]]]]]]]]]]].
  set (A := pre ++ chk :: mid1 ++ cmt :: mid2) in *.
  assert (HA : pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post = A ++ crt :: post)
    by (unfold A; list_eq).
  assert (HB : pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt] = A ++ [crt])
    by (unfold A; list_eq).
  rewrite HA in Htr. rewrite HB in Hafter.
  induction post as [| x post' _] using rev_ind.
  - apply app_inj_tail in Htr as [_ ->]. exact Hk3.
  - exfalso.
    replace (A ++ crt :: post' ++ [x]) with ((A ++ crt :: post') ++ [x]) in Htr by list_eq.
    apply app_inj_tail in Htr as [Htr _]. rewrite Htr in Hdown.
    replace (A ++ crt :: post') with ((A ++ [crt]) ++ post') in Hdown by list_eq.
    rewrite run_app, (Hstay post' _ Hafter) in Hdown. discriminate.
Qed.

(* The neutral form of only_certify_raises needs a3 alone, no clean start,
   no chain: the raising move is not a base move. *)
Theorem dep_raise_not_base : a3 -> forall s m,
  m_record M s = false -> m_record M (m_step M s m) = true -> ti_kind I m <> KBase.
Proof. intros H3 s m H0 H1 Hk. rewrite (H3 s m Hk), H0 in H1. discriminate. Qed.

(* complete_has_free_move: a1 + c1. *)
Theorem dep_free_move : a1 -> c1 -> exists m, m_cost M m = 0.
Proof.
  intros Hk Hc. exists (ub_compile (ti_base I) (CINC RA)). rewrite Hc.
  unfold record_move. rewrite Hk. reflexivity.
Qed.

(* one_move_record_excluded: a2 + b2. *)
Theorem dep_one_move : a2 -> b2 ->
  ~ exists m : m_move M, forall s, m_record M (m_step M s m) = true.
Proof.
  intros Hclean Hchain [m Hm].
  destruct (Hchain (load I 0 0) [m] (Hclean 0 0) (Hm _))
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr _]]]]]]]]].
  apply (f_equal (@length _)) in Htr. simpl in Htr.
  rewrite !app_length in Htr. simpl in Htr. rewrite app_length in Htr. simpl in Htr. lia.
Qed.

(* Window: every window printed: a1 + a2 + a3 + b1 + c1 + c2 (no b2..b4, no d). *)
Theorem dep_every_window : a1 -> a2 -> a3 -> b1 -> c1 -> c2 ->
  forall s : m_state M, exists a b m,
    ti_kind I m = KBase /\ m_cost M m = 0 /\
    ub_window (ti_base I) (m_step M (load I a b) m) = ub_window (ti_base I) s /\
    m_record M (m_step M (load I a b) m) = false /\
    ti_ledger I (m_step M (load I a b) m) = ti_ledger I (load I a b).
Proof.
  intros Hk Hclean Hbase Hcl0 Hcost Hled s.
  destruct (ub_window (ti_base I) s) as [pc [x y]] eqn:Hw.
  exists (S x), y, (ub_compile (ti_base I) (CDEC RA pc)).
  assert (Hkm : ti_kind I (ub_compile (ti_base I) (CDEC RA pc)) = KBase) by apply Hk.
  assert (Hc0 : m_cost M (ub_compile (ti_base I) (CDEC RA pc)) = 0)
    by (rewrite Hcost; unfold record_move; rewrite Hkm; reflexivity).
  split; [exact Hkm |]. split; [exact Hc0 |]. split.
  - unfold load.
    destruct (ub_sim (ti_base I) (ub_load (ti_base I) (S x) y) (CDEC RA pc)
                (ub_load_live (ti_base I) (S x) y)) as [Hs _].
    rewrite Hs, ub_load_window. reflexivity.
  - split; [rewrite (Hbase _ _ Hkm); apply Hcl0, Hclean |]. rewrite Hled, Hc0. lia.
Qed.

End Deps.

Print Assumptions clauses_split.
Print Assumptions dep_toll.
Print Assumptions dep_three_moves.
Print Assumptions dep_three_ledger.
Print Assumptions dep_committed.
Print Assumptions dep_check_can_fail.
Print Assumptions dep_some_run.
Print Assumptions dep_only_certify.
Print Assumptions dep_raise_not_base.
Print Assumptions dep_free_move.
Print Assumptions dep_one_move.
Print Assumptions dep_every_window.
