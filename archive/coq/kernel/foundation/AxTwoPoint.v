(** AxTwoPoint: certification is the two-point axis.

    A machine of the book (one-bit record) is an axis machine over the
    two-point order false < true in which every claim stands for "true".
    This file proves that the book's four clauses are, one for one, the four
    clauses of the axis definition at that order:

      lift_base_iff     universal base            <->  axis base clause
      lift_toll_iff     exact toll                <->  axis toll clause
      lift_nonvac_iff   non-vacuity               <->  axis non-vacuity clause
      lift_earned_iff   earned record (given the base clause)
                                                  <->  axis earned clause
      ax_tc_two_point_iff   thiele_complete_with I  <->  ax_tc_with (lift_ai I)

    so the book's definition is the special case, and every theorem of the
    book about Thiele-complete machines is a theorem about the two-point axis.

    The earned clause is per move on the axis and per run for the bit.  They
    agree on the two-point order because the move that raises the bit is the
    last move of the run that first raises it. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxLatch AxComplete.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Definition lift_am (M : T.machine) : amachine bool two_pre :=
  mk_am bool two_pre (T.m_state M) (T.m_move M) (T.m_step M) (T.m_cost M) (T.m_record M).

Definition lift_ub {M : T.machine} (u : T.universal_base M)
  : T.universal_base (am_bare (lift_am M)) :=
  T.mk_ub (am_bare (lift_am M)) (T.ub_window u) (T.ub_live u) (T.ub_compile u)
    (T.ub_load u) (T.ub_load_window u) (T.ub_load_live u) (T.ub_sim u).

Definition lift_ai {M : T.machine} (I : T.thiele_interface M) : ax_interface (lift_am M) :=
  mk_axi bool two_pre (lift_am M) (lift_ub (T.ti_base I)) (T.ti_claim I) (T.ti_kind I)
    (T.ti_meaning I) (T.ti_check I) (T.ti_same I) (T.ti_clean I) (T.ti_ledger I)
    false (fun _ => true).

Lemma run_lift : forall M tr s, T.run M tr s = am_run (lift_am M) tr s.
Proof. intros M tr. induction tr as [| m tr IH]; intro s; simpl; auto. Qed.

Lemma run_keeps_true : forall M, (forall s m, T.m_record M s = true -> T.m_record M (T.m_step M s m) = true) ->
  forall tr s, T.m_record M s = true -> T.m_record M (T.run M tr s) = true.
Proof.
  intros M H tr. induction tr as [| m tr IH]; intros s Hs; simpl; [exact Hs |].
  apply IH. apply H. exact Hs.
Qed.

Lemma two_exit : forall x y : bool, ~ bp_le two_pre x y -> x = true /\ y = false.
Proof.
  intros x y H. destruct x, y; try (exfalso; apply H; unfold bp_le; simpl; reflexivity);
    split; reflexivity.
Qed.

Lemma two_not_le_false : forall x, ~ bp_le two_pre x false -> x = true.
Proof.
  intros x H. destruct x; [reflexivity |]. exfalso. apply H. unfold bp_le. reflexivity.
Qed.

Section Clauses.

Variable M : T.machine.
Variable I : T.thiele_interface M.

Lemma two_le_true_l : forall r, bp_le two_pre true r <-> r = true.
Proof. intro r. unfold bp_le. simpl. destruct r; simpl; split; auto. Qed.

Lemma two_le_iff : forall x y, bp_le two_pre x y <-> (x = true -> y = true).
Proof. intros x y. apply two_le. Qed.

Theorem lift_base_iff : T.universal_base_clause I <-> axc_base (lift_ai I).
Proof.
  unfold T.universal_base_clause, axc_base. simpl. split.
  - intros [H1 [H2 [H3 H4]]]. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
    intros s m. apply two_le_iff. apply H4.
  - intros [H1 [H2 [H3 H4]]]. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
    intros s m. apply (proj1 (two_le_iff _ _) (H4 s m)).
Qed.

Theorem lift_toll_iff : T.exact_toll_clause I <-> axc_toll (lift_ai I).
Proof. unfold T.exact_toll_clause, axc_toll. simpl. split; intro H; exact H. Qed.

Theorem lift_nonvac_iff : T.non_vacuity_clause I <-> axc_nonvac (lift_ai I).
Proof.
  unfold T.non_vacuity_clause, axc_nonvac. simpl. split.
  - intros [c [chk [cmt [crt [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]].
    exists c, chk, cmt, crt. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
    split; [| split; [exact H5 | exact H6]].
    intros a b. exact (iff_trans (two_le_true_l _) (H4 a b)).
  - intros [c [chk [cmt [crt [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]].
    exists c, chk, cmt, crt. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
    split; [| split; [exact H5 | exact H6]].
    intros a b. exact (iff_trans (iff_sym (two_le_true_l _)) (H4 a b)).
Qed.

(** The earned clauses agree, given the base clause. *)
Theorem lift_earned_iff : T.universal_base_clause I ->
  (T.earned_record_clause I <-> axc_earned (lift_ai I)).
Proof.
  intros Hbase. pose proof Hbase as [_ [_ [_ Hperm]]].
  unfold T.earned_record_clause, axc_earned. simpl. split.
  - intros [Hcl [Hch [Hs Hr]]].
    split; [exact Hcl |]. split; [| split; [exact Hs | exact Hr]].
    intros s0 tr m Hc0 Hex.
    unfold ax_exit_step in Hex.
    destruct (two_exit _ _ Hex) as [Hnext0 Hcur0].
    assert (Hnext : T.m_record M (T.m_step M (am_run (lift_am M) tr s0) m) = true) by exact Hnext0.
    assert (Hcur : T.m_record M (am_run (lift_am M) tr s0) = false) by exact Hcur0.
    assert (Hrun : T.m_record M (T.run M (tr ++ [m]) s0) = true).
    { rewrite T.run_app. simpl. rewrite run_lift. exact Hnext. }
    destruct (Hch s0 (tr ++ [m]) Hc0 Hrun)
      as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [Hk1 [Hk2 [Hk3 [Hck [Hsame [Hbef Haft]]]]]]]]]]]]]]].
    assert (Hpost : post = []).
    { destruct post as [| x post'] using rev_ind; [reflexivity |]. exfalso.
      replace (pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post' ++ [x])
        with ((pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post') ++ [x]) in Htr
        by (repeat first [rewrite <- app_assoc | progress simpl]; reflexivity).
      apply app_inj_tail in Htr as [Htr _].
      assert (Hup : T.m_record M (T.run M (tr) s0) = true).
      { rewrite Htr.
        replace (pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post')
          with ((pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt]) ++ post')
          by (repeat first [rewrite <- app_assoc | progress simpl]; reflexivity).
        rewrite T.run_app. apply (run_keeps_true M (fun s m0 => Hperm s m0)). exact Haft. }
      rewrite run_lift in Hup. rewrite Hup in Hcur. discriminate. }
    subst post.
    replace (pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: [])
      with ((pre ++ chk :: mid1 ++ cmt :: mid2) ++ [crt]) in Htr
      by (repeat first [rewrite <- app_assoc | progress simpl]; reflexivity).
    apply app_inj_tail in Htr as [Htr Hm]. subst crt.
    exists pre, c, chk, mid1, cmt, mid2.
    split; [exact Htr |]. split; [exact Hk1 |]. split; [exact Hk2 |].
    split; [exact Hk3 |]. split; [rewrite <- run_lift; exact Hck |].
    split; [intros t1 t2 H12; rewrite <- !run_lift; apply (Hsame t1 t2 H12) |].
    refine (conj _ (conj _ _)).
    + apply two_le_iff. intro H. discriminate (eq_trans (eq_sym H) Hcur).
    + exact (proj2 (two_le_true_l _) Hnext).
    + intros w _ Hw. apply (proj1 (two_le_true_l w)) in Hw. rewrite Hw.
      apply two_le_iff. intro. reflexivity.
  - intros [Hcl [Hex [Hs Hr]]].
    split; [exact Hcl |]. split; [| split; [exact Hs | exact Hr]].
    intros s0 tr Hc0 Hrec.
    assert (H0 : bp_le two_pre (T.m_record M s0) false)
      by (rewrite (Hcl s0 Hc0); apply bp_le_refl).
    assert (H1 : ~ bp_le two_pre (T.m_record M (am_run (lift_am M) tr s0)) false).
    { rewrite <- run_lift. rewrite Hrec. unfold bp_le. simpl. discriminate. }
    destruct (ax_first_exit (lift_ai I) tr s0 H0 H1) as [pre [m [post [Htr [Hle [Hexit Hnf]]]]]].
    destruct (Hex s0 pre m Hc0 Hexit)
      as [pre' [c [chk [mid1 [cmt [mid2 [Hpre [Hk1 [Hk2 [Hk3 [Hck [Hsame Hlub]]]]]]]]]]]].
    exists pre', c, chk, mid1, cmt, mid2, m, post.
    split; [rewrite Htr, Hpre; repeat first [rewrite <- app_assoc | progress simpl]; reflexivity |].
    split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
    split; [rewrite run_lift; exact Hck |].
    split; [intros t1 t2 H12; rewrite !run_lift; apply (Hsame t1 t2 H12) |].
    assert (Hl0 : (pre' ++ chk :: mid1 ++ cmt :: mid2) = pre) by (rewrite Hpre; reflexivity).
    assert (Hl1 : (pre' ++ chk :: mid1 ++ cmt :: mid2 ++ [m]) = pre ++ [m])
      by (rewrite Hpre; repeat first [rewrite <- app_assoc | progress simpl]; reflexivity).
    split.
    + refine (eq_trans (f_equal (fun l => T.m_record M (T.run M l s0)) Hl0) _).
      rewrite run_lift.
      assert (Hle2 : bp_le two_pre (T.m_record M (am_run (lift_am M) pre s0)) false) by exact Hle.
      destruct (T.m_record M (am_run (lift_am M) pre s0)) eqn:E; [| reflexivity].
      exfalso. unfold bp_le in Hle2. simpl in Hle2. discriminate.
    + refine (eq_trans (f_equal (fun l => T.m_record M (T.run M l s0)) Hl1) _).
      rewrite run_lift, am_run_snoc.
      apply two_not_le_false in Hnf. exact Hnf.
Qed.

Theorem ax_tc_two_point_iff : T.thiele_complete_with I <-> ax_tc_with (lift_ai I).
Proof.
  split.
  - intros [Hb [He [Ht Hn]]].
    split; [apply lift_base_iff; exact Hb |]. split; [apply lift_earned_iff; [exact Hb | exact He] |].
    split; [apply lift_toll_iff; exact Ht | apply lift_nonvac_iff; exact Hn].
  - intros [Hb [He [Ht Hn]]].
    assert (Hb' : T.universal_base_clause I) by (apply lift_base_iff; exact Hb).
    split; [exact Hb' |]. split; [apply lift_earned_iff; [exact Hb' | exact He] |].
    split; [apply lift_toll_iff; exact Ht | apply lift_nonvac_iff; exact Hn].
Qed.

End Clauses.

Print Assumptions lift_base_iff.
Print Assumptions lift_toll_iff.
Print Assumptions lift_nonvac_iff.
Print Assumptions lift_earned_iff.
Print Assumptions ax_tc_two_point_iff.
