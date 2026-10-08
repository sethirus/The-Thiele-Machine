(** LiftConverse: what the lifting needs of a base, and nothing less.

    LiftCore.v shows that every universal base lifts.  This file shows the
    premise is also exactly what a Thiele-complete machine carries, and that
    the cheap ways of failing the premise do fail.

      lift_reduct_universal    Every Thiele-complete machine, for any interface
                               it is Thiele-complete with, has a universal base
                               on its base moves alone (the moves whose kind is
                               KBase): the machine with the record moves
                               removed.  So a Thiele-complete machine is a
                               universal base plus an earned layer, and the
                               base is whatever universal base you like.
      lift_projection_run      In the other direction the lifted machine runs
                               its base: from a live state, a run of base moves
                               moves the base component exactly as the base
                               runs on its own.
      lift_finite_branching_not_complete
                               A base with finitely many successors of each
                               state (a fixed-program Turing machine, a finite
                               automaton, anything whose move set collapses to
                               finitely many effects at every state) is never
                               the base of a Thiele-complete machine, for any
                               interface at all.  Reason: from the loaded state
                               (1, (1, 0)) the instructions CDEC A j, for every
                               j, move to infinitely many different windows
                               (j, (0, 0)) in one move.  A universal base needs
                               infinitely many distinct moves.
      lift_canonical_nonvac_iff
                               With the canonical interface of the lift, the
                               non-vacuity clause holds exactly when the cap is
                               at least 1 and some claim is true at one loaded
                               start and false at another.

    No axioms and no unfinished proofs.                                                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
From Minimal Require Import LiftCore LiftPigeon.

(** * A Thiele-complete machine's base moves form a universal base *)

Section Reduct.

Variable M : T.machine.
Variable I : T.thiele_interface M.

(** The machine with only the base moves, free, with no record. *)
Definition lift_reduct : T.machine :=
  T.mk_machine (T.m_state M) {m : T.m_move M | T.ti_kind I m = T.KBase}
    (fun s m => T.m_step M s (proj1_sig m)) (fun _ => 0) (fun _ => false).

Definition lift_reduct_ub (HB : T.universal_base_clause I)
  : T.universal_base lift_reduct :=
  T.mk_ub lift_reduct (T.ub_window (T.ti_base I)) (T.ub_live (T.ti_base I))
    (fun i => exist _ (T.ub_compile (T.ti_base I) i) (proj1 HB i))
    (T.ub_load (T.ti_base I)) (T.ub_load_window (T.ti_base I))
    (T.ub_load_live (T.ti_base I))
    (fun s i Hl => T.ub_sim (T.ti_base I) s i Hl).

End Reduct.

Theorem lift_reduct_universal : forall M, T.thiele_complete M ->
  exists I : T.thiele_interface M, T.thiele_complete_with I /\
    inhabited (T.universal_base (lift_reduct M I)).
Proof.
  intros M [I HI]. exists I. split; [exact HI |].
  exact (inhabits (lift_reduct_ub M I (proj1 HI))).
Qed.

(** * The lifted machine runs its base *)

Section Projection.

Variable M0 : T.machine.
Variable LG : lift_lang (T.m_state M0).
Variable cap : nat.

Lemma lift_projection : forall (s : lift_lstate M0 LG) m, lift_ls_err s = false ->
  lift_ls_base (lift_step cap s (lift_LBase m)) = T.m_step M0 (lift_ls_base s) m /\
  lift_ls_err (lift_step cap s (lift_LBase m)) = false.
Proof.
  intros s m He. unfold lift_step. rewrite He. simpl. split; reflexivity.
Qed.

Theorem lift_projection_run : forall tr (s : lift_lstate M0 LG), lift_ls_err s = false ->
  lift_ls_base (lift_lrun cap (map (fun m => @lift_LBase M0 LG m) tr) s) = T.run M0 tr (lift_ls_base s) /\
  lift_ls_err (lift_lrun cap (map (fun m => @lift_LBase M0 LG m) tr) s) = false.
Proof.
  induction tr as [| m tr IH]; intros s He.
  - simpl. unfold lift_lrun. simpl. auto.
  - simpl map. rewrite lift_lrun_cons. destruct (lift_projection s m He) as [Hb He'].
    destruct (IH _ He') as [IH1 IH2]. split; [| exact IH2].
    rewrite IH1, Hb. reflexivity.
Qed.

End Projection.

(** * Finite branching defeats the premise *)

(** Each state has finitely many successors: the step at that state factors
    through a finite set of boxes of moves.  No decidability of equality of
    states is needed to say it. *)
Definition lift_finitely_branching (M0 : T.machine) : Prop :=
  forall s, exists N (idx : T.m_move M0 -> nat),
    (forall m, idx m < N) /\
    forall m m', idx m = idx m' -> T.m_step M0 s m = T.m_step M0 s m'.

Theorem lift_finite_branching_not_complete : forall M0 LG cap,
  lift_finitely_branching M0 -> ~ T.thiele_complete (lift_machine M0 LG cap).
Proof.
  intros M0 LG cap Hfb [I [Hbase [_ [Htoll _]]]].
  set (UL := T.ti_base I).
  set (s0 := T.ub_load UL 1 0).
  pose proof (T.ub_load_live UL 1 0) as Hl0.
  pose proof (T.ub_load_window UL 1 0) as Hw0.
  change (T.ub_window UL s0 = (1, (1, 0))) in Hw0.
  change (T.ub_live UL s0) in Hl0.
  destruct (Hfb (lift_ls_base s0)) as [N [idx [Hidx Hfac]]].
  set (mv := fun j => T.ub_compile UL (T.CDEC T.RA j)).
  assert (Hbm : forall j, exists b, mv j = lift_LBase b).
  { intro j. pose proof (proj1 Hbase (T.CDEC T.RA j)) as Hk.
    pose proof (proj1 Htoll (mv j)) as Hc. unfold T.record_move in Hc.
    fold UL in Hk. unfold mv in *. rewrite Hk in Hc.
    destruct (T.ub_compile UL (T.CDEC T.RA j)) eqn:E; simpl in Hc;
      try discriminate. exists m. reflexivity. }
  assert (Hwin : forall j, T.ub_window UL (lift_step cap s0 (mv j)) = (j, (0, 0))).
  { intro j. destruct (T.ub_sim UL s0 (T.CDEC T.RA j) Hl0) as [Hw _].
    change (T.ub_window UL (lift_step cap s0 (mv j))
            = T.cm_exec (T.CDEC T.RA j) (T.ub_window UL s0)) in Hw.
    rewrite Hw, Hw0. reflexivity. }
  set (f := fun j => match mv j with lift_LBase b => idx b | _ => 0 end).
  destruct (lift_pigeon (S N) f) as [i [j [Hij [Hj Hf]]]].
  - intros j Hj. unfold f. destruct (mv j); [| lia | lia | lia]. specialize (Hidx m). lia.
  - destruct (Hbm i) as [bi Hi]. destruct (Hbm j) as [bj Hjm].
    unfold f in Hf. rewrite Hi, Hjm in Hf.
    assert (Hs : lift_step cap s0 (mv i) = lift_step cap s0 (mv j)).
    { rewrite Hi, Hjm. unfold lift_step.
      destruct (lift_ls_err s0); [reflexivity |].
      simpl. rewrite (Hfac bi bj Hf). reflexivity. }
    pose proof (Hwin i) as Wi. pose proof (Hwin j) as Wj.
    rewrite Hs in Wi. rewrite Wi in Wj. injection Wj as Hij'. lia.
Qed.

(** * A base that forgets its state defeats the premise *)

(** A base with infinitely many moves can still fail: if the step ignores the
    state it is applied to (a base that jumps to the number its move names),
    then two runs that differ only in their first move, and end with the same
    move, end in the same state, so no window can tell INC A, INC A from
    INC B, INC A. *)
Definition lift_stateless (M0 : T.machine) : Prop :=
  forall b b' m, T.m_step M0 b m = T.m_step M0 b' m.

Lemma lift_stateless_two_moves : forall M0 LG cap, lift_stateless M0 ->
  forall (s : lift_lstate M0 LG) bA bB,
  lift_step cap (lift_step cap s (lift_LBase bA)) (lift_LBase bA)
  = lift_step cap (lift_step cap s (lift_LBase bB)) (lift_LBase bA).
Proof.
  intros M0 LG cap Hst [b v fs ch er mu ce] bA bB.
  destruct er; unfold lift_step; simpl; [reflexivity |].
  f_equal. apply Hst.
Qed.

Theorem lift_stateless_not_complete : forall M0 LG cap,
  lift_stateless M0 -> ~ T.thiele_complete (lift_machine M0 LG cap).
Proof.
  intros M0 LG cap Hst [I [Hbase [_ [Htoll _]]]].
  set (UL := T.ti_base I).
  set (s0 := T.ub_load UL 0 0).
  pose proof (T.ub_load_live UL 0 0) as Hl0.
  pose proof (T.ub_load_window UL 0 0) as Hw0.
  change (T.ub_window UL s0 = (1, (0, 0))) in Hw0.
  change (T.ub_live UL s0) in Hl0.
  assert (Hform : forall i, exists b, T.ub_compile UL i = lift_LBase b).
  { intro i. pose proof (proj1 Hbase i) as Hk.
    pose proof (proj1 Htoll (T.ub_compile UL i)) as Hc. unfold T.record_move in Hc.
    fold UL in Hk. rewrite Hk in Hc.
    destruct (T.ub_compile UL i) eqn:E; simpl in Hc; try discriminate.
    exists m. reflexivity. }
  destruct (Hform (T.CINC T.RA)) as [bA HA].
  destruct (Hform (T.CINC T.RB)) as [bB HB].
  set (mA := T.ub_compile UL (T.CINC T.RA)) in *.
  set (mB := T.ub_compile UL (T.CINC T.RB)) in *.
  set (sA := T.m_step (lift_machine M0 LG cap) s0 mA).
  set (sB := T.m_step (lift_machine M0 LG cap) s0 mB).
  destruct (T.ub_sim UL s0 (T.CINC T.RA) Hl0) as [W1 L1].
  destruct (T.ub_sim UL s0 (T.CINC T.RB) Hl0) as [V1 M1].
  destruct (T.ub_sim UL sA (T.CINC T.RA) L1) as [W2 L2].
  destruct (T.ub_sim UL sB (T.CINC T.RA) M1) as [V2 M2].
  assert (Heq : T.m_step (lift_machine M0 LG cap) sA mA
                = T.m_step (lift_machine M0 LG cap) sB mA).
  { unfold sA, sB. rewrite HB, HA.
    exact (lift_stateless_two_moves M0 LG cap Hst s0 bA bB). }
  change (T.ub_window UL (T.m_step (lift_machine M0 LG cap) sA mA)
          = T.cm_exec (T.CINC T.RA) (T.ub_window UL sA)) in W2.
  change (T.ub_window UL (T.m_step (lift_machine M0 LG cap) sB mA)
          = T.cm_exec (T.CINC T.RA) (T.ub_window UL sB)) in V2.
  rewrite Heq in W2. rewrite V2 in W2.
  change (T.ub_window UL sA = T.cm_exec (T.CINC T.RA) (T.ub_window UL s0)) in W1.
  change (T.ub_window UL sB = T.cm_exec (T.CINC T.RB) (T.ub_window UL s0)) in V1.
  rewrite W1, V1, Hw0 in W2. simpl in W2. discriminate W2.
Qed.

(** A universal base is never finitely branching: from the loaded state
    (1, (1, 0)) the instructions CDEC A j reach infinitely many windows. *)
Theorem lift_ub_not_finitely_branching : forall M0 (U : T.universal_base M0),
  ~ lift_finitely_branching M0.
Proof.
  intros M0 U Hfb.
  set (s0 := T.ub_load U 1 0).
  pose proof (T.ub_load_live U 1 0) as Hl0.
  pose proof (T.ub_load_window U 1 0) as Hw0.
  change (T.ub_live U s0) in Hl0. change (T.ub_window U s0 = (1, (1, 0))) in Hw0.
  destruct (Hfb s0) as [N [idx [Hidx Hfac]]].
  set (mv := fun j => T.ub_compile U (T.CDEC T.RA j)).
  assert (Hwin : forall j, T.ub_window U (T.m_step M0 s0 (mv j)) = (j, (0, 0))).
  { intro j. destruct (T.ub_sim U s0 (T.CDEC T.RA j) Hl0) as [Hw _].
    change (T.ub_window U (T.m_step M0 s0 (mv j)) = T.cm_exec (T.CDEC T.RA j) (T.ub_window U s0))
      in Hw. rewrite Hw, Hw0. reflexivity. }
  destruct (lift_pigeon N (fun j => idx (mv j))) as [i [j [Hij [Hj Hf]]]].
  - intros j Hj. apply Hidx.
  - pose proof (Hfac _ _ Hf) as Hs.
    pose proof (Hwin i) as Wi. pose proof (Hwin j) as Wj.
    rewrite Hs in Wi. rewrite Wi in Wj. injection Wj as Hij'. lia.
Qed.

(** In particular a machine with finitely many moves, a fixed program, is
    not a universal base. *)
Corollary lift_finite_moves_not_a_base : forall M0 N (idx : T.m_move M0 -> nat),
  (forall m, idx m < N) -> (forall m m', idx m = idx m' -> m = m') ->
  inhabited (T.universal_base M0) -> False.
Proof.
  intros M0 N idx Hb Hi [U]. apply (lift_ub_not_finitely_branching M0 U).
  intro s. exists N, idx. split; [exact Hb |]. intros m m' H. rewrite (Hi m m' H). reflexivity.
Qed.

(** * The canonical interface: non-vacuity is exactly the two premises *)

Section Canon.

Variable M0 : T.machine.
Variable LG : lift_lang (T.m_state M0).
Variable U : T.universal_base M0.

Theorem lift_canonical_nonvac_iff : forall cap,
  T.non_vacuity_clause (lift_interface M0 LG cap U) <->
  0 < cap /\ lift_nonvacuous U LG.
Proof.
  intro cap. split.
  - intros [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hya Hnb]]]]]]]]].
    destruct Hya as [a [b Hy]]. destruct Hnb as [a' [b' Hn]].
    assert (Hchk : chk = lift_LCheck c)
      by (destruct chk; simpl in Hk1; try discriminate; injection Hk1 as ->; reflexivity).
    assert (Hcmt : cmt = lift_LCommit c)
      by (destruct cmt; simpl in Hk2; try discriminate; injection Hk2 as ->; reflexivity).
    assert (Hcrt : crt = lift_LCertify)
      by (destruct crt; simpl in Hk3; try discriminate; reflexivity).
    split.
    + destruct cap as [| cap]; [| lia]. exfalso.
      pose proof (proj2 (Hiff a b) Hy) as Hr. rewrite Hchk, Hcmt, Hcrt in Hr.
      change (lift_ls_cert (lift_lrun 0 [lift_LCheck c; lift_LCommit c;
                                              lift_LCertify] (lift_load U a b))
              = true) in Hr.
      assert (Hk : lift_check_ok 0 (lift_load U a b) c = false).
      { unfold lift_check_ok. simpl. rewrite andb_false_iff. right. reflexivity. }
      rewrite lift_lrun_cons, (lift_step_check_fail M0 LG 0 (lift_load U a b) c
                            eq_refl Hk) in Hr.
      rewrite lift_run_err in Hr; [simpl in Hr; discriminate | reflexivity].
    + exists c. split; [exists a, b; exact Hy | exists a', b'; exact Hn].
  - intros [Hcap Hnv]. apply lift_nonvac_clause; assumption.
Qed.

End Canon.

Print Assumptions lift_reduct_universal.
Print Assumptions lift_projection_run.
Print Assumptions lift_finite_branching_not_complete.
Print Assumptions lift_stateless_not_complete.
Print Assumptions lift_ub_not_finitely_branching.
Print Assumptions lift_finite_moves_not_a_base.
Print Assumptions lift_canonical_nonvac_iff.
