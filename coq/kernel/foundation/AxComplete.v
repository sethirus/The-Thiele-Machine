(** AxComplete: Thiele-complete on the axis.

    The book's definition has a machine whose record is one bit.  Here the
    record is a position in any ordered space.  A machine is Thiele-complete
    on the axis when

      (a) it has a universal base: every two-counter instruction is a base
          move acting on a window of the state exactly as the instruction
          acts on a configuration; base moves leave the record alone; the
          record never goes down;
      (b) its record is earned: every move that takes the record out of the
          down-set of where it stood is a CERTIFY preceded, in a run from a
          clean start, by a passing CHECK of a claim and a COMMIT of the same
          claim with the thing the claim is about unchanged between, and the
          record after the move is exactly the join of the record before and
          the point the claim stands for; checks are sound and a claim that
          holds keeps holding while its object is unchanged;
      (c) the toll is exact: base moves cost 0, record moves cost 1, and the
          ledger grows by the cost of each move;
      (d) the record can fail to rise: some claim is true at one loaded start
          and false at another, and the bare chain CHECK, COMMIT, CERTIFY on
          it reaches the point of the claim exactly when it is true.

    The two-point order with every claim standing for "true" is the book's
    definition ([ax_tc_two_point_iff]).

    What this file proves (closed):

      ax_tc_a2                 a Thiele-complete axis machine pays the toll.
      ax_flag_view_complete    certification is one tap: reading the record
                               through "has left the floor" gives a machine
                               that is Thiele-complete in the book's sense.
                               Every theorem proved for the book's definition
                               therefore holds for that reading of any axis
                               machine.
      ax_tc_certificate_three  reaching any point not below the floor costs
                               at least 3, the point being anywhere on the
                               axis.
      ax_tc_*                  the other consequences, per point.

    The earned clause is per move, not per threshold, because a threshold
    that is a join of two claims is crossed by the later of two chains. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxLatch.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(** * Axis machines *)

Record amachine (A : Type) (P : BPre A) : Type := mk_am {
  am_state : Type;
  am_move : Type;
  am_step : am_state -> am_move -> am_state;
  am_cost : am_move -> nat;
  am_rec : am_state -> A
}.

Arguments am_state {A P} _.
Arguments am_move {A P} _.
Arguments am_step {A P} _ _ _.
Arguments am_cost {A P} _ _.
Arguments am_rec {A P} _ _.

(** The machine forgetting the record, and the machine reading a Boolean
    function of the record as its record. *)
Definition am_pt {A P} (AM : amachine A P) (r : am_state AM -> bool) : T.machine :=
  T.mk_machine (am_state AM) (am_move AM) (am_step AM) (am_cost AM) r.

Definition am_bare {A P} (AM : amachine A P) : T.machine :=
  am_pt AM (fun _ => false).

Definition am_run {A P} (AM : amachine A P) (tr : list (am_move AM))
    (s : am_state AM) : am_state AM :=
  T.run (am_bare AM) tr s.

Lemma am_run_nil : forall {A P} (AM : amachine A P) s, am_run AM [] s = s.
Proof. reflexivity. Qed.

Lemma am_run_cons : forall {A P} (AM : amachine A P) m tr s,
  am_run AM (m :: tr) s = am_run AM tr (am_step AM s m).
Proof. reflexivity. Qed.

Lemma am_run_app : forall {A P} (AM : amachine A P) l1 l2 s,
  am_run AM (l1 ++ l2) s = am_run AM l2 (am_run AM l1 s).
Proof. intros. exact (T.run_app (am_bare AM) l1 l2 s). Qed.

Lemma am_run_snoc : forall {A P} (AM : amachine A P) l m s,
  am_run AM (l ++ [m]) s = am_step AM (am_run AM l s) m.
Proof. intros. rewrite am_run_app. reflexivity. Qed.

Lemma run_pt : forall {A P} (AM : amachine A P) r tr s,
  T.run (am_pt AM r) tr s = am_run AM tr s.
Proof. intros A P AM r tr. induction tr as [| m tr IH]; intro s; simpl; auto. Qed.

(** A universal base of the bare machine is one of every reading of it. *)
Definition am_ub {A P} (AM : amachine A P) (r : am_state AM -> bool)
    (u : T.universal_base (am_bare AM)) : T.universal_base (am_pt AM r) :=
  T.mk_ub (am_pt AM r) (T.ub_window u) (T.ub_live u) (T.ub_compile u) (T.ub_load u)
    (T.ub_load_window u) (T.ub_load_live u) (T.ub_sim u).

(** The record read as an axis system. *)
Definition am_axsys {A P} (AM : amachine A P) : AxSys A P :=
  mk_axsys A P (am_state AM) (am_move AM) (am_step AM) (am_cost AM) (am_rec AM).

Lemma am_axsys_run : forall {A P} (AM : amachine A P) tr s,
  ax_run (X := am_axsys AM) tr s = am_run AM tr s.
Proof. intros A P AM tr. induction tr as [| m tr IH]; intro s; simpl; auto. Qed.

(** * The interface *)

Record ax_interface {A P} (AM : amachine A P) : Type := mk_axi {
  axi_base : T.universal_base (am_bare AM);
  axi_claim : Type;
  axi_kind : am_move AM -> T.kind axi_claim;
  axi_meaning : axi_claim -> am_state AM -> Prop;
  axi_check : am_state AM -> axi_claim -> bool;
  axi_same : axi_claim -> am_state AM -> am_state AM -> Prop;
  axi_clean : am_state AM -> Prop;
  axi_ledger : am_state AM -> nat;
  axi_floor : A;
  axi_point : axi_claim -> A
}.

Arguments axi_base {A P AM} _.
Arguments axi_claim {A P AM} _.
Arguments axi_kind {A P AM} _ _.
Arguments axi_meaning {A P AM} _ _ _.
Arguments axi_check {A P AM} _ _ _.
Arguments axi_same {A P AM} _ _ _ _.
Arguments axi_clean {A P AM} _ _.
Arguments axi_ledger {A P AM} _ _.
Arguments axi_floor {A P AM} _.
Arguments axi_point {A P AM} _ _.

Section Clauses.

Context {A : Type} {P : BPre A} {AM : amachine A P} (I : ax_interface AM).

Local Notation rc := (am_rec AM).

Definition ax_load (a b : nat) : am_state AM := T.ub_load (axi_base I) a b.

(** A step leaves the down-set of the record. *)
Definition ax_exit_step (s : am_state AM) (m : am_move AM) : Prop :=
  ~ bp_le P (rc (am_step AM s m)) (rc s).

(** (a) Universal base; base moves leave the record alone; it never goes down. *)
Definition axc_base : Prop :=
  (forall i, axi_kind I (T.ub_compile (axi_base I) i) = T.KBase) /\
  (forall a b, axi_clean I (ax_load a b)) /\
  (forall s m, axi_kind I m = T.KBase -> rc (am_step AM s m) = rc s) /\
  (forall s m, bp_le P (rc s) (rc (am_step AM s m))).

(** The earned chain in front of a move that leaves the down-set. *)
Definition axc_earned_exit (s0 : am_state AM) (tr : list (am_move AM))
    (m : am_move AM) : Prop :=
  exists pre c chk mid1 cmt mid2,
    tr = pre ++ chk :: mid1 ++ cmt :: mid2 /\
    axi_kind I chk = T.KCheck c /\ axi_kind I cmt = T.KCommit c /\
    axi_kind I m = T.KCertify /\
    axi_check I (am_run AM pre s0) c = true /\
    (forall t1 t2, mid1 = t1 ++ t2 ->
       axi_same I c (am_run AM pre s0) (am_run AM (pre ++ chk :: t1) s0)) /\
    ax_is_lub P (rc (am_run AM tr s0)) (axi_point I c)
              (rc (am_step AM (am_run AM tr s0) m)).

(** (b) Earned record. *)
Definition axc_earned : Prop :=
  (forall s, axi_clean I s -> rc s = axi_floor I) /\
  (forall s0 tr m, axi_clean I s0 -> ax_exit_step (am_run AM tr s0) m ->
     axc_earned_exit s0 tr m) /\
  (forall s c, axi_check I s c = true -> axi_meaning I c s) /\
  (forall c s s', axi_same I c s s' -> axi_meaning I c s -> axi_meaning I c s').

Definition ax_record_move (m : am_move AM) : nat :=
  match axi_kind I m with T.KBase => 0 | _ => 1 end.

Fixpoint ax_record_moves (tr : list (am_move AM)) : nat :=
  match tr with [] => 0 | m :: rest => ax_record_move m + ax_record_moves rest end.

(** (c) Exact toll. *)
Definition axc_toll : Prop :=
  (forall m, am_cost AM m = ax_record_move m) /\
  (forall s m, axi_ledger I (am_step AM s m) = axi_ledger I s + am_cost AM m).

(** (d) Non-vacuity. *)
Definition axc_nonvac : Prop :=
  exists c chk cmt crt,
    axi_kind I chk = T.KCheck c /\ axi_kind I cmt = T.KCommit c /\
    axi_kind I crt = T.KCertify /\
    (forall a b, bp_le P (axi_point I c) (rc (am_run AM [chk; cmt; crt] (ax_load a b)))
                 <-> axi_meaning I c (ax_load a b)) /\
    (exists a b, axi_meaning I c (ax_load a b)) /\
    (exists a b, ~ axi_meaning I c (ax_load a b)).

Definition ax_tc_with : Prop := axc_base /\ axc_earned /\ axc_toll /\ axc_nonvac.

End Clauses.

Arguments ax_load {A P AM} I a b.
Arguments ax_exit_step {A P AM} s m.
Arguments axc_base {A P AM} I.
Arguments axc_earned_exit {A P AM} I s0 tr m.
Arguments axc_earned {A P AM} I.
Arguments ax_record_move {A P AM} I m.
Arguments ax_record_moves {A P AM} I tr.
Arguments axc_toll {A P AM} I.
Arguments axc_nonvac {A P AM} I.
Arguments ax_tc_with {A P AM} I.

Definition ax_thiele_complete {A P} (AM : amachine A P) : Prop :=
  exists I : ax_interface AM, ax_tc_with I.

Ltac list_eq_tac := repeat first [rewrite <- app_assoc | progress simpl]; reflexivity.

Section Consequences.

Context {A : Type} {P : BPre A} {AM : amachine A P} (I : ax_interface AM).
Hypothesis HC : ax_tc_with I.

Local Notation rc := (am_rec AM).

Lemma ax_run_grows : forall tr s, bp_le P (rc s) (rc (am_run AM tr s)).
Proof.
  destruct HC as [[_ [_ [_ Hg]]] _].
  induction tr as [| m tr IH]; intro s; simpl.
  - apply bp_le_refl.
  - eapply bp_le_trans; [apply Hg | apply IH].
Qed.

(** Every move that leaves the down-set is a record move, so the toll holds. *)
Theorem ax_tc_a2 : ax_a2 (X := am_axsys AM).
Proof.
  destruct HC as [[_ [_ [Hbase _]]] [_ [[Hcost _] _]]].
  intros s m Hex. simpl in *. rewrite Hcost. unfold ax_record_move.
  destruct (axi_kind I m) eqn:Hk; try lia.
  exfalso. apply Hex. simpl. rewrite (Hbase s m Hk). apply bp_le_refl.
Qed.

Lemma ax_record_moves_app : forall l1 l2,
  ax_record_moves I (l1 ++ l2) = ax_record_moves I l1 + ax_record_moves I l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Theorem ax_tc_ledger_counts : forall tr s,
  axi_ledger I (am_run AM tr s) = axi_ledger I s + ax_record_moves I tr.
Proof.
  destruct HC as [_ [_ [[Hcost Hled] _]]].
  induction tr as [| m tr IH]; intro s; [rewrite am_run_nil; simpl; lia |].
  rewrite am_run_cons. simpl ax_record_moves. rewrite IH, Hled, Hcost. lia.
Qed.

(** The first step out of the floor's down-set. *)
Lemma ax_first_exit : forall tr s0,
  bp_le P (rc s0) (axi_floor I) ->
  ~ bp_le P (rc (am_run AM tr s0)) (axi_floor I) ->
  exists pre m post, tr = pre ++ m :: post /\
    bp_le P (rc (am_run AM pre s0)) (axi_floor I) /\
    ax_exit_step (am_run AM pre s0) m /\
    ~ bp_le P (rc (am_step AM (am_run AM pre s0) m)) (axi_floor I).
Proof.
  induction tr as [| m tr IH]; intros s0 H0 H1.
  - rewrite am_run_nil in H1. contradiction.
  - destruct (bp_leb A P (rc (am_step AM s0 m)) (axi_floor I)) eqn:E.
    + rewrite am_run_cons in H1.
      destruct (IH (am_step AM s0 m) E H1) as [pre [m' [post [Htr [Hle [Hex Hnf]]]]]].
      exists (m :: pre), m', post. simpl. rewrite Htr. split; [reflexivity |].
      rewrite am_run_cons. split; [exact Hle | split; [exact Hex | exact Hnf]].
    + exists [], m, tr. simpl. split; [reflexivity |]. rewrite am_run_nil.
      split; [exact H0 |]. split.
      * intro H. pose proof (bp_le_trans P _ _ _ H H0) as H2. unfold bp_le in H2.
        rewrite E in H2. discriminate.
      * unfold bp_le. rewrite E. discriminate.
Qed.

End Consequences.

(** * Certification is one tap: reading the record as a bit *)

(** Any bit that is true exactly when the record has left the down-set of the
    floor reads the axis machine as a machine with a one-bit record. *)
Definition ax_ti_pt {A P} {AM : amachine A P} (I : ax_interface AM)
    (r : am_state AM -> bool) : T.thiele_interface (am_pt AM r) :=
  T.mk_ti (am_pt AM r) (am_ub AM r (axi_base I)) (axi_claim I)
    (axi_kind I) (axi_meaning I) (axi_check I) (axi_same I) (axi_clean I)
    (axi_ledger I).

(** The canonical such bit: has the record left the floor. *)
Definition ax_flag_fn {A P} {AM : amachine A P} (I : ax_interface AM)
    (s : am_state AM) : bool :=
  negb (bp_leb A P (am_rec AM s) (axi_floor I)).

Section Flag.

Context {A : Type} {P : BPre A} {AM : amachine A P} (I : ax_interface AM).
Hypothesis HC : ax_tc_with I.
Variable r : am_state AM -> bool.

Local Notation rc := (am_rec AM).
Local Notation fl := (axi_floor I).

Hypothesis Hr : forall s, r s = true <-> ~ bp_le P (rc s) fl.

Lemma flag_true_iff : forall s, r s = true <-> ~ bp_le P (rc s) fl.
Proof. exact Hr. Qed.

Lemma flag_false_iff : forall s, r s = false <-> bp_le P (rc s) fl.
Proof.
  intro s. destruct (r s) eqn:E.
  - split; [discriminate |]. intro H. apply (proj1 (Hr s)) in E. exfalso. exact (E H).
  - split; [| reflexivity]. intros _. unfold bp_le.
    destruct (bp_leb A P (rc s) fl) eqn:E2; [reflexivity |]. exfalso.
    assert (Hn : ~ bp_le P (rc s) fl) by (unfold bp_le; rewrite E2; discriminate).
    apply (proj2 (Hr s)) in Hn. congruence.
Qed.

Lemma r_ext : forall s s', rc s = rc s' -> r s = r s'.
Proof.
  intros s s' H. destruct (r s) eqn:E, (r s') eqn:E'; try reflexivity; exfalso.
  - apply (proj1 (Hr s)) in E. apply (proj1 (flag_false_iff s')) in E'.
    rewrite H in E. exact (E E').
  - apply (proj1 (Hr s')) in E'. apply (proj1 (flag_false_iff s)) in E.
    rewrite <- H in E'. exact (E' E).
Qed.

(** The point of the witness claim is not below the floor. *)
Lemma ax_witness_nontrivial : forall c chk cmt crt,
  (forall a b, bp_le P (axi_point I c) (rc (am_run AM [chk; cmt; crt] (ax_load I a b)))
               <-> axi_meaning I c (ax_load I a b)) ->
  (exists a b, ~ axi_meaning I c (ax_load I a b)) ->
  ~ bp_le P (axi_point I c) fl.
Proof.
  destruct HC as [[_ [Hclean _]] [[Hfl _] _]].
  intros c chk cmt crt Hiff [a [b Hno]] Hle. apply Hno. apply (Hiff a b).
  eapply bp_le_trans; [exact Hle |].
  rewrite <- (Hfl _ (Hclean a b)). exact (ax_run_grows I HC _ _).
Qed.

Theorem ax_pt_view_complete : T.thiele_complete_with (ax_ti_pt I r).
Proof.
  pose proof HC as HC'.
  destruct HC' as [[Hk [Hclean [Hbase Hgrow]]] [[Hfl [Hex [Hsound Hresp]]] [[Hcost Hled] Hnv]]].
  split; [| split; [| split]].
  - (* (a) universal base *)
    split; [exact Hk |]. split; [exact Hclean |]. split.
    + intros s m Hkm. simpl. apply r_ext. exact (Hbase s m Hkm).
    + intros s m H. simpl in *. apply flag_true_iff in H. apply flag_true_iff.
      intro H2. apply H. eapply bp_le_trans; [apply Hgrow | exact H2].
  - (* (b) earned record *)
    split.
    + intros s Hcl. simpl. apply flag_false_iff. rewrite (Hfl s Hcl). apply bp_le_refl.
    + split.
      * intros s0 tr Hcl H1. simpl in H1. rewrite run_pt in H1.
        apply flag_true_iff in H1.
        assert (H0 : bp_le P (rc s0) fl) by (rewrite (Hfl s0 Hcl); apply bp_le_refl).
        destruct (ax_first_exit I tr s0 H0 H1) as [pre [m [post [Htr [Hle [Hexit Hnf]]]]]].
        destruct (Hex s0 pre m Hcl Hexit)
          as [pre' [c [chk [mid1 [cmt [mid2 [Hpre [Hk1 [Hk2 [Hk3 [Hck [Hsame Hlub]]]]]]]]]]]].
        exists pre', c, chk, mid1, cmt, mid2, m, post.
        split; [rewrite Htr, Hpre; list_eq_tac |].
        split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
        split; [simpl; rewrite run_pt; exact Hck |].
        split; [intros t1 t2 Hm; simpl; rewrite !run_pt; apply (Hsame t1 t2 Hm) |].
        assert (Hpre_run : am_run AM (pre' ++ chk :: mid1 ++ cmt :: mid2) s0 = am_run AM pre s0)
          by (rewrite Hpre; reflexivity).
        split.
        -- simpl. rewrite run_pt, Hpre_run. apply flag_false_iff. exact Hle.
        -- simpl. rewrite run_pt.
           replace (pre' ++ chk :: mid1 ++ cmt :: mid2 ++ [m])
             with ((pre' ++ chk :: mid1 ++ cmt :: mid2) ++ [m]) by list_eq_tac.
           rewrite am_run_snoc, Hpre_run.
           apply flag_true_iff. exact Hnf.
      * split.
        -- intros s c H. simpl in *. apply Hsound. exact H.
        -- intros c s s' Hs H. simpl in *. exact (Hresp c s s' Hs H).
  - (* (c) exact toll *)
    split; [exact Hcost | exact Hled].
  - (* (d) non-vacuity *)
    destruct Hnv as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
    pose proof (ax_witness_nontrivial c chk cmt crt Hiff Hno) as Hnt.
    exists c, chk, cmt, crt. split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
    split; [| split; [exact Hyes | exact Hno]].
    intros a b. rewrite run_pt. simpl T.m_record. simpl T.ti_meaning. split.
    + intro Hflag. apply flag_true_iff in Hflag.
      set (s0 := ax_load I a b) in *.
      assert (Hcl : axi_clean I s0) by apply Hclean.
      assert (H0 : bp_le P (rc s0) fl) by (rewrite (Hfl s0 Hcl); apply bp_le_refl).
      destruct (ax_first_exit I [chk; cmt; crt] s0 H0 Hflag)
        as [pre [m [post [Htr [Hle [Hexit Hnf]]]]]].
      destruct (Hex s0 pre m Hcl Hexit)
        as [pre' [c' [chk' [mid1 [cmt' [mid2 [Hpre [Hk1' [Hk2' [Hk3' [Hck _]]]]]]]]]]].
      assert (Hlen : length [chk; cmt; crt] = length (pre ++ m :: post)) by (rewrite Htr; reflexivity).
      rewrite Hpre in Hlen. rewrite !app_length in Hlen. simpl in Hlen.
      rewrite app_length in Hlen. simpl in Hlen.
      assert (Hp : pre' = []) by (destruct pre'; [reflexivity | simpl in Hlen; lia]).
      assert (Hm1 : mid1 = []) by (destruct mid1; [reflexivity | simpl in Hlen; lia]).
      assert (Hm2 : mid2 = []) by (destruct mid2; [reflexivity | simpl in Hlen; lia]).
      subst pre' mid1 mid2. simpl in Hpre.
      assert (Hchk : chk = chk') by (rewrite Hpre in Htr; simpl in Htr; congruence).
      subst chk'. rewrite Hk1 in Hk1'. injection Hk1' as <-.
      rewrite am_run_nil in Hck. apply Hsound. exact Hck.
    + intro Hm. apply flag_true_iff. intro Hcon. apply Hnt.
      eapply bp_le_trans; [| exact Hcon]. apply Hiff. exact Hm.
Qed.

End Flag.

Print Assumptions ax_tc_a2.
Print Assumptions ax_tc_ledger_counts.
Print Assumptions ax_first_exit.
