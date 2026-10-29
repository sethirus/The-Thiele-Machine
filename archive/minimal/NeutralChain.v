(** NeutralChain.v: in what sense the Thiele-complete record is
    "the latch of the certification event", and when a neutral lift fails. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Require Import Minimal.NeutralComplete.

(* The certification event with NO mention of the record: a passing CHECK
   of c, a COMMIT of c with c's subject unchanged in between, then a
   CERTIFY move (whether or not it raises anything). *)
Definition chain_event {M} (I : thiele_interface M) (s0 : m_state M) (tr : list (m_move M)) : Prop :=
  exists pre c chk mid1 cmt mid2 crt post,
    tr = pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post /\
    ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\ ti_kind I crt = KCertify /\
    ti_check I (run M pre s0) c = true /\
    (forall t1 t2, mid1 = t1 ++ t2 -> ti_same I c (run M pre s0) (run M (pre ++ chk :: t1) s0)).

(* One direction holds on every Thiele-complete machine: the record is up
   only after the certification event. *)
Theorem tc_record_implies_event : forall M (I : thiele_interface M),
  thiele_complete_with I -> forall s0 tr, ti_clean I s0 ->
  m_record M (run M tr s0) = true -> chain_event I s0 tr.
Proof.
  intros M I [_ [[_ [Hch _]] _]] s0 tr H0 H1.
  destruct (Hch s0 tr H0 H1)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [Hk1 [Hk2 [Hk3 [Hck [Hs _]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, mid2, crt, post.
  exact (conj Htr (conj Hk1 (conj Hk2 (conj Hk3 (conj Hck Hs))))).
Qed.

(* The converse fails on the book's own small machine: from start (0, 1),
   CHECK Zero A passes, CHECK Zero B fails and traps, COMMIT Zero A and
   CERTIFY then do nothing. The event occurred (A untouched, check passed,
   commit and certify moves present) and the record is down. So the
   record is not the latch of the record-free certification event; it is
   only bounded by it. *)
Definition bad_tr : list E.instr :=
  [E.CHECK E.PZero E.CA; E.CHECK E.PZero E.CB; E.COMMIT E.PZero E.CA; E.CERTIFY].

Theorem small_event_without_record :
  ti_clean earned_interface (E.start 0 1) /\
  chain_event earned_interface (E.start 0 1) bad_tr /\
  m_record earned_machine (run earned_machine bad_tr (E.start 0 1)) = false.
Proof.
  split; [apply E.start_clean |]. split; [| reflexivity].
  exists [], (E.PZero, E.CA), (E.CHECK E.PZero E.CA), [E.CHECK E.PZero E.CB],
         (E.COMMIT E.PZero E.CA), [], E.CERTIFY, [].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [reflexivity |].
  intros t1 t2 H.
  destruct t1 as [| x t1]; [simpl; split; reflexivity |].
  destruct t1 as [| y t1].
  - injection H as Hx _. subst x. simpl. split; reflexivity.
  - injection H as _ H. destruct t1; discriminate H.
Qed.

(* A neutral lift can fail for an event that is non-constant on states but
   constant on every state the loaded starts reach: a hidden bit. *)
Definition hidden : machine :=
  mk_machine (cm_conf * bool) cm_instr (fun s i => (cm_exec i (fst s), snd s)) (fun _ => 0)
    (fun _ => false).

Definition hidden_base : universal_base hidden.
Proof.
  refine (mk_ub hidden fst (fun _ => True) (fun i => i) (fun a b => ((1, (a, b)), false)) _ _ _).
  - reflexivity.
  - intros; exact I.
  - intros [x r] i _. split; [reflexivity | exact I].
Defined.

Definition hidden_event (_ : unit) (s : cm_conf * bool) : bool := snd s.

Lemma hidden_run_bit : forall w s, snd (run hidden w s) = snd s.
Proof. induction w as [| i w IH]; intro s; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Theorem hidden_event_nonconstant :
  hidden_event tt ((1, (0, 0)), true) = true /\ hidden_event tt ((1, (0, 0)), false) = false.
Proof. split; reflexivity. Qed.

Theorem hidden_lift_no_distinction :
  ~ n_distinction_clause (nlift_interface hidden unit hidden_event hidden_base).
Proof.
  intro H. apply nlift_distinction_iff in H.
  destruct H as [w [k [a [b [a' [b' [H1 _]]]]]]].
  unfold hidden_event in H1. rewrite hidden_run_bit in H1. discriminate.
Qed.

(* Under permanence, the latch of a reading along a run is the reading at
   the end: so a host that carries the latch carries the record itself. *)
Theorem permanent_latch_is_record : forall M (st : m_state M) (tr : list (m_move M)),
  (forall s m, m_record M s = true -> m_record M (m_step M s m) = true) ->
  (exists l1 l2, tr = l1 ++ l2 /\ m_record M (run M l1 st) = true) <->
  m_record M (run M tr st) = true.
Proof.
  intros M st tr Hp.
  assert (Hstay : forall l s, m_record M s = true -> m_record M (run M l s) = true)
    by (induction l; intros; simpl; auto).
  split.
  - intros [l1 [l2 [-> H]]]. rewrite run_app. apply Hstay, H.
  - intro H. exists tr, []. rewrite app_nil_r. auto.
Qed.

Print Assumptions tc_record_implies_event.
Print Assumptions small_event_without_record.
Print Assumptions hidden_lift_no_distinction.
Print Assumptions permanent_latch_is_record.
