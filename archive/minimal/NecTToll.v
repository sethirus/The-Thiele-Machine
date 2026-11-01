(** NecTToll.v: the exact-toll clause, and two conjuncts of the earned-record
    clause, are necessary.

    For every Thiele-complete interface I, this file builds a neighbour that
    meets every clause of the definition but one conjunct, and shows what
    breaks.

      [nec_t_doubled_cost_meets_all_but_toll]  Charge twice as much for every
        move. The universal base, the earned record and non-vacuity still
        hold (none of them mentions a price), the exact toll fails, and the
        machine is not Thiele-complete through any interface, because a
        Thiele-complete machine charges 0 or 1 for each move.
      [nec_t_ledgerless_meets_all_but_ledger]  Keep every cost but let the
        ledger read 0 at every state. Everything holds except that the ledger
        grows by the cost of each move, and a run that raises the record
        then ends with a ledger below its start plus 3.
      [nec_t_unsound_check_meets_all_but_soundness]  Let every CHECK pass.
        Everything holds except that a passing check means its claim, and no
        CHECK fails on a false claim at any loaded state.
      [nec_t_same_true_meets_all_but_respect]  Call every pair of states
        "the thing the claim is about is unchanged". Everything holds except
        that a claim that holds keeps holding while that is unchanged, and
        a claim that held at one loaded state is false at another that the
        relation counts as unchanged. *)

From Coq Require Import List Arith Lia Bool Setoid.
Import ListNotations.
Require Import Minimal.ThieleComplete.

(* ================================================================= *)
(* The doubled-cost neighbour.                                        *)
(* ================================================================= *)

Definition cost_machine (M : machine) (f : m_move M -> nat) : machine :=
  mk_machine (m_state M) (m_move M) (m_step M) f (m_record M).

Lemma run_cm : forall M f tr s, run (cost_machine M f) tr s = run M tr s.
Proof. intros M f. induction tr as [| m tr IH]; intro s; cbn; [reflexivity | apply IH]. Qed.

Definition cm_base {M : machine} {f : m_move M -> nat} (U : universal_base M) :
  universal_base (cost_machine M f) :=
  mk_ub (cost_machine M f) (ub_window U) (ub_live U) (ub_compile U) (ub_load U)
    (ub_load_window U) (ub_load_live U) (ub_sim U).

Definition cm_interface {M : machine} (f : m_move M -> nat) (I : thiele_interface M) :
  thiele_interface (cost_machine M f) :=
  mk_ti (cost_machine M f) (cm_base (ti_base I)) (ti_claim I) (ti_kind I)
    (ti_meaning I) (ti_check I) (ti_same I) (ti_clean I) (ti_ledger I).

Lemma earned_chain_cm : forall M f (I : thiele_interface M) s0 tr,
  earned_chain I s0 tr -> earned_chain (cm_interface f I) s0 tr.
Proof.
  intros M f I s0 tr H. unfold earned_chain in *. cbn.
  setoid_rewrite run_cm. exact H.
Qed.

Theorem nec_t_doubled_cost_meets_all_but_toll : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  let f := fun m => 2 * m_cost M m in
  universal_base_clause (cm_interface f I) /\
  earned_record_clause (cm_interface f I) /\
  non_vacuity_clause (cm_interface f I) /\
  ~ exact_toll_clause (cm_interface f I) /\
  ~ thiele_complete (cost_machine M f).
Proof.
  intros M I HC f. destruct HC as [Ha [Hb [Hc Hd]]].
  split; [exact Ha |].
  split.
  - destruct Hb as [Hb1 [Hb2 Hb34]]. split; [exact Hb1 |]. split; [| exact Hb34].
    intros s0 tr Hcl Hr. apply earned_chain_cm. apply Hb2; [exact Hcl |].
    cbn in Hr. rewrite run_cm in Hr. exact Hr.
  - split; [exact Hd |].
    destruct Hd as [c [chk [cmt [crt [Hk1 [_ [_ [_ _]]]]]]]].
    assert (Hcost : m_cost M chk = 1).
    { destruct Hc as [Hc1 _]. rewrite Hc1. unfold record_move. rewrite Hk1. reflexivity. }
    split.
    + intros [Hc1 _]. specialize (Hc1 chk). cbn in Hc1. unfold record_move in Hc1.
      cbn in Hc1. rewrite Hk1 in Hc1. unfold f in Hc1. rewrite Hcost in Hc1. discriminate Hc1.
    + intro Hcomplete. pose proof (complete_costs_at_most_one _ Hcomplete chk) as H.
      cbn in H. unfold f in H. rewrite Hcost in H. lia.
Qed.

(* ================================================================= *)
(* The three interface-level neighbours.                              *)
(* ================================================================= *)

(* Same machine, same base, same everything, with one field replaced. *)
Definition with_ledger {M : machine} (I : thiele_interface M) (l : m_state M -> nat) :
  thiele_interface M :=
  mk_ti M (ti_base I) (ti_claim I) (ti_kind I) (ti_meaning I) (ti_check I)
    (ti_same I) (ti_clean I) l.

Definition with_check {M : machine} (I : thiele_interface M)
  (ck : m_state M -> ti_claim I -> bool) : thiele_interface M :=
  mk_ti M (ti_base I) (ti_claim I) (ti_kind I) (ti_meaning I) ck
    (ti_same I) (ti_clean I) (ti_ledger I).

Definition with_same {M : machine} (I : thiele_interface M)
  (sm : ti_claim I -> m_state M -> m_state M -> Prop) : thiele_interface M :=
  mk_ti M (ti_base I) (ti_claim I) (ti_kind I) (ti_meaning I) (ti_check I)
    sm (ti_clean I) (ti_ledger I).

(* The ledger that reads 0 everywhere. *)
Theorem nec_t_ledgerless_meets_all_but_ledger : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  let J := with_ledger I (fun _ => 0) in
  universal_base_clause J /\ earned_record_clause J /\ non_vacuity_clause J /\
  (forall m, m_cost M m = record_move J m) /\
  ~ exact_toll_clause J /\
  exists a b tr, ti_clean J (load J a b) /\
    m_record M (run M tr (load J a b)) = true /\
    ti_ledger J (run M tr (load J a b)) < ti_ledger J (load J a b) + 3.
Proof.
  intros M I HC J. destruct HC as [Ha [Hb [Hc Hd]]].
  split; [exact Ha |]. split; [exact Hb |]. split; [exact Hd |].
  split; [exact (proj1 Hc) |].
  destruct Hd as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [[a [b Hyes]] _]]]]]]]]].
  assert (Hcost : m_cost M chk = 1).
  { rewrite (proj1 Hc chk). unfold record_move. rewrite Hk1. reflexivity. }
  split.
  - intros [_ H]. specialize (H (load I a b) chk). cbn in H. rewrite Hcost in H. lia.
  - exists a, b, [chk; cmt; crt]. split; [apply Ha |].
    split; [apply Hiff, Hyes |]. cbn. lia.
Qed.

(* A checker that says yes to everything. *)
Theorem nec_t_unsound_check_meets_all_but_soundness : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  let J := with_check I (fun _ _ => true) in
  universal_base_clause J /\ exact_toll_clause J /\ non_vacuity_clause J /\
  (forall s0 tr, ti_clean J s0 -> m_record M (run M tr s0) = true -> earned_chain J s0 tr) /\
  (forall s, ti_clean J s -> m_record M s = false) /\
  (forall c s s', ti_same J c s s' -> ti_meaning J c s -> ti_meaning J c s') /\
  ~ (forall s c, ti_check J s c = true -> ti_meaning J c s) /\
  ~ (exists a b chk c, ti_kind J chk = KCheck c /\ ti_check J (load J a b) c = false /\
       ~ ti_meaning J c (load J a b)).
Proof.
  intros M I HC J. destruct HC as [Ha [[Hb1 [Hb2 [Hb3 Hb4]]] [Hc Hd]]].
  split; [exact Ha |]. split; [exact Hc |]. split; [exact Hd |].
  split.
  - intros s0 tr Hcl Hr.
    destruct (Hb2 s0 tr Hcl Hr) as [pre [c [chk [mid1 [cmt [mid2 [crt [post H]]]]]]]].
    exists pre, c, chk, mid1, cmt, mid2, crt, post.
    destruct H as [Htr [K1 [K2 [K3 [_ [Hs Hrest]]]]]].
    split; [exact Htr |]. split; [exact K1 |]. split; [exact K2 |]. split; [exact K3 |].
    split; [reflexivity |]. split; [exact Hs | exact Hrest].
  - split; [exact Hb1 |]. split; [exact Hb4 |]. split.
    + intro H. destruct Hd as [c [chk [cmt [crt [K1 [K2 [K3 [Hiff [Hyes [a [b Hno]]]]]]]]]]].
      apply Hno. apply (H (load I a b) c). reflexivity.
    + intros [a [b [chk [c [_ [H _]]]]]]. cbn in H. discriminate H.
Qed.

(* Everything counts as "unchanged". *)
Theorem nec_t_same_true_meets_all_but_respect : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  let J := with_same I (fun _ _ _ => True) in
  universal_base_clause J /\ exact_toll_clause J /\ non_vacuity_clause J /\
  (forall s0 tr, ti_clean J s0 -> m_record M (run M tr s0) = true -> earned_chain J s0 tr) /\
  (forall s, ti_clean J s -> m_record M s = false) /\
  (forall s c, ti_check J s c = true -> ti_meaning J c s) /\
  ~ (forall c s s', ti_same J c s s' -> ti_meaning J c s -> ti_meaning J c s').
Proof.
  intros M I HC J. destruct HC as [Ha [[Hb1 [Hb2 [Hb3 Hb4]]] [Hc Hd]]].
  split; [exact Ha |]. split; [exact Hc |]. split; [exact Hd |].
  split.
  - intros s0 tr Hcl Hr.
    destruct (Hb2 s0 tr Hcl Hr) as [pre [c [chk [mid1 [cmt [mid2 [crt [post H]]]]]]]].
    exists pre, c, chk, mid1, cmt, mid2, crt, post.
    destruct H as [Htr [K1 [K2 [K3 [Hck [_ Hrest]]]]]].
    split; [exact Htr |]. split; [exact K1 |]. split; [exact K2 |]. split; [exact K3 |].
    split; [exact Hck |]. split; [intros; exact Logic.I | exact Hrest].
  - split; [exact Hb1 |]. split; [exact Hb3 |].
    intro H. destruct Hd as [c [chk [cmt [crt [K1 [K2 [K3 [Hiff [[a [b Hyes]] [a' [b' Hno]]]]]]]]]]].
    apply Hno. apply (H c (load I a b) (load I a' b')); [exact Logic.I | exact Hyes].
Qed.

Print Assumptions nec_t_doubled_cost_meets_all_but_toll.
Print Assumptions nec_t_ledgerless_meets_all_but_ledger.
Print Assumptions nec_t_unsound_check_meets_all_but_soundness.
Print Assumptions nec_t_same_true_meets_all_but_respect.
