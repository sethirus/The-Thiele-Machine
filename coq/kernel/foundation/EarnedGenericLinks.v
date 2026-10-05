(** EarnedGenericLinks.v: EarnedGeneric.v and ThieleComplete.v as instances
    of the book's CertificationSystem record.

    EarnedGeneric.v and ThieleComplete.v prove everything on the standard
    library alone. This file connects them to the record the rest of the
    work is stated over, with no new assumptions:

      - the small machine over any property language is a
        CertificationSystem, and universal_nfi_any_substrate gives its
        trace floor                      [generic_cs, earned_generic_floor];
        the toll needs nothing of the language, because only CERTIFY raises
        the flag and CERTIFY costs 1;
      - with an exact claim equality, a certified run from a clean start
        costs at least 3 on that record  [earned_generic_certified_floor];
        with an exact checker, every fact in the table whose version is
        current holds of its counter     [earned_generic_cs_sound];
      - the sorted-list language of EarnedGeneric.v is such a language
        [sorted_cs, sorted_machine_floor, sorted_certified_floor,
         sorted_cs_sound]; on that record the chain CHECK, COMMIT, CERTIFY
        on "A is a sorted list" certifies from A = 18 (the list [1; 2])
        paying 3, and from A = 20 (the list [2; 1]) does not
        [sorted_cs_demo_certifies, sorted_cs_demo_refused];
      - every Thiele-complete machine, in the strong sense of
        ThieleComplete.v, gives a CertificationSystem whose toll holds, so
        the strong notion yields the weak record and the floor
        [complete_cs, thiele_complete_floor];
      - the small machine of EarnedCore.v, read through its
        Thiele-completeness, is the record earned_cs of EarnedCoreLinks.v
        step for step and cost for cost [earned_complete_agrees], and every
        Thiele-complete generic machine is generic_cs the same way
        [generic_complete_agrees, sorted_complete_agrees].              *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Sorted.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.
Require Kernel.EarnedCoreLinks.
Require Minimal.EarnedCore.
Require Minimal.EarnedGeneric.
Require Minimal.ThieleComplete.
Module E := Minimal.EarnedCore.
Module G := Minimal.EarnedGeneric.
Module T := Minimal.ThieleComplete.

(* ================================================================= *)
(* The machine over any property language.                            *)
(* ================================================================= *)

(* The small machine over a property language with claim equality prop_eqb
   and checker eval, read as a CertificationSystem. *)
Definition generic_cs {prop : Type} (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) : CertificationSystem :=
  mk_cert_system (@G.state prop) (@G.instr prop) (G.exec prop_eqb eval)
    (@G.cost prop) (@G.cert prop) (G.generic_a2 prop_eqb eval).

Lemma generic_cs_run : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@G.instr prop)) (s : @G.state prop),
  cs_run (generic_cs prop_eqb eval) tr s = G.run prop_eqb eval tr s.
Proof. intros prop prop_eqb eval tr. induction tr; intros; simpl; auto. Qed.

Lemma generic_cs_cost : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@G.instr prop)),
  cs_total_cost (generic_cs prop_eqb eval) tr = G.total_cost tr.
Proof. intros prop prop_eqb eval tr. induction tr; simpl; auto. Qed.

(* Any trace that raises the flag costs at least 1, for every language. *)
Theorem earned_generic_floor : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@G.instr prop)) (s0 : @G.state prop),
  G.cert s0 = false -> G.cert (G.run prop_eqb eval tr s0) = true ->
  G.total_cost tr >= 1.
Proof.
  intros prop prop_eqb eval tr s0 H0 H1.
  rewrite <- (@generic_cs_cost prop prop_eqb eval tr).
  apply (universal_nfi_any_substrate (generic_cs prop_eqb eval) tr s0 H0).
  rewrite generic_cs_run. exact H1.
Qed.

(* With exact claim equality, a certified run from a clean start costs at
   least 3 on the record: the CHECK, the COMMIT and the CERTIFY. *)
Theorem earned_generic_certified_floor :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  forall (eval : prop -> nat -> bool) (tr : list (@G.instr prop)) (s0 : @G.state prop),
  G.clean_start s0 ->
  cs_cert (generic_cs prop_eqb eval) (cs_run (generic_cs prop_eqb eval) tr s0) = true ->
  cs_total_cost (generic_cs prop_eqb eval) tr >= 3.
Proof.
  intros prop prop_eqb Heq eval tr s0 Hc H1.
  rewrite generic_cs_cost. rewrite generic_cs_run in H1.
  destruct (G.generic_certified_run_min_cost prop_eqb Heq eval s0 tr Hc H1) as [H3 _].
  exact H3.
Qed.

(* With an exact checker, a fact in the table whose version is current
   holds of its counter, on every run of the record from a clean start. *)
Theorem earned_generic_cs_sound :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool)
         (eval : prop -> nat -> bool) (holds : prop -> nat -> Prop),
  (forall p v, eval p v = true <-> holds p v) ->
  forall (s0 : @G.state prop) (tr : list (@G.instr prop)) (f : @G.fact prop),
  G.clean_start s0 ->
  In f (G.facts (G.core_of (cs_run (generic_cs prop_eqb eval) tr s0))) ->
  G.f_ver f = G.ver (G.core_of (cs_run (generic_cs prop_eqb eval) tr s0)) (G.f_ctr f) ->
  holds (G.f_prop f) (G.val (G.core_of (cs_run (generic_cs prop_eqb eval) tr s0)) (G.f_ctr f)).
Proof.
  intros prop prop_eqb eval holds Hiff s0 tr f Hc Hin Hv.
  rewrite generic_cs_run in *.
  exact (G.generic_checker_soundness prop_eqb eval holds Hiff s0 tr f Hc Hin Hv).
Qed.

(* ================================================================= *)
(* The sorted-list language.                                          *)
(* ================================================================= *)

Definition sorted_cs : CertificationSystem := generic_cs G.sprop_eqb G.seval.

Theorem sorted_machine_floor : forall (tr : list (@G.instr G.sprop)) (s0 : @G.state G.sprop),
  G.cert s0 = false -> G.cert (G.run G.sprop_eqb G.seval tr s0) = true ->
  G.total_cost tr >= 1.
Proof.
  intros tr s0 H0 H1.
  exact (@earned_generic_floor G.sprop G.sprop_eqb G.seval tr s0 H0 H1).
Qed.

Theorem sorted_certified_floor :
  forall (tr : list (@G.instr G.sprop)) (s0 : @G.state G.sprop),
  G.clean_start s0 ->
  cs_cert sorted_cs (cs_run sorted_cs tr s0) = true ->
  cs_total_cost sorted_cs tr >= 3.
Proof.
  intros tr s0 Hc H1.
  exact (@earned_generic_certified_floor G.sprop G.sprop_eqb G.sprop_eqb_eq G.seval
           tr s0 Hc H1).
Qed.

(* A current fact "PSorted of A" in the table means A decodes to a sorted
   list. *)
Theorem sorted_cs_sound :
  forall (s0 : @G.state G.sprop) (tr : list (@G.instr G.sprop)) (c : G.ctr),
  G.clean_start s0 ->
  In (G.mkfact G.PSorted c (G.ver (G.core_of (cs_run sorted_cs tr s0)) c))
     (G.facts (G.core_of (cs_run sorted_cs tr s0))) ->
  Sorted le (G.decode (G.val (G.core_of (cs_run sorted_cs tr s0)) c)).
Proof.
  intros s0 tr c Hc Hin.
  exact (@earned_generic_cs_sound G.sprop G.sprop_eqb G.seval G.sholds G.seval_iff
           s0 tr _ Hc Hin eq_refl).
Qed.

(* The three-move chain on "A is a sorted list", as a trace of the record. *)
Theorem sorted_cs_demo_certifies :
  cs_cert sorted_cs (cs_run sorted_cs G.sorted_run (G.start 18 0)) = true /\
  cs_total_cost sorted_cs G.sorted_run = 3.
Proof. split; vm_compute; reflexivity. Qed.

Theorem sorted_cs_demo_refused :
  cs_cert sorted_cs (cs_run sorted_cs G.sorted_run (G.start 20 0)) = false /\
  G.err (G.core_of (cs_run sorted_cs G.sorted_run (G.start 20 0))) = true.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================= *)
(* Thiele-complete machines.                                          *)
(* ================================================================= *)

(* A machine whose toll holds, read as a CertificationSystem. *)
Definition weak_cs (M : T.machine) (H : T.weakly_thiele_complete M) : CertificationSystem :=
  mk_cert_system (T.m_state M) (T.m_move M) (T.m_step M) (T.m_cost M) (T.m_record M)
    (proj1 H).

(* The strong notion yields the weak record: a Thiele-complete machine is a
   CertificationSystem. *)
Definition complete_cs (M : T.machine) (H : T.thiele_complete M) : CertificationSystem :=
  @weak_cs M (T.thiele_complete_is_weak M H).

Lemma complete_cs_run : forall (M : T.machine) (H : T.thiele_complete M)
    (tr : list (T.m_move M)) (s : T.m_state M),
  cs_run (@complete_cs M H) tr s = T.run M tr s.
Proof. intros M H tr. induction tr; intros; simpl; auto. Qed.

(* Any trace of a Thiele-complete machine that raises its record costs at
   least 1. *)
Theorem thiele_complete_floor : forall (M : T.machine) (H : T.thiele_complete M)
    (tr : list (T.m_move M)) (s0 : T.m_state M),
  T.m_record M s0 = false -> T.m_record M (T.run M tr s0) = true ->
  cs_total_cost (@complete_cs M H) tr >= 1.
Proof.
  intros M H tr s0 H0 H1.
  apply (universal_nfi_any_substrate (@complete_cs M H) tr s0 H0).
  rewrite complete_cs_run. exact H1.
Qed.

(* The small machine of EarnedCore.v, read through its Thiele-completeness. *)
Definition earned_complete_cs : CertificationSystem :=
  @complete_cs T.earned_machine T.earned_core_thiele_complete.

(* It is earned_cs of EarnedCoreLinks.v, step for step and cost for cost. *)
Theorem earned_complete_agrees : forall (tr : list E.instr) (s : E.state),
  cs_run earned_complete_cs tr s = cs_run EarnedCoreLinks.earned_cs tr s /\
  cs_total_cost earned_complete_cs tr = cs_total_cost EarnedCoreLinks.earned_cs tr.
Proof.
  induction tr as [| i rest IH]; intros s; [split; reflexivity |].
  destruct (IH (E.exec s i)) as [Hr Hc]. split.
  - change (cs_run earned_complete_cs rest (E.exec s i)
            = cs_run EarnedCoreLinks.earned_cs rest (E.exec s i)).
    exact Hr.
  - change (E.cost i + cs_total_cost earned_complete_cs rest
            = E.cost i + cs_total_cost EarnedCoreLinks.earned_cs rest).
    rewrite Hc. reflexivity.
Qed.

(* Every Thiele-complete generic machine, read through its
   Thiele-completeness, is generic_cs step for step and cost for cost. *)
Theorem generic_complete_agrees :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool)
         (H : T.thiele_complete (T.generic_machine prop_eqb eval))
         (tr : list (@G.instr prop)) (s : @G.state prop),
  cs_run (@complete_cs _ H) tr s = cs_run (generic_cs prop_eqb eval) tr s /\
  cs_total_cost (@complete_cs _ H) tr = cs_total_cost (generic_cs prop_eqb eval) tr.
Proof.
  intros prop prop_eqb eval H tr.
  induction tr as [| i rest IH]; intros s; [split; reflexivity |].
  destruct (IH (G.exec prop_eqb eval s i)) as [Hr Hc]. split.
  - change (cs_run (@complete_cs _ H) rest (G.exec prop_eqb eval s i)
            = cs_run (generic_cs prop_eqb eval) rest (G.exec prop_eqb eval s i)).
    exact Hr.
  - change (G.cost i + cs_total_cost (@complete_cs _ H) rest
            = G.cost i + cs_total_cost (generic_cs prop_eqb eval) rest).
    rewrite Hc. reflexivity.
Qed.

(* The sorted-list machine, read through its Thiele-completeness, is
   sorted_cs. *)
Theorem sorted_complete_agrees :
  forall (tr : list (@G.instr G.sprop)) (s : @G.state G.sprop),
  cs_run (@complete_cs _ T.sorted_machine_thiele_complete) tr s = cs_run sorted_cs tr s /\
  cs_total_cost (@complete_cs _ T.sorted_machine_thiele_complete) tr
    = cs_total_cost sorted_cs tr.
Proof.
  intros tr s.
  exact (@generic_complete_agrees G.sprop G.sprop_eqb G.seval
           T.sorted_machine_thiele_complete tr s).
Qed.

Print Assumptions generic_cs.
Print Assumptions earned_generic_floor.
Print Assumptions earned_generic_certified_floor.
Print Assumptions earned_generic_cs_sound.
Print Assumptions sorted_machine_floor.
Print Assumptions sorted_certified_floor.
Print Assumptions sorted_cs_sound.
Print Assumptions sorted_cs_demo_certifies.
Print Assumptions sorted_cs_demo_refused.
Print Assumptions complete_cs.
Print Assumptions thiele_complete_floor.
Print Assumptions earned_complete_agrees.
Print Assumptions generic_complete_agrees.
Print Assumptions sorted_complete_agrees.
