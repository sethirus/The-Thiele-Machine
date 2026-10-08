(** CzCS: the composition of certification systems.

    A certification system (UniversalCertificationCost.v, the book's record)
    has states, moves, a step, a cost per move and a yes/no reading that pays
    the toll: a step that turns the reading from no to yes costs at least 1.
    Two certification systems run side by side form a system whose states are
    pairs and whose moves are the moves of either.  The reading of the
    composite can be either threshold of the pair of readings:

      cmpz_cs_or    "some part has certified";
      cmpz_cs_and   "every part has certified".

    Both pay the toll, so both are certification systems; this is the
    composition that the book left open.  What the toll then says:

      cmpz_cs_run         a run of the composite is the pair of the runs of
                          the two projections of its trace;
      cmpz_cs_total       the cost of a trace is the cost of its left part
                          plus the cost of its right part;
      cmpz_cs_or_floor    certifying "some part" from a start where no part
                          has certified costs at least 1 (the book's floor);
      cmpz_cs_and_floor   certifying "every part" from a start where no part
                          has certified costs at least 2: the tolls add;
      cmpz_cs_and_tight   and 2 is attained whenever each part can certify
                          for 1.

    The composite of two Thiele-complete machines, with the pair of readings
    as its record, is Thiele-complete ([CzProdTC.cmpz_prod_tc]); here only the
    toll is used, which every certification system has. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import CzProd CzProdTC.
Require Import Kernel.UniversalCertificationCost.

Definition cmpz_cs_am (C : CertificationSystem) : amachine bool two_pre :=
  mk_am bool two_pre (cs_state C) (cs_instr C) (cs_step C) (cs_cost C) (cs_cert C).

Lemma cmpz_cs_run : forall C tr s, cs_run C tr s = am_run (cmpz_cs_am C) tr s.
Proof. intros C. induction tr as [| i tr IH]; intro s; simpl; [reflexivity | apply IH]. Qed.

Lemma cmpz_cs_total_eq : forall C tr, cs_total_cost C tr = cmpz_cost (cmpz_cs_am C) tr.
Proof.
  intros C. induction tr as [| i tr IH]; [reflexivity |].
  simpl. rewrite IH. unfold cmpz_cost. simpl. reflexivity.
Qed.

(** The pair of two certification systems, before a reading is chosen. *)
Definition cmpz_cs_pair_step (C1 C2 : CertificationSystem)
    (s : cs_state C1 * cs_state C2) (m : cs_instr C1 + cs_instr C2) : cs_state C1 * cs_state C2 :=
  match m with
  | inl x => (cs_step C1 (fst s) x, snd s)
  | inr y => (fst s, cs_step C2 (snd s) y)
  end.

Definition cmpz_cs_pair_cost (C1 C2 : CertificationSystem) (m : cs_instr C1 + cs_instr C2) : nat :=
  match m with inl x => cs_cost C1 x | inr y => cs_cost C2 y end.

Definition cmpz_cs_or (C1 C2 : CertificationSystem) : CertificationSystem.
Proof.
  refine (mk_cert_system (cs_state C1 * cs_state C2) (cs_instr C1 + cs_instr C2)
            (cmpz_cs_pair_step C1 C2) (cmpz_cs_pair_cost C1 C2)
            (fun s => orb (cs_cert C1 (fst s)) (cs_cert C2 (snd s))) _).
  intros [s1 s2] [x | y] H0 H1; simpl in *.
  - apply orb_false_iff in H0 as [H0a H0b]. rewrite H0b, orb_false_r in H1.
    exact (cs_cert_costs C1 s1 x H0a H1).
  - apply orb_false_iff in H0 as [H0a H0b]. rewrite H0a in H1. simpl in H1.
    exact (cs_cert_costs C2 s2 y H0b H1).
Defined.

Definition cmpz_cs_and (C1 C2 : CertificationSystem) : CertificationSystem.
Proof.
  refine (mk_cert_system (cs_state C1 * cs_state C2) (cs_instr C1 + cs_instr C2)
            (cmpz_cs_pair_step C1 C2) (cmpz_cs_pair_cost C1 C2)
            (fun s => andb (cs_cert C1 (fst s)) (cs_cert C2 (snd s))) _).
  intros [s1 s2] [x | y] H0 H1; simpl in *.
  - apply andb_true_iff in H1 as [H1a H1b]. rewrite H1b in H0. rewrite andb_true_r in H0.
    exact (cs_cert_costs C1 s1 x H0 H1a).
  - apply andb_true_iff in H1 as [H1a H1b]. rewrite H1a in H0. simpl in H0.
    exact (cs_cert_costs C2 s2 y H0 H1b).
Defined.

Lemma cmpz_cs_or_run : forall C1 C2 tr s,
  cs_run (cmpz_cs_or C1 C2) tr s
    = (cs_run C1 (cmpz_lefts tr) (fst s), cs_run C2 (cmpz_rights tr) (snd s)).
Proof.
  intros C1 C2. induction tr as [| [x | y] tr IH]; intros [s1 s2]; simpl; try reflexivity;
    rewrite IH; reflexivity.
Qed.

Lemma cmpz_cs_and_run : forall C1 C2 tr s,
  cs_run (cmpz_cs_and C1 C2) tr s
    = (cs_run C1 (cmpz_lefts tr) (fst s), cs_run C2 (cmpz_rights tr) (snd s)).
Proof.
  intros C1 C2. induction tr as [| [x | y] tr IH]; intros [s1 s2]; simpl; try reflexivity;
    rewrite IH; reflexivity.
Qed.

Theorem cmpz_cs_or_total : forall C1 C2 tr,
  cs_total_cost (cmpz_cs_or C1 C2) tr
    = cs_total_cost C1 (cmpz_lefts tr) + cs_total_cost C2 (cmpz_rights tr).
Proof.
  intros C1 C2. induction tr as [| [x | y] tr IH]; [reflexivity | |]; simpl; rewrite IH; lia.
Qed.

Theorem cmpz_cs_and_total : forall C1 C2 tr,
  cs_total_cost (cmpz_cs_and C1 C2) tr
    = cs_total_cost C1 (cmpz_lefts tr) + cs_total_cost C2 (cmpz_rights tr).
Proof.
  intros C1 C2. induction tr as [| [x | y] tr IH]; [reflexivity | |]; simpl; rewrite IH; lia.
Qed.

(** The book's floor, for the composite: some part certified costs at least 1. *)
Theorem cmpz_cs_or_floor : forall C1 C2 tr s,
  cs_cert (cmpz_cs_or C1 C2) s = false ->
  cs_cert (cmpz_cs_or C1 C2) (cs_run (cmpz_cs_or C1 C2) tr s) = true ->
  cs_total_cost (cmpz_cs_or C1 C2) tr >= 1.
Proof.
  intros C1 C2 tr s H0 H1.
  exact (universal_nfi_any_substrate (cmpz_cs_or C1 C2) tr s H0 H1).
Qed.

(** Every part certified costs at least 2: the tolls add. *)
Theorem cmpz_cs_and_floor : forall C1 C2 tr s,
  cs_cert C1 (fst s) = false -> cs_cert C2 (snd s) = false ->
  cs_cert (cmpz_cs_and C1 C2) (cs_run (cmpz_cs_and C1 C2) tr s) = true ->
  cs_total_cost (cmpz_cs_and C1 C2) tr >= 2.
Proof.
  intros C1 C2 tr s H1 H2 H3.
  rewrite cmpz_cs_and_run in H3. simpl in H3. apply andb_true_iff in H3 as [H3a H3b].
  rewrite cmpz_cs_and_total.
  pose proof (universal_nfi_any_substrate C1 (cmpz_lefts tr) (fst s) H1 H3a) as A.
  pose proof (universal_nfi_any_substrate C2 (cmpz_rights tr) (snd s) H2 H3b) as B.
  lia.
Qed.

(** And 2 is attained whenever each part can certify for 1. *)
Theorem cmpz_cs_and_tight : forall C1 C2 s1 s2 (tr1 : list (cs_instr C1)) (tr2 : list (cs_instr C2)),
  cs_cert C1 s1 = false -> cs_cert C2 s2 = false ->
  cs_cert C1 (cs_run C1 tr1 s1) = true -> cs_total_cost C1 tr1 = 1 ->
  cs_cert C2 (cs_run C2 tr2 s2) = true -> cs_total_cost C2 tr2 = 1 ->
  exists tr : list (cs_instr C1 + cs_instr C2),
    cs_cert (cmpz_cs_and C1 C2) (cs_run (cmpz_cs_and C1 C2) tr (s1, s2)) = true /\
    cs_total_cost (cmpz_cs_and C1 C2) tr = 2.
Proof.
  intros C1 C2 s1 s2 tr1 tr2 _ _ H1 C1c H2 C2c.
  exists (map inl tr1 ++ map inr tr2). split.
  - rewrite cmpz_cs_and_run. simpl.
    rewrite cmpz_lefts_app, cmpz_rights_app,
            (cmpz_lefts_map_inl (Y := cs_instr C2)), (cmpz_rights_map_inl (Y := cs_instr C2)),
            (cmpz_lefts_map_inr (X := cs_instr C1)), (cmpz_rights_map_inr (X := cs_instr C1)).
    rewrite app_nil_r. simpl. rewrite H1, H2. reflexivity.
  - rewrite cmpz_cs_and_total.
    rewrite cmpz_lefts_app, cmpz_rights_app,
            (cmpz_lefts_map_inl (Y := cs_instr C2)), (cmpz_rights_map_inl (Y := cs_instr C2)),
            (cmpz_lefts_map_inr (X := cs_instr C1)), (cmpz_rights_map_inr (X := cs_instr C1)).
    rewrite app_nil_r. simpl. lia.
Qed.

Print Assumptions cmpz_cs_or.
Print Assumptions cmpz_cs_and.
Print Assumptions cmpz_cs_or_total.
Print Assumptions cmpz_cs_and_total.
Print Assumptions cmpz_cs_or_floor.
Print Assumptions cmpz_cs_and_floor.
Print Assumptions cmpz_cs_and_tight.
