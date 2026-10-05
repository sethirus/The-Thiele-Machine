(** UniversalInterpreterLinks.v: the universal interpreter host as an
    instance of the book's CertificationSystem record.

    UniversalRun.v proves that one fixed program U, run on the machine of
    EarnedMulti.v with the single property PSlot of UniversalCodes.v,
    simulates every program of the small machine of EarnedCore.v, matches
    its halting, its outputs, its ledger and its flag, and earns its own
    flag on its own chain. This file connects that host to the record the
    rest of the work is stated over, with no new assumptions:

      - the machine of EarnedMulti.v over any property language is a
        CertificationSystem, and universal_nfi_any_substrate gives its
        trace floor                        [multi_cs, multi_cs_floor];
        the interpreter host is that record at PSlot [interp_cs], and
        U's own run from the loaded start is a run of the record
        [interp_cs_runs_U];
      - every run of U that raises the host flag pays at least 3 on the
        record: the CHECK, the COMMIT and the CERTIFY of its own chain
        [interp_U_certified_floor];
      - whether U halts on the code of a guest program and its two inputs
        is the guest's own halting problem [interp_halting_iff], so it is
        undecidable by the vendored two-counter reduction of
        EarnedCoreLinks.v                  [interp_halting_undecidable];
      - the host, read through universal_thiele_complete, is the record
        complete_cs of EarnedGenericLinks.v, and that record is interp_cs
        step for step and cost for cost   [interp_complete_agrees], so the
        floor of thiele_complete_floor holds for U's runs
        [interp_U_complete_floor];
      - the pigeonhole obstruction of UniversalNoCopy.v, stated on the
        record: for any host property language and any finite list of host
        properties a translation lands in, two different guest claims
        "A >= n" and "A >= m" go to one host property, the guest's
        CHECK (PGe n), COMMIT (PGe m) traps on every start, and on the
        record the same two moves on a register copying the guest's A
        commit without a trap                [multi_cs_no_exact_copy]. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Kernel Require Import UniversalCertificationCost.
Require Kernel.EarnedCoreLinks.
Require Kernel.EarnedGenericLinks.
Require Kernel.UniversalLayout.
Require Kernel.UniversalSim.
Require Kernel.UniversalRun.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Require Minimal.ThieleComplete.
Require Minimal.UniversalCodes.
Require Minimal.UniversalNoCopy.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.
Module T := Minimal.ThieleComplete.
Module C := Minimal.UniversalCodes.
Module N := Minimal.UniversalNoCopy.
Module R := Kernel.UniversalRun.

(* ================================================================= *)
(* The machine with a counter for every number, over any language.    *)
(* ================================================================= *)

(* The machine of EarnedMulti.v over a property language with claim
   equality prop_eqb and checker eval, read as a CertificationSystem. *)
Definition multi_cs {prop : Type} (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) : CertificationSystem :=
  mk_cert_system (@M.state prop) (@M.instr prop) (M.exec prop_eqb eval)
    (@M.cost prop) (@M.cert prop) (M.multi_a2 prop_eqb eval).

Lemma multi_cs_run : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@M.instr prop)) (s : @M.state prop),
  cs_run (multi_cs prop_eqb eval) tr s = M.run prop_eqb eval tr s.
Proof. intros prop prop_eqb eval tr. induction tr; intros; simpl; auto. Qed.

Lemma multi_cs_cost : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@M.instr prop)),
  cs_total_cost (multi_cs prop_eqb eval) tr = M.total_cost tr.
Proof. intros prop prop_eqb eval tr. induction tr; simpl; auto. Qed.

(* Any trace that raises the flag costs at least 1, for every language. *)
Theorem multi_cs_floor : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@M.instr prop)) (s0 : @M.state prop),
  M.cert s0 = false -> M.cert (M.run prop_eqb eval tr s0) = true ->
  M.total_cost tr >= 1.
Proof.
  intros prop prop_eqb eval tr s0 H0 H1.
  rewrite <- (@multi_cs_cost prop prop_eqb eval tr).
  apply (universal_nfi_any_substrate (multi_cs prop_eqb eval) tr s0 H0).
  rewrite multi_cs_run. exact H1.
Qed.

(* ================================================================= *)
(* The interpreter host.                                              *)
(* ================================================================= *)

(* The host of UniversalRun.v: the machine of EarnedMulti.v with the one
   property PSlot. *)
Definition interp_cs : CertificationSystem := multi_cs C.hprop_eqb C.heval.

(* U's run of n steps from the loaded start hload P x y is the run, on the
   record, of the instructions U actually executes. *)
Theorem interp_cs_runs_U : forall (P : list E.instr) (x y n : nat),
  cs_run interp_cs
    (M.trace_of C.hprop_eqb C.heval n Kernel.UniversalLayout.U (Kernel.UniversalSim.hload P x y))
    (Kernel.UniversalSim.hload P x y)
  = R.hrun P x y n.
Proof.
  intros P x y n. unfold interp_cs. rewrite multi_cs_run.
  unfold R.hrun. symmetry. apply M.multi_run_prog_trace.
Qed.

(* A run of U that raises the host flag pays at least 3 on the record. *)
Theorem interp_U_certified_floor : forall (P : list E.instr) (x y n : nat),
  M.cert (R.hrun P x y n) = true ->
  cs_total_cost interp_cs
    (M.trace_of C.hprop_eqb C.heval n Kernel.UniversalLayout.U (Kernel.UniversalSim.hload P x y))
  >= 3.
Proof.
  intros P x y n Hc.
  unfold interp_cs. rewrite multi_cs_cost.
  rewrite <- (interp_cs_runs_U P x y n) in Hc.
  unfold interp_cs in Hc. rewrite multi_cs_run in Hc.
  destruct (M.multi_certified_run_min_cost C.hprop_eqb C.hprop_eqb_eq C.heval
              (Kernel.UniversalSim.hload P x y) _ (M.multi_start_clean _) Hc) as [H3 _].
  exact H3.
Qed.

(* ================================================================= *)
(* Halting of U is undecidable.                                       *)
(* ================================================================= *)

(* The halting problem of the one fixed program U: does U, started on the
   code of P and the inputs x and y, ever halt. *)
Definition INTERP_HALTING (q : list E.instr * nat * nat) : Prop :=
  let '(P, x, y) := q in
  exists n, M.halted Kernel.UniversalLayout.U (M.core_of (R.hrun P x y n)).

(* It is the guest's own halting problem, input for input. *)
Theorem interp_halting_iff : forall (P : list E.instr) (x y : nat),
  EarnedCoreLinks.EARNED_HALTING (P, x, y) <-> INTERP_HALTING (P, x, y).
Proof.
  intros P x y. simpl.
  pose proof (R.universal_halting P x y) as H.
  unfold R.grun in H. exact H.
Qed.

(* So it is undecidable: the two-counter halting problem reduces to the
   small machine's (EarnedCoreLinks.v), and that reduces to U's. *)
Theorem interp_halting_undecidable : undecidable INTERP_HALTING.
Proof.
  apply (undecidability_from_reducibility EarnedCoreLinks.earned_core_halting_undecidable).
  exists (fun q => q).
  intros [[P x] y]. apply interp_halting_iff.
Qed.

(* ================================================================= *)
(* The host through its Thiele-completeness.                          *)
(* ================================================================= *)

(* The host machine of UniversalRun.v, read through
   universal_thiele_complete as complete_cs of EarnedGenericLinks.v. *)
Definition interp_complete_cs : CertificationSystem :=
  @EarnedGenericLinks.complete_cs R.host_machine R.universal_thiele_complete.

(* It is interp_cs, step for step and cost for cost. *)
Theorem interp_complete_agrees : forall (tr : list (@M.instr C.hprop)) (s : @M.state C.hprop),
  cs_run interp_complete_cs tr s = cs_run interp_cs tr s /\
  cs_total_cost interp_complete_cs tr = cs_total_cost interp_cs tr.
Proof.
  induction tr as [| i rest IH]; intros s; [split; reflexivity |].
  destruct (IH (M.exec C.hprop_eqb C.heval s i)) as [Hr Hc]. split.
  - change (cs_run interp_complete_cs rest (M.exec C.hprop_eqb C.heval s i)
            = cs_run interp_cs rest (M.exec C.hprop_eqb C.heval s i)).
    exact Hr.
  - change (M.cost i + cs_total_cost interp_complete_cs rest
            = M.cost i + cs_total_cost interp_cs rest).
    rewrite Hc. reflexivity.
Qed.

(* The floor of a Thiele-complete machine, on U's runs: a run of U that
   raises the host flag costs at least 1 on complete_cs. *)
Theorem interp_U_complete_floor : forall (P : list E.instr) (x y n : nat),
  M.cert (R.hrun P x y n) = true ->
  cs_total_cost interp_complete_cs
    (M.trace_of C.hprop_eqb C.heval n Kernel.UniversalLayout.U (Kernel.UniversalSim.hload P x y))
  >= 1.
Proof.
  intros P x y n Hc.
  apply (@EarnedGenericLinks.thiele_complete_floor R.host_machine R.universal_thiele_complete
           _ (Kernel.UniversalSim.hload P x y)).
  - reflexivity.
  - rewrite R.U_run_on_host_machine. exact Hc.
Qed.

(* ================================================================= *)
(* No host fact on an exact copy of the guest counter.                *)
(* ================================================================= *)

(* For any host property language with an exact claim equality, any
   checker, and any translation of guest properties into a finite list of
   host properties that passes whatever the guest's check passes: two
   different claims "A >= n" and "A >= m" go to one host property, the
   guest program CHECK (PGe n) A; COMMIT (PGe m) A traps on every start,
   and on the record the translated two moves on a host register holding
   the guest's value of A, from any untrapped state with room in its fact
   table and A >= n, end untrapped with the channel naming the commitment. *)
Theorem multi_cs_no_exact_copy :
  forall (hprop : Type) (hprop_eqb : hprop -> hprop -> bool),
  (forall p q, hprop_eqb p q = true <-> p = q) ->
  forall (heval : hprop -> nat -> bool) (Q : list hprop) (tr : E.prop -> hprop),
  (forall p, In (tr p) Q) ->
  (forall p v, E.eval p v = true -> heval (tr p) v = true) ->
  exists n m,
    n <> m /\ tr (E.PGe n) = tr (E.PGe m) /\
    (forall a b, E.err (E.core_of (E.run_prog 2 (N.guest n m) (E.start a b))) = true) /\
    (forall a (r : nat) (s : @M.state hprop),
       n <= a -> M.vals (M.core_of s) r = a -> M.err (M.core_of s) = false ->
       length (M.facts (M.core_of s)) < M.fact_cap ->
       M.err (M.core_of (cs_run (multi_cs hprop_eqb heval)
                           [M.CHECK (tr (E.PGe n)) r; M.COMMIT (tr (E.PGe m)) r] s)) = false /\
       M.chan (M.core_of (cs_run (multi_cs hprop_eqb heval)
                            [M.CHECK (tr (E.PGe n)) r; M.COMMIT (tr (E.PGe m)) r] s))
         = Some (M.mkfact (tr (E.PGe m)) r (M.vers (M.core_of s) r))).
Proof.
  intros hprop hprop_eqb Heq heval Q tr HQ Hsound.
  destruct (N.no_exact_copy_host hprop_eqb Heq heval Q tr HQ Hsound)
    as [n [m [Hnm [_ [Htr [Htrap Hhost]]]]]].
  exists n, m. split; [exact Hnm |]. split; [exact Htr |]. split; [exact Htrap |].
  intros a r s Ha Hr He Hcap. rewrite multi_cs_run.
  destruct (Hhost a 0 r s Ha Hr He Hcap) as [_ [_ Hrun]].
  exact Hrun.
Qed.

Print Assumptions multi_cs.
Print Assumptions multi_cs_floor.
Print Assumptions interp_cs.
Print Assumptions interp_cs_runs_U.
Print Assumptions interp_U_certified_floor.
Print Assumptions interp_halting_iff.
Print Assumptions interp_halting_undecidable.
Print Assumptions interp_complete_cs.
Print Assumptions interp_complete_agrees.
Print Assumptions interp_U_complete_floor.
Print Assumptions multi_cs_no_exact_copy.
