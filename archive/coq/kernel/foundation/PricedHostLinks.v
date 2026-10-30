(** PricedHostLinks.v: the priced universal interpreter host as an instance
    of the book's CertificationSystem record.

    UniversalPRun.v proves that one fixed program U_P, run on the machine of
    EarnedMultiPriced.v with the single property PSlot of UniversalPCodes.v,
    simulates every program of the priced machine of EarnedPriced.v over the
    universal property language cg_uprop, matches its halting, its outputs,
    its ledger and its flag, and earns its own flag on its own chain.
    PresentedUniversal.v runs every computably presented machine on it. This
    file connects that host to the record the rest of the work is stated
    over, with no new assumptions:

      - the machine of EarnedMultiPriced.v over any property language is a
        CertificationSystem, and universal_nfi_any_substrate gives its trace
        floor                                  [pu_multi_cs, pu_multi_cs_floor];
        the priced interpreter host is that record at PSlot [priced_interp_cs],
        and U_P's own run from the loaded start is a run of the record
        [priced_interp_cs_runs_U_P];
      - every run of U_P that raises the host flag pays at least 3 on the
        record: the CHECK, the COMMIT and the CERTIFY of its own chain
        [priced_interp_U_P_certified_floor];
      - whether U_P halts on the code of a priced guest program and its two
        inputs is that guest's own halting problem [priced_interp_halting_iff],
        and that problem is undecidable, by the vendored two-counter reduction
        through the two-counter programs the guest runs
        [priced_guest_halting_undecidable, priced_interp_halting_undecidable];
      - the host, read through pu_universal_thiele_complete, is the record
        complete_cs of EarnedGenericLinks.v, and that record is the priced
        interpreter record step for step and cost for cost
        [priced_interp_complete_agrees], so the floor of
        thiele_complete_floor holds for U_P's runs
        [priced_interp_U_P_complete_floor].                                *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Coq Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
From Kernel Require Import UniversalCertificationCost.
Require Kernel.EarnedCoreLinks.
Require Kernel.EarnedGenericLinks.
Require Kernel.CompilerChecker.
Require Kernel.UniversalPCodes.
Require Kernel.UniversalPLayout.
Require Kernel.UniversalPSim.
Require Kernel.UniversalPRun.
Require Minimal.EarnedGeneric.
Require Minimal.EarnedPriced.
Require Minimal.EarnedMultiPriced.
Require Minimal.PricedComplete.
Require Minimal.ThieleComplete.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Module M := Minimal.EarnedMultiPriced.
Module T := Minimal.ThieleComplete.
Module PC := Minimal.PricedComplete.
Module CK := Kernel.CompilerChecker.
Module C := Kernel.UniversalPCodes.
Module R := Kernel.UniversalPRun.
Module ECL := Kernel.EarnedCoreLinks.

(* ================================================================= *)
(* The machine with a counter for every number, over any language.    *)
(* ================================================================= *)

(* The machine of EarnedMultiPriced.v over a property language with claim
   equality prop_eqb and checker eval, read as a CertificationSystem. *)
Definition pu_multi_cs {prop : Type} (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) : CertificationSystem :=
  mk_cert_system (@M.pu_state prop) (@M.pu_instr prop) (M.pu_exec prop_eqb eval)
    (@M.pu_cost prop) (@M.cert prop) (M.pu_multi_a2 prop_eqb eval).

Lemma pu_multi_cs_run : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@M.pu_instr prop)) (s : @M.pu_state prop),
  cs_run (pu_multi_cs prop_eqb eval) tr s = M.pu_run prop_eqb eval tr s.
Proof. intros prop prop_eqb eval tr. induction tr; intros; simpl; auto. Qed.

Lemma pu_multi_cs_cost : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@M.pu_instr prop)),
  cs_total_cost (pu_multi_cs prop_eqb eval) tr = M.pu_total_cost tr.
Proof. intros prop prop_eqb eval tr. induction tr; simpl; auto. Qed.

(* Any trace that raises the flag costs at least 1, for every language. *)
Theorem pu_multi_cs_floor : forall (prop : Type) (prop_eqb : prop -> prop -> bool)
    (eval : prop -> nat -> bool) (tr : list (@M.pu_instr prop)) (s0 : @M.pu_state prop),
  M.cert s0 = false -> M.cert (M.pu_run prop_eqb eval tr s0) = true ->
  M.pu_total_cost tr >= 1.
Proof.
  intros prop prop_eqb eval tr s0 H0 H1.
  rewrite <- (@pu_multi_cs_cost prop prop_eqb eval tr).
  apply (universal_nfi_any_substrate (pu_multi_cs prop_eqb eval) tr s0 H0).
  rewrite pu_multi_cs_run. exact H1.
Qed.

(* ================================================================= *)
(* The priced interpreter host.                                       *)
(* ================================================================= *)

(* The host of UniversalPRun.v: the machine of EarnedMultiPriced.v with the
   one property PSlot. *)
Definition priced_interp_cs : CertificationSystem :=
  pu_multi_cs C.pu_hprop_eqb C.pu_heval.

(* U_P's run of n steps from the loaded start pu_hload P x y is the run, on
   the record, of the instructions U_P actually executes. *)
Theorem priced_interp_cs_runs_U_P : forall (P : list C.E.instr) (x y n : nat),
  cs_run priced_interp_cs
    (M.pu_trace_of C.pu_hprop_eqb C.pu_heval n Kernel.UniversalPLayout.U_P
       (Kernel.UniversalPSim.pu_hload P x y))
    (Kernel.UniversalPSim.pu_hload P x y)
  = R.pu_hrun P x y n.
Proof.
  intros P x y n. unfold priced_interp_cs. rewrite pu_multi_cs_run.
  unfold R.pu_hrun. symmetry. apply M.pu_multi_run_prog_trace.
Qed.

(* A run of U_P that raises the host flag pays at least 3 on the record. *)
Theorem priced_interp_U_P_certified_floor : forall (P : list C.E.instr) (x y n : nat),
  M.cert (R.pu_hrun P x y n) = true ->
  cs_total_cost priced_interp_cs
    (M.pu_trace_of C.pu_hprop_eqb C.pu_heval n Kernel.UniversalPLayout.U_P
       (Kernel.UniversalPSim.pu_hload P x y))
  >= 3.
Proof.
  intros P x y n Hc.
  unfold priced_interp_cs. rewrite pu_multi_cs_cost.
  rewrite <- (priced_interp_cs_runs_U_P P x y n) in Hc.
  unfold priced_interp_cs in Hc. rewrite pu_multi_cs_run in Hc.
  destruct (M.pu_multi_certified_run_min_cost C.pu_hprop_eqb C.pu_hprop_eqb_eq C.pu_heval
              (Kernel.UniversalPSim.pu_hload P x y) _ (M.pu_multi_start_clean _) Hc)
    as [H3 _].
  exact H3.
Qed.

(* ================================================================= *)
(* Halting of U_P is undecidable.                                     *)
(* ================================================================= *)

(* The halting problem of the priced guest machine over cg_uprop: does the
   program P halt from the start with counters x and y. *)
Definition PRICED_GUEST_HALTING (q : list C.E.instr * nat * nat) : Prop :=
  let '(P, x, y) := q in
  exists m, C.E.halted P (C.E.core_of (C.E.run_prog m P (C.E.start x y))).

(* The halting problem of the one fixed program U_P: does U_P, started on
   the code of P and the inputs x and y, ever halt. *)
Definition PRICED_INTERP_HALTING (q : list C.E.instr * nat * nat) : Prop :=
  let '(P, x, y) := q in
  exists n, M.pu_halted Kernel.UniversalPLayout.U_P (M.core_of (R.pu_hrun P x y n)).

(* It is the guest's own halting problem, input for input. *)
Theorem priced_interp_halting_iff : forall (P : list C.E.instr) (x y : nat),
  PRICED_GUEST_HALTING (P, x, y) <-> PRICED_INTERP_HALTING (P, x, y).
Proof.
  intros P x y. simpl.
  pose proof (R.pu_universal_halting P x y) as H.
  unfold R.pu_grun in H. exact H.
Qed.

(* The two-counter programs the guest runs: INC and DEC only. *)
Definition cm_of_mm2 (i : mm2_instr) : T.cm_instr :=
  match i with
  | mm2_inc_a => T.CINC T.RA
  | mm2_inc_b => T.CINC T.RB
  | mm2_dec_a j => T.CDEC T.RA j
  | mm2_dec_b j => T.CDEC T.RB j
  end.

Lemma cm_of_mm2_agrees : forall i, T.earned_minsky (cm_of_mm2 i) = ECL.of_mm2 i.
Proof. intros [| | j | j]; reflexivity. Qed.

(* A compiled two-counter program is fetched exactly as on the reference
   machine, and never stops on a HALT, so on an untrapped state the priced
   machine reads the instruction the reference machine reads. *)
Lemma priced_next_compiled : forall (Pc : list T.cm_instr) (k : @G.core C.E.prop),
  G.err k = false ->
  P.pr_next_instr (map (@PC.priced_compile C.E.prop) Pc) k
  = option_map (@PC.priced_compile C.E.prop) (T.cm_fetch Pc (G.pc k)).
Proof.
  intros Pc k He. unfold P.pr_next_instr. rewrite He.
  rewrite (P.pr_fetch_map _ _ (@PC.priced_compile C.E.prop) Pc (G.pc k)).
  change (T.cm_fetch Pc (G.pc k)) with (G.fetch Pc (G.pc k)).
  destruct (G.fetch Pc (G.pc k)) as [i |]; simpl; [| reflexivity].
  destruct i as [[|] | [|] j]; reflexivity.
Qed.

Lemma priced_run_prog_is_prog_run : forall n (Pc : list T.cm_instr) (s : @G.state C.E.prop),
  G.err (G.core_of s) = false ->
  C.E.run_prog n (map (@PC.priced_compile C.E.prop) Pc) s
  = T.prog_run (PC.priced_base C.E.prop_eqb C.E.eval) n Pc s.
Proof.
  induction n as [| n IH]; intros Pc s He; [reflexivity |].
  simpl. unfold P.pr_step. rewrite (@priced_next_compiled Pc _ He).
  destruct (T.cm_fetch Pc (G.pc (G.core_of s))) as [i |] eqn:Hf; simpl.
  - destruct (PC.priced_sim C.E.prop_eqb C.E.eval s i He) as [_ He'].
    apply IH. exact He'.
  - apply P.pr_run_prog_halted. unfold P.pr_halted.
    rewrite (@priced_next_compiled Pc _ He). rewrite Hf. reflexivity.
Qed.

Lemma priced_halted_is_prog_halted : forall (Pc : list T.cm_instr) (s : @G.state C.E.prop),
  G.err (G.core_of s) = false ->
  C.E.halted (map (@PC.priced_compile C.E.prop) Pc) (G.core_of s)
  <-> T.prog_halted (PC.priced_base C.E.prop_eqb C.E.eval) Pc s.
Proof.
  intros Pc s He. unfold C.E.halted, P.pr_halted. rewrite (@priced_next_compiled Pc _ He).
  unfold T.prog_halted, PC.priced_base. simpl. unfold T.generic_window. simpl.
  destruct (T.cm_fetch Pc (G.pc (G.core_of s))); simpl; split; congruence.
Qed.

(* A two-counter program halts from (a, b) iff its compiled image halts as
   a program of the priced guest machine. *)
Theorem priced_guest_halting_correspondence : forall Pc a b,
  (exists n, T.cm_step Pc (T.cm_run n Pc (1, (a, b))) = None) <->
  PRICED_GUEST_HALTING (map (@PC.priced_compile C.E.prop) Pc, a, b).
Proof.
  intros Pc a b. simpl.
  rewrite (T.base_halting_correspondence _ (PC.priced_base C.E.prop_eqb C.E.eval) Pc a b).
  assert (Hrun : forall n, C.E.run_prog n (map (@PC.priced_compile C.E.prop) Pc) (C.E.start a b)
                 = T.prog_run (PC.priced_base C.E.prop_eqb C.E.eval) n Pc
                     (T.ub_load (PC.priced_base C.E.prop_eqb C.E.eval) a b)).
  { intro n. apply priced_run_prog_is_prog_run. reflexivity. }
  (* every run of a compiled program stays untrapped *)
  assert (Hok : forall n, G.err (G.core_of (T.prog_run (PC.priced_base C.E.prop_eqb C.E.eval) n Pc
                     (T.ub_load (PC.priced_base C.E.prop_eqb C.E.eval) a b))) = false).
  { intro n.
    exact (proj2 (T.base_runs_every_program _ (PC.priced_base C.E.prop_eqb C.E.eval) n Pc _
                    (T.ub_load_live (PC.priced_base C.E.prop_eqb C.E.eval) a b))). }
  split; intros [n Hn]; exists n.
  - rewrite Hrun. apply priced_halted_is_prog_halted; [apply Hok |]. exact Hn.
  - rewrite Hrun in Hn. apply (@priced_halted_is_prog_halted Pc _ (Hok n)). exact Hn.
Qed.

(* The priced guest's halting problem is undecidable: the two-counter
   halting problem reduces to it through the programs INC and DEC compile
   to (EarnedCoreLinks.v, ThieleComplete.v). *)
Theorem priced_guest_halting_undecidable : undecidable PRICED_GUEST_HALTING.
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exists (fun q => let '(Q, a, b) := q in
            (map (@PC.priced_compile C.E.prop) (map cm_of_mm2 Q), a, b)).
  intros [[Q a] b].
  refine (iff_trans (ECL.mm2_halting_iff Q a b) _).
  refine (iff_trans _ (priced_guest_halting_correspondence (map cm_of_mm2 Q) a b)).
  assert (Hm : map T.earned_minsky (map cm_of_mm2 Q) = map ECL.of_mm2 Q).
  { rewrite map_map. apply map_ext. intro i. apply cm_of_mm2_agrees. }
  rewrite <- Hm.
  symmetry. exact (T.earned_core_runs_counter_programs (map cm_of_mm2 Q) a b).
Qed.

(* So U_P's halting problem is undecidable too: the guest's halting problem
   reduces to it by the identity. *)
Theorem priced_interp_halting_undecidable : undecidable PRICED_INTERP_HALTING.
Proof.
  apply (undecidability_from_reducibility priced_guest_halting_undecidable).
  exists (fun q => q).
  intros [[P x] y]. apply priced_interp_halting_iff.
Qed.

(* ================================================================= *)
(* The host through its Thiele-completeness.                          *)
(* ================================================================= *)

(* The host machine of UniversalPRun.v, read through
   pu_universal_thiele_complete as complete_cs of EarnedGenericLinks.v. *)
Definition priced_interp_complete_cs : CertificationSystem :=
  @EarnedGenericLinks.complete_cs R.pu_host_machine R.pu_universal_thiele_complete.

(* It is priced_interp_cs, step for step and cost for cost. *)
Theorem priced_interp_complete_agrees :
  forall (tr : list (@M.pu_instr C.pu_hprop)) (s : @M.pu_state C.pu_hprop),
  cs_run priced_interp_complete_cs tr s = cs_run priced_interp_cs tr s /\
  cs_total_cost priced_interp_complete_cs tr = cs_total_cost priced_interp_cs tr.
Proof.
  induction tr as [| i rest IH]; intros s; [split; reflexivity |].
  destruct (IH (M.pu_exec C.pu_hprop_eqb C.pu_heval s i)) as [Hr Hc]. split.
  - change (cs_run priced_interp_complete_cs rest (M.pu_exec C.pu_hprop_eqb C.pu_heval s i)
            = cs_run priced_interp_cs rest (M.pu_exec C.pu_hprop_eqb C.pu_heval s i)).
    exact Hr.
  - change (M.pu_cost i + cs_total_cost priced_interp_complete_cs rest
            = M.pu_cost i + cs_total_cost priced_interp_cs rest).
    rewrite Hc. reflexivity.
Qed.

(* The floor of a Thiele-complete machine, on U_P's runs: a run of U_P that
   raises the host flag costs at least 1 on complete_cs. *)
Theorem priced_interp_U_P_complete_floor : forall (P : list C.E.instr) (x y n : nat),
  M.cert (R.pu_hrun P x y n) = true ->
  cs_total_cost priced_interp_complete_cs
    (M.pu_trace_of C.pu_hprop_eqb C.pu_heval n Kernel.UniversalPLayout.U_P
       (Kernel.UniversalPSim.pu_hload P x y))
  >= 1.
Proof.
  intros P x y n Hc.
  apply (@EarnedGenericLinks.thiele_complete_floor R.pu_host_machine R.pu_universal_thiele_complete
           _ (Kernel.UniversalPSim.pu_hload P x y)).
  - reflexivity.
  - rewrite R.pu_U_run_on_host_machine. exact Hc.
Qed.

Print Assumptions pu_multi_cs.
Print Assumptions pu_multi_cs_floor.
Print Assumptions priced_interp_cs.
Print Assumptions priced_interp_cs_runs_U_P.
Print Assumptions priced_interp_U_P_certified_floor.
Print Assumptions priced_interp_halting_iff.
Print Assumptions priced_guest_halting_correspondence.
Print Assumptions priced_guest_halting_undecidable.
Print Assumptions priced_interp_halting_undecidable.
Print Assumptions priced_interp_complete_cs.
Print Assumptions priced_interp_complete_agrees.
Print Assumptions priced_interp_U_P_complete_floor.
