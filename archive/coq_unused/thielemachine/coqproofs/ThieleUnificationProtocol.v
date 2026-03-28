(**
  THIELE UNIFICATION PROTOCOL (Machine-checkable scaffold)

  This file is a *protocol binding layer*: it pins the protocol’s
  “substrate + opcodes + μ-laws + locality” to the kernel VM semantics.

  It deliberately avoids any spacetime/physics primitives.
*)

From Coq Require Import List Arith.PeanoNat Lia.
From Coq Require Import Setoids.Setoid.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof MuLedgerConservation.

Module ThieleUnificationProtocol.

  (** ---------------------------------------------------------------------
      PART I — FOUNDATIONAL SUBSTRATE (no physics primitives)
      --------------------------------------------------------------------- *)

  Definition ThieleState : Type := VMState.VMState.
  Definition ModuleId : Type := VMState.ModuleID.
  Definition Opcode : Type := VMStep.vm_instruction.

  Definition step : ThieleState -> Opcode -> ThieleState -> Prop := VMStep.vm_step.
  Definition run (fuel : nat) (trace : list Opcode) (s : ThieleState) : ThieleState :=
    SimulationProof.run_vm fuel trace s.

  Definition mu (s : ThieleState) : nat := s.(VMState.vm_mu).

  (** Opcode names required by the protocol exist as kernel instructions:
      - PNEW      ↦ instr_pnew
      - PDISCOVER ↦ instr_pdiscover
      - PSPLIT    ↦ instr_psplit
      - LASSERT   ↦ instr_lassert
      - PMERGE    ↦ instr_pmerge
   *)

  (** ---------------------------------------------------------------------
      PART II — CORE ALGEBRAIC LAWS (kernel-level)
      --------------------------------------------------------------------- *)

  (** Functoriality of execution: splitting fuel composes runs. *)
  Lemma run_functorial :
    forall m n trace s,
      run (m + n) trace s = run n trace (run m trace s).
  Proof.
    unfold run.
    induction m as [|m IH]; intros n trace s.
    - simpl. reflexivity.
    - replace (S m + n)%nat with (S (m + n))%nat by lia.
      simpl (SimulationProof.run_vm (S (m + n)) trace s).
      destruct (nth_error trace (VMState.vm_pc s)) as [instr|] eqn:Hfetch.
      + (* fetch succeeds *)
        simpl.
        (* Replace the scrutinee everywhere (including inside matches) then simplify. *)
        setoid_rewrite Hfetch.
        cbn.
        exact (IH n trace (SimulationProof.vm_apply s instr)).
      + (* fetch fails *)
        simpl.
        setoid_rewrite Hfetch.
        cbn.
        destruct n as [|n].
        * reflexivity.
        * simpl (SimulationProof.run_vm (S n) trace s).
          setoid_rewrite Hfetch.
          cbn.
          reflexivity.
  Qed.

  (** μ monotonicity under execution. *)
  Theorem mu_monotone :
    forall fuel trace s,
      mu s <= mu (run fuel trace s).
  Proof.
    intros fuel trace s.
    unfold mu, run.
    apply MuLedgerConservation.run_vm_mu_monotonic.
  Qed.

  (** μ conservation law: μ(final) = μ(init) + Σ(costs). *)
  Theorem mu_ledger_conservation :
    forall fuel trace s,
      mu (run fuel trace s) =
        mu s + MuLedgerConservation.ledger_sum (MuLedgerConservation.ledger_entries fuel trace s).
  Proof.
    intros fuel trace s.
    unfold mu, run.
    exact (MuLedgerConservation.run_vm_mu_conservation fuel trace s).
  Qed.

  (** Resource compositionality for *independent sequential phases*:
      μ(after phase1+phase2) = μ(after phase1) + Σ(costs of phase2 from that state).

      This is an algebraic corollary of functoriality + μ ledger conservation.
   *)
  Corollary mu_phase_split :
    forall m n trace s,
      mu (run (m + n) trace s) =
        mu (run m trace s) +
        MuLedgerConservation.ledger_sum
          (MuLedgerConservation.ledger_entries n trace (run m trace s)).
  Proof.
    intros m n trace s.
    rewrite run_functorial.
    rewrite mu_ledger_conservation.
    reflexivity.
  Qed.

  (** ---------------------------------------------------------------------
      LOCALITY / NO-SIGNALING (kernel graph update locality)
      --------------------------------------------------------------------- *)

  Lemma graph_lookup_modules_insert_other :
    forall mods mid mid' m',
      mid <> mid' ->
      VMState.graph_lookup_modules (VMState.graph_insert_modules mods mid m') mid' =
      VMState.graph_lookup_modules mods mid'.
  Proof.
    induction mods as [|[id m0] rest IH]; intros mid mid' m' Hneq; simpl.
    - (* inserting into empty list *)
      destruct (Nat.eqb mid mid') eqn:Heq.
      + apply Nat.eqb_eq in Heq. subst. contradiction.
      + reflexivity.
    - destruct (Nat.eqb id mid) eqn:Hid_mid.
      + (* overwrite at head: id = mid *)
        pose proof Hid_mid as Hid_mid_true.
        apply Nat.eqb_eq in Hid_mid_true. subst id.
        (* reduce the insert-at-head case *)
        cbn [VMState.graph_insert_modules].
        try rewrite Nat.eqb_refl.
        (* lookup mid' skips the overwritten head because mid <> mid' *)
        assert (Nat.eqb mid mid' = false) as Hskip.
        { apply Nat.eqb_neq. exact Hneq. }
        simpl.
        rewrite !Hskip.
        reflexivity.
      + (* no overwrite at head *)
        (* reduce the insert-no-overwrite case *)
        cbn [VMState.graph_insert_modules].
        try rewrite Hid_mid.
        destruct (Nat.eqb id mid') eqn:Hid_mid'.
        * (* lookup hits head on both sides *)
          simpl. rewrite Hid_mid'. reflexivity.
        * (* lookup goes to tail; apply IH *)
          simpl.
          rewrite Hid_mid'.
          apply IH. exact Hneq.
  Qed.

  (** [graph_lookup_update_other]: formal specification. *)
  Lemma graph_lookup_update_other :
    forall g mid mid' m',
      mid <> mid' ->
      VMState.graph_lookup (VMState.graph_update g mid m') mid' = VMState.graph_lookup g mid'.
  Proof.
    intros g mid mid' m' Hneq.
    unfold VMState.graph_lookup, VMState.graph_update.
    simpl.
    apply graph_lookup_modules_insert_other.
    exact Hneq.
  Qed.

  (** [graph_add_axiom_other_unchanged]: formal specification. *)
  Lemma graph_add_axiom_other_unchanged :
    forall g mid mid' ax,
      mid <> mid' ->
      VMState.graph_lookup (VMState.graph_add_axiom g mid ax) mid' = VMState.graph_lookup g mid'.
  Proof.
    intros g mid mid' ax Hneq.
    unfold VMState.graph_add_axiom.
    destruct (VMState.graph_lookup g mid) as [m|] eqn:Hlookup; [|reflexivity].
    (* update touches only [mid] *)
    apply graph_lookup_update_other; exact Hneq.
  Qed.

  (** [graph_add_axioms_other_unchanged]: formal specification. *)
  Lemma graph_add_axioms_other_unchanged :
    forall axs g mid mid',
      mid <> mid' ->
      VMState.graph_lookup (VMState.graph_add_axioms g mid axs) mid' = VMState.graph_lookup g mid'.
  Proof.
    intros axs g mid mid' Hneq.
    unfold VMState.graph_add_axioms.
    revert g.
    induction axs as [|ax axs IH]; intro g; simpl.
    - reflexivity.
    - rewrite (IH (VMState.graph_add_axiom g mid ax)).
      rewrite graph_add_axiom_other_unchanged by exact Hneq.
      reflexivity.
  Qed.

  (** [no_signaling_pdiscover_graph]: formal specification. *)
  Theorem no_signaling_pdiscover_graph :
    forall s module evidence cost other,
      module <> other ->
      VMState.graph_lookup (VMState.vm_graph (SimulationProof.vm_apply s (VMStep.instr_pdiscover module evidence cost))) other =
      VMState.graph_lookup (VMState.vm_graph s) other.
  Proof.
    intros s module evidence cost other Hneq.
    simpl.
    (* vm_apply for pdiscover uses graph_record_discovery = graph_add_axioms *)
    unfold VMState.graph_record_discovery.
    apply graph_add_axioms_other_unchanged.
    exact Hneq.
  Qed.

  (** ---------------------------------------------------------------------
      PART III+ (Physics pillars): status

      The repository contains further files under [Physics], [Spacetime],
      [ThieleManifold], and [SpacetimeProjection] that explore projection-based
      physics embeddings.

      HOWEVER: a *fully internal* derivation of Relativity/QM/Gauge/Thermo as
      theorems of this substrate requires a formal “Reality interface”
      (observables + symmetry actions + admissibility constraints).

      Minimal missing ingredient (must be stated explicitly, not implied):
        - a typed observation functor from the substrate to an observation algebra.

      This file intentionally does not postulate that interface.
      --------------------------------------------------------------------- *)

End ThieleUnificationProtocol.
