(**
  THIELE UNIFICATION — TENSORIALITY (Kernel VM locality algebra)

  This module discharges the protocol’s “tensorial / independence” requirement
  for *local per-module operations* in the kernel VM semantics.

  Concretely: updates that target distinct module IDs commute observationally
  (they do not affect each other’s graph entries).
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From ThieleMachine Require Import ThieleUnificationProtocol.

Module ThieleUnificationTensor.

  (** [pg_next_id_graph_add_axiom]: formal specification. *)
  Lemma pg_next_id_graph_add_axiom :
    forall g mid ax,
      VMState.pg_next_id (VMState.graph_add_axiom g mid ax) = VMState.pg_next_id g.
  Proof.
    intros g mid ax.
    unfold VMState.graph_add_axiom.
    destruct (VMState.graph_lookup g mid) as [m|] eqn:?; [|reflexivity].
    unfold VMState.graph_update; simpl.
    reflexivity.
  Qed.

  (** [pg_next_id_graph_add_axioms]: formal specification. *)
  Lemma pg_next_id_graph_add_axioms :
    forall axs g mid,
      VMState.pg_next_id (VMState.graph_add_axioms g mid axs) = VMState.pg_next_id g.
  Proof.
    intros axs g mid.
    unfold VMState.graph_add_axioms.
    revert g.
    induction axs as [|ax axs IH]; intro g; simpl.
    - reflexivity.
    - rewrite (IH (VMState.graph_add_axiom g mid ax)).
      apply pg_next_id_graph_add_axiom.
  Qed.

  (** [graph_lookup_insert_modules_same]: formal specification. *)
  Lemma graph_lookup_insert_modules_same :
    forall modules mid m,
      VMState.graph_lookup_modules
        (VMState.graph_insert_modules modules mid (VMState.normalize_module m))
        mid
      = Some (VMState.normalize_module m).
  Proof.
    intros modules mid m.
    induction modules as [|(id, ms) rest IH]; simpl.
    - simpl.
      rewrite Nat.eqb_refl.
      reflexivity.
    - destruct (Nat.eqb id mid) eqn:Heq.
      + simpl.
        rewrite Nat.eqb_refl.
        reflexivity.
      + simpl.
        rewrite Heq.
        exact IH.
  Qed.

  (** [graph_lookup_update_same]: formal specification. *)
  Lemma graph_lookup_update_same :
    forall g mid m,
      VMState.graph_lookup (VMState.graph_update g mid m) mid =
      Some (VMState.normalize_module m).
  Proof.
    intros g mid m.
    unfold VMState.graph_lookup, VMState.graph_update.
    simpl.
    apply graph_lookup_insert_modules_same.
  Qed.

  (** [graph_add_axiom_mid_lookup_respects_lookup]: formal specification. *)
  Lemma graph_add_axiom_mid_lookup_respects_lookup :
    forall g1 g2 mid ax,
      VMState.graph_lookup g1 mid = VMState.graph_lookup g2 mid ->
      VMState.graph_lookup (VMState.graph_add_axiom g1 mid ax) mid =
      VMState.graph_lookup (VMState.graph_add_axiom g2 mid ax) mid.
  Proof.
    intros g1 g2 mid ax Hlk.
    unfold VMState.graph_add_axiom.
    (* rewrite the deciding lookup on g1 to be the same as g2 *)
    rewrite Hlk.
    destruct (VMState.graph_lookup g2 mid) as [m|] eqn:Hm.
    - (* both sides update mid with the same updated module; lookup(mid) is canonical *)
      rewrite !graph_lookup_update_same.
      reflexivity.
    - (* both sides are identity graphs at [mid] *)
      rewrite Hlk.
      rewrite Hm.
      reflexivity.
  Qed.

  (** [graph_add_axioms_mid_lookup_respects_lookup]: formal specification. *)
  Lemma graph_add_axioms_mid_lookup_respects_lookup :
    forall axs g1 g2 mid,
      VMState.graph_lookup g1 mid = VMState.graph_lookup g2 mid ->
      VMState.graph_lookup (VMState.graph_add_axioms g1 mid axs) mid =
      VMState.graph_lookup (VMState.graph_add_axioms g2 mid axs) mid.
  Proof.
    intros axs g1 g2 mid Hlk.
    unfold VMState.graph_add_axioms.
    revert g1 g2 Hlk.
    induction axs as [|ax axs IH]; intros g1 g2 Hlk; simpl.
    - exact Hlk.
    - apply IH.
      apply graph_add_axiom_mid_lookup_respects_lookup.
      exact Hlk.
  Qed.

  (** A lightweight notion of graph extensional equality. *)
  Definition graph_ext_eq (g1 g2 : VMState.PartitionGraph) : Prop :=
    (forall mid, VMState.graph_lookup g1 mid = VMState.graph_lookup g2 mid) /\
    VMState.pg_next_id g1 = VMState.pg_next_id g2.

  (** Graph-level commutation for discovery evidence on distinct modules. *)
  Theorem graph_record_discovery_commutes :
    forall g m1 ev1 m2 ev2,
      m1 <> m2 ->
      graph_ext_eq
        (VMState.graph_record_discovery (VMState.graph_record_discovery g m1 ev1) m2 ev2)
        (VMState.graph_record_discovery (VMState.graph_record_discovery g m2 ev2) m1 ev1).
  Proof.
    intros g m1 ev1 m2 ev2 Hneq.
    unfold graph_ext_eq.
    split.
    - intro mid.
      destruct (Nat.eq_dec mid m1) as [Hmid1|Hmid1].
      + subst mid.
        (* LHS: outer update at m2 doesn't affect lookup m1 *)
        unfold VMState.graph_record_discovery.
        rewrite ThieleUnificationProtocol.graph_add_axioms_other_unchanged
          by (intro H; apply Hneq; symmetry; exact H).
        (* RHS: base graph differs only at m2, so lookup at m1 is the same, hence the m1-update result matches. *)
        apply (graph_add_axioms_mid_lookup_respects_lookup ev1).
        assert (Hm2m1 : m2 <> m1) by (intro H; apply Hneq; symmetry; exact H).
        symmetry.
        apply ThieleUnificationProtocol.graph_add_axioms_other_unchanged.
        exact Hm2m1.
      + destruct (Nat.eq_dec mid m2) as [Hmid2|Hmid2].
        * subst mid.
          (* symmetric to the m1 case *)
          unfold VMState.graph_record_discovery.
          (* First, drop the outer m1-update on the RHS (it does not affect lookup at m2). *)
          rewrite (ThieleUnificationProtocol.graph_add_axioms_other_unchanged ev1
                     (VMState.graph_add_axioms g m2 ev2) m1 m2 Hneq).
          (* Now show the LHS m2-update result is independent of whether we pre-applied the m1-update. *)
          apply (graph_add_axioms_mid_lookup_respects_lookup ev2).
          apply ThieleUnificationProtocol.graph_add_axioms_other_unchanged.
          exact Hneq.
        * (* neither module: both updates leave this lookup unchanged *)
          unfold VMState.graph_record_discovery.
          rewrite ThieleUnificationProtocol.graph_add_axioms_other_unchanged
            by (intro H; apply Hmid2; symmetry; exact H).
          rewrite ThieleUnificationProtocol.graph_add_axioms_other_unchanged
            by (intro H; apply Hmid1; symmetry; exact H).
          rewrite ThieleUnificationProtocol.graph_add_axioms_other_unchanged
            by (intro H; apply Hmid1; symmetry; exact H).
          rewrite ThieleUnificationProtocol.graph_add_axioms_other_unchanged
            by (intro H; apply Hmid2; symmetry; exact H).
          reflexivity.
    - unfold VMState.graph_record_discovery.
      rewrite !pg_next_id_graph_add_axioms.
      reflexivity.
  Qed.

  (** Observable commutation (what we actually need): graph lookups coincide after swapping two independent discoveries. *)
  Theorem vm_apply_pdiscover_commutes_lookup :
    forall s m1 ev1 c1 m2 ev2 c2 other,
      m1 <> m2 ->
      VMState.graph_lookup
        (VMState.vm_graph
           (SimulationProof.vm_apply (SimulationProof.vm_apply s (VMStep.instr_pdiscover m1 ev1 c1))
                                    (VMStep.instr_pdiscover m2 ev2 c2)))
        other
      =
      VMState.graph_lookup
        (VMState.vm_graph
           (SimulationProof.vm_apply (SimulationProof.vm_apply s (VMStep.instr_pdiscover m2 ev2 c2))
                                    (VMStep.instr_pdiscover m1 ev1 c1)))
        other.
  Proof.
    intros s m1 ev1 c1 m2 ev2 c2 other Hneq.
    (* unfold vm_apply pdiscover twice *)
    simpl.
    unfold VMState.graph_record_discovery.
    (* Use commutation of graph_record_discovery at lookup level. *)
    pose proof (graph_record_discovery_commutes (VMState.vm_graph s) m1 ev1 m2 ev2 Hneq) as [Hlook _].
    exact (Hlook other).
  Qed.

End ThieleUnificationTensor.
