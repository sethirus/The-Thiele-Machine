(** * Embedding the reversible lattice gas into the Thiele VM

    This optional study connects the discrete physics model from
    [Physics.DiscreteModel] to the verified VM semantics.  The encoding and
    compiled trace stay abstract; once a simulation lemma is available, the
    conservation laws and irreversibility bounds transport automatically. *)

From Coq Require Import List Lia.
From Physics Require Import DiscreteModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

Section PhysicsEmbedding.
  Context (encode_lattice : Lattice -> VMState)
          (decode_lattice : VMState -> Lattice)
          (physics_trace : list vm_instruction).

  Variable decode_encode_id : forall L, decode_lattice (encode_lattice L) = L.
  Variable physics_vm_step_simulation :
    forall L, decode_lattice (run_vm 1 physics_trace (encode_lattice L)) = physics_step L.

  Variable physics_trace_irreversible_free :
    forall pc instr, nth_error physics_trace pc = Some instr -> instruction_cost instr = 0.

  (** ** Embedding correctness: one VM run step realises one physics step. *)
  Lemma thiele_implements_physics_step :
    forall L,
      decode_lattice (run_vm 1 physics_trace (encode_lattice L)) = physics_step L.
  Proof. apply physics_vm_step_simulation. Qed.

  (** A more descriptive alias so the case study reads cleanly. *)
  Definition thiele_implements_lattice_step := thiele_implements_physics_step.

  (** ** Machine-level conservation laws *)
  Lemma vm_preserves_particle_count :
    forall L,
      particle_count (decode_lattice (run_vm 1 physics_trace (encode_lattice L))) =
      particle_count L.
  Proof.
    intros L. rewrite physics_vm_step_simulation.
    apply physics_preserves_particle_count.
  Qed.

  Lemma vm_preserves_momentum :
    forall L,
      momentum (decode_lattice (run_vm 1 physics_trace (encode_lattice L))) =
      momentum L.
  Proof.
    intros L. rewrite physics_vm_step_simulation.
    apply physics_preserves_momentum.
  Qed.

  Theorem lattice_vm_conserves_observables :
    forall L,
      particle_count (decode_lattice (run_vm 1 physics_trace (encode_lattice L))) = particle_count L /\
      momentum (decode_lattice (run_vm 1 physics_trace (encode_lattice L))) = momentum L.
  Proof.
    intro L. split; [apply vm_preserves_particle_count | apply vm_preserves_momentum].
  Qed.

  Corollary vm_preserves_lattice_invariants :
    forall L,
      decode_lattice (run_vm 1 physics_trace (encode_lattice L)) = physics_step L /\
      particle_count (decode_lattice (run_vm 1 physics_trace (encode_lattice L))) = particle_count L /\
      momentum (decode_lattice (run_vm 1 physics_trace (encode_lattice L))) = momentum L.
  Proof.
    intro L.
    split.
    - apply physics_vm_step_simulation.
    - split; [apply vm_preserves_particle_count | apply vm_preserves_momentum].
  Qed.

  (** ** Reversibility reflected in ledger and irreversibility counters *)
  Lemma physics_trace_irreversible_count_zero :
    forall fuel s, irreversible_count fuel physics_trace s = 0.
  Proof.
    induction fuel as [|fuel IH]; intros s; simpl; auto.
    destruct (nth_error physics_trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl; auto.
    specialize (physics_trace_irreversible_free _ _ Hlookup) as Hcost.
    assert (irreversible_bits instr = 0) by (unfold irreversible_bits; rewrite Hcost; reflexivity).
    rewrite H. simpl.
    apply IH.
  Qed.

  Lemma physics_trace_ledger_sum_zero :
    forall fuel s, ledger_sum (ledger_entries fuel physics_trace s) = 0.
  Proof.
    induction fuel as [|fuel IH]; intros s; simpl; auto.
    destruct (nth_error physics_trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl; auto.
    specialize (physics_trace_irreversible_free _ _ Hlookup) as Hcost.
    rewrite Hcost. simpl.
    specialize (IH (vm_apply s instr)).
    rewrite IH. lia.
  Qed.

  Corollary run_vm_mu_constant_for_physics :
    forall fuel s,
      (run_vm fuel physics_trace s).(vm_mu) = s.(vm_mu).
  Proof.
    intros fuel s.
    rewrite run_vm_mu_conservation.
    specialize (physics_trace_ledger_sum_zero fuel s) as Hsum.
    lia.
  Qed.

  Theorem lattice_irreversible_count_zero :
    forall fuel s, irreversible_count fuel physics_trace s = 0.
  Proof. apply physics_trace_irreversible_count_zero. Qed.

  Corollary faithful_physics_mu_constant :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = physics_trace ->
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu).
  Proof.
    intros Impl fuel s Htrace.
    pose proof (hw_refines_vm Impl fuel s) as Hrefine.
    rewrite Htrace in Hrefine.
    rewrite Hrefine.
    apply run_vm_mu_constant_for_physics.
  Qed.

  Corollary faithful_physics_irreversibility_lower_bound :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = physics_trace ->
      irreversible_count fuel Impl.(hw_trace) (Impl.(hw_decode) s) = 0 /\
      0 <= (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) -
           (Impl.(hw_decode) s).(vm_mu).
  Proof.
    intros Impl fuel s Htrace.
    split.
    - rewrite Htrace. apply physics_trace_irreversible_count_zero.
    - pose proof (faithful_impl_irreversibility_lower_bound Impl fuel s) as Hbound.
      rewrite Htrace in Hbound.
      specialize (physics_trace_irreversible_count_zero fuel (Impl.(hw_decode) s)) as Hzero.
      lia.
  Qed.

  Corollary lattice_mu_const_for_faithful_impl :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = physics_trace ->
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu).
  Proof. apply faithful_physics_mu_constant. Qed.

  (** ** Wrapped embedding witness for the PhysicsIsomorphism scaffold *)
  Definition lattice_gas_embedding : ThieleEmbedding lattice_gas_model :=
    {| emb_trace := physics_trace;
       emb_encode := (encode_lattice : phys_state lattice_gas_model -> VMState);
       emb_decode := (decode_lattice : VMState -> phys_state lattice_gas_model);
       emb_roundtrip := decode_encode_id;
       emb_step_sim := physics_vm_step_simulation;
       emb_cost_free := Some physics_trace_irreversible_free;
       emb_cost_positive := None |}.

  Lemma lattice_gas_trace_cost_free : embedding_trace_cost_free lattice_gas_embedding.
  Proof. exists physics_trace_irreversible_free; reflexivity. Qed.

  Corollary lattice_gas_zero_irreversibility_generic :
    forall fuel s,
      irreversible_count fuel physics_trace s = 0 /\
      (run_vm fuel physics_trace s).(vm_mu) = s.(vm_mu).
  Proof.
    intros fuel s.
    eapply (@reversible_embedding_zero_irreversibility lattice_gas_model lattice_gas_embedding); eauto.
    - exact I.
    - apply lattice_gas_trace_cost_free.
  Qed.

  Corollary lattice_gas_mu_const_for_faithful_impl_generic :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = physics_trace ->
      irreversible_count fuel Impl.(hw_trace) (Impl.(hw_decode) s) = 0 /\
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu).
  Proof.
    intros Impl fuel s Htrace.
    eapply (@reversible_embedding_zero_irreversibility_hw lattice_gas_model lattice_gas_embedding); eauto.
    - exact I.
    - apply lattice_gas_trace_cost_free.
  Qed.

  Theorem lattice_gas_embeddable : embeddable lattice_gas_model.
  Proof. exists lattice_gas_embedding; exact I. Qed.
End PhysicsEmbedding.

