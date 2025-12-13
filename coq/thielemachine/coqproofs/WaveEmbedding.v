(** * Embedding a reversible wave model into the Thiele VM

    This optional study mirrors the reversible lattice gas but focuses on a
    simple left/right propagating wave.  The embedding is abstract: any VM
    trace that simulates one [wave_step] with zero-cost instructions inherits
    the energy/momentum conservation laws and the µ-constancy/zero
    irreversibility guarantees provided by the ledger. *)

From Coq Require Import List Lia.
From Physics Require Import WaveModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

Section WaveEmbedding.
  Context (encode_wave : WaveState -> VMState)
          (decode_wave : VMState -> WaveState)
          (wave_trace : list vm_instruction).

  Variable decode_encode_id : forall S, decode_wave (encode_wave S) = S.
  Variable wave_vm_step_simulation :
    forall S, decode_wave (run_vm 1 wave_trace (encode_wave S)) = wave_step S.

  Variable wave_trace_irreversible_free :
    forall pc instr, nth_error wave_trace pc = Some instr -> instruction_cost instr = 0.

  (** ** Embedding correctness and invariants *)
  Lemma thiele_implements_wave_step :
    forall S,
      decode_wave (run_vm 1 wave_trace (encode_wave S)) = wave_step S.
  Proof. apply wave_vm_step_simulation. Qed.

  Lemma vm_preserves_wave_energy :
    forall S,
      wave_energy (decode_wave (run_vm 1 wave_trace (encode_wave S))) =
      wave_energy S.
  Proof.
    intro S. rewrite wave_vm_step_simulation.
    apply wave_energy_conserved.
  Qed.

  Lemma vm_preserves_wave_momentum :
    forall S,
      wave_momentum (decode_wave (run_vm 1 wave_trace (encode_wave S))) =
      wave_momentum S.
  Proof.
    intro S. rewrite wave_vm_step_simulation.
    apply wave_momentum_conserved.
  Qed.

  Corollary wave_vm_conserves_observables :
    forall S,
      wave_energy (decode_wave (run_vm 1 wave_trace (encode_wave S))) = wave_energy S /\
      wave_momentum (decode_wave (run_vm 1 wave_trace (encode_wave S))) = wave_momentum S.
  Proof.
    intro S. split; [apply vm_preserves_wave_energy | apply vm_preserves_wave_momentum].
  Qed.

  Corollary vm_wave_conservation_bundle :
    forall S,
      decode_wave (run_vm 1 wave_trace (encode_wave S)) = wave_step S /\
      wave_energy (decode_wave (run_vm 1 wave_trace (encode_wave S))) = wave_energy S /\
      wave_momentum (decode_wave (run_vm 1 wave_trace (encode_wave S))) = wave_momentum S.
  Proof.
    intro S. repeat split; auto using wave_vm_step_simulation, vm_preserves_wave_energy, vm_preserves_wave_momentum.
  Qed.

  (** ** Irreversibility accounting *)
  Lemma wave_trace_irreversible_count_zero :
    forall fuel s, irreversible_count fuel wave_trace s = 0.
  Proof.
    induction fuel as [|fuel IH]; intros s; simpl; auto.
    destruct (nth_error wave_trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl; auto.
    specialize (wave_trace_irreversible_free _ _ Hlookup) as Hcost.
    assert (irreversible_bits instr = 0) by (unfold irreversible_bits; rewrite Hcost; reflexivity).
    rewrite H. simpl. apply IH.
  Qed.

  Lemma wave_trace_ledger_sum_zero :
    forall fuel s, ledger_sum (ledger_entries fuel wave_trace s) = 0.
  Proof.
    induction fuel as [|fuel IH]; intros s; simpl; auto.
    destruct (nth_error wave_trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl; auto.
    specialize (wave_trace_irreversible_free _ _ Hlookup) as Hcost.
    rewrite Hcost. simpl. specialize (IH (vm_apply s instr)). lia.
  Qed.

  Corollary run_vm_mu_constant_for_wave :
    forall fuel s, (run_vm fuel wave_trace s).(vm_mu) = s.(vm_mu).
  Proof.
    intros fuel s.
    rewrite run_vm_mu_conservation.
    specialize (wave_trace_ledger_sum_zero fuel s) as Hsum.
    lia.
  Qed.

  Theorem wave_irreversible_count_zero :
    forall fuel s, irreversible_count fuel wave_trace s = 0.
  Proof. apply wave_trace_irreversible_count_zero. Qed.

  Corollary faithful_wave_mu_constant :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = wave_trace ->
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu).
  Proof.
    intros Impl fuel s Htrace.
    pose proof (hw_refines_vm Impl fuel s) as Hrefine.
    rewrite Htrace in Hrefine.
    rewrite Hrefine.
    apply run_vm_mu_constant_for_wave.
  Qed.

  Corollary faithful_wave_irreversibility_lower_bound :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = wave_trace ->
      irreversible_count fuel Impl.(hw_trace) (Impl.(hw_decode) s) = 0 /\
      0 <= (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) -
           (Impl.(hw_decode) s).(vm_mu).
  Proof.
    intros Impl fuel s Htrace.
    split.
    - rewrite Htrace. apply wave_trace_irreversible_count_zero.
    - pose proof (faithful_impl_irreversibility_lower_bound Impl fuel s) as Hbound.
      rewrite Htrace in Hbound.
      specialize (wave_trace_irreversible_count_zero fuel (Impl.(hw_decode) s)) as Hzero.
      lia.
  Qed.

  Corollary wave_mu_const_for_faithful_impl :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = wave_trace ->
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu).
  Proof. apply faithful_wave_mu_constant. Qed.

  (** ** Wrapped embedding witness for the PhysicsIsomorphism scaffold *)
  Definition wave_embedding : ThieleEmbedding wave_model :=
    {| emb_trace := wave_trace;
       emb_encode := (encode_wave : phys_state wave_model -> VMState);
       emb_decode := (decode_wave : VMState -> phys_state wave_model);
       emb_roundtrip := decode_encode_id;
       emb_step_sim := wave_vm_step_simulation;
       emb_cost_free := Some wave_trace_irreversible_free;
       emb_cost_positive := None |}.

  Lemma wave_trace_cost_free : embedding_trace_cost_free wave_embedding.
  Proof. exists wave_trace_irreversible_free; reflexivity. Qed.

  Corollary wave_zero_irreversibility_generic :
    forall fuel s,
      irreversible_count fuel wave_trace s = 0 /\
      (run_vm fuel wave_trace s).(vm_mu) = s.(vm_mu).
  Proof.
    intros fuel s.
    eapply (@reversible_embedding_zero_irreversibility wave_model wave_embedding); eauto.
    - exact I.
    - apply wave_trace_cost_free.
  Qed.

  Corollary wave_mu_const_for_faithful_impl_generic :
    forall (Impl : FaithfulImplementation) fuel s,
      Impl.(hw_trace) = wave_trace ->
      irreversible_count fuel Impl.(hw_trace) (Impl.(hw_decode) s) = 0 /\
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu).
  Proof.
    intros Impl fuel s Htrace.
    eapply (@reversible_embedding_zero_irreversibility_hw wave_model wave_embedding); eauto.
    - exact I.
    - apply wave_trace_cost_free.
  Qed.

  Theorem wave_embeddable : embeddable wave_model.
  Proof. exists wave_embedding; exact I. Qed.
End WaveEmbedding.
