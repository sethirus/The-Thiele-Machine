(** * Physics-as-computation scaffold and conjectures

    This optional study packages a shared interface for discrete physics
    models, a single embedding contract into the verified VM, and the
    conjectures that drive the "physics ≅ computation" programme.  Concrete
    witnesses live in the embedding modules for the reversible lattice gas, the
    dissipative lattice, and the wave model.
*)

From Coq Require Import String ZArith Lia List PeanoNat.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge.
From Physics Require Import DiscreteModel DissipativeModel WaveModel.

Local Open Scope string_scope.
Import ListNotations.

(** ** Discrete physics interface

    The interface keeps only the minimal structure we want to reason about
    across all case studies: a step function, locality/finiteness markers, and
    two standard observables with an energy law that can either be conserving
    or strictly decreasing.
*)
Record DiscretePhysics := {
  phys_state       : Type;
  phys_step        : phys_state -> phys_state;
  phys_locality    : Prop;
  phys_finiteness  : Prop;
  phys_energy      : phys_state -> nat;
  phys_momentum    : phys_state -> Z;
  phys_energy_law  : forall s,
      phys_energy (phys_step s) = phys_energy s \/
      phys_energy (phys_step s) < phys_energy s;
  phys_reversible  : Prop
}.

(** ** Canonical embeddings into the VM

    A [ThieleEmbedding] packages the program trace plus encode/decode pair that
    realises one physics step as one VM step.  Each concrete case study can
    instantiate this record and then reuse the generic reversible/dissipative
    lemmas below.
*)
Record ThieleEmbedding (DP : DiscretePhysics) := {
  emb_trace        : list vm_instruction;
  emb_encode       : phys_state DP -> VMState;
  emb_decode       : VMState -> phys_state DP;
  emb_roundtrip    : forall s, emb_decode (emb_encode s) = s;
  emb_step_sim     : forall s,
      emb_decode (run_vm 1 emb_trace (emb_encode s)) = phys_step DP s;
  emb_cost_free    : option (forall pc instr,
                        nth_error emb_trace pc = Some instr ->
                        instruction_cost instr = 0);
  emb_cost_positive: option (forall pc instr,
                        nth_error emb_trace pc = Some instr ->
                        instruction_cost instr >= 1)
}.

Definition embedding_trace_cost_free {DP} (E : ThieleEmbedding DP) : Prop :=
  exists pf, emb_cost_free DP E = Some pf.

Definition embedding_trace_cost_positive {DP} (E : ThieleEmbedding DP) : Prop :=
  exists pf, emb_cost_positive DP E = Some pf.

(** ** Generic irreversible-bit and µ behaviour for an embedding *)
  Section EmbeddingLemmas.
  Context {DP : DiscretePhysics} (E : ThieleEmbedding DP).

  Notation trace := (emb_trace DP E).
  Notation encode := (emb_encode DP E).
  Notation decode := (emb_decode DP E).

(** [reversible_trace_irreversibility_count_zero]: formal specification. *)
Lemma reversible_trace_irreversibility_count_zero :
  embedding_trace_cost_free E ->
  forall fuel s_vm, irreversible_count fuel trace s_vm = 0.
Proof.
  intros Hfree fuel.
  destruct Hfree as [pf_cost Hcf].
  induction fuel as [|fuel IH]; intros s_vm; simpl; auto.
  destruct (nth_error trace (vm_pc s_vm)) as [instr|] eqn:Hlookup; simpl; auto.
  specialize (pf_cost _ _ Hlookup) as Hcost.
  pose proof (irreversible_bits_le_cost instr) as Hbound.
  assert (irreversible_bits instr = 0) by (rewrite Hcost in Hbound; lia).
  rewrite H. simpl. apply IH.
Qed.

(** [reversible_trace_ledger_sum_zero]: formal specification. *)
Lemma reversible_trace_ledger_sum_zero :
  embedding_trace_cost_free E ->
  forall fuel s_vm, ledger_sum (ledger_entries fuel trace s_vm) = 0.
Proof.
  intros Hfree fuel.
  destruct Hfree as [pf_cost Hcf].
  induction fuel as [|fuel IH]; intros s_vm; simpl; auto.
  destruct (nth_error trace (vm_pc s_vm)) as [instr|] eqn:Hlookup; simpl; auto.
  specialize (pf_cost _ _ Hlookup) as Hcost.
  rewrite Hcost. simpl.
  specialize (IH (vm_apply s_vm instr)). lia.
Qed.

(** [reversible_embedding_zero_irreversibility]: formal specification. *)
Lemma reversible_embedding_zero_irreversibility :
  phys_reversible DP -> embedding_trace_cost_free E ->
    forall fuel (s_vm : VMState),
      irreversible_count fuel trace s_vm = 0 /\
      (run_vm fuel trace s_vm).(vm_mu) = s_vm.(vm_mu).
Proof.
  intros _ Hfree fuel s_vm.
  split.
  - apply reversible_trace_irreversibility_count_zero; assumption.
  - rewrite run_vm_mu_conservation.
    specialize (reversible_trace_ledger_sum_zero Hfree fuel s_vm) as Hsum.
    lia.
Qed.

(** [irreversible_count_positive_from_cost]: formal specification. *)
Lemma irreversible_count_positive_from_cost :
  embedding_trace_cost_positive E ->
  forall fuel s_vm instr,
    fuel > 0 -> nth_error trace s_vm.(vm_pc) = Some instr ->
    irreversible_count fuel trace s_vm >= 1.
Proof.
  intros Hpos fuel s_vm instr Hfuel Hlookup.
  destruct Hpos as [pf_cost Hposcf].
  destruct fuel as [|fuel']; [lia|].
  simpl. rewrite Hlookup.
  specialize (pf_cost _ _ Hlookup) as Hcost.
  unfold irreversible_bits.
  destruct (Nat.eqb (instruction_cost instr) 0) eqn:Hzero.
  - apply Nat.eqb_eq in Hzero. lia.
  - lia.
Qed.

(** [dissipative_embedding_mu_gap]: formal specification. *)
Lemma dissipative_embedding_mu_gap :
  embedding_trace_cost_positive E ->
  forall fuel s_vm instr,
    fuel > 0 -> nth_error trace s_vm.(vm_pc) = Some instr ->
    (run_vm fuel trace s_vm).(vm_mu) >= s_vm.(vm_mu) + 1.
Proof.
  intros Hpos fuel s_vm instr Hfuel Hlookup.
  specialize (run_vm_irreversibility_gap fuel trace s_vm) as Hgap.
  specialize (irreversible_count_positive_from_cost Hpos fuel s_vm instr Hfuel Hlookup) as Hirr.
  lia.
Qed.

(** [reversible_embedding_zero_irreversibility_hw]: formal specification. *)
Lemma reversible_embedding_zero_irreversibility_hw :
  phys_reversible DP -> embedding_trace_cost_free E ->
  forall (Impl : FaithfulImplementation) fuel s_hw,
    Impl.(hw_trace) = trace ->
    irreversible_count fuel Impl.(hw_trace) (Impl.(hw_decode) s_hw) = 0 /\
    (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s_hw)).(vm_mu) =
    (Impl.(hw_decode) s_hw).(vm_mu).
Proof.
  intros Hrev Hfree Impl fuel s_hw Htrace.
  split.
  - rewrite Htrace. apply reversible_trace_irreversibility_count_zero; assumption.
  - pose proof (hw_refines_vm Impl fuel s_hw) as Hrefine.
    rewrite Htrace in Hrefine.
    rewrite Hrefine.
    specialize (reversible_embedding_zero_irreversibility Hrev Hfree fuel (hw_decode Impl s_hw)) as Hmu.
    tauto.
Qed.

(** [dissipative_embedding_mu_gap_hw]: formal specification. *)
Lemma dissipative_embedding_mu_gap_hw :
  embedding_trace_cost_positive E ->
  forall (Impl : FaithfulImplementation) fuel s_hw instr,
    fuel > 0 -> Impl.(hw_trace) = trace ->
    nth_error trace (hw_decode Impl s_hw).(vm_pc) = Some instr ->
    (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s_hw)).(vm_mu) >=
      (Impl.(hw_decode) s_hw).(vm_mu) + 1.
Proof.
  intros Hpos Impl fuel s_hw instr Hfuel Htrace Hlookup.
  pose proof (hw_refines_vm Impl fuel s_hw) as Hrefine.
  rewrite Htrace in Hrefine.
  rewrite Hrefine.
  eapply dissipative_embedding_mu_gap; eauto.
Qed.
End EmbeddingLemmas.


(** ** Concrete physics models (structure only) *)
Definition lattice_gas_model : DiscretePhysics.
Proof.
  refine {| phys_state := DiscreteModel.Lattice;
            phys_step := DiscreteModel.physics_step;
            phys_locality := True;
            phys_finiteness := True;
            phys_energy := DiscreteModel.particle_count;
            phys_momentum := DiscreteModel.momentum;
            phys_energy_law := _;
            phys_reversible := True |}.
  intro L.
  left.
  apply DiscreteModel.physics_preserves_particle_count.
Defined.

  Definition dissipative_model : DiscretePhysics.
  Proof.
    refine {| phys_state := DissipativeModel.Lattice;
              phys_step := DissipativeModel.dissipative_step;
              phys_locality := True;
              phys_finiteness := True;
              phys_energy := DissipativeModel.energy;
              phys_momentum := fun _ => 0%Z;
              phys_energy_law := _;
              phys_reversible := False |}.
    intro l.
    destruct (Nat.eq_dec (DissipativeModel.energy l) 0) as [Hz|Hnz].
    - left. rewrite Hz, DissipativeModel.dissipative_step_energy_zero. reflexivity.
    - right. apply DissipativeModel.dissipative_energy_strict_when_hot. lia.
  Defined.

Definition wave_model : DiscretePhysics.
Proof.
  refine {| phys_state := WaveModel.WaveState;
            phys_step := WaveModel.wave_step;
            phys_locality := True;
            phys_finiteness := True;
            phys_energy := WaveModel.wave_energy;
            phys_momentum := WaveModel.wave_momentum;
            phys_energy_law := _;
            phys_reversible := True |}.
  intro S.
  left.
  apply WaveModel.wave_energy_conserved.
Defined.

(** ** Case-study catalogue for the paper appendix *)
Record EmbeddingCaseStudy := {
  study_name      : string;
  study_model     : DiscretePhysics;
  study_invariants: string;
  study_entropy   : string;
  study_status    : string
}.

Definition lattice_gas_case : EmbeddingCaseStudy.
Proof.
  refine {| study_name := "Reversible lattice gas";
            study_model := lattice_gas_model;
            study_invariants := "Particle count and momentum conserved; involutive local swap";
            study_entropy := "µ and irreversible_count stay zero along the compiled trace";
            study_status := "Embedding and faithful µ-constancy in PhysicsEmbedding.v" |}.
Defined.

Definition dissipative_case : EmbeddingCaseStudy.
Proof.
  refine {| study_name := "Dissipative lattice";
            study_model := dissipative_model;
            study_invariants := "Energy strictly drops on any hot configuration";
            study_entropy := "Any faithful implementation pays ≥1 µ per simulated step";
            study_status := "Embedding and lower bound packaged in DissipativeEmbedding.v" |}.
Defined.

Definition wave_case : EmbeddingCaseStudy.
Proof.
  refine {| study_name := "Wave propagation";
            study_model := wave_model;
            study_invariants := "Energy and momentum conserved; step is invertible";
            study_entropy := "µ and irreversible_count stay zero along the propagated trace";
            study_status := "Embedding hooks live in WaveEmbedding.v" |}.
Defined.

Definition embedded_case_studies : list EmbeddingCaseStudy :=
  lattice_gas_case :: dissipative_case :: wave_case :: nil.

(** ** Embedding goals and conjectures *)
Definition embeddable (DP : DiscretePhysics) : Prop :=
  exists (E : ThieleEmbedding DP), True.

Definition reversible_complete : Prop :=
  forall DP, phys_reversible DP -> phys_locality DP -> embeddable DP.

Definition dissipative_entropy_compatible : Prop :=
  forall DP,
    (exists s, phys_energy DP (phys_step DP s) < phys_energy DP s) ->
    embeddable DP.

Definition lattice_gas_embedding_goal : Prop := embeddable lattice_gas_model.
Definition dissipative_embedding_goal : Prop := embeddable dissipative_model.
Definition wave_embedding_goal : Prop := embeddable wave_model.

