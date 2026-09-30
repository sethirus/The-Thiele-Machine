(** Closed evidence for the frozen Part 1, Item 1.2 propositions. *)

From Coq Require Import List Bool Arith.PeanoNat Lia NArith.
Import ListNotations.

From Kernel Require Import EventGeneralizationTargets EventSwapCore.
From Kernel Require Import VMState VMStep SimulationProof VMUnboundedStep.
From Kernel Require Import MuInitiality.
From Kernel Require Import NecessityAbstract ShadowPricing.
From Kernel Require Import PermanentCertification PermanentRecordPricing.
From Kernel Require Import FiniteCertMachine.
From Kernel Require Import BlindnessRepresentation ProjectionNonExistence.
From Kernel Require Import ThieleTraceProjection WitnessPreservationImpossibility.
From Kernel Require Import CHSHStatisticalBridge.
From Kernel Require Import SpacetimeEmergence VMWord64BoundednessObstruction.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import StructuralCore StructuralCoreRound2.
From Kernel Require Import StructuralCoreRound3 StructuralUniqueness.
From Kernel Require Import StructuralScheduleUniqueness.
From Kernel Require Import UniversalCertificationCost TraceStateDescent.

(** A graph-allocation event. A zero-cost PNEW writes it. *)
Definition eg_graph_reading : Reading :=
  fun s => 1 <=? pg_next_id (vm_graph s).

Lemma eg_next_id_monotone : forall s i,
  pg_next_id (vm_graph s) <= pg_next_id (vm_graph (vm_apply s i)).
Proof.
  intros s i.
  destruct i; cbn [vm_apply];
    repeat match goal with
    | |- context [if ?x then _ else _] => destruct x eqn:?
    | |- context [match ?x with Some _ => _ | None => _ end] => destruct x eqn:?
    | |- context [let '(_, _) := ?x in _] => destruct x eqn:?
    end;
    cbn [vm_graph advance_state advance_state_reveal advance_state_rm
         jump_state jump_state_rm];
    try lia.
  all: repeat match goal with H : ?x = (_, _) |- _ => is_var x; subst x end.
  all: first
    [ apply graph_hw_psplit_next_id_nondec
    | apply graph_hw_pmerge_next_id_nondec
    | rewrite graph_update_module_tensor_next_id_same; lia
    | match goal with H : graph_add_module ?g ?r ?a = _ |- _ =>
        pose proof (graph_add_module_next_id_nondec g r a) as Hn;
        rewrite H in Hn; exact Hn end
    | match goal with H : graph_add_morphism ?g ?a ?b ?c ?d = _ |- _ =>
        pose proof (graph_add_morphism_next_id_same g a b c d) as Hn;
        rewrite H in Hn; simpl in Hn; lia end
    | match goal with H : graph_compose_morphisms _ _ _ = Some _ |- _ =>
        rewrite (graph_compose_morphisms_next_id_same _ _ _ _ _ H); lia end
    | match goal with H : graph_add_identity _ _ = Some _ |- _ =>
        rewrite (graph_add_identity_next_id_same _ _ _ _ H); lia end
    | match goal with H : graph_tensor_morphisms _ _ _ = Some _ |- _ =>
        rewrite (graph_tensor_morphisms_next_id_same _ _ _ _ _ H); lia end
    | match goal with H : graph_delete_morphism _ _ = Some _ |- _ =>
        rewrite (graph_delete_morphism_next_id_same _ _ _ H); lia end ].
Qed.

Lemma eg_graph_latchable : latchable eg_graph_reading.
Proof.
  split.
  - intros s i H. unfold eg_graph_reading in *.
    apply Nat.leb_le in H. apply Nat.leb_le.
    pose proof (eg_next_id_monotone s i). lia.
  - exists abs_zero, (instr_pnew [] 0). split; reflexivity.
Qed.

Lemma eg_graph_not_priced : ~ EventSwapCore.priced eg_graph_reading.
Proof.
  intro H. specialize (H abs_zero (instr_pnew [] 0) eq_refl eq_refl).
  simpl in H. lia.
Qed.

Lemma eg_graph_not_step_mu : ~ event_step_mu_paid eg_graph_reading.
Proof.
  intro H. specialize (H abs_zero (instr_pnew [] 0)).
  assert (W : event_writes eg_graph_reading abs_zero (instr_pnew [] 0))
    by (split; reflexivity).
  specialize (H W). rewrite vm_apply_mu in H. simpl in H. lia.
Qed.

Lemma eg_graph_not_trace_mu : ~ event_trace_mu_paid eg_graph_reading.
Proof.
  intro H. apply eg_graph_not_step_mu.
  intros s i W. exact (H [i] s W).
Qed.

Lemma eg_graph_not_trace_cost :
  ~ (forall trace s, event_trace_writes eg_graph_reading trace s ->
       event_trace_cost trace >= 1).
Proof.
  intro H. specialize (H [instr_pnew [] 0] abs_zero).
  assert (W : event_trace_writes eg_graph_reading [instr_pnew [] 0] abs_zero)
    by (split; reflexivity).
  specialize (H W). simpl in H. lia.
Qed.

Theorem eg_refutes_generalized_step_price : ~ generalized_step_price.
Proof.
  intro H. exact (eg_graph_not_priced (H eg_graph_reading eg_graph_latchable)).
Qed.

Theorem eg_refutes_generalized_step_mu : ~ generalized_step_mu.
Proof.
  intro H. exact (eg_graph_not_step_mu (H eg_graph_reading eg_graph_latchable)).
Qed.

Theorem eg_refutes_generalized_step_price_and_mu :
  ~ generalized_step_price_and_mu.
Proof.
  intros H.
  specialize (H eg_graph_reading eg_graph_latchable abs_zero (instr_pnew [] 0)).
  assert (W : event_writes eg_graph_reading abs_zero (instr_pnew [] 0))
    by (split; reflexivity).
  destruct (H W) as [Hcost _]. simpl in Hcost. lia.
Qed.

Theorem eg_refutes_generalized_trace_mu : ~ generalized_trace_mu.
Proof.
  intro H. exact (eg_graph_not_trace_mu (H eg_graph_reading eg_graph_latchable)).
Qed.

Theorem eg_refutes_generalized_trace_cost : ~ generalized_trace_cost.
Proof.
  intro H.
  exact (eg_graph_not_trace_cost (H eg_graph_reading eg_graph_latchable)).
Qed.

Theorem eg_refutes_generalized_event_unit_price_lower_bounds_mu :
  ~ generalized_event_unit_price_lower_bounds_mu.
Proof.
  intro H.
  specialize (H eg_graph_reading eg_graph_latchable abs_zero (instr_pnew [] 0) eq_refl).
  unfold event_unit_cost, event_unit_charge in H. simpl in H. lia.
Qed.

Theorem eg_refutes_generalized_partition_refinement_nonfree :
  ~ generalized_partition_refinement_nonfree.
Proof.
  intro H. apply eg_refutes_generalized_trace_mu.
  intros E HL trace s W. exact (proj2 (H E HL trace s W)).
Qed.

Theorem eg_refutes_generalized_partition_free_but_event_nonfree :
  ~ generalized_partition_free_but_event_nonfree.
Proof.
  intros [_ [_ [_ [_ [_ [_ H]]]]]].
  exact (eg_refutes_generalized_trace_mu H).
Qed.

Theorem eg_refutes_generalized_bounded_run_mu : ~ generalized_bounded_run_mu.
Proof.
  intro H.
  specialize (H eg_graph_reading eg_graph_latchable 1
                [instr_pnew [] 0] abs_zero eq_refl eq_refl eq_refl).
  change (0 < vm_mu (vm_apply abs_zero (instr_pnew [] 0))) in H.
  rewrite vm_apply_mu in H. simpl in H. lia.
Qed.

Theorem eg_refutes_generalized_certify_pnew_separation :
  ~ generalized_certify_pnew_separation.
Proof.
  intro H.
  specialize (H eg_graph_reading eg_graph_latchable abs_zero).
  destruct H as [_ [_ [_ HE]]]. discriminate.
Qed.

(** Every trace-level false-to-true change contains a semantic writer. *)
Lemma eg_trace_has_writer : forall E, event_trace_has_writer E.
Proof.
  intros E trace.
  induction trace as [| i rest IH]; intros s [Hs Hend].
  - simpl in Hend. rewrite Hs in Hend. discriminate.
  - simpl in Hend.
    destruct (E (vm_apply s i)) eqn:Hmid.
    + exists i. split; [left; reflexivity |].
      exists s. split; assumption.
    + destruct (IH (vm_apply s i) (conj Hmid Hend))
        as [j [Hin [before Hwrite]]].
      exists j. split; [right; exact Hin |]. exists before. exact Hwrite.
Qed.

Theorem eg_proves_generalized_trace_writer : generalized_trace_writer.
Proof. intros E _. exact (eg_trace_has_writer E). Qed.

(** The finite-state theorems depend only on permanence and finiteness. *)
Theorem eg_proves_generalized_finite_permanent : generalized_finite_permanent.
Proof. intros E [Hperm _]. exact Hperm. Qed.

Theorem eg_proves_generalized_finite_writer_merge :
  generalized_finite_writer_merge.
Proof.
  intros E [Hperm _] s i Hs Hwrite.
  exact (PermanentCertification.permanent_flip_is_not_injective
           FState FInstr fstep E all_fstates s i fin_finite Hperm Hs Hwrite).
Qed.

Theorem eg_proves_generalized_finite_a2_from_merging_price :
  generalized_finite_a2_from_merging_price.
Proof.
  intros E [Hperm _].
  exact (PermanentCertification.a2_from_merging_price_and_permanence
           FState FInstr fstep E fcost all_fstates fin_finite Hperm
           fin_merging_priced).
Qed.

Theorem eg_proves_generalized_finite_a2_from_compression_price :
  generalized_finite_a2_from_compression_price.
Proof.
  intros E [Hperm _].
  exact (PermanentRecordPricing.a2_from_compression_price_and_permanence
           FState FInstr fstep E fcost fstate_eq_dec all_fstates fin_finite
           Hperm fin_compression_priced).
Qed.

(** The canonical unit charge is exact by Boolean case analysis. *)
Theorem eg_proves_generalized_event_unit_pricing_exact :
  generalized_event_unit_pricing_exact.
Proof.
  intros E _; split; intros s i H.
  - unfold ShadowPricing.flips in H.
    unfold event_unit_cost, event_unit_charge. rewrite H. lia.
  - unfold ShadowPricing.flips in H.
    unfold event_unit_cost, event_unit_charge. rewrite H. reflexivity.
Qed.

(** Full event projections expose both requested coordinates. *)
Theorem eg_proves_generalized_projection_irredundancy :
  generalized_projection_irredundancy.
Proof.
  intros E _; repeat split.
  - exists (fun x => let '(_, _, _, m, _) := x in m).
    intro s. reflexivity.
  - exists (fun x => let '(_, _, _, _, e) := x in e).
    intro s. reflexivity.
  - intros C P Hforget.
    exact (NecessityAbstract.forgets_mu_not_mu_complete P Hforget).
  - intros C P [s1 [s2 [HP HE]]] [Omega HO].
    apply HE. rewrite <- (HO s1), <- (HO s2), HP. reflexivity.
Qed.

Theorem eg_proves_generalized_joint_ledger_necessity :
  generalized_joint_ledger_necessity.
Proof.
  intros E _ [Omega HO].
  apply NecessityAbstract.turing_ram_mu_necessity.
  exists (fun x => fst (Omega x)). intro s.
  pose proof (f_equal fst (HO s)) as H. exact H.
Qed.

Theorem eg_proves_generalized_revocation_boundary :
  generalized_revocation_boundary.
Proof.
  intros S I step E Hperm [s [i [Hs Hoff]]].
  specialize (Hperm s i Hs). rewrite Hoff in Hperm. discriminate.
Qed.

Theorem eg_proves_generalized_certified_spec : generalized_certified_spec.
Proof. intros E trace s0. reflexivity. Qed.

(** The positive-ledger event is visible to the forgetful projection. *)
Definition eg_mu_reading : Reading := fun s => 1 <=? vm_mu s.

Lemma eg_mu_latchable : latchable eg_mu_reading.
Proof.
  split.
  - intros s i H. unfold eg_mu_reading in *.
    apply Nat.leb_le in H. apply Nat.leb_le. rewrite vm_apply_mu. lia.
  - exists abs_zero, (instr_certify 0). split; reflexivity.
Qed.

Lemma eg_mu_visible_to_forget : ~ hidden_from_forget eg_mu_reading.
Proof.
  intro H. apply H. exists (fun t => 1 <=? tms_mu t). intro s. reflexivity.
Qed.

Theorem eg_refutes_generalized_forget_hidden : ~ generalized_forget_hidden.
Proof.
  intro H. exact (eg_mu_visible_to_forget (H eg_mu_reading eg_mu_latchable)).
Qed.

(** A correct register and memory size is a projection-visible latch. Its
    writer starts from a VMState allowed by the record type but outside the
    fixed-size machine invariant. *)
Definition eg_size_view (regs mem : list nat) : bool :=
  (length regs =? REG_COUNT) && (length mem =? MEM_SIZE).

Definition eg_size_reading : Reading :=
  fun s => eg_size_view (vm_regs s) (vm_mem s).

Lemma eg_size_reading_spec : forall s,
  eg_size_reading s = true <->
  length (vm_regs s) = REG_COUNT /\ length (vm_mem s) = MEM_SIZE.
Proof.
  intro s. unfold eg_size_reading, eg_size_view.
  rewrite andb_true_iff, !Nat.eqb_eq. tauto.
Qed.

Lemma eg_size_permanent : permanent_reading eg_size_reading.
Proof.
  intros s i H. apply eg_size_reading_spec in H. destruct H as [Hrl Hml].
  apply eg_size_reading_spec.
  destruct i; cbn [vm_apply];
    repeat match goal with
    | |- context [if ?x then _ else _] => destruct x
    | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
    | |- context [let '(_, _) := ?x in _] => destruct x
    end;
    cbn [vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
         vm_logic_acc vm_mstatus vm_witness vm_certified
         advance_state advance_state_reveal advance_state_rm
         jump_state jump_state_rm];
    split;
    (exact Hrl || exact Hml
     || (apply write_reg_length; exact Hrl)
     || (apply write_mem_length; exact Hml)
     || (apply swap_regs_length; exact Hrl)).
Qed.

Definition eg_size_broken : VMState := {|
  vm_graph := abs_empty_graph;
  vm_csrs := abs_empty_csrs;
  vm_regs := repeat 0 15;
  vm_mem := repeat 0 128;
  vm_pc := 0;
  vm_mu := 0;
  vm_mu_tensor := repeat 0 16;
  vm_err := false;
  vm_logic_acc := 0;
  vm_mstatus := 0;
  vm_witness := abs_empty_witness;
  vm_certified := false
|}.

Definition eg_size_repair : vm_instruction := instr_load_imm 15 0 0.

Lemma eg_size_broken_off : eg_size_reading eg_size_broken = false.
Proof. reflexivity. Qed.

Lemma eg_size_repair_on :
  eg_size_reading (vm_apply eg_size_broken eg_size_repair) = true.
Proof. reflexivity. Qed.

Lemma eg_size_latchable : latchable eg_size_reading.
Proof.
  split; [exact eg_size_permanent |].
  exists eg_size_broken, eg_size_repair.
  exact (conj eg_size_broken_off eg_size_repair_on).
Qed.

Lemma eg_size_visible_to_bare : ~ hidden_from_bare eg_size_reading.
Proof.
  intro H. apply H.
  exists (fun t => eg_size_view (bto_regs t) (bto_mem t)).
  intro s. reflexivity.
Qed.

Lemma eg_size_bare_price_exact : ~ bare_price_inexact eg_size_reading.
Proof.
  intro H.
  destruct (ShadowPricing.window_showing_reading_prices_exactly
              VMState vm_instruction BareTMObservable vm_apply eg_size_reading
              bare_observable
              (fun t => eg_size_view (bto_regs t) (bto_mem t))
              (fun s => eq_refl)) as [price Hprice].
  exact (H price Hprice).
Qed.

Lemma eg_size_forget_price_exact : ~ forget_price_inexact eg_size_reading.
Proof.
  intro H.
  destruct (ShadowPricing.window_showing_reading_prices_exactly
              VMState vm_instruction TMSnapshot vm_apply eg_size_reading forget
              (fun t => eg_size_view (tms_regs t) (tms_mem t))
              (fun s => eq_refl)) as [price Hprice].
  exact (H price Hprice).
Qed.

Theorem eg_refutes_generalized_bare_price_inexact :
  ~ generalized_bare_price_inexact.
Proof.
  intro H. exact (eg_size_bare_price_exact (H eg_size_reading eg_size_latchable)).
Qed.

Theorem eg_refutes_generalized_forget_price_inexact :
  ~ generalized_forget_price_inexact.
Proof.
  intro H.
  exact (eg_size_forget_price_exact (H eg_size_reading eg_size_latchable)).
Qed.

Lemma eg_size_complete_strict : event_complete P_strict eg_size_reading.
Proof.
  exists (fun x => eg_size_view (NecessityAbstract.ss_regs x)
                                (NecessityAbstract.ss_mem x)).
  intro s. reflexivity.
Qed.

Lemma eg_size_complete_cost : event_complete P_cost eg_size_reading.
Proof.
  exists (fun x => eg_size_view (NecessityAbstract.cs_regs x)
                                (NecessityAbstract.cs_mem x)).
  intro s. reflexivity.
Qed.

Theorem eg_refutes_generalized_strict_projection_necessity :
  ~ generalized_strict_projection_necessity.
Proof.
  intro H. exact ((H eg_size_reading eg_size_latchable) eg_size_complete_strict).
Qed.

Theorem eg_refutes_generalized_cost_projection_necessity :
  ~ generalized_cost_projection_necessity.
Proof.
  intro H. exact ((H eg_size_reading eg_size_latchable) eg_size_complete_cost).
Qed.

Theorem eg_refutes_generalized_projection_classification :
  ~ generalized_projection_classification.
Proof.
  intro H.
  destruct (H eg_size_reading eg_size_latchable)
    as [_ [_ [_ [Hstrict _]]]].
  exact (Hstrict eg_size_complete_strict).
Qed.

Theorem eg_refutes_generalized_mutual_independence :
  ~ generalized_mutual_independence.
Proof.
  intro H.
  destruct (H eg_size_reading eg_size_latchable) as [_ [Hstrict _]].
  exact (Hstrict eg_size_complete_strict).
Qed.

Theorem eg_refutes_generalized_three_component_independence :
  ~ generalized_three_component_independence.
Proof.
  intros [H _]. exact (eg_refutes_generalized_mutual_independence H).
Qed.

(** The size event is decidable from the projected trace. *)
Definition eg_default_classical : ClassicalSnapshot :=
  project_state default_vmstate.

Definition eg_classical_size_decider (t : ClassicalTrace) : bool :=
  eg_size_view
    (ThieleTraceProjection.cs_regs (List.last t eg_default_classical))
    (ThieleTraceProjection.cs_mem (List.last t eg_default_classical)).

Lemma eg_classical_size_decider_correct : forall t,
  eg_classical_size_decider (project_trace t) =
  trace_event_decider eg_size_reading t.
Proof.
  intro t. induction t using rev_ind.
  - reflexivity.
  - unfold eg_classical_size_decider, trace_event_decider, project_trace,
      last_state, eg_default_classical.
    rewrite map_app. simpl. rewrite !List.last_last. reflexivity.
Qed.

Theorem eg_refutes_generalized_no_classical_event_decider :
  ~ generalized_no_classical_event_decider.
Proof.
  intro H. apply (H eg_size_reading eg_size_latchable).
  exists eg_classical_size_decider. exact eg_classical_size_decider_correct.
Qed.

(** A positive-cost checkpoint is an injective writer of the mu event. *)
Lemma eg_checkpoint_one_injective :
  PermanentCertification.step_injective vm_apply
    (instr_checkpoint String.EmptyString 1).
Proof.
  intros [g1 c1 r1 m1 p1 u1 t1 e1 l1 s1 w1 b1]
         [g2 c2 r2 m2 p2 u2 t2 e2 l2 s2 w2 b2] H.
  cbn [vm_apply advance_state apply_cost instruction_cost] in H.
  pose proof (f_equal vm_graph H) as Hg.
  pose proof (f_equal vm_csrs H) as Hc.
  pose proof (f_equal vm_regs H) as Hr.
  pose proof (f_equal vm_mem H) as Hm.
  pose proof (f_equal vm_pc H) as Hp.
  pose proof (f_equal vm_mu H) as Hu.
  pose proof (f_equal vm_mu_tensor H) as Ht.
  pose proof (f_equal vm_err H) as He.
  pose proof (f_equal vm_logic_acc H) as Hl.
  pose proof (f_equal vm_mstatus H) as Hs.
  pose proof (f_equal vm_witness H) as Hw.
  pose proof (f_equal vm_certified H) as Hb.
  cbn in Hg, Hc, Hr, Hm, Hp, Hu, Ht, He, Hl, Hs, Hw, Hb.
  apply Nat.succ_inj in Hp.
  assert (u1 = u2) by lia.
  subst. reflexivity.
Qed.

Lemma eg_mu_checkpoint_write :
  event_writes eg_mu_reading abs_zero (instr_checkpoint String.EmptyString 1).
Proof. split; reflexivity. Qed.

Theorem eg_refutes_generalized_vm_writer_merge :
  ~ generalized_vm_writer_merge.
Proof.
  intro H.
  specialize (H eg_mu_reading eg_mu_latchable abs_zero
                (instr_checkpoint String.EmptyString 1) eg_mu_checkpoint_write).
  exact (H eg_checkpoint_one_injective).
Qed.

Theorem eg_refutes_generalized_vm_priced_merge_bundle :
  ~ generalized_vm_priced_merge_bundle.
Proof.
  intro H. apply eg_refutes_generalized_vm_writer_merge.
  intros E HL s i HW. exact (proj1 (proj1 (H E HL) s i HW)).
Qed.

(** The graph countermodel can carry the explicit CHSH count witness. *)
Definition eg_chsh_zero : VMState := {|
  vm_graph := abs_empty_graph;
  vm_csrs := abs_empty_csrs;
  vm_regs := [];
  vm_mem := [];
  vm_pc := 0;
  vm_mu := 0;
  vm_mu_tensor := repeat 0 16;
  vm_err := false;
  vm_logic_acc := 0;
  vm_mstatus := 0;
  vm_witness := violation_wc;
  vm_certified := false
|}.

Lemma eg_chsh_pnew_violation :
  chsh_violation_certified (vm_apply eg_chsh_zero (instr_pnew [] 0)).
Proof.
  unfold chsh_violation_certified. simpl.
  exact violation_wc_exceeds_bell.
Qed.

Theorem eg_refutes_generalized_nonlocal_witness_step :
  ~ generalized_nonlocal_witness_step.
Proof.
  intro H.
  specialize (H eg_graph_reading eg_graph_latchable eg_chsh_zero
                (instr_pnew [] 0) eq_refl eq_refl eg_chsh_pnew_violation).
  destruct H as [Hcost _]. simpl in Hcost. lia.
Qed.

Theorem eg_refutes_generalized_nonlocal_witness_trace :
  ~ generalized_nonlocal_witness_trace.
Proof.
  intro H.
  specialize (H eg_graph_reading eg_graph_latchable [instr_pnew [] 0]
                eg_chsh_zero eq_refl eq_refl eg_chsh_pnew_violation).
  change (vm_mu (vm_apply eg_chsh_zero (instr_pnew [] 0)) >=
          vm_mu eg_chsh_zero + 1) in H.
  rewrite vm_apply_mu in H. simpl in H. lia.
Qed.

(** Replacing the record leaves the billed machine's dynamics and ledger
    unchanged. *)
Lemma eg_billed_event_ledger : forall E,
  ledger_carried (billed_event_core E).
Proof. intro E. exact billed_core_ledger. Qed.

Lemma eg_billed_event_a2 : forall E,
  rc_a2 (billed_event_core E).
Proof.
  intros E x _ _. exact (billed_step_cost_pos x).
Qed.

Lemma eg_billed_event_carries : forall E,
  rcm_latchable ThieleCore E -> carries_record (billed_event_core E).
Proof.
  intros E [_ [x [Hfalse Htrue]]].
  destruct x as [p s].
  exists (p, s, 0), 1. split; [exact I |].
  exact Htrue.
Qed.

Lemma eg_billed_event_halting : forall E,
  halting_problem_coverage (billed_event_core E).
Proof. intro E. exact billed_core_halting_problem_coverage. Qed.

Theorem eg_proves_generalized_billed_core_adequate :
  generalized_billed_core_adequate.
Proof.
  intros E HL. repeat split.
  - apply eg_billed_event_ledger.
  - apply eg_billed_event_a2.
  - exact (eg_billed_event_carries E HL).
  - apply eg_billed_event_halting.
Qed.

Definition eg_billed_event_cover (E : rc_state ThieleCore -> bool) :
  ComputationalCover (billed_event_core E) (thiele_event_core E).
Proof.
  refine (Build_ComputationalCover (billed_event_core E) (thiele_event_core E)
            billed_cover_state _ _ _ _).
  - intros; exact I.
  - intros [p s] _. exists (p, s, 0). split; [exact I | reflexivity].
  - intros [[p s] k]. reflexivity.
  - intros [[p s] k]. simpl. tauto.
Defined.

Definition eg_billed_base_cover (E : rc_state ThieleCore -> bool) :
  ComputationalCover (billed_event_core E) ThieleCore.
Proof.
  refine (Build_ComputationalCover (billed_event_core E) ThieleCore
            billed_cover_state _ _ _ _).
  - intros; exact I.
  - intros [p s] _. exists (p, s, 0). split; [exact I | reflexivity].
  - intros [[p s] k]. reflexivity.
  - intros [[p s] k]. simpl. tauto.
Defined.

Lemma eg_billed_event_permanent : forall E,
  rcm_latchable ThieleCore E -> record_permanent (billed_event_core E).
Proof.
  intros E [Hperm _] [[p s] k] H.
  change (E (p, run_vm_u 1 p s) = true).
  exact (Hperm (p, s) H).
Qed.

Lemma eg_billed_event_write : forall E,
  rcm_latchable ThieleCore E -> reachable_record_write (billed_event_core E).
Proof.
  intros E [_ [x [Hfalse Htrue]]].
  destruct x as [p s].
  exists (p, s, 0), 0. repeat split; assumption || exact I.
Qed.

Theorem eg_proves_generalized_billed_core_honest_extension :
  generalized_billed_core_honest_extension.
Proof.
  intros E HL.
  split; [exact (inhabits (eg_billed_base_cover E)) |].
  split; [apply eg_billed_event_ledger |].
  split; [apply eg_billed_event_a2 |].
  split.
  - exact (eg_billed_event_permanent E HL).
  - exact (eg_billed_event_write E HL).
Qed.

Theorem eg_proves_generalized_uniqueness_round1_refutation :
  generalized_uniqueness_round1_refutation.
Proof.
  intros E _ [R [_ [Hback Hstep]]].
  destruct (Hback ([], init_state) I) as [m [_ Hr]].
  destruct (Hstep m ([], init_state) Hr) as [_ [Hcost _]].
  pose proof (billed_step_cost_pos m) as Hpos.
  change (step_cost (billed_event_core E) m >= 1) in Hpos.
  rewrite Hcost in Hpos.
  change (step_cost ThieleCore ([], init_state) >= 1) in Hpos.
  rewrite empty_program_free in Hpos. lia.
Qed.

Theorem eg_proves_generalized_uniqueness_round2_refutation :
  generalized_uniqueness_round2_refutation.
Proof.
  intros E _ [R [_ [Hback Hstep]]].
  destruct (Hback ([], init_state) I) as [m [_ Hr]].
  destruct (Hstep m ([], init_state) Hr) as [_ [_ [_ [Hcost _]]]].
  pose proof (billed_step_cost_pos m) as Hpos.
  change (step_cost (billed_event_core E) m >= 1) in Hpos.
  rewrite Hcost in Hpos.
  change (step_cost ThieleCore ([], init_state) >= 1) in Hpos.
  rewrite empty_program_free in Hpos. lia.
Qed.

Theorem eg_proves_generalized_schedule_uniqueness :
  generalized_schedule_uniqueness.
Proof.
  intros M B C HB [Hrecord [HM _]].
  split; [exact HM |]. split; [exact HB |].
  exists (fun m b => cover_state M B C m = b).
  split; [intros m b H; exact H |].
  split.
  - intros m Hm. exists (cover_state M B C m).
    split; [exact (cover_initial M B C m Hm) | reflexivity].
  - split.
    + intros b Hb.
      destruct (cover_surjective_initial M B C b Hb) as [m [Hm Heq]].
      exists m. split; assumption.
    + intros m b Hmb. subst b.
      split; [apply Hrecord |].
      split; [apply (cover_halted M B C) |].
      apply (cover_step M B C).
Qed.

(** Graph allocation supplies a latchable record transition that the base
    Thiele schedule prices at zero. *)
Definition eg_core_graph_event (x : rc_state ThieleCore) : bool :=
  eg_graph_reading (snd x).

Lemma eg_vm_apply_u_graph : forall s i,
  vm_graph (vm_apply_u s i) = vm_graph (vm_apply s i).
Proof.
  intros s i. destruct i; cbn [vm_apply_u vm_apply];
    repeat match goal with
    | |- context [if ?x then _ else _] => destruct x eqn:?
    | |- context [match ?x with Some _ => _ | None => _ end] =>
        destruct x eqn:?
    | |- context [let '(_, _) := ?x in _] => destruct x eqn:?
    end;
    reflexivity.
Qed.

Lemma eg_core_graph_event_latchable :
  rcm_latchable ThieleCore eg_core_graph_event.
Proof.
  split.
  - intros [p s] H. unfold eg_core_graph_event in *.
    change (eg_graph_reading (run_vm_u 1 p s) = true).
    simpl. destruct (nth_error p (vm_pc s)) as [i |] eqn:Hi.
    + unfold eg_graph_reading. rewrite eg_vm_apply_u_graph.
      exact (proj1 eg_graph_latchable s i H).
    + exact H.
  - exists ([instr_pnew [] 0], abs_zero). split; reflexivity.
Qed.

Lemma eg_thiele_graph_event_not_a2 :
  ~ rc_a2 (thiele_event_core eg_core_graph_event).
Proof.
  intro H.
  specialize (H ([instr_pnew [] 0], abs_zero) eq_refl eq_refl).
  change (vm_mu (vm_apply abs_zero (instr_pnew [] 0)) - vm_mu abs_zero >= 1)
    in H.
  rewrite vm_apply_mu in H. simpl in H. lia.
Qed.

Theorem eg_refutes_generalized_billed_schedule_equivalence :
  ~ generalized_billed_schedule_equivalence.
Proof.
  intro H.
  destruct (H eg_core_graph_event eg_core_graph_event_latchable) as [C Hequiv].
  apply eg_thiele_graph_event_not_a2.
  exact (proj2 (proj1 (proj2 Hequiv))).
Qed.

Theorem eg_refutes_generalized_surcharged_schedule_equivalence :
  ~ generalized_surcharged_schedule_equivalence.
Proof.
  intro H.
  destruct (H (fun _ => 0) eg_core_graph_event
                eg_core_graph_event_latchable) as [C Hequiv].
  apply eg_thiele_graph_event_not_a2.
  exact (proj2 (proj1 (proj2 Hequiv))).
Qed.

(** Event-parametric reachable simulations satisfy the same descent criterion
    as the certification-specialized construction. *)
Lemma eg_event_simulation_evaluates_trace :
  forall E M base (simulation : ReachableEventSimulation E M base) t,
    event_reachable_map E M base simulation (vm_trace_eval t) =
    target_trace_eval M base t.
Proof.
  intros E M base simulation t. induction t using rev_ind.
  - exact (event_reachable_map_base E M base simulation).
  - rewrite vm_trace_eval_extend, target_trace_eval_extend.
    rewrite event_reachable_map_step, IHt. reflexivity.
Qed.

Lemma eg_event_simulation_requires_compatibility :
  forall E M base, ReachableEventSimulation E M base ->
    trace_fiber_compatible M base /\ event_trace_compatible E M base.
Proof.
  intros E M base simulation. split.
  - intros t u Heq.
    rewrite <- (eg_event_simulation_evaluates_trace E M base simulation t).
    rewrite <- (eg_event_simulation_evaluates_trace E M base simulation u), Heq.
    reflexivity.
  - intro t.
    rewrite <- (eg_event_simulation_evaluates_trace E M base simulation t).
    apply event_reachable_map_reading.
Qed.

Definition eg_build_event_simulation
    (representative : VMState -> list vm_instruction)
    (representative_correct : forall t,
       vm_trace_eval (representative (vm_trace_eval t)) = vm_trace_eval t)
    (E : Reading) (M : CertCostMachine) (base : ccm_state M)
    (Hfiber : trace_fiber_compatible M base)
    (Hevent : event_trace_compatible E M base) :
    ReachableEventSimulation E M base.
Proof.
  refine {| event_reachable_map :=
              fun s => target_trace_eval M base (representative s) |}.
  - change (target_trace_eval M base (representative (vm_trace_eval [])) =
            target_trace_eval M base []).
    apply Hfiber. apply representative_correct.
  - intros t i. rewrite <- vm_trace_eval_extend.
    rewrite (Hfiber _ _ (representative_correct (t ++ [i]))).
    rewrite target_trace_eval_extend.
    rewrite (Hfiber _ _ (representative_correct t)). reflexivity.
  - intro t. rewrite (Hfiber _ _ (representative_correct t)). apply Hevent.
Defined.

Theorem eg_proves_generalized_reachable_simulation_exists :
  generalized_reachable_simulation_exists.
Proof.
  intros representative Hrepresentative E M base. split.
  - intros [simulation].
    exact (eg_event_simulation_requires_compatibility E M base simulation).
  - intros [Hfiber Hevent]. constructor.
    exact (eg_build_event_simulation representative Hrepresentative
             E M base Hfiber Hevent).
Qed.

Theorem eg_proves_generalized_reachable_simulation_unique :
  generalized_reachable_simulation_unique.
Proof.
  intros E M base left right t.
  rewrite !eg_event_simulation_evaluates_trace. reflexivity.
Qed.

Theorem eg_proves_generalized_agreement_does_not_imply_descent :
  generalized_agreement_does_not_imply_descent.
Proof.
  intros E _. split.
  - intro t. reflexivity.
  - intro H.
    assert (Heq : vm_trace_eval [] = vm_trace_eval [instr_jump 0 0])
      by reflexivity.
    specialize (H [] [instr_jump 0 0] Heq). discriminate.
Qed.

Lemma eg_escs_run_embed :
  forall E (SCS : EventSimulatingCertificationSystem E)
         (trace : list (cs_instr (escs_base E SCS)))
         (s0 : cs_state (escs_base E SCS)),
    escs_embed E SCS (cs_run (escs_base E SCS) trace s0) =
    fold_left vm_apply (map (escs_decode E SCS) trace)
      (escs_embed E SCS s0).
Proof.
  intros E SCS trace. induction trace as [| i rest IH]; intros s0; simpl.
  - reflexivity.
  - rewrite IH. f_equal. exact (escs_step_commutes E SCS s0 i).
Qed.

Theorem eg_proves_generalized_simulating_system_representation :
  generalized_simulating_system_representation.
Proof.
  intros E SCS s0 trace Hpre Hpost. split.
  - exact (universal_nfi_any_substrate (escs_base E SCS)
             trace s0 Hpre Hpost).
  - rewrite <- eg_escs_run_embed.
    rewrite <- (escs_event_reflects E SCS). exact Hpost.
Qed.

(** One closed result theorem is exposed for each frozen logical identity. *)
Theorem item1_2_result_01 : ~ generalized_step_mu.
Proof. exact eg_refutes_generalized_step_mu. Qed.
Theorem item1_2_result_02 : ~ generalized_step_price.
Proof. exact eg_refutes_generalized_step_price. Qed.
Theorem item1_2_result_03 : ~ generalized_step_price.
Proof. exact eg_refutes_generalized_step_price. Qed.
Theorem item1_2_result_04 : ~ generalized_step_mu.
Proof. exact eg_refutes_generalized_step_mu. Qed.
Theorem item1_2_result_05 : ~ generalized_trace_mu.
Proof. exact eg_refutes_generalized_trace_mu. Qed.
Theorem item1_2_result_06 : generalized_trace_writer.
Proof. exact eg_proves_generalized_trace_writer. Qed.
Theorem item1_2_result_07 : ~ generalized_forget_hidden.
Proof. exact eg_refutes_generalized_forget_hidden. Qed.
Theorem item1_2_result_08 : generalized_finite_writer_merge.
Proof. exact eg_proves_generalized_finite_writer_merge. Qed.
Theorem item1_2_result_09 : generalized_finite_a2_from_compression_price.
Proof. exact eg_proves_generalized_finite_a2_from_compression_price. Qed.
Theorem item1_2_result_10 : generalized_finite_a2_from_merging_price.
Proof. exact eg_proves_generalized_finite_a2_from_merging_price. Qed.
Theorem item1_2_result_11 : generalized_finite_permanent.
Proof. exact eg_proves_generalized_finite_permanent. Qed.
Theorem item1_2_result_12 : ~ generalized_vm_writer_merge.
Proof. exact eg_refutes_generalized_vm_writer_merge. Qed.
Theorem item1_2_result_13 : ~ generalized_vm_priced_merge_bundle.
Proof. exact eg_refutes_generalized_vm_priced_merge_bundle. Qed.
Theorem item1_2_result_14 : ~ generalized_trace_mu.
Proof. exact eg_refutes_generalized_trace_mu. Qed.
Theorem item1_2_result_15 : ~ generalized_vm_priced_merge_bundle.
Proof. exact eg_refutes_generalized_vm_priced_merge_bundle. Qed.
Theorem item1_2_result_16 : ~ generalized_event_unit_price_lower_bounds_mu.
Proof. exact eg_refutes_generalized_event_unit_price_lower_bounds_mu. Qed.
Theorem item1_2_result_17 : generalized_event_unit_pricing_exact.
Proof. exact eg_proves_generalized_event_unit_pricing_exact. Qed.
Theorem item1_2_result_18 : generalized_projection_irredundancy.
Proof. exact eg_proves_generalized_projection_irredundancy. Qed.
Theorem item1_2_result_19 : ~ generalized_cost_projection_necessity.
Proof. exact eg_refutes_generalized_cost_projection_necessity. Qed.
Theorem item1_2_result_20 : ~ generalized_projection_classification.
Proof. exact eg_refutes_generalized_projection_classification. Qed.
Theorem item1_2_result_21 : ~ generalized_mutual_independence.
Proof. exact eg_refutes_generalized_mutual_independence. Qed.
Theorem item1_2_result_22 : ~ generalized_three_component_independence.
Proof. exact eg_refutes_generalized_three_component_independence. Qed.
Theorem item1_2_result_23 : ~ generalized_strict_projection_necessity.
Proof. exact eg_refutes_generalized_strict_projection_necessity. Qed.
Theorem item1_2_result_24 : ~ generalized_partition_free_but_event_nonfree.
Proof. exact eg_refutes_generalized_partition_free_but_event_nonfree. Qed.
Theorem item1_2_result_25 : ~ generalized_partition_refinement_nonfree.
Proof. exact eg_refutes_generalized_partition_refinement_nonfree. Qed.
Theorem item1_2_result_26 : generalized_revocation_boundary.
Proof. exact eg_proves_generalized_revocation_boundary. Qed.
Theorem item1_2_result_27 : ~ generalized_bounded_run_mu.
Proof. exact eg_refutes_generalized_bounded_run_mu. Qed.
Theorem item1_2_result_28 : ~ generalized_forget_hidden.
Proof. exact eg_refutes_generalized_forget_hidden. Qed.
Theorem item1_2_result_29 : ~ generalized_forget_hidden.
Proof. exact eg_refutes_generalized_forget_hidden. Qed.
Theorem item1_2_result_30 : ~ generalized_forget_hidden.
Proof. exact eg_refutes_generalized_forget_hidden. Qed.
Theorem item1_2_result_31 : ~ generalized_forget_hidden.
Proof. exact eg_refutes_generalized_forget_hidden. Qed.
Theorem item1_2_result_32 : ~ generalized_bare_price_inexact.
Proof. exact eg_refutes_generalized_bare_price_inexact. Qed.
Theorem item1_2_result_33 : ~ generalized_forget_price_inexact.
Proof. exact eg_refutes_generalized_forget_price_inexact. Qed.
Theorem item1_2_result_34 : ~ generalized_billed_schedule_equivalence.
Proof. exact eg_refutes_generalized_billed_schedule_equivalence. Qed.
Theorem item1_2_result_35 : ~ generalized_surcharged_schedule_equivalence.
Proof. exact eg_refutes_generalized_surcharged_schedule_equivalence. Qed.
Theorem item1_2_result_36 : generalized_schedule_uniqueness.
Proof. exact eg_proves_generalized_schedule_uniqueness. Qed.
Theorem item1_2_result_37 : generalized_billed_core_adequate.
Proof. exact eg_proves_generalized_billed_core_adequate. Qed.
Theorem item1_2_result_38 : generalized_billed_core_honest_extension.
Proof. exact eg_proves_generalized_billed_core_honest_extension. Qed.
Theorem item1_2_result_39 : generalized_uniqueness_round1_refutation.
Proof. exact eg_proves_generalized_uniqueness_round1_refutation. Qed.
Theorem item1_2_result_40 : generalized_uniqueness_round2_refutation.
Proof. exact eg_proves_generalized_uniqueness_round2_refutation. Qed.
Theorem item1_2_result_41 : generalized_agreement_does_not_imply_descent.
Proof. exact eg_proves_generalized_agreement_does_not_imply_descent. Qed.
Theorem item1_2_result_42 : generalized_reachable_simulation_exists.
Proof. exact eg_proves_generalized_reachable_simulation_exists. Qed.
Theorem item1_2_result_43 : generalized_reachable_simulation_unique.
Proof. exact eg_proves_generalized_reachable_simulation_unique. Qed.
Theorem item1_2_result_44 : generalized_simulating_system_representation.
Proof. exact eg_proves_generalized_simulating_system_representation. Qed.
Theorem item1_2_result_45 : ~ generalized_trace_cost.
Proof. exact eg_refutes_generalized_trace_cost. Qed.
Theorem item1_2_result_46 : ~ generalized_trace_cost.
Proof. exact eg_refutes_generalized_trace_cost. Qed.
Theorem item1_2_result_47 : ~ generalized_step_price_and_mu.
Proof. exact eg_refutes_generalized_step_price_and_mu. Qed.
Theorem item1_2_result_48 : ~ generalized_trace_mu.
Proof. exact eg_refutes_generalized_trace_mu. Qed.
Theorem item1_2_result_49 : ~ generalized_nonlocal_witness_step.
Proof. exact eg_refutes_generalized_nonlocal_witness_step. Qed.
Theorem item1_2_result_50 : ~ generalized_nonlocal_witness_trace.
Proof. exact eg_refutes_generalized_nonlocal_witness_trace. Qed.
Theorem item1_2_result_51 : ~ generalized_no_classical_event_decider.
Proof. exact eg_refutes_generalized_no_classical_event_decider. Qed.
Theorem item1_2_result_52 : generalized_joint_ledger_necessity.
Proof. exact eg_proves_generalized_joint_ledger_necessity. Qed.
Theorem item1_2_result_53 : ~ generalized_certify_pnew_separation.
Proof. exact eg_refutes_generalized_certify_pnew_separation. Qed.
Theorem item1_2_result_54 : ~ generalized_strict_projection_necessity.
Proof. exact eg_refutes_generalized_strict_projection_necessity. Qed.
Theorem item1_2_result_55 : generalized_certified_spec.
Proof. exact eg_proves_generalized_certified_spec. Qed.

Print Assumptions item1_2_result_01.
Print Assumptions item1_2_result_02.
Print Assumptions item1_2_result_03.
Print Assumptions item1_2_result_04.
Print Assumptions item1_2_result_05.
Print Assumptions item1_2_result_06.
Print Assumptions item1_2_result_07.
Print Assumptions item1_2_result_08.
Print Assumptions item1_2_result_09.
Print Assumptions item1_2_result_10.
Print Assumptions item1_2_result_11.
Print Assumptions item1_2_result_12.
Print Assumptions item1_2_result_13.
Print Assumptions item1_2_result_14.
Print Assumptions item1_2_result_15.
Print Assumptions item1_2_result_16.
Print Assumptions item1_2_result_17.
Print Assumptions item1_2_result_18.
Print Assumptions item1_2_result_19.
Print Assumptions item1_2_result_20.
Print Assumptions item1_2_result_21.
Print Assumptions item1_2_result_22.
Print Assumptions item1_2_result_23.
Print Assumptions item1_2_result_24.
Print Assumptions item1_2_result_25.
Print Assumptions item1_2_result_26.
Print Assumptions item1_2_result_27.
Print Assumptions item1_2_result_28.
Print Assumptions item1_2_result_29.
Print Assumptions item1_2_result_30.
Print Assumptions item1_2_result_31.
Print Assumptions item1_2_result_32.
Print Assumptions item1_2_result_33.
Print Assumptions item1_2_result_34.
Print Assumptions item1_2_result_35.
Print Assumptions item1_2_result_36.
Print Assumptions item1_2_result_37.
Print Assumptions item1_2_result_38.
Print Assumptions item1_2_result_39.
Print Assumptions item1_2_result_40.
Print Assumptions item1_2_result_41.
Print Assumptions item1_2_result_42.
Print Assumptions item1_2_result_43.
Print Assumptions item1_2_result_44.
Print Assumptions item1_2_result_45.
Print Assumptions item1_2_result_46.
Print Assumptions item1_2_result_47.
Print Assumptions item1_2_result_48.
Print Assumptions item1_2_result_49.
Print Assumptions item1_2_result_50.
Print Assumptions item1_2_result_51.
Print Assumptions item1_2_result_52.
Print Assumptions item1_2_result_53.
Print Assumptions item1_2_result_54.
Print Assumptions item1_2_result_55.
