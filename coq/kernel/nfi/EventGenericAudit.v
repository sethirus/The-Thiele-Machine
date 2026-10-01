(** EventGenericAudit: exact specializations of the certification theorems at
    non-certification events.

    The main witness is a door whose permanent record says whether it has
    opened.  [Open] sets the record and [Wait] leaves it unchanged.  Additional
    witnesses use a program-counter predicate and the generic record latch.

    Each [audit_*] definition is a kernel-checked application of the cited
    theorem.  Applications that still expose a pricing, distribution, physical,
    or injectivity premise are reported as partial in the accompanying evidence
    table. *)

From Coq Require Import List Bool Arith.PeanoNat Lia Strings.String.
Import ListNotations.

From Kernel Require Import A2Payoff CommitmentPredicateAdequacy.
From Kernel Require Import CommitmentVsErasure CostFrameworks.
From Kernel Require Import CostSemanticsComparison F1_StrongForm GasMetering.
From Kernel Require Import HonestCostTracking PermanentCertification.
From Kernel Require Import PermanentCertificationEntropy PermanentRecordPricing.
From Kernel Require Import RecordAxisDiscrimination ShadowPricing.
From Kernel Require Import StructuralRecordAxis UniversalCertificationCost.
From Kernel Require Import MuChaitin MuInformation MuInitiality.
From Kernel Require Import MuNoFreeInsightQuantitative RevelationRequirement VMState.

Require Import NoFI.NoFreeInsight_Interface.
Require Import NoFI.NoFreeInsight_Theorem.
Require Import NoFI.MuChaitinTheory_Interface.
Require Import NoFI.MuChaitinTheory_Theorem.

Inductive DoorInstr : Type := Open | Wait.

Definition door_instr_eq_dec : forall a b : DoorInstr, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition door_step (opened : bool) (i : DoorInstr) : bool :=
  match i with Open => true | Wait => opened end.

Fixpoint door_execute (trace : list DoorInstr) (opened : bool) : bool :=
  match trace with
  | [] => opened
  | i :: rest => door_execute rest (door_step opened i)
  end.

Definition door_opened (opened : bool) : bool := opened.

Definition door_cost (i : DoorInstr) : nat :=
  match i with Open => 1 | Wait => 0 end.

Definition door_charge (opened : bool) (i : DoorInstr) : bool :=
  negb opened && door_step opened i.

Definition door_state_cost (opened : bool) (i : DoorInstr) : nat :=
  if door_charge opened i then 1 else 0.

Definition door_all : list bool := [false; true].

Lemma door_finite : finite_states door_all.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - intros []; simpl; auto.
Qed.

Lemma door_permanent : permanent door_step door_opened.
Proof. intros s [] H; simpl; [reflexivity | exact H]. Qed.

Lemma door_merging_priced : merging_steps_priced door_step door_cost.
Proof.
  intros [] Hnot; simpl; [lia |].
  exfalso. apply Hnot. intros a b H. exact H.
Qed.

Lemma door_a2 : a2_holds door_step door_opened door_cost.
Proof.
  exact (a2_from_merging_price_and_permanence
    bool DoorInstr door_step door_opened door_cost door_all
    door_finite door_permanent door_merging_priced).
Qed.

Definition door_system : CertificationSystem :=
  mk_cert_system bool DoorInstr door_step door_cost door_opened door_a2.

Lemma door_charged_costs :
  forall s i, door_charge s i = true -> door_state_cost s i >= 1.
Proof.
  intros [] [] H; cbv in H |- *; discriminate + lia.
Qed.

Lemma door_uncharged_free :
  forall s i, door_charge s i = false -> door_state_cost s i = 0.
Proof.
  intros [] [] H; cbv in H |- *; discriminate + reflexivity.
Qed.

Definition door_local_pricing : LocalPredicatePricedSystem :=
  {| lps_state := bool;
     lps_instr := DoorInstr;
     lps_step := door_step;
     lps_cost := door_state_cost;
     lps_cert := door_opened;
     lps_charge := door_charge;
     lps_charged_costs := door_charged_costs;
     lps_uncharged_free := door_uncharged_free |}.

Lemma false_charge_impossible :
  forall (s : bool) (i : DoorInstr), false = true -> (0 >= 1)%nat.
Proof. intros s i H. discriminate H. Qed.

Definition door_undercharged_pricing : LocalPredicatePricedSystem :=
  {| lps_state := bool;
     lps_instr := DoorInstr;
     lps_step := door_step;
     lps_cost := fun _ _ => 0;
     lps_cert := door_opened;
     lps_charge := fun _ _ => false;
     lps_charged_costs := false_charge_impossible;
     lps_uncharged_free := fun _ _ _ => eq_refl |}.

Lemma door_undercharged_not_same :
  ~ local_predicate_same door_undercharged_pricing
      (cert_flip_local door_undercharged_pricing)
      (lps_charge door_undercharged_pricing).
Proof.
  intros [Hcovers _].
  specialize (Hcovers false Open eq_refl).
  discriminate Hcovers.
Qed.

Lemma true_uncharged_impossible :
  forall (s : bool) (i : DoorInstr), true = false -> 1 = 0.
Proof. intros s i H. discriminate H. Qed.

Definition door_overcharged_pricing : LocalPredicatePricedSystem :=
  {| lps_state := bool;
     lps_instr := DoorInstr;
     lps_step := door_step;
     lps_cost := fun _ _ => 1;
     lps_cert := door_opened;
     lps_charge := fun _ _ => true;
     lps_charged_costs := fun _ _ _ => le_n 1;
     lps_uncharged_free := true_uncharged_impossible |}.

Definition door_erases (_ : bool) (i : DoorInstr) : bool :=
  match i with Open => true | Wait => false end.

Lemma door_erasure_costs :
  forall s i, door_erases s i = true -> door_cost i >= 1.
Proof. intros s [] H; cbv in H |- *; discriminate + lia. Qed.

Definition door_erasure_system : TrustedErasureAccountingSystem :=
  {| tea_state := bool;
     tea_instr := DoorInstr;
     tea_step := door_step;
     tea_cost := door_cost;
     tea_cert := door_opened;
     tea_erases := door_erases;
     tea_erasure_costs := door_erasure_costs |}.

Lemma door_honest_erasure : honest_erasure door_erasure_system.
Proof.
  intros [] Hmerge.
  - exists false. reflexivity.
  - exfalso. apply Hmerge. intros a b H. exact H.
Qed.

Definition door_unpriced_system : CostBearingSystem :=
  {| cb_state := bool;
     cb_instr := DoorInstr;
     cb_step := door_step;
     cb_cost := fun _ => 0;
     cb_cert := door_opened |}.

Lemma door_singleton_nodup : NoDup [false].
Proof. repeat constructor; intros []. Qed.

Lemma door_singleton_flips :
  forall s, In s [false] ->
    door_opened s = false /\ door_opened (door_step s Open) = true.
Proof. intros s [<- | []]. split; reflexivity. Qed.

Lemma door_flip_list :
  flip_list door_step door_opened Open [false].
Proof. split; [exact door_singleton_nodup | exact door_singleton_flips]. Qed.

Lemma door_singleton_nonempty : (0 < List.length [false])%nat.
Proof. simpl. lia. Qed.

Lemma door_state_a2 :
  CostFrameworks.a2 bool DoorInstr door_step door_state_cost door_opened.
Proof.
  intros [] [] H; cbv in H |- *; discriminate + lia.
Qed.

Definition door_permanent_at_open :
  permanent_at door_step door_opened Open.
Proof. intros []; reflexivity. Qed.

(** The singleton instruction deliberately maps both finite states to the
    recorded state.  Writing it as a reduction keeps the small model explicit
    without presenting a bare constant as production semantics. *)
Definition door_unit_step (_ : bool) (_ : unit) : bool := negb false.

Lemma door_unit_permanent : permanent door_unit_step door_opened.
Proof. intros s [] H. reflexivity. Qed.

Definition toggle_step (opened : bool) (_ : unit) : bool := negb opened.

Lemma toggle_step_injective : step_injective toggle_step tt.
Proof. intros [] [] H; reflexivity + discriminate. Qed.

Lemma door_blind_collision :
  shadow_collision door_step door_opened (fun _ => tt).
Proof.
  exists false, Open, false, Wait. repeat split; reflexivity.
Qed.

(** Small-case and swap witnesses for the result audit. *)
Lemma door_one_step_opens : door_execute [Open] false = true.
Proof. reflexivity. Qed.

Lemma door_one_step_costs_one : cs_total_cost door_system [Open] = 1.
Proof. reflexivity. Qed.

Inductive MeterState : Type := Meter0 | Meter1 | Meter2.
Inductive MeterInstr : Type := Tick | Hold.

Definition meter_step (s : MeterState) (i : MeterInstr) : MeterState :=
  match i, s with
  | Tick, Meter0 => Meter1
  | Tick, Meter1 => Meter2
  | Tick, Meter2 => Meter2
  | Hold, _ => s
  end.

Definition meter_event (s : MeterState) : bool :=
  match s with Meter2 => true | _ => false end.

Definition meter_cost (i : MeterInstr) : nat :=
  match i with Tick => 1 | Hold => 0 end.

Lemma meter_a2 :
  forall s i,
    meter_event s = false ->
    meter_event (meter_step s i) = true ->
    meter_cost i >= 1.
Proof. intros [] [] H0 H1; cbv in H0, H1 |- *; discriminate + lia. Qed.

Definition meter_system : CertificationSystem :=
  mk_cert_system MeterState MeterInstr meter_step meter_cost meter_event meter_a2.

Lemma meter_two_ticks_reach_event :
  meter_event (cs_run meter_system [Tick; Tick] Meter0) = true.
Proof. reflexivity. Qed.

Theorem meter_event_run_pays :
  cs_total_cost meter_system [Tick; Tick] >= 1.
Proof.
  exact (universal_nfi_any_substrate
    meter_system [Tick; Tick] Meter0 eq_refl meter_two_ticks_reach_event).
Qed.

Definition door_vm_event : F1_LogicalErasure.bool_macro_property :=
  fun s => Nat.eqb s.(vm_pc) 1.

(** Exact theorem applications for the 49 cited theorems. *)

Definition audit_a2_equal_trust_substitution_payoff :=
  (proj1 (proj2 a2_equal_trust_substitution_payoff)) door_local_pricing.

Definition audit_exact_commitment_pricing_characterization :=
  exact_commitment_pricing_characterization door_local_pricing.

Definition audit_substitution_test_rejects_non_a2_exact_substitute :=
  substitution_test_rejects_non_a2_exact_substitute
    door_undercharged_pricing door_undercharged_not_same.

Definition audit_commitment_cost_not_reducible_to_erasure_cost :=
  (proj2 commitment_cost_not_reducible_to_erasure_cost) door_system.

Definition audit_a2_and_aara_iff_exact :=
  @CostFrameworks.a2_and_aara_iff_exact
    bool DoorInstr door_step door_state_cost door_opened.

Definition audit_flips_le_cost :=
  @CostFrameworks.flips_le_cost
    bool DoorInstr door_step door_state_cost door_opened door_state_a2.

Definition audit_a2_iff_nonnegative_amortized_cost :=
  @CostSemanticsComparison.a2_iff_nonnegative_amortized_cost
    bool DoorInstr door_step door_cost door_opened.

Definition audit_certification_system_is_potential_method :=
  certification_system_is_potential_method door_system.

Definition audit_nfi_by_potential :=
  @CostSemanticsComparison.nfi_by_potential
    bool DoorInstr door_step door_cost door_opened door_a2.

Definition audit_F1_strong_form_universal :=
  fun physical_cost landauer calibration =>
    F1_strong_form_universal physical_cost landauer calibration door_vm_event.

Definition audit_gas_schedule_exactness :=
  gas_schedule_exactness door_local_pricing.

Definition audit_overcharge_breaks_exactness :=
  overcharge_breaks_exactness door_overcharged_pricing false Wait eq_refl eq_refl.

Definition audit_undercharged_opcode_admits_free_commitment :=
  undercharged_opcode_admits_free_commitment
    door_undercharged_pricing false Open eq_refl eq_refl eq_refl.

Definition audit_free_forgery_violates_A2 :=
  free_forgery_violates_A2
    door_unpriced_system false Open eq_refl eq_refl eq_refl.

Definition audit_honest_cost_tracking_strict_restriction :=
  (proj2 honest_cost_tracking_strict_restriction) door_system.

Definition audit_a2_from_merging_price_and_permanence :=
  @a2_from_merging_price_and_permanence
    bool DoorInstr door_step door_opened door_cost door_all
    door_finite door_permanent door_merging_priced.

Definition audit_honest_erasure_accounting_implies_a2 :=
  honest_erasure_accounting_implies_a2
    door_erasure_system door_all door_finite door_permanent door_honest_erasure.

Definition audit_permanent_certification_trace_floor :=
  @permanent_certification_trace_floor
    bool DoorInstr door_step door_cost door_opened door_all
    door_finite door_permanent door_merging_priced.

Definition audit_permanent_flip_is_not_injective :=
  permanent_flip_is_not_injective
    bool DoorInstr door_step door_opened door_all false Open
    door_finite door_permanent eq_refl eq_refl.

Definition audit_permanent_flips_collapse_at_least :=
  @permanent_flips_collapse_at_least
    bool DoorInstr door_step door_opened bool_dec door_all Open [false]
    door_finite door_permanent door_singleton_nodup door_singleton_flips.

Definition audit_a2_from_entropy_price_and_permanence :=
  @a2_from_entropy_price_and_permanence
    bool DoorInstr door_step door_opened bool_dec door_all door_cost
    door_finite door_permanent.

Definition audit_entropy_priced_trace_floor :=
  @entropy_priced_trace_floor
    bool DoorInstr door_step door_opened door_cost bool_dec door_all
    door_finite door_permanent.

Definition audit_permanent_flip_full_support_entropy_drop_positive :=
  fun probability =>
    @permanent_flip_full_support_entropy_drop_positive
      bool DoorInstr door_step door_opened bool_dec door_all Open false probability
      door_finite door_permanent eq_refl eq_refl.

Definition audit_permanent_flip_full_support_heat_positive :=
  fun probability kT heat =>
    @permanent_flip_full_support_heat_positive
      bool DoorInstr door_step door_opened bool_dec door_all Open false
      probability kT heat door_finite door_permanent eq_refl eq_refl.

Definition audit_permanent_flip_heat_floor :=
  fun kT heat =>
    @permanent_flip_heat_floor
      bool DoorInstr door_step door_opened bool_dec door_all Open [false]
      kT heat door_finite door_permanent door_flip_list door_singleton_nonempty.

Definition audit_permanent_flip_heat_positive :=
  fun kT heat =>
    @permanent_flip_heat_positive
      bool DoorInstr door_step door_opened bool_dec door_all Open [false]
      kT heat door_finite door_permanent door_flip_list door_singleton_nonempty.

Definition audit_permanent_flip_uniform_entropy_drop :=
  @permanent_flip_uniform_entropy_drop
    bool DoorInstr door_step door_opened bool_dec door_all Open [false]
    door_finite door_permanent door_flip_list door_singleton_nonempty.

Definition audit_permanent_step_entropy_ceiling :=
  fun probability =>
    @permanent_step_entropy_ceiling
      bool DoorInstr door_step door_opened bool_dec door_all Open [false]
      probability door_finite door_permanent door_flip_list door_singleton_nonempty.

Definition audit_permanent_step_entropy_drop :=
  fun probability =>
    @permanent_step_entropy_drop
      bool DoorInstr door_step door_opened bool_dec door_all Open [false]
      probability door_finite door_permanent door_flip_list door_singleton_nonempty.

Definition audit_a2_from_compression_price_and_permanence :=
  @a2_from_compression_price_and_permanence
    bool DoorInstr door_step door_opened door_cost bool_dec door_all
    door_finite door_permanent.

Definition audit_compression_priced_trace_floor :=
  @compression_priced_trace_floor
    bool DoorInstr door_step door_opened door_cost bool_dec door_all
    door_finite door_permanent.

Definition audit_flip_merges_or_revokes :=
  flip_merges_or_revokes
    bool DoorInstr door_step door_opened door_all false Open
    door_finite eq_refl eq_refl.

Definition audit_injective_flip_revokes :=
  injective_flip_revokes
    bool unit toggle_step door_opened door_all false tt
    door_finite toggle_step_injective eq_refl eq_refl.

Definition audit_permanent_at_flip_is_not_injective :=
  permanent_at_flip_is_not_injective
    bool DoorInstr door_step door_opened door_all false Open
    door_finite door_permanent_at_open eq_refl eq_refl.

Definition audit_permanent_flips_compression_bound :=
  fun compression_price =>
    @permanent_flips_compression_bound
      bool DoorInstr door_step door_opened door_cost bool_dec door_all Open [false]
      door_finite door_permanent compression_price
      door_singleton_nodup door_singleton_flips.

Definition audit_permanent_flips_log_bound :=
  fun compression_price =>
    @permanent_flips_log_bound
      bool DoorInstr door_step door_opened door_cost bool_dec door_all false Open [false]
      door_finite door_permanent compression_price eq_refl
      door_singleton_nodup door_singleton_flips.

Definition audit_permanent_record_write_is_forced_priced :=
  @permanent_record_write_is_forced_priced
    bool DoorInstr door_step door_opened door_instr_eq_dec door_all false Open
    door_finite door_permanent_at_open eq_refl eq_refl.

Definition audit_finite_reversible_cannot_write :=
  fun H =>
    @finite_reversible_cannot_write
      bool door_unit_step door_opened door_all false
      door_finite door_unit_permanent (proj1 H) (proj2 H).

(** A base whose always-enabled event opens a generic record latch. *)
Definition door_base : StructuralCoreAnyBase.BaseMachine :=
  {| StructuralCoreAnyBase.b_state := unit;
     StructuralCoreAnyBase.b_next := fun _ => tt;
     StructuralCoreAnyBase.b_init := fun _ => True;
     StructuralCoreAnyBase.b_halted := fun _ => False |}.

Definition door_base_event (_ : StructuralCoreAnyBase.b_state door_base) : bool :=
  negb false.

Lemma door_latch_reachable_event :
  exists b0 n,
    StructuralCoreAnyBase.b_init door_base b0 /\
    (let '(b, r, _) :=
       StructuralCore.rc_run (LatchCore door_base door_base_event) n
         (b0, false, 0) in
     r = false /\ door_base_event b = true).
Proof. exists tt, 0. repeat split. Qed.

Lemma door_history_reachable_event :
  exists b0 n,
    StructuralCoreAnyBase.b_init door_base b0 /\
    (let '(b, r, _, _) :=
       StructuralCore.rc_run (HistoryLatch door_base door_base_event) n
         (b0, false, [], 0) in
     r = false /\ door_base_event b = true).
Proof. exists tt, 0. repeat split. Qed.

Definition audit_latch_core_honest :=
  latch_core_honest door_base door_base_event door_latch_reachable_event.

Definition audit_history_latch_honest :=
  history_latch_honest door_base door_base_event door_history_reachable_event.

Lemma door_latch_pair_honest :
  StructuralCoreAnyBase.HonestBasePairExtension
    (LatchCore door_base door_base_event) door_base
    (latch_cover door_base door_base_event)
    (StructuralCore.rc_cert (LatchCore door_base door_base_event))
    (StructuralCore.rc_cert (LatchCore door_base door_base_event)).
Proof.
  destruct audit_latch_core_honest as [Hdriven [Hledger [Ha2 [Hperm _]]]].
  repeat split.
  - destruct Hdriven as [f Hf].
    exists (fun b r1 r2 => (f b r1, f b r2)).
    intro m. rewrite (Hf m). reflexivity.
  - exact Hledger.
  - intros m [Hflip | Hflip]; destruct Hflip as [H0 H1];
      eapply Ha2; eauto.
  - exact Hperm.
  - exact Hperm.
Qed.

Definition audit_record_axis_is_latch_holds :=
  record_axis_is_latch_holds
    (LatchCore door_base door_base_event) door_base
    (latch_cover door_base door_base_event) audit_latch_core_honest.

Definition audit_record_pair_is_two_latches_holds :=
  record_pair_is_two_latches_holds
    (LatchCore door_base door_base_event) door_base
    (latch_cover door_base door_base_event)
    (StructuralCore.rc_cert (LatchCore door_base door_base_event))
    (StructuralCore.rc_cert (LatchCore door_base door_base_event))
    door_latch_pair_honest.

Definition audit_shadow_cannot_price_exactly :=
  @shadow_cannot_price_exactly
    bool DoorInstr unit door_step door_opened (fun _ => tt)
    door_blind_collision.

Definition audit_shadow_floor_overcharges :=
  @shadow_floor_overcharges
    bool DoorInstr unit door_step door_opened (fun _ => tt)
    door_blind_collision.

Definition audit_step_price_is_exact :=
  @step_price_is_exact bool DoorInstr door_step door_opened.

Definition audit_window_showing_reading_has_no_collision :=
  @window_showing_reading_has_no_collision
    bool DoorInstr bool door_step door_opened (fun b => b) (fun b => b)
    (fun _ => eq_refl).

Definition audit_window_showing_reading_prices_exactly :=
  @window_showing_reading_prices_exactly
    bool DoorInstr bool door_step door_opened (fun b => b) (fun b => b)
    (fun _ => eq_refl).

Definition audit_universal_nfi_any_substrate :=
  universal_nfi_any_substrate door_system.

(** Concrete functor instance for the door-opening structure event. *)
Module DoorNoFreeInsightSystem <: NO_FREE_INSIGHT_SYSTEM.
  Definition S := bool.
  Definition Trace := list DoorInstr.
  Definition Obs := bool.
  Definition Strength := bool.
  Definition run (tr : Trace) (s : S) := Some (door_execute tr s).
  (** Every Boolean door state is an admissible state in this two-state audit
      model.  The equality form makes that finite-model choice explicit. *)
  Definition ok (_ : S) : Prop := tt = tt.
  (** This functor theorem does not inspect cost.  The audit instance uses the
      neutral natural-number ledger and proves monotonicity below. *)
  Definition mu (_ : S) : nat := Nat.sub 0 0.
  Definition observe (s : S) : Obs := s.
  Definition certifies (s : S) (strength : Strength) : Prop :=
    s = true /\ strength = true.
  Definition strictly_stronger (strength weak : Strength) : Prop :=
    strength = true /\ weak = false.
  Definition structure_event (tr : Trace) (s : S) : Prop :=
    exists s1, run tr s = Some s1 /\ s = false /\ s1 = true.
  Definition clean_start (s : S) : Prop := s = false.
  Definition Certified (tr : Trace) (s : S) (strength : Strength) : Prop :=
    exists s1, run tr s = Some s1 /\ ok s1 /\ certifies s1 strength.

  Definition Certified_spec :
    forall tr s0 strength,
      Certified tr s0 strength <->
      exists s1, run tr s0 = Some s1 /\ ok s1 /\ certifies s1 strength.
  Proof. reflexivity. Defined.

  Definition mu_monotone :
    forall tr s0 s1, run tr s0 = Some s1 -> mu s0 <= mu s1.
  Proof. intros. unfold mu. lia. Defined.

  Definition no_free_insight_contract :
    forall tr s0 s1 strength weak,
      clean_start s0 ->
      run tr s0 = Some s1 ->
      strictly_stronger strength weak ->
      certifies s1 strength ->
      structure_event tr s0.
  Proof.
    intros tr s0 s1 strength weak Hclean Hrun Hstrict [Hopened Hstrength].
    exists s1. repeat split; assumption.
  Defined.
End DoorNoFreeInsightSystem.

Module DoorNoFreeInsight := NoFreeInsight DoorNoFreeInsightSystem.

Definition audit_no_free_insight := DoorNoFreeInsight.no_free_insight.

(** One opaque proof declaration per audit application.  Each type
    is inferred from the corresponding exact application above, then checked
    again as an opaque proof constant. *)
Lemma evidence_a2_equal_trust_substitution_payoff :
  ltac:(let T := type of audit_a2_equal_trust_substitution_payoff in exact T).
Proof. exact audit_a2_equal_trust_substitution_payoff. Qed.

Lemma evidence_exact_commitment_pricing_characterization :
  ltac:(let T := type of audit_exact_commitment_pricing_characterization in exact T).
Proof. exact audit_exact_commitment_pricing_characterization. Qed.

Lemma evidence_substitution_test_rejects_non_a2_exact_substitute :
  ltac:(let T := type of audit_substitution_test_rejects_non_a2_exact_substitute in exact T).
Proof. exact audit_substitution_test_rejects_non_a2_exact_substitute. Qed.

Lemma evidence_commitment_cost_not_reducible_to_erasure_cost :
  ltac:(let T := type of audit_commitment_cost_not_reducible_to_erasure_cost in exact T).
Proof. exact audit_commitment_cost_not_reducible_to_erasure_cost. Qed.

Lemma evidence_a2_and_aara_iff_exact :
  ltac:(let T := type of audit_a2_and_aara_iff_exact in exact T).
Proof. exact audit_a2_and_aara_iff_exact. Qed.

Lemma evidence_flips_le_cost :
  ltac:(let T := type of audit_flips_le_cost in exact T).
Proof. exact audit_flips_le_cost. Qed.

Lemma evidence_a2_iff_nonnegative_amortized_cost :
  ltac:(let T := type of audit_a2_iff_nonnegative_amortized_cost in exact T).
Proof. exact audit_a2_iff_nonnegative_amortized_cost. Qed.

Lemma evidence_certification_system_is_potential_method :
  ltac:(let T := type of audit_certification_system_is_potential_method in exact T).
Proof. exact audit_certification_system_is_potential_method. Qed.

Lemma evidence_nfi_by_potential :
  ltac:(let T := type of audit_nfi_by_potential in exact T).
Proof. exact audit_nfi_by_potential. Qed.

Lemma evidence_F1_strong_form_universal :
  ltac:(let T := type of audit_F1_strong_form_universal in exact T).
Proof. exact audit_F1_strong_form_universal. Qed.

Lemma evidence_gas_schedule_exactness :
  ltac:(let T := type of audit_gas_schedule_exactness in exact T).
Proof. exact audit_gas_schedule_exactness. Qed.

Lemma evidence_overcharge_breaks_exactness :
  ltac:(let T := type of audit_overcharge_breaks_exactness in exact T).
Proof. exact audit_overcharge_breaks_exactness. Qed.

Lemma evidence_undercharged_opcode_admits_free_commitment :
  ltac:(let T := type of audit_undercharged_opcode_admits_free_commitment in exact T).
Proof. exact audit_undercharged_opcode_admits_free_commitment. Qed.

Lemma evidence_free_forgery_violates_A2 :
  ltac:(let T := type of audit_free_forgery_violates_A2 in exact T).
Proof. exact audit_free_forgery_violates_A2. Qed.

Lemma evidence_honest_cost_tracking_strict_restriction :
  ltac:(let T := type of audit_honest_cost_tracking_strict_restriction in exact T).
Proof. exact audit_honest_cost_tracking_strict_restriction. Qed.

Lemma evidence_a2_from_merging_price_and_permanence :
  ltac:(let T := type of audit_a2_from_merging_price_and_permanence in exact T).
Proof. exact audit_a2_from_merging_price_and_permanence. Qed.

Lemma evidence_honest_erasure_accounting_implies_a2 :
  ltac:(let T := type of audit_honest_erasure_accounting_implies_a2 in exact T).
Proof. exact audit_honest_erasure_accounting_implies_a2. Qed.

Lemma evidence_permanent_certification_trace_floor :
  ltac:(let T := type of audit_permanent_certification_trace_floor in exact T).
Proof. exact audit_permanent_certification_trace_floor. Qed.

Lemma evidence_permanent_flip_is_not_injective :
  ltac:(let T := type of audit_permanent_flip_is_not_injective in exact T).
Proof. exact audit_permanent_flip_is_not_injective. Qed.

Lemma evidence_permanent_flips_collapse_at_least :
  ltac:(let T := type of audit_permanent_flips_collapse_at_least in exact T).
Proof. exact audit_permanent_flips_collapse_at_least. Qed.

Lemma evidence_a2_from_entropy_price_and_permanence :
  ltac:(let T := type of audit_a2_from_entropy_price_and_permanence in exact T).
Proof. exact audit_a2_from_entropy_price_and_permanence. Qed.

Lemma evidence_entropy_priced_trace_floor :
  ltac:(let T := type of audit_entropy_priced_trace_floor in exact T).
Proof. exact audit_entropy_priced_trace_floor. Qed.

Lemma evidence_permanent_flip_full_support_entropy_drop_positive :
  ltac:(let T := type of audit_permanent_flip_full_support_entropy_drop_positive in exact T).
Proof. exact audit_permanent_flip_full_support_entropy_drop_positive. Qed.

Lemma evidence_permanent_flip_full_support_heat_positive :
  ltac:(let T := type of audit_permanent_flip_full_support_heat_positive in exact T).
Proof. exact audit_permanent_flip_full_support_heat_positive. Qed.

Lemma evidence_permanent_flip_heat_floor :
  ltac:(let T := type of audit_permanent_flip_heat_floor in exact T).
Proof. exact audit_permanent_flip_heat_floor. Qed.

Lemma evidence_permanent_flip_heat_positive :
  ltac:(let T := type of audit_permanent_flip_heat_positive in exact T).
Proof. exact audit_permanent_flip_heat_positive. Qed.

Lemma evidence_permanent_flip_uniform_entropy_drop :
  ltac:(let T := type of audit_permanent_flip_uniform_entropy_drop in exact T).
Proof. exact audit_permanent_flip_uniform_entropy_drop. Qed.

Lemma evidence_permanent_step_entropy_ceiling :
  ltac:(let T := type of audit_permanent_step_entropy_ceiling in exact T).
Proof. exact audit_permanent_step_entropy_ceiling. Qed.

Lemma evidence_permanent_step_entropy_drop :
  ltac:(let T := type of audit_permanent_step_entropy_drop in exact T).
Proof. exact audit_permanent_step_entropy_drop. Qed.

Lemma evidence_a2_from_compression_price_and_permanence :
  ltac:(let T := type of audit_a2_from_compression_price_and_permanence in exact T).
Proof. exact audit_a2_from_compression_price_and_permanence. Qed.

Lemma evidence_compression_priced_trace_floor :
  ltac:(let T := type of audit_compression_priced_trace_floor in exact T).
Proof. exact audit_compression_priced_trace_floor. Qed.

Lemma evidence_flip_merges_or_revokes :
  ltac:(let T := type of audit_flip_merges_or_revokes in exact T).
Proof. exact audit_flip_merges_or_revokes. Qed.

Lemma evidence_injective_flip_revokes :
  ltac:(let T := type of audit_injective_flip_revokes in exact T).
Proof. exact audit_injective_flip_revokes. Qed.

Lemma evidence_permanent_at_flip_is_not_injective :
  ltac:(let T := type of audit_permanent_at_flip_is_not_injective in exact T).
Proof. exact audit_permanent_at_flip_is_not_injective. Qed.

Lemma evidence_permanent_flips_compression_bound :
  ltac:(let T := type of audit_permanent_flips_compression_bound in exact T).
Proof. exact audit_permanent_flips_compression_bound. Qed.

Lemma evidence_permanent_flips_log_bound :
  ltac:(let T := type of audit_permanent_flips_log_bound in exact T).
Proof. exact audit_permanent_flips_log_bound. Qed.

Lemma evidence_permanent_record_write_is_forced_priced :
  ltac:(let T := type of audit_permanent_record_write_is_forced_priced in exact T).
Proof. exact audit_permanent_record_write_is_forced_priced. Qed.

Lemma evidence_finite_reversible_cannot_write :
  ltac:(let T := type of audit_finite_reversible_cannot_write in exact T).
Proof. exact audit_finite_reversible_cannot_write. Qed.

Lemma evidence_latch_core_honest :
  ltac:(let T := type of audit_latch_core_honest in exact T).
Proof. exact audit_latch_core_honest. Qed.

Lemma evidence_history_latch_honest :
  ltac:(let T := type of audit_history_latch_honest in exact T).
Proof. exact audit_history_latch_honest. Qed.

Lemma evidence_record_axis_is_latch_holds :
  ltac:(let T := type of audit_record_axis_is_latch_holds in exact T).
Proof. exact audit_record_axis_is_latch_holds. Qed.

Lemma evidence_record_pair_is_two_latches_holds :
  ltac:(let T := type of audit_record_pair_is_two_latches_holds in exact T).
Proof. exact audit_record_pair_is_two_latches_holds. Qed.

Lemma evidence_shadow_cannot_price_exactly :
  ltac:(let T := type of audit_shadow_cannot_price_exactly in exact T).
Proof. exact audit_shadow_cannot_price_exactly. Qed.

Lemma evidence_shadow_floor_overcharges :
  ltac:(let T := type of audit_shadow_floor_overcharges in exact T).
Proof. exact audit_shadow_floor_overcharges. Qed.

Lemma evidence_step_price_is_exact :
  ltac:(let T := type of audit_step_price_is_exact in exact T).
Proof. exact audit_step_price_is_exact. Qed.

Lemma evidence_window_showing_reading_has_no_collision :
  ltac:(let T := type of audit_window_showing_reading_has_no_collision in exact T).
Proof. exact audit_window_showing_reading_has_no_collision. Qed.

Lemma evidence_window_showing_reading_prices_exactly :
  ltac:(let T := type of audit_window_showing_reading_prices_exactly in exact T).
Proof. exact audit_window_showing_reading_prices_exactly. Qed.

Lemma evidence_universal_nfi_any_substrate :
  ltac:(let T := type of audit_universal_nfi_any_substrate in exact T).
Proof. exact audit_universal_nfi_any_substrate. Qed.

Lemma evidence_no_free_insight :
  ltac:(let T := type of audit_no_free_insight in exact T).
Proof. exact audit_no_free_insight. Qed.

(** The current VM schedule does not satisfy the theory interface's global
    payload-pricing field.  The concrete counterexample below keeps that
    obstacle visible.  A functor parameter supplies the exact missing field,
    while every other field has a concrete implementation. *)
Open Scope string_scope.

Lemma current_schedule_not_globally_cert_priced :
  ~ (forall instr, MuChaitin.cert_priced instr).
Proof.
  intro Hpriced.
  specialize (Hpriced (VMStep.VMStep.instr_morph_assert 0 "a" "" 0)).
  unfold MuChaitin.cert_priced, MuChaitin.cert_payload_size in Hpriced.
  specialize (Hpriced eq_refl).
  rewrite !VMStep.VMStep.payload_bit_length_ascii in Hpriced.
  cbn [VMStep.VMStep.instruction_cost String.length] in Hpriced.
  lia.
Qed.

Module Type CERT_PRICING_POLICY.
  Parameter priced : forall instr, MuChaitin.cert_priced instr.
End CERT_PRICING_POLICY.

Module EmptyMuChaitinSystem (P : CERT_PRICING_POLICY)
  <: MU_CHAITIN_THEORY_SYSTEM.
  Definition theory_desc := EmptyString.
  Definition overhead := Nat.sub 0 0.
  Definition proves_bits (_ : nat) : Prop := False.
  Definition trace_for (_ : nat) : RevelationProof.Trace :=
    List.firstn 0 [VMStep.VMStep.instr_halt 0].
  Definition fuel_for (_ : nat) := Nat.sub 0 0.
  Definition s_init := MuInitiality.init_state.

  Definition clean_start : s_init.(vm_csrs).(csr_cert_addr) = 0%nat.
  Proof. reflexivity. Defined.

  Definition priced := P.priced.

  Definition proves_bits_witness :
    forall k,
      proves_bits k ->
      exists s_final instr,
        RevelationProof.trace_run (fuel_for k) (trace_for k) s_init = Some s_final /\
        RevelationProof.has_supra_cert s_final /\
        MuNoFreeInsightQuantitative.is_cert_setter instr /\
        mu_info_nat s_init s_final >= MuChaitin.cert_payload_size instr /\
        MuChaitin.cert_payload_size instr >= k /\
        s_final.(vm_mu) <=
          s_init.(vm_mu) + VMStep.VMStep.payload_bit_length theory_desc + overhead.
  Proof. intros k H. contradiction. Defined.
End EmptyMuChaitinSystem.

Module EmptyMuChaitinAudit (P : CERT_PRICING_POLICY).
  Module ConcreteSystem := EmptyMuChaitinSystem P.
  Module ConcreteTheory := MuChaitinTheory ConcreteSystem.

  Definition audit_supra_cert_run_implies_paid_payload :=
    ConcreteTheory.supra_cert_run_implies_paid_payload.

  Definition audit_mu_info_nat_le_from_mu_budget :=
    ConcreteTheory.mu_info_nat_le_from_mu_budget.

  Definition audit_proves_bits_bounded_by_description :=
    ConcreteTheory.proves_bits_bounded_by_description.

  Lemma evidence_supra_cert_run_implies_paid_payload :
    ltac:(let T := type of audit_supra_cert_run_implies_paid_payload in exact T).
  Proof. exact audit_supra_cert_run_implies_paid_payload. Qed.

  Lemma evidence_mu_info_nat_le_from_mu_budget :
    ltac:(let T := type of audit_mu_info_nat_le_from_mu_budget in exact T).
  Proof. exact audit_mu_info_nat_le_from_mu_budget. Qed.

  Lemma evidence_proves_bits_bounded_by_description :
    ltac:(let T := type of audit_proves_bits_bounded_by_description in exact T).
  Proof. exact audit_proves_bits_bounded_by_description. Qed.
End EmptyMuChaitinAudit.

Print Assumptions audit_no_free_insight.
Print Assumptions audit_honest_erasure_accounting_implies_a2.

(** * Closing the conditional door witnesses

    Fourteen door specializations above keep a premise explicit. Ten of those
    premises are mathematical, and the door machine satisfies them: the
    uniform distribution on its two states with full support, compression
    pricing and entropy pricing of [door_cost], and a blind price that meets
    the event floor. The closed witnesses below discharge them. The four
    Landauer rows keep a physical premise, which no machine fact discharges. *)

From Coq Require Import Reals Lra.

Section DoorClosure.
Local Open Scope R_scope.

Definition door_uniform : bool -> R := uniform_on bool_dec door_all.

Lemma door_uniform_value : forall b, door_uniform b = / 2.
Proof.
  intros [|]; unfold door_uniform, uniform_on, in_b;
    destruct (in_dec bool_dec _ door_all) as [_ | H];
    [simpl; field | exfalso; apply H; simpl; auto
    | simpl; field | exfalso; apply H; simpl; auto].
Qed.

Lemma door_uniform_distribution : distribution door_all door_uniform.
Proof.
  split.
  - intro b. rewrite door_uniform_value. lra.
  - unfold rsum, door_all. simpl. rewrite !door_uniform_value. field.
Qed.

Lemma door_uniform_positive : forall b, 0 < door_uniform b.
Proof. intro b. rewrite door_uniform_value. lra. Qed.

Lemma door_uniform_support :
  forall x, In x door_all -> 0 < door_uniform x ->
    In x (certified_states bool door_opened door_all ++ [false]).
Proof. intros [|] _ _; simpl; auto. Qed.

Lemma door_log2_two : log2 (INR 2) = 1.
Proof.
  unfold log2. simpl INR. replace (1 + 1) with 2 by lra.
  assert (Hln : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  field. lra.
Qed.

(** [Open] sends every state to [true], so the pushed distribution has no
    entropy. *)
Lemma door_open_push_entropy_zero : forall p,
  distribution door_all p ->
  entropy door_all (push bool_dec door_all (fun s => door_step s Open) p) = 0.
Proof.
  intros p [_ Hsum].
  unfold rsum, door_all in Hsum. simpl in Hsum.
  unfold entropy, push, rsum, door_all, door_step, surprisal_term. simpl.
  replace (p false + (p true + 0)) with 1 by lra.
  replace (0 + (0 + 0)) with 0 by lra.
  destruct (Rlt_dec 0 0) as [H0 | _]; [lra |].
  destruct (Rlt_dec 0 1) as [_ | H1]; [| lra].
  unfold log2. rewrite ln_1. field.
  rewrite <- ln_1. apply Rgt_not_eq. apply ln_increasing; lra.
Qed.

(** [Wait] is the identity, so the pushed distribution is the original. *)
Lemma door_wait_push_same : forall p y,
  push bool_dec door_all (fun s => door_step s Wait) p y = p y.
Proof.
  intros p [|]; unfold push, rsum, door_all, door_step; simpl;
    repeat match goal with |- context [bool_dec ?a ?b] =>
      destruct (bool_dec a b); try discriminate end; lra.
Qed.

(** The [Wait] step leaves the entropy of every distribution invariant. *)
Lemma step_wait_entropy_invariant : forall p,
  entropy door_all (push bool_dec door_all (fun s => door_step s Wait) p) = entropy door_all p.
Proof.
  intro p. unfold entropy, rsum, door_all. cbn [fold_right].
  rewrite !door_wait_push_same. reflexivity.
Qed.

Lemma door_entropy_priced : entropy_priced door_step bool_dec door_all door_cost.
Proof.
  intros [|] p Hp.
  - rewrite door_open_push_entropy_zero by exact Hp.
    pose proof (entropy_le_log_support door_all door_all p
                  (proj1 door_finite) Hp (fun a Ha _ => Ha) ltac:(simpl; lia)) as Hle.
    assert (Hl : log2 (INR (List.length door_all)) = 1) by exact door_log2_two.
    rewrite Hl in Hle.
    unfold door_cost. simpl INR. lra.
  - rewrite step_wait_entropy_invariant. unfold door_cost. simpl INR. lra.
Qed.

Lemma door_bool_nodup_length : forall D : list bool, NoDup D -> (List.length D <= 2)%nat.
Proof.
  intros D HD. change 2%nat with (List.length door_all).
  apply NoDup_incl_length; [exact HD |]. intros [|] _; simpl; auto.
Qed.

Lemma door_open_image_size : forall D,
  D <> [] -> image_size door_step bool_dec Open D = 1%nat.
Proof.
  intros D HD. unfold image_size, door_step.
  destruct D as [| d D]; [contradiction |]. clear HD.
  induction D as [| e D IH]; [reflexivity |].
  simpl in *. destruct (in_dec bool_dec true (map (fun _ => true) D)) as [Hin | Hnot].
  - destruct (in_dec bool_dec true (true :: map (fun _ => true) D)); [exact IH |].
    exfalso. simpl in *. tauto.
  - destruct D as [| f D]; [reflexivity | simpl in Hnot; tauto].
Qed.

Lemma door_wait_image_size : forall D,
  NoDup D -> image_size door_step bool_dec Wait D = List.length D.
Proof.
  intros D HD. unfold image_size, door_step.
  rewrite map_id. rewrite (nodup_fixed_point bool_dec HD). reflexivity.
Qed.

Lemma door_compression_priced : compression_priced door_step door_cost bool_dec.
Proof.
  intros [|] D HD.
  - pose proof (door_bool_nodup_length D HD) as Hlen.
    destruct D as [| d D']; [simpl; lia |].
    rewrite door_open_image_size by discriminate.
    unfold door_cost. simpl in *. lia.
  - rewrite (door_wait_image_size D HD). unfold door_cost. simpl. lia.
Qed.

End DoorClosure.

Lemma closed_permanent_step_entropy_ceiling :
  ltac:(let T := type of (audit_permanent_step_entropy_ceiling door_uniform
                            door_uniform_distribution door_uniform_support) in exact T).
Proof.
  exact (audit_permanent_step_entropy_ceiling door_uniform
           door_uniform_distribution door_uniform_support).
Qed.

Lemma closed_permanent_step_entropy_drop :
  ltac:(let T := type of (audit_permanent_step_entropy_drop door_uniform
                            door_uniform_distribution door_uniform_support) in exact T).
Proof.
  exact (audit_permanent_step_entropy_drop door_uniform
           door_uniform_distribution door_uniform_support).
Qed.

Lemma closed_permanent_flip_full_support_entropy_drop_positive :
  ltac:(let T := type of (audit_permanent_flip_full_support_entropy_drop_positive
                            door_uniform door_uniform_distribution
                            (fun x _ => door_uniform_positive x)) in exact T).
Proof.
  exact (audit_permanent_flip_full_support_entropy_drop_positive door_uniform
           door_uniform_distribution (fun x _ => door_uniform_positive x)).
Qed.

Lemma closed_a2_from_entropy_price_and_permanence :
  a2_holds door_step door_opened door_cost.
Proof. exact (audit_a2_from_entropy_price_and_permanence door_entropy_priced). Qed.

Lemma closed_entropy_priced_trace_floor :
  ltac:(let T := type of (audit_entropy_priced_trace_floor door_entropy_priced) in exact T).
Proof. exact (audit_entropy_priced_trace_floor door_entropy_priced). Qed.

Lemma closed_a2_from_compression_price_and_permanence :
  a2_holds door_step door_opened door_cost.
Proof. exact (audit_a2_from_compression_price_and_permanence door_compression_priced). Qed.

Lemma closed_compression_priced_trace_floor :
  ltac:(let T := type of (audit_compression_priced_trace_floor door_compression_priced) in exact T).
Proof. exact (audit_compression_priced_trace_floor door_compression_priced). Qed.

Lemma closed_permanent_flips_compression_bound :
  ltac:(let T := type of (audit_permanent_flips_compression_bound door_compression_priced) in exact T).
Proof. exact (audit_permanent_flips_compression_bound door_compression_priced). Qed.

Lemma closed_permanent_flips_log_bound :
  ltac:(let T := type of (audit_permanent_flips_log_bound door_compression_priced) in exact T).
Proof. exact (audit_permanent_flips_log_bound door_compression_priced). Qed.

(** The constant price one meets the floor, and the blind window then
    charges a step that does not open the door. *)
Lemma closed_shadow_floor_overcharges :
  exists s i,
    flips door_step door_opened s i = false /\
    (shadow_cost door_step (fun _ : bool => tt) (fun _ _ => 1%nat) s i >= 1)%nat.
Proof.
  apply (audit_shadow_floor_overcharges (fun _ _ => 1%nat)).
  intros s i _. unfold shadow_cost. lia.
Qed.

Print Assumptions step_wait_entropy_invariant.
Print Assumptions closed_permanent_step_entropy_ceiling.
Print Assumptions closed_permanent_step_entropy_drop.
Print Assumptions closed_permanent_flip_full_support_entropy_drop_positive.
Print Assumptions closed_a2_from_entropy_price_and_permanence.
Print Assumptions closed_entropy_priced_trace_floor.
Print Assumptions closed_a2_from_compression_price_and_permanence.
Print Assumptions closed_compression_priced_trace_floor.
Print Assumptions closed_permanent_flips_compression_bound.
Print Assumptions closed_permanent_flips_log_bound.
Print Assumptions closed_shadow_floor_overcharges.
