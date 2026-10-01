(** Event-generic propositions.

    This file contains definitions only.  It states the exact propositions
    obtained when the certification reading in the certification theorems is
    replaced by an arbitrary latchable reading.  Proofs and counterexamples
    are in EventGeneralization.v. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality RevelationRequirement.
From Kernel Require Import PermanentCertification FiniteCertMachine.
From Kernel Require Import BlindnessRepresentation ProjectionNonExistence.
From Kernel Require Import ShadowPricing EventSwapCore NecessityAbstract.
From Kernel Require Import AbstractNoFI CHSHStatisticalBridge.
From Kernel Require Import StructuralCore StructuralCoreCover.
From Kernel Require Import StructuralCoreSchedule StructuralUniqueness.
From Kernel Require Import StructuralScheduleUniqueness.
From Kernel Require Import UniversalCertificationCost TraceStateDescent.
From Kernel Require Import WitnessPreservationImpossibility.
From Kernel Require Import ThieleTraceProjection.

(** A semantic writer is defined from the reading, rather than by naming an
    opcode.  This is the event-generic replacement for [cert_addr_setterb]. *)
Definition event_writes (E : Reading) (s : VMState) (i : vm_instruction) : Prop :=
  E s = false /\ E (vm_apply s i) = true.

Definition event_run (trace : list vm_instruction) (s : VMState) : VMState :=
  fold_left vm_apply trace s.

Definition event_trace_writes (E : Reading) (trace : list vm_instruction)
    (s : VMState) : Prop := E s = false /\ E (event_run trace s) = true.

Definition event_step_mu_paid (E : Reading) : Prop :=
  forall s i, event_writes E s i ->
    vm_mu (vm_apply s i) >= vm_mu s + 1.

Definition event_trace_mu_paid (E : Reading) : Prop :=
  forall trace s, event_trace_writes E trace s ->
    vm_mu (event_run trace s) >= vm_mu s + 1.

Definition event_trace_has_writer (E : Reading) : Prop :=
  forall trace s, event_trace_writes E trace s ->
    exists i, In i trace /\ exists before, event_writes E before i.

Definition event_writers_merge (E : Reading) : Prop :=
  forall s i, event_writes E s i ->
    ~ PermanentCertification.step_injective vm_apply i.

Definition generalized_step_price : Prop :=
  forall E, EventSwapCore.latchable E -> EventSwapCore.priced E.

Definition generalized_step_mu : Prop :=
  forall E, latchable E -> event_step_mu_paid E.

Definition generalized_step_price_and_mu : Prop :=
  forall E, latchable E -> forall s i, event_writes E s i ->
    instruction_cost i >= 1 /\ vm_mu (vm_apply s i) >= vm_mu s + 1.

Definition generalized_trace_mu : Prop :=
  forall E, latchable E -> event_trace_mu_paid E.

Fixpoint event_trace_cost (trace : list vm_instruction) : nat :=
  match trace with
  | [] => 0
  | i :: rest => instruction_cost i + event_trace_cost rest
  end.

Definition generalized_trace_cost : Prop :=
  forall E, latchable E -> forall trace s,
    event_trace_writes E trace s -> event_trace_cost trace >= 1.

Definition generalized_trace_writer : Prop :=
  forall E, latchable E -> event_trace_has_writer E.

Definition generalized_vm_writer_merge : Prop :=
  forall E, latchable E -> event_writers_merge E.

Definition generalized_vm_priced_merge_bundle : Prop :=
  forall E, latchable E ->
    (forall s i, event_writes E s i ->
       ~ PermanentCertification.step_injective vm_apply i /\
       instruction_cost i >= 1) /\
    (exists i, ~ PermanentCertification.step_injective vm_apply i /\
               instruction_cost i = 0) /\
    ~ PermanentCertification.merging_steps_priced vm_apply instruction_cost.

Definition generalized_forget_hidden : Prop :=
  forall E, latchable E -> hidden_from_forget E.

Definition generalized_bare_hidden : Prop :=
  forall E, latchable E -> hidden_from_bare E.

Definition generalized_forget_price_inexact : Prop :=
  forall E, latchable E -> forget_price_inexact E.

Definition generalized_bare_price_inexact : Prop :=
  forall E, latchable E -> bare_price_inexact E.

Definition event_unit_charge (E : Reading) (s : VMState)
    (i : vm_instruction) : bool := negb (E s) && E (vm_apply s i).

Definition event_unit_cost (E : Reading) (s : VMState)
    (i : vm_instruction) : nat := if event_unit_charge E s i then 1 else 0.

Definition generalized_event_unit_pricing_exact : Prop :=
  forall E, latchable E ->
    ShadowPricing.meets_floor vm_apply E (event_unit_cost E) /\
    ShadowPricing.never_overcharges vm_apply E (event_unit_cost E).

Definition generalized_event_unit_price_lower_bounds_mu : Prop :=
  forall E, latchable E -> forall s i,
    event_unit_charge E s i = true ->
    event_unit_cost E s i <= instruction_cost i.

Definition generalized_partition_refinement_nonfree : Prop :=
  forall E, latchable E -> forall trace s,
    event_trace_writes E trace s ->
    (exists i, In i trace /\ instruction_cost i >= 1 /\
               exists before, event_writes E before i) /\
    vm_mu (event_run trace s) >= vm_mu s + 1.

Definition generalized_partition_free_but_event_nonfree : Prop :=
  (exists r, instruction_cost (instr_pnew r 0) = 0) /\
  (exists m l r, instruction_cost (instr_psplit m l r 0) = 0) /\
  (exists m1 m2, instruction_cost (instr_pmerge m1 m2 0) = 0) /\
  (forall r c, cert_addr_setterb (instr_pnew r c) = false) /\
  (forall m l r c, cert_addr_setterb (instr_psplit m l r c) = false) /\
  (forall m1 m2 c, cert_addr_setterb (instr_pmerge m1 m2 c) = false) /\
  generalized_trace_mu.

Definition generalized_bounded_run_mu : Prop :=
  forall E, latchable E -> forall fuel program s,
    E s = false -> vm_mu s = 0 -> E (run_vm fuel program s) = true ->
    0 < vm_mu (run_vm fuel program s).

(** The finite model keeps its state space, transition, and price schedule.
    Only its record reading is replaced. *)
Definition freading_latchable (E : FState -> bool) : Prop :=
  PermanentCertification.permanent fstep E /\
  exists s i, E s = false /\ E (fstep s i) = true.

Definition generalized_finite_permanent : Prop :=
  forall E, freading_latchable E ->
    PermanentCertification.permanent fstep E.

Definition generalized_finite_writer_merge : Prop :=
  forall E, freading_latchable E ->
    forall s i, E s = false -> E (fstep s i) = true ->
      ~ PermanentCertification.step_injective fstep i.

Definition generalized_finite_a2_from_merging_price : Prop :=
  forall E, freading_latchable E ->
    PermanentCertification.a2_holds fstep E fcost.

Definition generalized_finite_a2_from_compression_price : Prop :=
  forall E, freading_latchable E ->
    PermanentCertification.a2_holds fstep E fcost.

(** Projection claims use semantic recoverability. *)
Definition event_complete {C : Type} (P : VMState -> C) (E : Reading) : Prop :=
  exists Omega : C -> bool, forall s, Omega (P s) = E s.

Definition event_pair_complete {C : Type} (P : VMState -> C)
    (E : Reading) : Prop :=
  exists Omega : C -> nat * bool,
    forall s, Omega (P s) = (vm_mu s, E s).

Definition projection_forgets_event {C : Type} (P : VMState -> C)
    (E : Reading) : Prop :=
  exists s1 s2, P s1 = P s2 /\ E s1 <> E s2.

Definition P_event (E : Reading) (s : VMState)
    : list nat * list nat * nat * bool :=
  (vm_mem s, vm_regs s, vm_pc s, E s).

Definition P_full_event (E : Reading) (s : VMState)
    : list nat * list nat * nat * nat * bool :=
  (vm_mem s, vm_regs s, vm_pc s, vm_mu s, E s).

Definition generalized_strict_projection_necessity : Prop :=
  forall E, latchable E -> ~ event_complete P_strict E.

Definition generalized_cost_projection_necessity : Prop :=
  forall E, latchable E -> ~ event_complete P_cost E.

Definition generalized_projection_irredundancy : Prop :=
  forall E, latchable E ->
    NecessityAbstract.mu_complete (P_full_event E) /\
    event_complete (P_full_event E) E /\
    (forall (C : Type) (P : VMState -> C),
       NecessityAbstract.proj_forgets_mu P ->
       ~ NecessityAbstract.mu_complete P) /\
    (forall (C : Type) (P : VMState -> C),
       projection_forgets_event P E -> ~ event_complete P E).

Definition generalized_projection_classification : Prop :=
  forall E, latchable E ->
    NecessityAbstract.mu_complete (P_full_event E) /\
    event_complete (P_full_event E) E /\
    ~ NecessityAbstract.mu_complete P_strict /\
    ~ event_complete P_strict E /\
    NecessityAbstract.mu_complete P_cost /\
    ~ event_complete P_cost E /\
    event_complete (P_event E) E /\
    ~ NecessityAbstract.mu_complete (P_event E).

Definition generalized_mutual_independence : Prop :=
  forall E, latchable E ->
    ~ NecessityAbstract.mu_complete P_strict /\
    ~ event_complete P_strict E /\
    ~ event_complete P_cost E /\
    ~ NecessityAbstract.mu_complete (P_event E).

Definition generalized_three_component_independence : Prop :=
  generalized_mutual_independence /\
  ~ exists Omega : FullMuLedgerShadow -> PartitionGraph,
      forall s, Omega (P_full s) = vm_graph s.

Definition generalized_joint_ledger_necessity : Prop :=
  forall E, latchable E -> ~ event_pair_complete P_strict E.

Definition generalized_certify_pnew_separation : Prop :=
  forall E, latchable E -> forall s,
    P_strict (vm_apply s (instr_certify 0)) =
      P_strict (vm_apply s (instr_pnew [] 0)) /\
    vm_mu (vm_apply s (instr_certify 0)) = vm_mu s + 1 /\
    vm_mu (vm_apply s (instr_pnew [] 0)) = vm_mu s /\
    E (vm_apply s (instr_certify 0)) = true.

(** Permanence and revocation are disjoint by definition. *)
Definition generalized_revocation_boundary : Prop :=
  forall (S I : Type) (step : S -> I -> S) (E : S -> bool),
    PermanentCertification.permanent step E ->
    ~ exists s i, E s = true /\ E (step s i) = false.

(** Replace only the record field of an RCM. *)
Definition with_record (M : RCM) (E : rc_state M -> bool) : RCM := {|
  rc_state := rc_state M;
  rc_next := rc_next M;
  rc_init := rc_init M;
  rc_cert := E;
  rc_mu := rc_mu M;
  rc_halted := rc_halted M
|}.

Definition rcm_latchable (M : RCM) (E : rc_state M -> bool) : Prop :=
  (forall s, E s = true -> E (rc_next M s) = true) /\
  exists s, E s = false /\ E (rc_next M s) = true.

Definition thiele_event_core (E : rc_state ThieleCore -> bool) : RCM :=
  with_record ThieleCore E.

Definition billed_event_reading (E : rc_state ThieleCore -> bool)
    (x : rc_state BilledCore) : bool := E (billed_cover_state x).

Definition billed_event_core (E : rc_state ThieleCore -> bool) : RCM :=
  with_record BilledCore (billed_event_reading E).

Definition surcharged_event_reading
    (extra : rc_state ThieleCore -> nat)
    (E : rc_state ThieleCore -> bool)
    (x : rc_state (SurchargedCore extra)) : bool :=
  E (surcharged_cover_state x).

Definition surcharged_event_core
    (extra : rc_state ThieleCore -> nat)
    (E : rc_state ThieleCore -> bool) : RCM :=
  with_record (SurchargedCore extra) (surcharged_event_reading extra E).

Definition generalized_billed_core_adequate : Prop :=
  forall E, rcm_latchable ThieleCore E -> Adequate (billed_event_core E).

Definition generalized_billed_core_honest_extension : Prop :=
  forall E, rcm_latchable ThieleCore E ->
    HonestVMExtension (billed_event_core E).

Definition generalized_billed_not_core_equiv : Prop :=
  forall E, rcm_latchable ThieleCore E ->
    ~ core_equiv (billed_event_core E) (thiele_event_core E).

Definition generalized_billed_not_observed_equiv : Prop :=
  forall E, rcm_latchable ThieleCore E ->
    ~ observed_core_equiv (billed_event_core E) (thiele_event_core E).

Definition schedule_priced (M : RCM) : Prop :=
  ledger_carried M /\ rc_a2 M.

Definition schedule_honest_between (M B : RCM)
    (C : ComputationalCover M B) : Prop :=
  (forall m, rc_cert M m = rc_cert B (cover_state M B C m)) /\
  schedule_priced M /\ record_permanent M /\ reachable_record_write M.

Definition equiv_mod_schedule_between (M B : RCM)
    (C : ComputationalCover M B) : Prop :=
  schedule_priced M /\ schedule_priced B /\
  exists R : rc_state M -> rc_state B -> Prop,
    (forall m b, R m b -> cover_state M B C m = b) /\
    (forall m, rc_init M m -> exists b, rc_init B b /\ R m b) /\
    (forall b, rc_init B b -> exists m, rc_init M m /\ R m b) /\
    (forall m b, R m b ->
       rc_cert M m = rc_cert B b /\
       (rc_halted M m <-> rc_halted B b) /\
       R (rc_next M m) (rc_next B b)).

Definition generalized_schedule_uniqueness : Prop :=
  forall M B (C : ComputationalCover M B),
    schedule_priced B -> schedule_honest_between M B C ->
    equiv_mod_schedule_between M B C.

Definition generalized_billed_schedule_equivalence : Prop :=
  forall E, rcm_latchable ThieleCore E ->
    exists C : ComputationalCover (billed_event_core E) (thiele_event_core E),
      equiv_mod_schedule_between (billed_event_core E) (thiele_event_core E) C.

Definition generalized_surcharged_schedule_equivalence : Prop :=
  forall extra E, rcm_latchable ThieleCore E ->
    exists C : ComputationalCover (surcharged_event_core extra E)
                                    (thiele_event_core E),
      equiv_mod_schedule_between (surcharged_event_core extra E)
                                 (thiele_event_core E) C.

(** Event-parametric reachable simulations. *)
Definition event_trace_compatible (E : Reading) (M : CertCostMachine)
    (base : ccm_state M) : Prop :=
  forall t, E (vm_trace_eval t) = ccm_cert M (target_trace_eval M base t).

Record ReachableEventSimulation (E : Reading) (M : CertCostMachine)
    (base : ccm_state M) := {
  event_reachable_map : VMState -> ccm_state M;
  event_reachable_map_base : event_reachable_map init_state = base;
  event_reachable_map_step : forall t i,
    event_reachable_map (vm_apply (vm_trace_eval t) i) =
      ccm_step M (event_reachable_map (vm_trace_eval t)) i;
  event_reachable_map_reading : forall t,
    E (vm_trace_eval t) = ccm_cert M (event_reachable_map (vm_trace_eval t))
}.

Definition generalized_reachable_simulation_exists : Prop :=
  forall (representative : VMState -> list vm_instruction),
    (forall t, vm_trace_eval (representative (vm_trace_eval t)) = vm_trace_eval t) ->
    forall E M base,
      inhabited (ReachableEventSimulation E M base) <->
      trace_fiber_compatible M base /\ event_trace_compatible E M base.

Definition generalized_reachable_simulation_unique : Prop :=
  forall E M base (left right : ReachableEventSimulation E M base) t,
    event_reachable_map E M base left (vm_trace_eval t) =
    event_reachable_map E M base right (vm_trace_eval t).

Definition history_event_compatible (E : Reading) : Prop :=
  forall t, E (vm_trace_eval t) = E (vm_trace_eval t).

Definition history_fiber_compatible : Prop :=
  forall t u, vm_trace_eval t = vm_trace_eval u -> t = u.

Definition generalized_agreement_does_not_imply_descent : Prop :=
  forall E, latchable E ->
    history_event_compatible E /\ ~ history_fiber_compatible.

(** An external certification system may reflect its reading into any chosen
    VM reading, not only [vm_certified]. *)
Record EventSimulatingCertificationSystem (E : Reading) := {
  escs_base : CertificationSystem;
  escs_decode : cs_instr escs_base -> vm_instruction;
  escs_embed : cs_state escs_base -> VMState;
  escs_step_commutes : forall s i,
    escs_embed (cs_step escs_base s i) =
      vm_apply (escs_embed s) (escs_decode i);
  escs_cost_preserved : forall i,
    cs_cost escs_base i >= instruction_cost (escs_decode i);
  escs_event_reflects : forall s,
    cs_cert escs_base s = E (escs_embed s)
}.

Definition generalized_simulating_system_representation : Prop :=
  forall E (SCS : EventSimulatingCertificationSystem E)
         (s0 : cs_state (escs_base E SCS))
         (trace : list (cs_instr (escs_base E SCS))),
    cs_cert (escs_base E SCS) s0 = false ->
    cs_cert (escs_base E SCS) (cs_run (escs_base E SCS) trace s0) = true ->
    cs_total_cost (escs_base E SCS) trace >= 1 /\
    E (fold_left vm_apply (map (escs_decode E SCS) trace)
         (escs_embed E SCS s0)) = true.

Definition trace_event_decider (E : Reading) (t : ThieleTrace) : bool :=
  E (last_state t).

Definition generalized_no_classical_event_decider : Prop :=
  forall E, latchable E ->
    ~ exists f : ClassicalTrace -> bool,
        forall t : ThieleTrace, f (project_trace t) = trace_event_decider E t.

Definition generalized_nonlocal_witness_step : Prop :=
  forall E, latchable E -> forall s i,
    E s = false -> E (vm_apply s i) = true ->
    chsh_violation_certified (vm_apply s i) ->
    instruction_cost i >= 1 /\ vm_mu (vm_apply s i) >= vm_mu s + 1.

Definition generalized_nonlocal_witness_trace : Prop :=
  forall E, latchable E -> forall trace s,
    E s = false -> E (event_run trace s) = true ->
    chsh_violation_certified (event_run trace s) ->
    vm_mu (event_run trace s) >= vm_mu s + 1.

Definition event_certified (E : Reading) (trace : list vm_instruction)
    (s0 : VMState) : Prop :=
  exists s1,
    RevelationProof.trace_run (S (length trace)) trace s0 = Some s1 /\
    vm_err s1 = false /\ E s1 = true.

Definition generalized_certified_spec : Prop :=
  forall E trace s0,
    event_certified E trace s0 <->
    exists s1,
      RevelationProof.trace_run (S (length trace)) trace s0 = Some s1 /\
      vm_err s1 = false /\ E s1 = true.
