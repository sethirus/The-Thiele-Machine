
(** =========================================================================
    SPACELAND: Abstract Interface for Partition-Aware Computation
    =========================================================================

    This file defines the abstract "Spaceland" interface without using
    Module Types / Parameters. Instead, we package operations + axioms into a
    dependent Record so the repository stays free of uninterpreted interface
    assumptions.
*)

From Coq Require Import List Bool ZArith Lia QArith.
From Coq Require QArith.
Import ListNotations.
Import QArith_base.
Open Scope Z_scope.

(** Labels are parameterized by the model's [ModuleId] type. *)
Inductive Label (ModuleId : Type) : Type :=
  | LCompute : Label ModuleId
  | LSplit : ModuleId -> Label ModuleId
  | LMerge : ModuleId -> ModuleId -> Label ModuleId
  | LObserve : ModuleId -> Label ModuleId.

Arguments LCompute {ModuleId}.
Arguments LSplit {ModuleId} _.
Arguments LMerge {ModuleId} _ _.
Arguments LObserve {ModuleId} _.

(** A Spaceland packages operations and their axioms. *)
Record Spaceland : Type :=
  {
    (* Core state/partition structure *)
    State : Type;
    Partition : Type;
    ModuleId : Type;
    get_partition : State -> Partition;
    module_of : State -> nat -> ModuleId;
    same_partition : State -> State -> Prop;
    partition_wellformed : forall (s : State),
      exists (modules : list ModuleId), (length modules > 0)%nat;

    (* Transition system *)
    Instruction : Type;
    program : State -> list Instruction;
    pc : State -> nat;
    is_in_footprint : Instruction -> nat -> bool;
    step : State -> Label ModuleId -> State -> Prop;
    step_deterministic : forall s l s1 s2,
      step s l s1 -> step s l s2 -> s1 = s2;
    module_independence : forall s s' i,
      step s (@LCompute ModuleId) s' ->
      nth_error (program s) (pc s) = Some i ->
      (forall m', is_in_footprint i m' = false -> module_of s m' = module_of s' m');

    (* μ accounting *)
    mu : State -> Label ModuleId -> State -> Z;
    mu_nonneg : forall s l s', step s l s' -> mu s l s' >= 0;

    (* Traces (constructor-shaped so axioms can talk about single steps) *)
    Trace : Type;
    TNil : State -> Trace;
    TCons : State -> Label ModuleId -> Trace -> Trace;
    trace_init : Trace -> State;
    trace_final : Trace -> State;
    valid_trace : Trace -> Prop;
    trace_mu : Trace -> Z;
    mu_monotone : forall t1 s l,
      valid_trace (TCons s l t1) ->
      trace_mu (TCons s l t1) >= trace_mu t1;
    trace_concat : Trace -> Trace -> Trace;
    mu_additive : forall t1 t2,
      trace_final t1 = trace_init t2 ->
      trace_mu (trace_concat t1 t2) = trace_mu t1 + trace_mu t2;

    (* Revelation costs *)
    mu_blind_free : forall s s',
      step s (@LCompute ModuleId) s' ->
      same_partition s s' ->
      mu s (@LCompute ModuleId) s' >= 0;
    mu_observe_positive : forall s (m : ModuleId) s',
      step s (LObserve m) s' ->
      mu s (LObserve m) s' > 0;
    mu_split_positive : forall s (m : ModuleId) s',
      step s (LSplit m) s' ->
      mu s (LSplit m) s' > 0;
    mu_merge_free : forall s (m1 m2 : ModuleId) s',
      step s (LMerge m1 m2) s' ->
      mu s (LMerge m1 m2) s' >= 0;

    (* Flatland projection *)
    PartitionTrace : Type;
    MuTrace : Type;
    partition_trace : Trace -> PartitionTrace;
    mu_trace : Trace -> MuTrace;
    project : Trace -> PartitionTrace * MuTrace;

    (* Receipts *)
    Receipt : Type;
    trace_labels : Trace -> list (Label ModuleId);
    trace_initial : Trace -> State;
    make_receipt : Trace -> Receipt;
    verify_receipt : Receipt -> bool;
    receipt_sound : forall (r : Receipt),
      verify_receipt r = true -> exists (t : Trace), make_receipt t = r;
    receipt_complete : forall (t : Trace),
      verify_receipt (make_receipt t) = true;

    (* Thermodynamic connection *)
    kT_ln2 : Q;
    landauer_bound : Z -> Q;
    mu_thermodynamic : forall s l s',
      step s l s' ->
      exists W : Q, Qle (landauer_bound (mu s l s')) W;
    blind_reversible : forall s s',
      step s (@LCompute ModuleId) s' ->
      mu s (@LCompute ModuleId) s' = 0 ->
      landauer_bound (mu s (@LCompute ModuleId) s') == 0%Q
  }.

(** Morphisms and isomorphisms between Spacelands. *)
Module SpacelandMorphism.
  Section WithSpacelands.
    Context (S1 S2 : Spaceland).

    Record Morphism : Type := {
      state_map : State S1 -> State S2;
      partition_map : Partition S1 -> Partition S2;
      label_map : Label (ModuleId S1) -> Label (ModuleId S2);
      preserve_partition : forall s,
        partition_map (get_partition S1 s) = get_partition S2 (state_map s);
      preserve_step : forall s l s',
        step S1 s l s' ->
        step S2 (state_map s) (label_map l) (state_map s');
      preserve_mu : forall s l s',
        step S1 s l s' ->
        mu S1 s l s' = mu S2 (state_map s) (label_map l) (state_map s')
    }.
  End WithSpacelands.
End SpacelandMorphism.

Module SpacelandIsomorphism.
  Section WithSpacelands.
    Context (S1 S2 : Spaceland).

    Record Isomorphism : Type := {
      state_map_fwd : State S1 -> State S2;
      partition_map_fwd : Partition S1 -> Partition S2;
      label_map_fwd : Label (ModuleId S1) -> Label (ModuleId S2);
      state_map_bwd : State S2 -> State S1;
      partition_map_bwd : Partition S2 -> Partition S1;
      label_map_bwd : Label (ModuleId S2) -> Label (ModuleId S1);

      preserve_partition_fwd : forall s,
        partition_map_fwd (get_partition S1 s) = get_partition S2 (state_map_fwd s);
      preserve_step_fwd : forall s l s',
        step S1 s l s' ->
        step S2 (state_map_fwd s) (label_map_fwd l) (state_map_fwd s');
      preserve_mu_fwd : forall s l s',
        step S1 s l s' ->
        mu S1 s l s' = mu S2 (state_map_fwd s) (label_map_fwd l) (state_map_fwd s');

      preserve_partition_bwd : forall s,
        partition_map_bwd (get_partition S2 s) = get_partition S1 (state_map_bwd s);
      preserve_step_bwd : forall s l s',
        step S2 s l s' ->
        step S1 (state_map_bwd s) (label_map_bwd l) (state_map_bwd s');
      preserve_mu_bwd : forall s l s',
        step S2 s l s' ->
        mu S2 s l s' = mu S1 (state_map_bwd s) (label_map_bwd l) (state_map_bwd s');

      inverse_state_fwd_bwd : forall (s : State S1), state_map_bwd (state_map_fwd s) = s;
      inverse_state_bwd_fwd : forall (s : State S2), state_map_fwd (state_map_bwd s) = s
    }.
  End WithSpacelands.
End SpacelandIsomorphism.

(** Placeholder statement of a representation theorem. *)
Section RepresentationTheorem.
  Context (S1 S2 : Spaceland).
  Definition same_projection : Prop :=
    exists (iso : SpacelandIsomorphism.Isomorphism S1 S2), True.

  Definition representation : Prop := same_projection.
End RepresentationTheorem.
