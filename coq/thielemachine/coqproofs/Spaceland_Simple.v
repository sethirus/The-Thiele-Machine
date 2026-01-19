(** Simple Spaceland axioms without QArith complexity *)

From Coq Require Import List Bool ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Module Type Spaceland.
  Variable State : Type.
  Variable Partition : Type.
  Variable ModuleId : Type.
  Variable get_partition : State -> Partition.
  Variable module_of : State -> nat -> ModuleId.
  
  Definition same_partition (s1 s2 : State) : Prop :=
    get_partition s1 = get_partition s2.
  
  Variable partition_wellformed : forall (s : State),
    exists (modules : list ModuleId), (length modules > 0)%nat.
  
  Inductive Label : Type :=
    | LCompute : Label
    | LSplit : ModuleId -> Label
    | LMerge : ModuleId -> ModuleId -> Label
    | LObserve : ModuleId -> Label.
  
  Variable step : State -> Label -> State -> Prop.
  
  Variable step_deterministic : forall s l s1 s2,
    step s l s1 -> step s l s2 -> s1 = s2.
  
  Variable module_independence : forall s s' m,
    step s LCompute s' ->
    (forall m', m' <> m -> module_of s m' = module_of s' m').
  
  Variable mu : State -> Label -> State -> Z.
  
  Variable mu_nonneg : forall s l s',
    step s l s' -> mu s l s' >= 0.
  
  Inductive Trace : Type :=
    | TNil : State -> Trace
    | TCons : State -> Label -> Trace -> Trace.
  
  Fixpoint trace_mu_impl (t : Trace) : Z :=
    match t with
    | TNil _ => 0
    | TCons s l rest =>
        match rest with
        | TNil s' => mu s l s'
        | TCons s' _ _ => mu s l s' + trace_mu_impl rest
        end
    end.
  
  Variable trace_mu : Trace -> Z.
  
  Variable mu_blind_free : forall s s',
    step s LCompute s' ->
    same_partition s s' ->
    mu s LCompute s' = 0.
  
  Definition PartitionTrace := list Partition.
  Definition MuTrace := list Z.
  
  Variable partition_trace : Trace -> PartitionTrace.
  Variable mu_trace : Trace -> MuTrace.
  Variable project : Trace -> PartitionTrace * MuTrace.
  
  Record Receipt := {
    initial_partition : Partition;
    final_partition : Partition;
    total_mu : Z
  }.
  
End Spaceland.
