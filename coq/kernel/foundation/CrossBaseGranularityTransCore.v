(** Transitivity of the weak base equivalence. *)

From Kernel Require Import StructuralCoreAnyBase CrossBaseGranularityCore.

Definition weak_base_equiv_trans : Prop :=
  forall (B1 B2 B3 : BaseMachine) (O : Type)
         (obs1 : b_state B1 -> O) (obs2 : b_state B2 -> O)
         (obs3 : b_state B3 -> O),
    weak_base_equiv B1 B2 O obs1 obs2 ->
    weak_base_equiv B2 B3 O obs2 obs3 ->
    weak_base_equiv B1 B3 O obs1 obs3.
