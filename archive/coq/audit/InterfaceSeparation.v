From Coq Require Import Arith Lia.
Require Minimal.ThieleComplete Minimal.NeutralComplete Minimal.NeutralMore
  Minimal.SlicedEstablishment Audit.StructuralBridge.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.
Module X := Minimal.NeutralMore.
Module S := Minimal.SlicedEstablishment.

Section FixedRule.
Variable State : Type.
Variable next : State -> State.
Variable K : Type.
Variable event : K -> State -> bool.

Definition fixed_rule_base : T.machine :=
  T.mk_machine State unit (fun s _ => next s) (fun _ => 0) (fun _ => false).

Definition fixed_rule_lift_is_sliced :
  S.SlicedInterface (N.nstate fixed_rule_base) State unit K :=
  StructuralBridge.lift_as_sliced fixed_rule_base K event.

Theorem fixed_rule_lift_is_not_neutral_complete :
  ~ N.neutral_complete (N.nlift fixed_rule_base K event).
Proof.
  apply X.nlift_finitely_branching_not_nc.
  intro s; exists 1, (fun _ => 0); split.
  - intros; lia.
  - intros; reflexivity.
Qed.

(* These two interfaces are not interchangeable. This does not say that
   the base cannot compute, or that no adaptive interpreter can run on it. *)
Theorem sliced_does_not_require_this_completeness :
  inhabited (S.SlicedInterface (N.nstate fixed_rule_base) State unit K) /\
  ~ N.neutral_complete (N.nlift fixed_rule_base K event).
Proof.
  split; [constructor; exact fixed_rule_lift_is_sliced|
    exact fixed_rule_lift_is_not_neutral_complete].
Qed.
End FixedRule.

Print Assumptions fixed_rule_lift_is_sliced.
Print Assumptions fixed_rule_lift_is_not_neutral_complete.
Print Assumptions sliced_does_not_require_this_completeness.
