(* LogicToPhysics.v — "Logic is physics" nucleus: cut = relational composition *)

Set Implicit Arguments.

Require Import Theory.Core.
Require Import Theory.PhysRel.

Section LogicToPhysics.
  Variable Gen : Type -> Type -> Type.

  (* Instantiate Core’s category C with RelCat. *)
  Let C := RelCategory.RelCat.

  (* A generator interpretation into relations (left abstract here). *)
  Variable interp0 : forall A B, Gen A B -> RelCategory.Rel A B.

  (* Extend to programs via Core's interp. *)
  Definition interp := @interp Type Gen C interp0.

  (* Cut is composition in the physics category Rel. *)
  (** [cut_is_relational_composition]: formal specification. *)
  Theorem cut_is_relational_composition :
    forall A B C0 (π1 : Prog Gen B C0) (π2 : Prog Gen A B),
      interp (cut π1 π2) =
      RelCategory.rel_comp (interp π1) (interp π2).
  Proof. intros. apply cut_is_composition. Qed.

End LogicToPhysics.
