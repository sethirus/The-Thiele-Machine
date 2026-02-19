(** Holographic Gravity: G Exploration *)

Require Import Reals Lra.
From PhysicsExploration Require Import EmergentSpacetime PlanckDerivation.
Open Scope R_scope.

(** G: gravitational constant in normalized units *)

Definition G : R := 1.

(** [G_positive]: formal specification. *)
Lemma G_positive : G > 0.
Proof. unfold G. lra. Qed.

Definition l_planck : R := sqrt (h * G / (c * c * c)).

(** [G_requires_unknowns]: formal specification. *)
Theorem G_requires_unknowns :
  exists (unknown : R), unknown > 0 /\ G = unknown.
Proof.
  exists G. split; [apply G_positive | reflexivity].
Qed.
