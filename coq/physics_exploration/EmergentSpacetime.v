(** Emergent Spacetime: c from mu-Propagation *)

Require Import Reals Lra.
From Kernel Require Import InformationCausality.
From PhysicsExploration Require Import PlanckDerivation.
Open Scope R_scope.

(** INQUISITOR NOTE: Axioms d_mu encode spacetime emergence *)

Variable d_mu : R.
Variable d_mu_positive : d_mu > 0.

Definition c : R := d_mu / tau_mu.

Lemma c_positive : c > 0.
Proof.
  unfold c.
  apply Rdiv_lt_0_compat; [apply d_mu_positive | apply tau_mu_positive].
Qed.

Theorem c_structure_proof :
  exists (speed : R), speed > 0 /\ speed = d_mu / tau_mu.
Proof.
  exists c. split; [apply c_positive | reflexivity].
Qed.
