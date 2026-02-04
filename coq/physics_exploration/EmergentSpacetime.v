(** Emergent Spacetime: c from mu-Propagation *)

Require Import Reals Lra.
From Kernel Require Import InformationCausality.
From PhysicsExploration Require Import PlanckDerivation.
Open Scope R_scope.

(** d_mu: operational distance unit (normalized) *)

Definition d_mu : R := 1.

Lemma d_mu_positive : d_mu > 0.
Proof. unfold d_mu. lra. Qed.

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
