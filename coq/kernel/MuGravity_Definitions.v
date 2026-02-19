From Coq Require Import Reals List.
Import ListNotations.

From Kernel Require Import MuGravity.

(** Layer 1: definitions and totality-facing helpers. *)

Definition module_neighbors_physical_only := module_neighbors_physical.
Definition module_neighbors_fallback := module_neighbors_complete.
Definition module_triangles_unique := module_triangles.
Definition horizon_predicate := is_horizon.
Definition curvature_measure := angle_defect_curvature.
Definition source_measure := stress_energy.
Definition weighted_mu_laplacian := mu_laplacian_w.
Definition residual_measure := calibration_residual.
Definition residual_rank := calibration_residual_rank.

(** [residual_rank_zero_exactly_residual_zero]: formal specification. *)
Lemma residual_rank_zero_exactly_residual_zero : forall s m,
  residual_rank s m = 0%nat <-> residual_measure s m = 0%R.
Proof.
  exact calibration_residual_rank_zero_iff.
Qed.
