(** A CHSH bound from two rotated-vector inequalities.

    [rotated_correlator_bounds] bounds the images of (1,1) and (1,-1)
    separately. It is a sufficient condition for the selected CHSH bound.
    It is neither an operator-norm characterization nor a condition satisfied
    by every classical or quantum correlator. The inequalities are supplied
    independently of the VM cost schedule. *)

(* SCOPE NOTE: standalone proof scope, standalone correlator algebra with explicit inequalities. *)
From Coq Require Import Reals Lra.

Local Open Scope R_scope.

Record CorrelatorBox : Type := {
  cb_E00 : R;
  cb_E01 : R;
  cb_E10 : R;
  cb_E11 : R;
}.

Definition chsh_S (b : CorrelatorBox) : R :=
  cb_E00 b + cb_E01 b + cb_E10 b - cb_E11 b.

Definition rotated_correlator_bounds (b : CorrelatorBox) : Prop :=
  (cb_E00 b + cb_E01 b)^2 + (cb_E10 b + cb_E11 b)^2 <= 2
  /\
  (cb_E00 b - cb_E01 b)^2 + (cb_E10 b - cb_E11 b)^2 <= 2.

Theorem tsirelson_bound_from_rotated_bounds :
  forall b : CorrelatorBox,
    rotated_correlator_bounds b ->
    Rabs (chsh_S b) <= 2 * sqrt 2.
Proof.
  intros b [Hu Hv].
  destruct b as [E00 E01 E10 E11].
  unfold chsh_S, rotated_correlator_bounds in *. simpl in Hu, Hv |- *.

  assert (HBnn : 0 <= (E10 + E11)^2) by apply pow2_ge_0.
  assert (HCnn : 0 <= (E00 - E01)^2) by apply pow2_ge_0.
  assert (HA2 : (E00 + E01)^2 <= 2) by lra.
  assert (HD2 : (E10 - E11)^2 <= 2) by lra.

  assert (Hsumdiff :
    (E00 + E01 + E10 - E11)^2 + ((E00 + E01) - (E10 - E11))^2
    = 2 * ((E00 + E01)^2 + (E10 - E11)^2)) by ring.
  assert (Hdiff_nn : 0 <= ((E00 + E01) - (E10 - E11))^2) by apply pow2_ge_0.
  assert (Hsq : (E00 + E01 + E10 - E11)^2 <= 8) by lra.

  assert (Hsqrt2_pos : 0 <= sqrt 2) by apply sqrt_pos.
  assert (Hsqrt2_sq : (sqrt 2)^2 = 2) by (rewrite pow2_sqrt; lra).
  assert (Hrhs_pos : 0 <= 2 * sqrt 2) by lra.
  assert (Hrhs_sq : (2 * sqrt 2)^2 = 8).
  { replace ((2 * sqrt 2)^2) with (4 * (sqrt 2)^2) by ring.
    rewrite Hsqrt2_sq. ring. }
  apply Rsqr_incr_0_var; [| exact Hrhs_pos].
  unfold Rsqr.
  assert (Habs_sq : Rabs (E00 + E01 + E10 - E11) * Rabs (E00 + E01 + E10 - E11)
                  = (E00 + E01 + E10 - E11)^2).
  { rewrite <- Rabs_mult.
    assert (Hsq_eq : (E00 + E01 + E10 - E11) * (E00 + E01 + E10 - E11)
                   = (E00 + E01 + E10 - E11)^2) by ring.
    rewrite Hsq_eq.
    apply Rabs_pos_eq.
    apply pow2_ge_0. }
  rewrite Habs_sq.
  replace ((2 * sqrt 2) * (2 * sqrt 2)) with ((2 * sqrt 2)^2) by ring.
  rewrite Hrhs_sq.
  exact Hsq.
Qed.

Definition pr_box : CorrelatorBox :=
  {| cb_E00 := 1; cb_E01 := 1; cb_E10 := 1; cb_E11 := -1 |}.

Lemma pr_box_violates_rotated_bounds : ~ rotated_correlator_bounds pr_box.
Proof.
  unfold rotated_correlator_bounds, pr_box. simpl.
  intros [H1 _].

  nra.
Qed.

Print Assumptions tsirelson_bound_from_rotated_bounds.
Print Assumptions pr_box_violates_rotated_bounds.

