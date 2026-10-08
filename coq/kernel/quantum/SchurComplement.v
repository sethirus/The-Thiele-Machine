(** SchurComplement: the Schur complement test for block quadratic forms.

    Over finite index lists LU and LW, take a symmetric P on LU with a
    symmetric inverse Pinv, any Q from LW to LU, and a symmetric R on LW. The
    block form of (u, w) is u^T P u + 2 u^T Q w + w^T R w, the quadratic form
    of the symmetric block matrix with blocks P, Q, Q^T, R.

    - Completing the square: the block form equals
      (u + z)^T P (u + z) + w^T (R - Q^T Pinv Q) w, where z = Pinv Q w
      ([schur_identity]).
    - The standard form: if P is positive semidefinite, the block form is
      nonnegative for every (u, w) if and only if the complement
      R - Q^T Pinv Q is positive semidefinite ([schur_complement_psd]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz.
Import ListNotations.
From Kernel Require Import FiniteSums.
Open Scope R_scope.

Section Schur.

Variables (U W : Type).
Variable eqU : forall a b : U, {a = b} + {a <> b}.
Variables (LU : list U) (LW : list W).
Hypothesis LU_nodup : NoDup LU.
Variables (P Pinv : U -> U -> R) (Q : U -> W -> R) (R0 : W -> W -> R).
Hypothesis P_sym : forall i j, P i j = P j i.
Hypothesis Pinv_sym : forall i j, Pinv i j = Pinv j i.
Hypothesis P_Pinv : forall i m, In i LU -> In m LU ->
  sumL LU (fun j => P i j * Pinv j m) = if eqU i m then 1 else 0.

Definition sc_mvU (A : U -> U -> R) (v : U -> R) (i : U) : R := sumL LU (fun j => A i j * v j).
Definition sc_Qw (w : W -> R) (i : U) : R := sumL LW (fun m => Q i m * w m).
Definition sc_qfU (A : U -> U -> R) (v : U -> R) : R := sumL LU (fun i => v i * sc_mvU A v i).
Definition sc_qfW (A : W -> W -> R) (w : W -> R) : R :=
  sumL LW (fun l => w l * sumL LW (fun m => A l m * w m)).

Definition sc_block (u : U -> R) (w : W -> R) : R :=
  sc_qfU P u + 2 * sumL LU (fun i => u i * sc_Qw w i) + sc_qfW R0 w.

Definition sc_z (w : W -> R) : U -> R := sc_mvU Pinv (sc_Qw w).

Definition sc_complement (l m : W) : R :=
  R0 l m - sumL LU (fun i => sumL LU (fun k => Q i l * Pinv i k * Q k m)).

Lemma sc_P_z : forall w i, In i LU -> sc_mvU P (sc_z w) i = sc_Qw w i.
Proof.
  intros w i Hi. unfold sc_z, sc_mvU.
  transitivity (sumL LU (fun k => sumL LU (fun j => P i j * Pinv j k) * sc_Qw w k)).
  - transitivity (sumL LU (fun j => sumL LU (fun k => P i j * (Pinv j k * sc_Qw w k)))).
    + apply sumL_ext. intros j _. rewrite <- sumL_scale_l. reflexivity.
    + rewrite sumL_swap. apply sumL_ext. intros k _. rewrite <- sumL_scale_r.
      apply sumL_ext. intros j _. ring.
  - transitivity (sumL LU (fun k => (if eqU i k then 1 else 0) * sc_Qw w k)).
    + apply sumL_ext. intros k Hk. rewrite (P_Pinv i k Hi Hk). reflexivity.
    + apply (sumL_delta U eqU LU i (sc_Qw w) LU_nodup Hi).
Qed.

Lemma sc_cross_sym : forall u v, sumL LU (fun i => v i * sc_mvU P u i) = sumL LU (fun i => u i * sc_mvU P v i).
Proof.
  intros u v. unfold sc_mvU.
  transitivity (sumL LU (fun i => sumL LU (fun j => v i * P i j * u j))).
  { apply sumL_ext. intros i _. rewrite <- sumL_scale_l. apply sumL_ext. intros j _. ring. }
  rewrite sumL_swap. apply sumL_ext. intros j _. rewrite <- sumL_scale_l.
  apply sumL_ext. intros i _. rewrite (P_sym i j). ring.
Qed.

Lemma sc_mvU_plus : forall A u v i, sc_mvU A (fun j => u j + v j) i = sc_mvU A u i + sc_mvU A v i.
Proof. intros A u v i. unfold sc_mvU. rewrite <- sumL_plus. apply sumL_ext. intros j _. ring. Qed.

Lemma sc_zQ : forall w,
  sumL LU (fun i => sc_z w i * sc_Qw w i) =
  sumL LW (fun l => w l * sumL LW (fun m => sumL LU (fun i => sumL LU (fun k =>
    Q i l * Pinv i k * Q k m)) * w m)).
Proof.
  intro w. unfold sc_z, sc_mvU, sc_Qw.
  (* both sides are the quadruple sum over i, k, l, m of w l Q i l Pinv i k Q k m w m *)
  transitivity (sumL LU (fun i => sumL LU (fun k => sumL LW (fun l => sumL LW (fun m =>
    w l * (Q i l * Pinv i k * Q k m) * w m))))).
  - apply sumL_ext. intros i _.
    transitivity (sumL LU (fun k => Pinv i k * sumL LW (fun m => Q k m * w m) * sumL LW (fun l => Q i l * w l))).
    + rewrite <- sumL_scale_r. reflexivity.
    + apply sumL_ext. intros k _.
      transitivity (Pinv i k * (sumL LW (fun l => Q i l * w l) * sumL LW (fun m => Q k m * w m))); [ring |].
      rewrite sumL_mult, <- sumL_scale_l. apply sumL_ext. intros l _.
      rewrite <- sumL_scale_l. apply sumL_ext. intros m _. ring.
  - etransitivity. { apply sumL_ext. intros i _. apply sumL_swap. }
    etransitivity. { apply sumL_swap. }
    apply sumL_ext. intros l _.
    transitivity (sumL LU (fun i => sumL LU (fun k => sumL LW (fun m => w l * (Q i l * Pinv i k * Q k m * w m))))).
    { apply sumL_ext. intros i _. apply sumL_ext. intros k _. apply sumL_ext. intros m _. ring. }
    transitivity (w l * sumL LU (fun i => sumL LU (fun k => sumL LW (fun m => Q i l * Pinv i k * Q k m * w m)))).
    { rewrite <- sumL_scale_l. apply sumL_ext. intros i _. rewrite <- sumL_scale_l.
      apply sumL_ext. intros k _. rewrite <- sumL_scale_l. reflexivity. }
    f_equal.
    etransitivity. { apply sumL_ext. intros i _. apply sumL_swap. }
    etransitivity. { apply sumL_swap. }
    apply sumL_ext. intros m _. rewrite <- sumL_scale_r. apply sumL_ext. intros i _.
    rewrite <- sumL_scale_r. reflexivity.
Qed.

Theorem schur_identity : forall u w,
  sc_block u w = sc_qfU P (fun i => u i + sc_z w i) + sc_qfW sc_complement w.
Proof.
  intros u w. unfold sc_block.
  assert (Hexp : sc_qfU P (fun i => u i + sc_z w i) =
                 sc_qfU P u + 2 * sumL LU (fun i => u i * sc_Qw w i) +
                 sumL LU (fun i => sc_z w i * sc_Qw w i)).
  { unfold sc_qfU.
    transitivity (sumL LU (fun i => u i * sc_mvU P u i) + sumL LU (fun i => u i * sc_mvU P (sc_z w) i) +
                  (sumL LU (fun i => sc_z w i * sc_mvU P u i) + sumL LU (fun i => sc_z w i * sc_mvU P (sc_z w) i))).
    - rewrite <- !sumL_plus. apply sumL_ext. intros i _. rewrite sc_mvU_plus. ring.
    - rewrite (sc_cross_sym u (sc_z w)).
      assert (E1 : sumL LU (fun i => u i * sc_mvU P (sc_z w) i) = sumL LU (fun i => u i * sc_Qw w i)).
      { apply sumL_ext. intros i Hi. rewrite (sc_P_z w i Hi). reflexivity. }
      assert (E2 : sumL LU (fun i => sc_z w i * sc_mvU P (sc_z w) i) = sumL LU (fun i => sc_z w i * sc_Qw w i)).
      { apply sumL_ext. intros i Hi. rewrite (sc_P_z w i Hi). reflexivity. }
      rewrite E1, E2. ring. }
  rewrite Hexp, sc_zQ. unfold sc_qfW, sc_complement.
  assert (E3 : sumL LW (fun l => w l * sumL LW (fun m => (R0 l m - sumL LU (fun i => sumL LU (fun k =>
                 Q i l * Pinv i k * Q k m))) * w m)) =
               sumL LW (fun l => w l * sumL LW (fun m => R0 l m * w m)) -
               sumL LW (fun l => w l * sumL LW (fun m => sumL LU (fun i => sumL LU (fun k =>
                 Q i l * Pinv i k * Q k m)) * w m))).
  { rewrite <- sumL_minus. apply sumL_ext. intros l _. rewrite <- Rmult_minus_distr_l. f_equal.
    rewrite <- sumL_minus. apply sumL_ext. intros m _. ring. }
  rewrite E3. ring.
Qed.

Theorem schur_complement_psd :
  (forall v, 0 <= sc_qfU P v) ->
  ((forall u w, 0 <= sc_block u w) <-> (forall w, 0 <= sc_qfW sc_complement w)).
Proof.
  intros HP. split.
  - intros Hblock w. pose proof (Hblock (fun i => - sc_z w i) w) as H.
    rewrite schur_identity in H.
    assert (Hz : sc_qfU P (fun i => - sc_z w i + sc_z w i) = 0).
    { unfold sc_qfU. rewrite <- (sumL_zero U LU). apply sumL_ext. intros i _. ring. }
    rewrite Hz in H. lra.
  - intros Hc u w. rewrite schur_identity. pose proof (HP (fun i => u i + sc_z w i)).
    pose proof (Hc w). lra.
Qed.

End Schur.

Print Assumptions schur_identity.
Print Assumptions schur_complement_psd.
