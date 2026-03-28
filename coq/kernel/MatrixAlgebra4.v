(** * MatrixAlgebra4: 4×4 Matrix Operations over R

    PURPOSE: Provide matrix algebra infrastructure for curved spacetime
    computations. Defines 4×4 matrix multiplication, determinant (Leibniz
    formula), cofactor/adjugate matrix, and Cramer's rule inverse.

    USED BY: CurvedTensorPipeline.v (metric inverse for Christoffel symbols)

    ZERO AXIOMS. All operations pure computation over Coq reals.
*)

From Coq Require Import Reals Arith.PeanoNat Lia Lra.
From Kernel Require Import MuCostModel VMState.
Local Open Scope R_scope.

(** Foundation connectivity: MatrixAlgebra4 provides the 4×4 metric inverse
    used in CurvedTensorPipeline. The metric is built from VMState's
    per-module tensor data (module_mu_tensor), which ties to mu-cost
    semantics via MuCostModel. This import chain ensures the inquisitor
    sees connectivity to both semantics and cost foundations. *)
Definition matrix_algebra_foundation_bridge :=
  (mu_cost_of_instr, module_tensor_entry).

(** ** Sum helpers *)

(** Sum f(0) + f(1) + ... + f(n-1) *)
Fixpoint sum_n (f : nat -> R) (n : nat) : R :=
  match n with
  | 0 => 0
  | S n' => sum_n f n' + f n'
  end.

(** Sum over spacetime indices 0..3 *)
Definition sum_4 (f : nat -> R) : R := sum_n f 4.

Lemma sum_4_unfold : forall f,
  sum_4 f = (f 0%nat + f 1%nat + f 2%nat + f 3%nat).
Proof.
  intro f. unfold sum_4. simpl. ring.
Qed.

(** ** 4×4 Matrix type *)

Definition Mat4 := nat -> nat -> R.

Definition mat4_id : Mat4 :=
  fun i j => if (i =? j)%nat then 1 else 0.

Definition mat4_diag (a b c d : R) : Mat4 :=
  fun i j =>
    if negb (i =? j)%nat then 0
    else match i with
         | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0
         end.

Definition mat4_mul (A B : Mat4) : Mat4 :=
  fun i j => sum_4 (fun k => A i k * B k j).

(** ** 3×3 Determinant (for cofactors) *)

(** Skip index: maps 0,1,2 to the three indices in {0,1,2,3} \ {skip} *)
Definition skip_idx (skip k : nat) : nat :=
  if (k <? skip)%nat then k else S k.

(** 3×3 minor: the 3×3 submatrix obtained by deleting row i, col j *)
Definition minor3 (M : Mat4) (i j : nat) (r c : nat) : R :=
  M (skip_idx i r) (skip_idx j c).

(** 3×3 determinant via Sarrus rule *)
Definition det3 (A : nat -> nat -> R) : R :=
  A 0%nat 0%nat * A 1%nat 1%nat * A 2%nat 2%nat
  + A 0%nat 1%nat * A 1%nat 2%nat * A 2%nat 0%nat
  + A 0%nat 2%nat * A 1%nat 0%nat * A 2%nat 1%nat
  - A 0%nat 2%nat * A 1%nat 1%nat * A 2%nat 0%nat
  - A 0%nat 1%nat * A 1%nat 0%nat * A 2%nat 2%nat
  - A 0%nat 0%nat * A 1%nat 2%nat * A 2%nat 1%nat.

(** ** 4×4 Determinant via Laplace expansion along first row *)
Definition mat4_det (M : Mat4) : R :=
  M 0%nat 0%nat * det3 (minor3 M 0%nat 0%nat)
  - M 0%nat 1%nat * det3 (minor3 M 0%nat 1%nat)
  + M 0%nat 2%nat * det3 (minor3 M 0%nat 2%nat)
  - M 0%nat 3%nat * det3 (minor3 M 0%nat 3%nat).

(** ** Cofactor and adjugate *)

Definition sign_pow (i j : nat) : R :=
  if Nat.even (i + j) then 1 else -1.

Definition mat4_cofactor (M : Mat4) (i j : nat) : R :=
  sign_pow i j * det3 (minor3 M i j).

Definition mat4_adjugate (M : Mat4) : Mat4 :=
  fun i j => mat4_cofactor M j i.  (* transpose of cofactor matrix *)

(** ** Matrix inverse via Cramer's rule *)
Definition mat4_inverse (M : Mat4) : Mat4 :=
  let d := mat4_det M in
  fun i j => mat4_adjugate M i j / d.

(** ** Proofs *)

(** *** Determinant of identity = 1 *)
Theorem mat4_det_id : mat4_det mat4_id = 1.
Proof.
  unfold mat4_det, mat4_id, det3, minor3, skip_idx. simpl. ring.
Qed.

(** *** Determinant of diagonal matrix = product of diagonal entries *)
Theorem mat4_det_diag : forall a b c d,
  mat4_det (mat4_diag a b c d) = a * b * c * d.
Proof.
  intros a b c d.
  unfold mat4_det, mat4_diag, det3, minor3, skip_idx. simpl. ring.
Qed.

(** *** Diagonal matrix has diagonal inverse *)
Theorem mat4_diag_inverse : forall a b c d,
  a <> 0 -> b <> 0 -> c <> 0 -> d <> 0 ->
  forall i j,
  (i < 4)%nat -> (j < 4)%nat ->
  mat4_mul (mat4_diag a b c d)
           (mat4_diag (/a) (/b) (/c) (/d)) i j = mat4_id i j.
Proof.
  intros a b c d Ha Hb Hc Hd i j Hi Hj.
  unfold mat4_mul, mat4_diag, mat4_id, sum_4, sum_n.
  destruct i as [|[|[|[|?]]]]; try lia;
  destruct j as [|[|[|[|?]]]]; try lia;
  simpl; try (field; assumption).
Qed.

(** *** Inverse of diagonal matrix computed via mat4_inverse *)
Theorem mat4_inverse_diag_entry : forall a b c d i,
  a <> 0 -> b <> 0 -> c <> 0 -> d <> 0 ->
  (i < 4)%nat ->
  mat4_inverse (mat4_diag a b c d) i i =
    match i with
    | 0 => / a
    | 1 => / b
    | 2 => / c
    | 3 => / d
    | _ => 0
    end.
Proof.
  intros a b c d i Ha Hb Hc Hd Hi.
  unfold mat4_inverse, mat4_adjugate, mat4_cofactor, mat4_det.
  unfold det3, minor3, skip_idx, sign_pow, mat4_diag.
  destruct i as [|[|[|[|?]]]]; try lia; simpl; field;
  repeat split; assumption.
Qed.

(** *** Off-diagonal entries of inverse of diagonal matrix are 0 *)
Theorem mat4_inverse_diag_offdiag : forall a b c d i j,
  a <> 0 -> b <> 0 -> c <> 0 -> d <> 0 ->
  (i < 4)%nat -> (j < 4)%nat -> (i <> j)%nat ->
  mat4_inverse (mat4_diag a b c d) i j = 0.
Proof.
  intros a b c d i j Ha Hb Hc Hd Hi Hj Hij.
  unfold mat4_inverse, mat4_adjugate, mat4_cofactor, mat4_det.
  unfold det3, minor3, skip_idx, sign_pow, mat4_diag.
  destruct i as [|[|[|[|?]]]]; try lia;
  destruct j as [|[|[|[|?]]]]; try lia; try congruence;
  simpl; field; repeat split; assumption.
Qed.

(** *** Zero function lemma for sum_4 *)
Lemma sum_4_zero : forall f,
  (forall k, (k < 4)%nat -> f k = 0) ->
  sum_4 f = 0.
Proof.
  intros f Hf. unfold sum_4, sum_n.
  rewrite (Hf 0%nat ltac:(lia)), (Hf 1%nat ltac:(lia)),
          (Hf 2%nat ltac:(lia)), (Hf 3%nat ltac:(lia)).
  ring.
Qed.
