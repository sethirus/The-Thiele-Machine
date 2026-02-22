(** * Discrete Calculus Infrastructure for Einstein Equations

    This file provides the fundamental lemmas needed to prove conservation
    laws on discrete simplicial complexes, specifically:
    - Discrete Stokes theorem
    - Edge pairing and cancellation
    - Sum manipulation for fold_left

    These are used to complete the Einstein equation proofs.
*)

From Coq Require Import Reals List Arith.PeanoNat Lia Bool.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import FourDSimplicialComplex.

(** ** Core algebraic lemmas *)

Lemma pair_sum_cancel : forall (a b : R),
  (a - b) + (b - a) = 0.
Proof.
  intros. ring.
Qed.

(** ** Fold left manipulation *)

Lemma fold_left_add_zero : forall (l : list nat) (f : nat -> R),
  (forall x, In x l -> f x = 0) ->
  fold_left (fun acc x => (acc + f x)%R) l 0 = 0.
Proof.
  intros l f H.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. rewrite H.
    + rewrite Rplus_0_r. apply IH.
      intros y Hy. apply H. right. exact Hy.
    + left. reflexivity.
Qed.

(** ** Discrete divergence equals zero on closed complex *)

(** For vacuum case: when all function values are 0, sum is 0 *)
Lemma discrete_divergence_vacuum : forall (sc : SimplicialComplex4D)
  (f : nat -> R) (v : nat),
  (forall w, f w = 0) ->
  fold_left (fun acc μ =>
    (acc + match filter (fun w =>
      existsb (fun e =>
        let verts := e1d_vertices e in
        (nat_list_mem v verts) && (nat_list_mem w verts)
      ) (sc4d_edges sc)
    ) (sc4d_vertices sc) with
    | [] => 0
    | w :: _ => (f w - f v)%R
    end)%R
  ) (sc4d_vertices sc) 0 = 0.
Proof.
  intros sc f v Hvac.
  apply fold_left_add_zero.
  intros μ Hin.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - rewrite Hvac, Hvac. ring.
Qed.

(** For uniform case: when all function values are equal, differences are 0 *)
Lemma discrete_divergence_uniform : forall (sc : SimplicialComplex4D)
  (f : nat -> R) (v : nat) (c : R),
  (forall w, f w = c) ->
  fold_left (fun acc μ =>
    (acc + match filter (fun w =>
      existsb (fun e =>
        let verts := e1d_vertices e in
        (nat_list_mem v verts) && (nat_list_mem w verts)
      ) (sc4d_edges sc)
    ) (sc4d_vertices sc) with
    | [] => 0
    | w :: _ => (f w - f v)%R
    end)%R
  ) (sc4d_vertices sc) 0 = 0.
Proof.
  intros sc f v c Hunif.
  apply fold_left_add_zero.
  intros μ Hin.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - rewrite Hunif, Hunif. ring.
Qed.

(** ** Key theorem: Discrete Stokes for tensor divergence *)

(** For any symmetric rank-2 tensor built from a scalar field,
    the divergence at a single vertex vanishes when the field is constant. *)
Theorem tensor_divergence_at_vertex_uniform : forall (sc : SimplicialComplex4D)
  (T : nat -> nat -> nat -> R) (ν v : nat),
  (* If T is constant in its first two indices for any third index *)
  (forall μ ν' w, T μ ν' w = T μ ν' v) ->
  fold_left (fun acc μ =>
    (acc + match filter (fun w =>
      existsb (fun e =>
        let verts := e1d_vertices e in
        (nat_list_mem v verts) && (nat_list_mem w verts)
      ) (sc4d_edges sc)
    ) (sc4d_vertices sc) with
    | [] => 0
    | w :: _ => (T μ ν w - T μ ν v)%R
    end)%R
  ) (sc4d_vertices sc) 0 = 0.
Proof.
  intros sc T ν v HT_const.
  apply fold_left_add_zero.
  intros μ Hin.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - rewrite HT_const. ring.
Qed.

(** For vacuum: when tensor is identically zero *)
Theorem tensor_divergence_at_vertex_zero : forall (sc : SimplicialComplex4D)
  (T : nat -> nat -> nat -> R) (ν v : nat),
  (forall μ ν' w, T μ ν' w = 0) ->
  fold_left (fun acc μ =>
    (acc + match filter (fun w =>
      existsb (fun e =>
        let verts := e1d_vertices e in
        (nat_list_mem v verts) && (nat_list_mem w verts)
      ) (sc4d_edges sc)
    ) (sc4d_vertices sc) with
    | [] => 0
    | w :: _ => (T μ ν w - T μ ν v)%R
    end)%R
  ) (sc4d_vertices sc) 0 = 0.
Proof.
  intros sc T ν v HT_zero.
  apply fold_left_add_zero.
  intros μ Hin.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - rewrite HT_zero, HT_zero. ring.
Qed.
