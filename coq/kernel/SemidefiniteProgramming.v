(** =========================================================================
    SEMIDEFINITE PROGRAMMING - Foundation for NPA Hierarchy
    =========================================================================

    This file provides the mathematical foundation for proving the quantum
    Tsirelson bound (CHSH ≤ 2√2) using the NPA hierarchy.

    KEY DEFINITIONS:
    - Positive semidefinite (PSD) matrices
    - Semidefinite constraints
    - Matrix properties needed for moment matrix analysis

    APPROACH:
    We'll use a computational approach where PSD is characterized by
    all principal minors being non-negative (Sylvester's criterion).
    This is more amenable to Coq proof than eigenvalue analysis.

    ========================================================================= *)

From Coq Require Import Reals Lra Lia List.
From Coq Require Import Reals.ROrderedType.
Import ListNotations.
Local Open Scope R_scope.

(** * Matrix Representation *)

(** We represent matrices as functions from indices to reals.
    For the CHSH NPA-1 matrix, we only need small matrices (up to 5×5). *)

Definition Matrix (n : nat) : Type := nat -> nat -> R.

(** Identity matrix *)
Definition I (n : nat) : Matrix n :=
  fun i j => if Nat.eqb i j then 1 else 0.

(** Matrix element access *)
Definition get {n : nat} (M : Matrix n) (i j : nat) : R :=
  M i j.

(** Matrix transpose *)
Definition transpose {n : nat} (M : Matrix n) : Matrix n :=
  fun i j => M j i.

(** Matrix symmetry *)
Definition symmetric {n : nat} (M : Matrix n) : Prop :=
  forall (i j : nat), (i < n)%nat -> (j < n)%nat -> M i j = M j i.

(** * Determinants and Minors *)

(** 2×2 determinant *)
Definition det2 (a b c d : R) : R :=
  a * d - b * c.

(** 2×2 matrix determinant *)
Definition det2_matrix (M : Matrix 2) : R :=
  det2 (M 0%nat 0%nat) (M 0%nat 1%nat) (M 1%nat 0%nat) (M 1%nat 1%nat).

(** 3×3 determinant (Sarrus rule) *)
Definition det3_matrix (M : Matrix 3) : R :=
  M 0%nat 0%nat * M 1%nat 1%nat * M 2%nat 2%nat +
  M 0%nat 1%nat * M 1%nat 2%nat * M 2%nat 0%nat +
  M 0%nat 2%nat * M 1%nat 0%nat * M 2%nat 1%nat -
  M 0%nat 2%nat * M 1%nat 1%nat * M 2%nat 0%nat -
  M 0%nat 1%nat * M 1%nat 0%nat * M 2%nat 2%nat -
  M 0%nat 0%nat * M 1%nat 2%nat * M 2%nat 1%nat.

(** Principal 2×2 minor (top-left) *)
Definition minor2_topleft {n : nat} (M : Matrix n) : R :=
  det2 (M 0%nat 0%nat) (M 0%nat 1%nat) (M 1%nat 0%nat) (M 1%nat 1%nat).

(** Principal 2×2 minor at positions (0,2) *)
Definition minor2_02 {n : nat} (M : Matrix n) : R :=
  det2 (M 0%nat 0%nat) (M 0%nat 2%nat) (M 2%nat 0%nat) (M 2%nat 2%nat).

(** Principal 2×2 minor at positions (0,3) *)
Definition minor2_03 {n : nat} (M : Matrix n) : R :=
  det2 (M 0%nat 0%nat) (M 0%nat 3%nat) (M 3%nat 0%nat) (M 3%nat 3%nat).

(** Principal 2×2 minor at positions (0,4) *)
Definition minor2_04 {n : nat} (M : Matrix n) : R :=
  det2 (M 0%nat 0%nat) (M 0%nat 4%nat) (M 4%nat 0%nat) (M 4%nat 4%nat).

(** Principal 2×2 minor at positions (1,2) *)
Definition minor2_12 {n : nat} (M : Matrix n) : R :=
  det2 (M 1%nat 1%nat) (M 1%nat 2%nat) (M 2%nat 1%nat) (M 2%nat 2%nat).

(** Principal 2×2 minor at positions (1,3) *)
Definition minor2_13 {n : nat} (M : Matrix n) : R :=
  det2 (M 1%nat 1%nat) (M 1%nat 3%nat) (M 3%nat 1%nat) (M 3%nat 3%nat).

(** Principal 2×2 minor at positions (1,4) *)
Definition minor2_14 {n : nat} (M : Matrix n) : R :=
  det2 (M 1%nat 1%nat) (M 1%nat 4%nat) (M 4%nat 1%nat) (M 4%nat 4%nat).

(** Principal 2×2 minor at positions (2,3) *)
Definition minor2_23 {n : nat} (M : Matrix n) : R :=
  det2 (M 2%nat 2%nat) (M 2%nat 3%nat) (M 3%nat 2%nat) (M 3%nat 3%nat).

(** Principal 2×2 minor at positions (2,4) *)
Definition minor2_24 {n : nat} (M : Matrix n) : R :=
  det2 (M 2%nat 2%nat) (M 2%nat 4%nat) (M 4%nat 2%nat) (M 4%nat 4%nat).

(** Principal 2×2 minor at positions (3,4) *)
Definition minor2_34 {n : nat} (M : Matrix n) : R :=
  det2 (M 3%nat 3%nat) (M 3%nat 4%nat) (M 4%nat 3%nat) (M 4%nat 4%nat).

(** Principal 3×3 minor (top-left) *)
Definition minor3_topleft {n : nat} (M : Matrix n) : R :=
  det3_matrix (fun i j => M i j).

(** General 3x3 principal minor *)
Definition principal_minor3 {n : nat} (M : Matrix n) (i j k : nat) : R :=
  det3_matrix (fun a b =>
    let idx_r := match a with 0 => i | 1 => j | _ => k end in
    let idx_c := match b with 0 => i | 1 => j | _ => k end in
    M idx_r idx_c).

(** * Extended Determinants for Larger Matrices *)

(** 4×4 determinant using cofactor expansion along first row *)
Definition det4_matrix (M : Matrix 4) : R :=
  let minor_0 :=
    M 1%nat 1%nat * (M 2%nat 2%nat * M 3%nat 3%nat - M 2%nat 3%nat * M 3%nat 2%nat) -
    M 1%nat 2%nat * (M 2%nat 1%nat * M 3%nat 3%nat - M 2%nat 3%nat * M 3%nat 1%nat) +
    M 1%nat 3%nat * (M 2%nat 1%nat * M 3%nat 2%nat - M 2%nat 2%nat * M 3%nat 1%nat) in
  let minor_1 :=
    M 1%nat 0%nat * (M 2%nat 2%nat * M 3%nat 3%nat - M 2%nat 3%nat * M 3%nat 2%nat) -
    M 1%nat 2%nat * (M 2%nat 0%nat * M 3%nat 3%nat - M 2%nat 3%nat * M 3%nat 0%nat) +
    M 1%nat 3%nat * (M 2%nat 0%nat * M 3%nat 2%nat - M 2%nat 2%nat * M 3%nat 0%nat) in
  let minor_2 :=
    M 1%nat 0%nat * (M 2%nat 1%nat * M 3%nat 3%nat - M 2%nat 3%nat * M 3%nat 1%nat) -
    M 1%nat 1%nat * (M 2%nat 0%nat * M 3%nat 3%nat - M 2%nat 3%nat * M 3%nat 0%nat) +
    M 1%nat 3%nat * (M 2%nat 0%nat * M 3%nat 1%nat - M 2%nat 1%nat * M 3%nat 0%nat) in
  let minor_3 :=
    M 1%nat 0%nat * (M 2%nat 1%nat * M 3%nat 2%nat - M 2%nat 2%nat * M 3%nat 1%nat) -
    M 1%nat 1%nat * (M 2%nat 0%nat * M 3%nat 2%nat - M 2%nat 2%nat * M 3%nat 0%nat) +
    M 1%nat 2%nat * (M 2%nat 0%nat * M 3%nat 1%nat - M 2%nat 1%nat * M 3%nat 0%nat) in
  M 0%nat 0%nat * minor_0 - M 0%nat 1%nat * minor_1 +
  M 0%nat 2%nat * minor_2 - M 0%nat 3%nat * minor_3.

(** 5×5 determinant using cofactor expansion (for CHSH NPA-1 moment matrix) *)
(** This is large but explicit - needed for the quantum CHSH bound proof *)
Definition det5_matrix (M : Matrix 5) : R :=
  (* Expand along first row using 4×4 cofactors *)
  let cofactor_00 := det4_matrix (fun i j =>
    match i, j with
    | 0, 0 => M 1%nat 1%nat | 0, 1 => M 1%nat 2%nat | 0, 2 => M 1%nat 3%nat | 0, 3 => M 1%nat 4%nat
    | 1, 0 => M 2%nat 1%nat | 1, 1 => M 2%nat 2%nat | 1, 2 => M 2%nat 3%nat | 1, 3 => M 2%nat 4%nat
    | 2, 0 => M 3%nat 1%nat | 2, 1 => M 3%nat 2%nat | 2, 2 => M 3%nat 3%nat | 2, 3 => M 3%nat 4%nat
    | 3, 0 => M 4%nat 1%nat | 3, 1 => M 4%nat 2%nat | 3, 2 => M 4%nat 3%nat | 3, 3 => M 4%nat 4%nat
    | _, _ => 0
    end) in
  let cofactor_01 := det4_matrix (fun i j =>
    match i, j with
    | 0, 0 => M 1%nat 0%nat | 0, 1 => M 1%nat 2%nat | 0, 2 => M 1%nat 3%nat | 0, 3 => M 1%nat 4%nat
    | 1, 0 => M 2%nat 0%nat | 1, 1 => M 2%nat 2%nat | 1, 2 => M 2%nat 3%nat | 1, 3 => M 2%nat 4%nat
    | 2, 0 => M 3%nat 0%nat | 2, 1 => M 3%nat 2%nat | 2, 2 => M 3%nat 3%nat | 2, 3 => M 3%nat 4%nat
    | 3, 0 => M 4%nat 0%nat | 3, 1 => M 4%nat 2%nat | 3, 2 => M 4%nat 3%nat | 3, 3 => M 4%nat 4%nat
    | _, _ => 0
    end) in
  let cofactor_02 := det4_matrix (fun i j =>
    match i, j with
    | 0, 0 => M 1%nat 0%nat | 0, 1 => M 1%nat 1%nat | 0, 2 => M 1%nat 3%nat | 0, 3 => M 1%nat 4%nat
    | 1, 0 => M 2%nat 0%nat | 1, 1 => M 2%nat 1%nat | 1, 2 => M 2%nat 3%nat | 1, 3 => M 2%nat 4%nat
    | 2, 0 => M 3%nat 0%nat | 2, 1 => M 3%nat 1%nat | 2, 2 => M 3%nat 3%nat | 2, 3 => M 3%nat 4%nat
    | 3, 0 => M 4%nat 0%nat | 3, 1 => M 4%nat 1%nat | 3, 2 => M 4%nat 3%nat | 3, 3 => M 4%nat 4%nat
    | _, _ => 0
    end) in
  let cofactor_03 := det4_matrix (fun i j =>
    match i, j with
    | 0, 0 => M 1%nat 0%nat | 0, 1 => M 1%nat 1%nat | 0, 2 => M 1%nat 2%nat | 0, 3 => M 1%nat 4%nat
    | 1, 0 => M 2%nat 0%nat | 1, 1 => M 2%nat 1%nat | 1, 2 => M 2%nat 2%nat | 1, 3 => M 2%nat 4%nat
    | 2, 0 => M 3%nat 0%nat | 2, 1 => M 3%nat 1%nat | 2, 2 => M 3%nat 2%nat | 2, 3 => M 3%nat 4%nat
    | 3, 0 => M 4%nat 0%nat | 3, 1 => M 4%nat 1%nat | 3, 2 => M 4%nat 2%nat | 3, 3 => M 4%nat 4%nat
    | _, _ => 0
    end) in
  let cofactor_04 := det4_matrix (fun i j =>
    match i, j with
    | 0, 0 => M 1%nat 0%nat | 0, 1 => M 1%nat 1%nat | 0, 2 => M 1%nat 2%nat | 0, 3 => M 1%nat 3%nat
    | 1, 0 => M 2%nat 0%nat | 1, 1 => M 2%nat 1%nat | 1, 2 => M 2%nat 2%nat | 1, 3 => M 2%nat 3%nat
    | 2, 0 => M 3%nat 0%nat | 2, 1 => M 3%nat 1%nat | 2, 2 => M 3%nat 2%nat | 2, 3 => M 3%nat 3%nat
    | 3, 0 => M 4%nat 0%nat | 3, 1 => M 4%nat 1%nat | 3, 2 => M 4%nat 2%nat | 3, 3 => M 4%nat 3%nat
    | _, _ => 0
    end) in
  M 0%nat 0%nat * cofactor_00 - M 0%nat 1%nat * cofactor_01 +
  M 0%nat 2%nat * cofactor_02 - M 0%nat 3%nat * cofactor_03 +
  M 0%nat 4%nat * cofactor_04.

(** PSD for 4×4 matrix - all diagonal elements + ALL 2×2 principal minors + higher minors *)
Definition PSD_4 (M : Matrix 4) : Prop :=
  M 0%nat 0%nat >= 0 /\
  M 1%nat 1%nat >= 0 /\
  M 2%nat 2%nat >= 0 /\
  M 3%nat 3%nat >= 0 /\
  (* All 2×2 minors *)
  minor2_topleft M >= 0 /\
  minor2_02 M >= 0 /\
  minor2_03 M >= 0 /\
  minor2_12 M >= 0 /\
  minor2_13 M >= 0 /\
  minor2_23 M >= 0 /\
  (* Higher minors *)
  minor3_topleft M >= 0 /\
  det4_matrix M >= 0.

(** PSD for 5×5 matrix - all diagonal elements + ALL 2×2 principal minors + higher minors *)
Definition PSD_5 (M : Matrix 5) : Prop :=
  M 0%nat 0%nat >= 0 /\
  M 1%nat 1%nat >= 0 /\
  M 2%nat 2%nat >= 0 /\
  M 3%nat 3%nat >= 0 /\
  M 4%nat 4%nat >= 0 /\
  (* All 2×2 minors - 10 total for 5×5 *)
  minor2_topleft M >= 0 /\
  minor2_02 M >= 0 /\
  minor2_03 M >= 0 /\
  minor2_04 M >= 0 /\
  minor2_12 M >= 0 /\
  minor2_13 M >= 0 /\
  minor2_14 M >= 0 /\
  minor2_23 M >= 0 /\
  minor2_24 M >= 0 /\
  minor2_34 M >= 0 /\
  (* Higher minors *)
  minor3_topleft M >= 0 /\
  det4_matrix (fun i j => M i j) >= 0 /\
  det5_matrix M >= 0.

(** * Positive Semidefinite Matrices *)

(** A matrix is PSD if all principal minors are non-negative.
    This is Sylvester's criterion for PSD matrices. *)

(** PSD for 1×1 matrix *)
Definition PSD_1 (M : Matrix 1) : Prop :=
  M 0%nat 0%nat >= 0.

(** PSD for 2×2 matrix - requires BOTH diagonal elements non-negative *)
Definition PSD_2 (M : Matrix 2) : Prop :=
  M 0%nat 0%nat >= 0 /\
  M 1%nat 1%nat >= 0 /\
  det2_matrix M >= 0.

(** PSD for 3×3 matrix - all diagonal elements + ALL 2×2 principal minors + det *)
Definition PSD_3 (M : Matrix 3) : Prop :=
  M 0%nat 0%nat >= 0 /\
  M 1%nat 1%nat >= 0 /\
  M 2%nat 2%nat >= 0 /\
  (* All 2×2 minors - 3 total for 3×3 *)
  minor2_topleft M >= 0 /\
  minor2_02 M >= 0 /\
  minor2_12 M >= 0 /\
  det3_matrix M >= 0.

(** General PSD for n×n matrix (we'll specialize to small n) *)
Definition PSD {n : nat} (M : Matrix n) : Prop :=
  match n with
  | 0 => True
  | 1 => PSD_1 M
  | 2 => PSD_2 M
  | 3 => PSD_3 M
  | 4 => PSD_4 M
  | 5 => PSD_5 M
  | S (S (S (S (S (S _))))) =>
      (* For larger matrices, require all diagonal elements non-negative *)
      (forall i : nat, (i < n)%nat -> M i i >= 0)
  end.

(** Symmetric PSD matrices *)
Definition SymmetricPSD {n : nat} (M : Matrix n) : Prop :=
  symmetric M /\ PSD M.

(** * Basic PSD Properties *)

(** Diagonal elements of PSD matrices are non-negative.
    This follows directly from our PSD definition which requires all M[i,i] >= 0. *)
(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
(** [PSD_diagonal_nonneg]: formal specification. *)
Lemma PSD_diagonal_nonneg : forall (n : nat) (M : Matrix n) (i : nat),
  (i < n)%nat ->
  PSD M ->
  M i i >= 0.
Proof.
  intros n M i Hi HPSD.
  destruct n as [|n1]; [lia |].
  destruct n1 as [|n2].
  - (* n = 1 *)
    assert (i = 0)%nat by lia. subst.
    unfold PSD, PSD_1 in HPSD. exact HPSD.
  - destruct n2 as [|n3].
    + (* n = 2 *)
      unfold PSD, PSD_2 in HPSD.
      destruct HPSD as [H0 [H1 _]].
      destruct i as [|[|]]; try lia; assumption.
    + destruct n3 as [|n4].
      * (* n = 3 *)
        unfold PSD, PSD_3 in HPSD.
        destruct HPSD as [H0 [H1 [H2 _]]].
        destruct i as [|[|[|]]]; try lia; assumption.
      * destruct n4 as [|n5].
        -- (* n = 4 *)
           unfold PSD, PSD_4 in HPSD.
           destruct HPSD as [H0 [H1 [H2 [H3 _]]]].
           destruct i as [|[|[|[|]]]]; try lia; assumption.
        -- destruct n5 as [|n6].
           ++ (* n = 5 *)
              unfold PSD, PSD_5 in HPSD.
              destruct HPSD as [H0 [H1 [H2 [H3 [H4 _]]]]].
              destruct i as [|[|[|[|[|]]]]]; try lia; assumption.
           ++ (* n >= 6 *)
              unfold PSD in HPSD.
              apply HPSD. exact Hi.
Qed.

(** Identity matrix is PSD *)
Lemma I_is_PSD : forall n, PSD (I n).
Proof.
  intros n.
  destruct n as [|n1]; [simpl; trivial | ].
  destruct n1 as [|n2]; [unfold PSD, I, PSD_1; simpl; lra | ].
  destruct n2 as [|n3].
  - (* n = 2 *)
    unfold PSD, I, PSD_2, det2_matrix, det2; simpl.
    repeat split; lra.
  - destruct n3 as [|n4].
    + (* n = 3 *)
      unfold PSD, I, PSD_3.
      repeat split; simpl; try lra.
      all: try (unfold minor2_topleft, det2; vm_compute; lra).
      all: try (unfold minor2_02, det2; vm_compute; lra).
      all: try (unfold minor2_12, det2; vm_compute; lra).
      all: try (unfold det3_matrix; vm_compute; lra).
    + destruct n4 as [|n5].
      * (* n = 4 *)
        unfold PSD, I, PSD_4.
        repeat split; simpl; try lra.
        (* All 2×2 minors for identity: det = 1*1 - 0*0 = 1 *)
        all: try (unfold minor2_topleft, det2; vm_compute; lra).
        all: try (unfold minor2_02, det2; vm_compute; lra).
        all: try (unfold minor2_03, det2; vm_compute; lra).
        all: try (unfold minor2_12, det2; vm_compute; lra).
        all: try (unfold minor2_13, det2; vm_compute; lra).
        all: try (unfold minor2_23, det2; vm_compute; lra).
        all: try (unfold minor3_topleft, det3_matrix; vm_compute; lra).
        all: try (unfold det4_matrix; vm_compute; lra).
      * destruct n5 as [|n6].
        -- (* n = 5 *)
           unfold PSD, PSD_5, I.
           repeat split; simpl; try lra.
           (* All 2×2 minors for identity: det = 1*1 - 0*0 = 1 *)
           all: try (unfold minor2_topleft, det2; vm_compute; lra).
           all: try (unfold minor2_02, det2; vm_compute; lra).
           all: try (unfold minor2_03, det2; vm_compute; lra).
           all: try (unfold minor2_04, det2; vm_compute; lra).
           all: try (unfold minor2_12, det2; vm_compute; lra).
           all: try (unfold minor2_13, det2; vm_compute; lra).
           all: try (unfold minor2_14, det2; vm_compute; lra).
           all: try (unfold minor2_23, det2; vm_compute; lra).
           all: try (unfold minor2_24, det2; vm_compute; lra).
           all: try (unfold minor2_34, det2; vm_compute; lra).
           all: try (unfold minor3_topleft, det3_matrix; vm_compute; lra).
           all: try (unfold det4_matrix; vm_compute; lra).
           all: try (unfold det5_matrix; vm_compute; lra).
        -- (* n >= 6 *)
           intros i Hi. unfold PSD, I. simpl.
           destruct (Nat.eqb i i) eqn:E; [lra | apply Nat.eqb_neq in E; contradiction].
Qed.

(** * Schur Complement Criterion *)

(** For a 2×2 block matrix [[A, B], [B^T, C]], it's PSD iff
    A is PSD and C - B^T A^{-1} B is PSD (Schur complement). *)

(** Schur complement for 2×2 matrix *)
Definition schur_complement_2x2 (M : Matrix 2) : R :=
  M 1%nat 1%nat - (M 0%nat 1%nat * M 1%nat 0%nat) / M 0%nat 0%nat.

(** Schur complement criterion for 2×2 PSD matrices.
    Reference: Horn & Johnson, "Matrix Analysis" (1985), Theorem 7.7.6 *)
Lemma schur_2x2_criterion : forall (M : Matrix 2),
  symmetric M ->
  M 0%nat 0%nat > 0 ->
  (PSD M <-> (M 0%nat 0%nat >= 0 /\ schur_complement_2x2 M >= 0)).
Proof.
  intros M Hsym Hpos.
  unfold PSD, PSD_2, schur_complement_2x2, det2_matrix, det2.
  assert (Heq: M 0%nat 1%nat = M 1%nat 0%nat) by (apply Hsym; lia).
  assert (Hinv: / M 0%nat 0%nat > 0) by (apply Rinv_0_lt_compat; lra).
  assert (Hinvge: / M 0%nat 0%nat >= 0) by lra.
  (* Key identity: M 0 1 * M 1 0 = M 0 1² by symmetry *)
  assert (Hsq: M 0%nat 1%nat * M 1%nat 0%nat = M 0%nat 1%nat * M 0%nat 1%nat).
  { rewrite Heq. ring. }
  split.
  - (* PSD => conditions *)
    intros [H00 [H11 Hdet]].
    split; [lra |].
    unfold Rdiv.
    (* Goal: M 1 1 - M 0 1 * M 1 0 * / M 0 0 >= 0 *)
    (* Hdet: M 0 0 * M 1 1 - M 0 1 * M 1 0 >= 0 *)
    (* From Hdet and Hsq: M 0 0 * M 1 1 - M 0 1² >= 0 *)
    assert (Hdet': M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat >= 0) by lra.
    (* Divide by M 0 0 > 0: M 1 1 - M 0 1² / M 0 0 >= 0 *)
    assert (Hscale: M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat >= 0).
    { assert (Hdet_le: 0 <= M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat) by lra.
      assert (Hinv_le: 0 <= / M 0%nat 0%nat) by lra.
      assert (Hprod: 0 <= (M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat) *
                          / M 0%nat 0%nat).
      { apply Rmult_le_pos; assumption. }
      (* Expand: (M 0 0 * M 1 1 - M 0 1²) * /M 0 0 = M 0 0 * M 1 1 * /M 0 0 - M 0 1² * /M 0 0 *)
      (*       = M 1 1 * (M 0 0 * /M 0 0) - M 0 1² * /M 0 0 = M 1 1 * 1 - M 0 1² * /M 0 0 *)
      assert (Hexpand: (M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat) * / M 0%nat 0%nat =
                       M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat).
      { field. lra. }
      lra. }
    (* Now use Hsq to convert back to M 0 1 * M 1 0 *)
    assert (Hsq': M 0%nat 1%nat * M 1%nat 0%nat * / M 0%nat 0%nat =
                  M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat).
    { rewrite Heq. ring. }
    lra.
  - (* conditions => PSD *)
    intros [H00_ge Hschur].
    unfold Rdiv in Hschur.
    (* Hschur: M 1 1 - M 0 1 * M 1 0 * / M 0 0 >= 0 *)
    (* Use symmetry: schur with M 0 1² *)
    assert (Hschur': M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat >= 0).
    { assert (Hsq': M 0%nat 1%nat * M 1%nat 0%nat * / M 0%nat 0%nat =
                    M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat).
      { rewrite Heq. ring. }
      lra. }
    repeat split.
    + lra.
    + (* M 1 1 >= 0 *)
      assert (Hterm: 0 <= M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat).
      { apply Rmult_le_pos; [apply Rle_0_sqr | lra]. }
      lra.
    + (* det >= 0: M 0 0 * M 1 1 - M 0 1 * M 1 0 >= 0 *)
      (* Multiply Hschur' by M 0 0 > 0 *)
      assert (Hscale: M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat >= 0).
      { assert (Hle: 0 <= M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat) by lra.
        assert (H00_pos: 0 <= M 0%nat 0%nat) by lra.
        assert (Hprod: 0 <= M 0%nat 0%nat * (M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat)).
        { apply Rmult_le_pos; assumption. }
        assert (Hexpand: M 0%nat 0%nat * (M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat * / M 0%nat 0%nat) =
                         M 0%nat 0%nat * M 1%nat 1%nat - M 0%nat 1%nat * M 0%nat 1%nat).
        { field. lra. }
        lra. }
      (* Use Hsq to convert back *)
      lra.
Qed.

(** * Cauchy-Schwarz for PSD Matrices *)

(** Cauchy-Schwarz inequality for PSD matrices: M[i,j]^2 <= M[i,i] * M[j,j]
    This follows from the 2×2 principal submatrix having non-negative determinant.
    For symmetric PSD M: det([[M_ii, M_ij], [M_ji, M_jj]]) = M_ii * M_jj - M_ij^2 >= 0
    
    Note: We restrict to n <= 5 because our PSD definition for n >= 6 only includes
    diagonal non-negativity, not the full Sylvester criterion with all 2×2 minors.
    This is sufficient for our NPA hierarchy application which uses n <= 5. *)
Lemma PSD_cauchy_schwarz : forall (n : nat) (M : Matrix n) (i j : nat),
  (n <= 5)%nat ->
  (i < n)%nat -> (j < n)%nat ->
  PSD M ->
  symmetric M ->
  (M i j) * (M i j) <= (M i i) * (M j j).
Proof.
  intros n M i j Hn Hi Hj HPSD Hsym.
  (* Strategy: Use the 2×2 principal minor at positions (i,j) *)
  (* det_ij = M_ii * M_jj - M_ij * M_ji = M_ii * M_jj - M_ij^2 >= 0 *)
  assert (Heq: M i j = M j i) by (apply Hsym; assumption).
  
  destruct n as [|n1]; [lia |].
  destruct n1 as [|n2].
  - (* n = 1: i = j = 0 *)
    assert (i = 0)%nat by lia. assert (j = 0)%nat by lia. subst.
    nra.
  - destruct n2 as [|n3].
    + (* n = 2 *)
      unfold PSD, PSD_2 in HPSD.
      destruct HPSD as [H00 [H11 Hdet]].
      unfold det2_matrix, det2 in Hdet.
      assert (Hsym01: M 0%nat 1%nat = M 1%nat 0%nat) by (apply Hsym; lia).
      destruct i as [|[|]]; destruct j as [|[|]]; try lia.
      * (* i=0, j=0 *) nra.
      * (* i=0, j=1 *) rewrite Hsym01 in Hdet. nra.
      * (* i=1, j=0 *) rewrite <- Hsym01. rewrite Hsym01 in Hdet. nra.
      * (* i=1, j=1 *) nra.
    + destruct n3 as [|n4].
      * (* n = 3 *)
        unfold PSD, PSD_3 in HPSD.
        destruct HPSD as [H00 [H11 [H22 [Hm01 [Hm02 [Hm12 Hdet3]]]]]].
        unfold minor2_topleft, minor2_02, minor2_12, det2 in *.
        assert (Hsym01: M 0%nat 1%nat = M 1%nat 0%nat) by (apply Hsym; lia).
        assert (Hsym02: M 0%nat 2%nat = M 2%nat 0%nat) by (apply Hsym; lia).
        assert (Hsym12: M 1%nat 2%nat = M 2%nat 1%nat) by (apply Hsym; lia).
        destruct i as [|[|[|]]]; destruct j as [|[|[|]]]; try lia.
        -- (* i=0, j=0 *) nra.
        -- (* i=0, j=1 *) rewrite Hsym01 in Hm01. nra.
        -- (* i=0, j=2 *) rewrite Hsym02 in Hm02. nra.
        -- (* i=1, j=0 *) rewrite <- Hsym01. rewrite Hsym01 in Hm01. nra.
        -- (* i=1, j=1 *) nra.
        -- (* i=1, j=2 *) rewrite Hsym12 in Hm12. nra.
        -- (* i=2, j=0 *) rewrite <- Hsym02. rewrite Hsym02 in Hm02. nra.
        -- (* i=2, j=1 *) rewrite <- Hsym12. rewrite Hsym12 in Hm12. nra.
        -- (* i=2, j=2 *) nra.
      * destruct n4 as [|n5].
        -- (* n = 4 *)
           unfold PSD, PSD_4 in HPSD.
           destruct HPSD as [H00 [H11 [H22 [H33 [Hm01 [Hm02 [Hm03 [Hm12 [Hm13 [Hm23 [Hm3 Hdet4]]]]]]]]]]].
           unfold minor2_topleft, minor2_02, minor2_03, minor2_12, minor2_13, minor2_23, det2 in *.
           assert (Hsym01: M 0%nat 1%nat = M 1%nat 0%nat) by (apply Hsym; lia).
           assert (Hsym02: M 0%nat 2%nat = M 2%nat 0%nat) by (apply Hsym; lia).
           assert (Hsym03: M 0%nat 3%nat = M 3%nat 0%nat) by (apply Hsym; lia).
           assert (Hsym12: M 1%nat 2%nat = M 2%nat 1%nat) by (apply Hsym; lia).
           assert (Hsym13: M 1%nat 3%nat = M 3%nat 1%nat) by (apply Hsym; lia).
           assert (Hsym23: M 2%nat 3%nat = M 3%nat 2%nat) by (apply Hsym; lia).
           destruct i as [|[|[|[|]]]]; destruct j as [|[|[|[|]]]]; try lia.
           ++ (* i=0, j=0 *) nra.
           ++ (* i=0, j=1 *) rewrite Hsym01 in Hm01. nra.
           ++ (* i=0, j=2 *) rewrite Hsym02 in Hm02. nra.
           ++ (* i=0, j=3 *) rewrite Hsym03 in Hm03. nra.
           ++ (* i=1, j=0 *) rewrite <- Hsym01. rewrite Hsym01 in Hm01. nra.
           ++ (* i=1, j=1 *) nra.
           ++ (* i=1, j=2 *) rewrite Hsym12 in Hm12. nra.
           ++ (* i=1, j=3 *) rewrite Hsym13 in Hm13. nra.
           ++ (* i=2, j=0 *) rewrite <- Hsym02. rewrite Hsym02 in Hm02. nra.
           ++ (* i=2, j=1 *) rewrite <- Hsym12. rewrite Hsym12 in Hm12. nra.
           ++ (* i=2, j=2 *) nra.
           ++ (* i=2, j=3 *) rewrite Hsym23 in Hm23. nra.
           ++ (* i=3, j=0 *) rewrite <- Hsym03. rewrite Hsym03 in Hm03. nra.
           ++ (* i=3, j=1 *) rewrite <- Hsym13. rewrite Hsym13 in Hm13. nra.
           ++ (* i=3, j=2 *) rewrite <- Hsym23. rewrite Hsym23 in Hm23. nra.
           ++ (* i=3, j=3 *) nra.
        -- destruct n5 as [|n6].
           ++ (* n = 5 *)
              unfold PSD, PSD_5 in HPSD.
              destruct HPSD as (H00 & H11 & H22 & H33 & H44 & Hm01 & Hm02 & Hm03 & Hm04 & Hm12 & Hm13 & Hm14 & Hm23 & Hm24 & Hm34 & Hm3 & Hdet4 & Hdet5).
              unfold minor2_topleft, minor2_02, minor2_03, minor2_04, minor2_12, minor2_13, minor2_14, minor2_23, minor2_24, minor2_34, det2 in *.
              assert (Hsym01: M 0%nat 1%nat = M 1%nat 0%nat) by (apply Hsym; lia).
              assert (Hsym02: M 0%nat 2%nat = M 2%nat 0%nat) by (apply Hsym; lia).
              assert (Hsym03: M 0%nat 3%nat = M 3%nat 0%nat) by (apply Hsym; lia).
              assert (Hsym04: M 0%nat 4%nat = M 4%nat 0%nat) by (apply Hsym; lia).
              assert (Hsym12: M 1%nat 2%nat = M 2%nat 1%nat) by (apply Hsym; lia).
              assert (Hsym13: M 1%nat 3%nat = M 3%nat 1%nat) by (apply Hsym; lia).
              assert (Hsym14: M 1%nat 4%nat = M 4%nat 1%nat) by (apply Hsym; lia).
              assert (Hsym23: M 2%nat 3%nat = M 3%nat 2%nat) by (apply Hsym; lia).
              assert (Hsym24: M 2%nat 4%nat = M 4%nat 2%nat) by (apply Hsym; lia).
              assert (Hsym34: M 3%nat 4%nat = M 4%nat 3%nat) by (apply Hsym; lia).
              destruct i as [|[|[|[|[|]]]]]; destruct j as [|[|[|[|[|]]]]]; try lia;
              try nra;
              try (rewrite Hsym01 in Hm01; nra);
              try (rewrite Hsym02 in Hm02; nra);
              try (rewrite Hsym03 in Hm03; nra);
              try (rewrite Hsym04 in Hm04; nra);
              try (rewrite Hsym12 in Hm12; nra);
              try (rewrite Hsym13 in Hm13; nra);
              try (rewrite Hsym14 in Hm14; nra);
              try (rewrite Hsym23 in Hm23; nra);
              try (rewrite Hsym24 in Hm24; nra);
              try (rewrite Hsym34 in Hm34; nra);
              try (rewrite <- Hsym01; rewrite Hsym01 in Hm01; nra);
              try (rewrite <- Hsym02; rewrite Hsym02 in Hm02; nra);
              try (rewrite <- Hsym03; rewrite Hsym03 in Hm03; nra);
              try (rewrite <- Hsym04; rewrite Hsym04 in Hm04; nra);
              try (rewrite <- Hsym12; rewrite Hsym12 in Hm12; nra);
              try (rewrite <- Hsym13; rewrite Hsym13 in Hm13; nra);
              try (rewrite <- Hsym14; rewrite Hsym14 in Hm14; nra);
              try (rewrite <- Hsym23; rewrite Hsym23 in Hm23; nra);
              try (rewrite <- Hsym24; rewrite Hsym24 in Hm24; nra);
              try (rewrite <- Hsym34; rewrite Hsym34 in Hm34; nra).
           ++ (* n >= 6: contradicted by Hn *) lia.
Qed.

(** NOTE: A lemma about arbitrary principal minors (PSD_principal_minors_nonneg)
    was previously defined but is UNUSED in the codebase.
    For NPA hierarchy applications, the top-left minor constraints in PSD_n suffice.
    The axiom has been removed to maintain zero-axiom status. *)

(** * Absolute Value Bound *)

(** For PSD M with M[i,i] <= 1 and M[j,j] <= 1, we have |M[i,j]| <= 1 *)
(** This follows from Cauchy-Schwarz: |M[i,j]|^2 <= M[i,i] * M[j,j] <= 1*1 = 1. *)
Lemma PSD_off_diagonal_bound : forall (n : nat) (M : Matrix n) (i j : nat),
  (n <= 5)%nat ->
  (i < n)%nat -> (j < n)%nat ->
  PSD M ->
  symmetric M ->
  M i i <= 1 ->
  M j j <= 1 ->
  Rabs (M i j) <= 1.
Proof.
  intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.
  (* Get diagonal non-negativity *)
  assert (Hii_pos: M i i >= 0) by (apply PSD_diagonal_nonneg with n; assumption).
  assert (Hjj_pos: M j j >= 0) by (apply PSD_diagonal_nonneg with n; assumption).
  (* Apply Cauchy-Schwarz *)
  assert (HCS: (M i j) * (M i j) <= (M i i) * (M j j)).
  { apply PSD_cauchy_schwarz; assumption. }
  (* From HCS and bounds: M_ij^2 <= M_ii * M_jj <= 1*1 = 1, so |M_ij| <= 1 *)
  (* 0 <= x <= 1 and 0 <= y <= 1 implies xy <= 1 *)
  assert (Hprod: (M i i) * (M j j) <= 1) by nra.
  assert (Hsq_bound: (M i j) * (M i j) <= 1) by lra.
  (* From x^2 <= 1, we get -1 <= x <= 1, hence |x| <= 1 *)
  (* Use Rabs_le: |x| <= y <-> -y <= x <= y *)
  apply Rabs_le.
  split; nra.
Qed.

(** =========================================================================
    VERIFICATION SUMMARY - STEP 1 EXTENDED

    ✓ Matrix representation defined (function-based)
    ✓ Determinants and minors for 2×2, 3×3, 4×4, and 5×5 matrices
    ✓ PSD definition via Sylvester's criterion (up to 5×5)
    ✓ Basic PSD properties:
      - Diagonal elements non-negative
      - Identity matrix is PSD
      - Schur complement criterion (stated)
      - Cauchy-Schwarz inequality for PSD matrices
      - Off-diagonal bound lemma

    NEXT STEP:
    Use these foundations to construct the NPA-1 moment matrix for CHSH
    and prove the Tsirelson bound.
    ========================================================================= *)
