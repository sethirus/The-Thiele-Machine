(** NPAMomentMatrix: the level-1 NPA matrix used by the CHSH quantum layer

  This file builds the level-1 NPA moment matrix for the CHSH scenario and
  packages the PSD constraints that the later Tsirelson arguments consume.
  Its role is structural: define the matrix, expose its entries, and isolate
  the algebraic conditions associated with the NPA-1 relaxation.

  The stronger optimization claim belongs elsewhere. This file is the matrix
  side of that pipeline, not the whole derivation of the final bound by
  itself.

  *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

From Coq Require Import Reals Lra Lia List.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import ConstructivePSD.

(** Operator Indices *)

(** NPAOperator: the finite operator labels used by this file.

    The five constructors are the identity label and four setting labels,
    Op_A0, Op_A1, Op_B0, and Op_B1. They are the rows and columns of the
    level-1 matrix used below. This inductive type is a label set; it does not
    by itself provide Hilbert-space operators, measurement rules, a state, or
    a physical realization of the labels.

    The later matrix definitions use the selected entries and PSD predicates
    explicitly. Any interpretation of those entries as quantum moments is an
    additional modeling premise, not a consequence of this constructor list.
*)
Inductive NPAOperator : Type :=
| Op_I    : NPAOperator  (* Identity *)
| Op_A0   : NPAOperator  (* Alice measurement 0 *)
| Op_A1   : NPAOperator  (* Alice measurement 1 *)
| Op_B0   : NPAOperator  (* Bob measurement 0 *)
| Op_B1   : NPAOperator. (* Bob measurement 1 *)

(** op_index: the fixed numeric positions used by the matrix functions.

    The mapping is explicit: Op_I maps to 0, Op_A0 and Op_A1 map to 1 and 2,
    and Op_B0 and Op_B1 map to 3 and 4. The function supplies an index for
    array-style access; it does not assert that a matrix entry has a physical
    expectation value. Injectivity is a finite property of this constructor
    mapping and must be proved separately if a later theorem needs it.
*)
Definition op_index (op : NPAOperator) : nat :=
  match op with
  | Op_I  => 0%nat
  | Op_A0 => 1%nat
  | Op_A1 => 2%nat
  | Op_B0 => 3%nat
  | Op_B1 => 4%nat
  end.

(** CHSH Correlators *)

(** CHSHCorrelations: four real inputs to the selected CHSH expression.

    The record stores E00, E01, E10, and E11. In this development they are
    real numbers supplied to algebraic predicates. The field names preserve
    the usual CHSH notation, but the record alone does not provide a joint
    probability distribution, a local hidden-variable model, a quantum state,
    or a physical experiment. Bounds or realizability statements require the
    separate premises and theorems that state them.
*)
Record CHSHCorrelations : Type := {
  E00 : R;  (* ⟨A0 ⊗ B0⟩ *)
  E01 : R;  (* ⟨A0 ⊗ B1⟩ *)
  E10 : R;  (* ⟨A1 ⊗ B0⟩ *)
  E11 : R;  (* ⟨A1 ⊗ B1⟩ *)
}.

(** S_value: the selected CHSH linear combination
    [E00 + E01 + E10 - E11]. The sign pattern is part of this record's
    notation. It does not by itself provide an operator, a state, a probability
    distribution, a Bell experiment, or any of the classical, quantum, or
    no-signaling bounds. Those statements belong to separate modules with
    separate premises.
*)
Definition S_value (c : CHSHCorrelations) : R :=
  c.(E00) + c.(E01) + c.(E10) - c.(E11).

(** NPA Moment Matrix Construction *)

(** The 5×5 NPA-1 moment matrix for CHSH.

    Matrix element Γ[i,j] represents the expectation value ⟨Op_i · Op_j⟩.

    Structure (with single-qubit marginals E_A0, E_A1, E_B0, E_B1):

    Row 0: [  1   , E_A0 , E_A1 , E_B0 , E_B1  ]
    Row 1: [ E_A0 ,  1   , ρ_AA , E00  , E01   ]
    Row 2: [ E_A1 , ρ_AA ,  1   , E10  , E11   ]
    Row 3: [ E_B0 , E00  , E10  ,  1   , ρ_BB  ]
    Row 4: [ E_B1 , E01  , E11  , ρ_BB ,  1    ]

    Where:
    - E_A0, E_A1: Alice's single-qubit expectations
    - E_B0, E_B1: Bob's single-qubit expectations
    - E_xy: CHSH correlators
    - ρ_AA = ⟨A0 · A1⟩: Alice's self-correlation
    - ρ_BB = ⟨B0 · B1⟩: Bob's self-correlation
    *)

Record NPAMomentMatrix : Type := {
  (* Single-qubit expectations *)
  npa_EA0 : R;
  npa_EA1 : R;
  npa_EB0 : R;
  npa_EB1 : R;

  (* CHSH correlators *)
  npa_E00 : R;
  npa_E01 : R;
  npa_E10 : R;
  npa_E11 : R;

  (* Self-correlations *)
  npa_rho_AA : R;  (* ⟨A0 · A1⟩ *)
  npa_rho_BB : R;  (* ⟨B0 · B1⟩ *)
}.

(** Convert NPA moment matrix to actual matrix *)
Definition npa_to_matrix (npa : NPAMomentMatrix) : Matrix 5 :=
  fun i j =>
    match i, j with
    (* Row 0 *)
    | 0%nat, 0%nat => 1
    | 0%nat, 1%nat => npa.(npa_EA0)
    | 0%nat, 2%nat => npa.(npa_EA1)
    | 0%nat, 3%nat => npa.(npa_EB0)
    | 0%nat, 4%nat => npa.(npa_EB1)

    (* Row 1 *)
    | 1%nat, 0%nat => npa.(npa_EA0)
    | 1%nat, 1%nat => 1
    | 1%nat, 2%nat => npa.(npa_rho_AA)
    | 1%nat, 3%nat => npa.(npa_E00)
    | 1%nat, 4%nat => npa.(npa_E01)

    (* Row 2 *)
    | 2%nat, 0%nat => npa.(npa_EA1)
    | 2%nat, 1%nat => npa.(npa_rho_AA)
    | 2%nat, 2%nat => 1
    | 2%nat, 3%nat => npa.(npa_E10)
    | 2%nat, 4%nat => npa.(npa_E11)

    (* Row 3 *)
    | 3%nat, 0%nat => npa.(npa_EB0)
    | 3%nat, 1%nat => npa.(npa_E00)
    | 3%nat, 2%nat => npa.(npa_E10)
    | 3%nat, 3%nat => 1
    | 3%nat, 4%nat => npa.(npa_rho_BB)

    (* Row 4 *)
    | 4%nat, 0%nat => npa.(npa_EB1)
    | 4%nat, 1%nat => npa.(npa_E01)
    | 4%nat, 2%nat => npa.(npa_E11)
    | 4%nat, 3%nat => npa.(npa_rho_BB)
    | 4%nat, 4%nat => 1

    (* Out of bounds *)
    | _, _ => 0
    end.

(** Quantum Realizability *)

(** A moment matrix is quantum realizable if it's PSD and symmetric *)
(** A moment matrix is quantum realizable if it's PSD and symmetric *)
Definition quantum_realizable (npa : NPAMomentMatrix) : Prop :=
  let M := nat_matrix_to_fin5 (npa_to_matrix npa) in
  symmetric5 M /\ PSD5 M.

Definition zero_marginal_npa (E00 E01 E10 E11 : R) : NPAMomentMatrix := {|
  npa_EA0 := 0;
  npa_EA1 := 0;
  npa_EB0 := 0;
  npa_EB1 := 0;
  npa_E00 := E00;
  npa_E01 := E01;
  npa_E10 := E10;
  npa_E11 := E11;
  npa_rho_AA := 0;
  npa_rho_BB := 0;
|}.

Definition zero_marginal_matrix (E00 E01 E10 E11 : R) : Matrix 5 := 
  npa_to_matrix (zero_marginal_npa E00 E01 E10 E11).

Definition correlator_4x4 (E00 E01 E10 E11 : R) : Matrix 4 := 
  fun i j => 
    match i, j with 
    | 0, 0 => 1   | 0, 1 => 0   | 0, 2 => E00 | 0, 3 => E01 
    | 1, 0 => 0   | 1, 1 => 1   | 1, 2 => E10 | 1, 3 => E11 
    | 2, 0 => E00 | 2, 1 => E10 | 2, 2 => 1   | 2, 3 => 0 
    | 3, 0 => E01 | 3, 1 => E11 | 3, 2 => 0   | 3, 3 => 1 
    | _, _ => 0 
    end.

(** Extract CHSH Correlations *)

Definition npa_to_chsh (npa : NPAMomentMatrix) : CHSHCorrelations := {|
  E00 := npa.(npa_E00);
  E01 := npa.(npa_E01);
  E10 := npa.(npa_E10);
  E11 := npa.(npa_E11);
|}.

(** Key Theorems *)

(** SCOPE NOTE: The following lemma relates quantum realizability to
    correlation bounds. This follows from PSD matrix properties 
    proven in ConstructivePSD.v. *)

(** If a moment matrix is quantum realizable, its CHSH correlators
    satisfy certain bounds. *)

(** Quantum realizability implies normalized correlators.
    Each CHSH correlator E_xy appears as an off-diagonal element M[i,j]
    of the moment matrix with M[i,i] = M[j,j] = 1 (diagonal normalization).
    PSD property + PSD5_off_diagonal_bound → |E_xy| ≤ 1. *)

(** Helper: all diagonals of npa_to_matrix are 1 *)
Lemma npa_diagonal_one : forall (npa : NPAMomentMatrix) (i : Fin5),
  nat_matrix_to_fin5 (npa_to_matrix npa) i i = 1.
Proof.
  intros npa i.
  unfold nat_matrix_to_fin5, npa_to_matrix.
  destruct (Fin.to_nat i) as [ni Hi].
  simpl.
  destruct ni as [|[|[|[|[|]]]]]; try reflexivity; lia.
Qed.

(** Fin5 indices for correlator positions *)
Definition idx1 : Fin5 := Fin.FS Fin.F1.
Definition idx2 : Fin5 := Fin.FS (Fin.FS Fin.F1).
Definition idx3 : Fin5 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Definition idx4 : Fin5 := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))).

(** E00 is at position (1, 3) *)
Lemma npa_E00_position : forall (npa : NPAMomentMatrix),
  nat_matrix_to_fin5 (npa_to_matrix npa) idx1 idx3 = npa.(npa_E00).
Proof.
  intro npa. unfold nat_matrix_to_fin5, npa_to_matrix, idx1, idx3.
  simpl. reflexivity.
Qed.

(** E01 is at position (1, 4) *)
Lemma npa_E01_position : forall (npa : NPAMomentMatrix),
  nat_matrix_to_fin5 (npa_to_matrix npa) idx1 idx4 = npa.(npa_E01).
Proof.
  intro npa. unfold nat_matrix_to_fin5, npa_to_matrix, idx1, idx4.
  simpl. reflexivity.
Qed.

(** E10 is at position (2, 3) *)
Lemma npa_E10_position : forall (npa : NPAMomentMatrix),
  nat_matrix_to_fin5 (npa_to_matrix npa) idx2 idx3 = npa.(npa_E10).
Proof.
  intro npa. unfold nat_matrix_to_fin5, npa_to_matrix, idx2, idx3.
  simpl. reflexivity.
Qed.

(** E11 is at position (2, 4) *)
Lemma npa_E11_position : forall (npa : NPAMomentMatrix),
  nat_matrix_to_fin5 (npa_to_matrix npa) idx2 idx4 = npa.(npa_E11).
Proof.
  intro npa. unfold nat_matrix_to_fin5, npa_to_matrix, idx2, idx4.
  simpl. reflexivity.
Qed.

(** rho_BB is at position (3, 4) — zero in zero_marginal_npa *)
Lemma npa_rho_BB_position : forall (npa : NPAMomentMatrix),
  nat_matrix_to_fin5 (npa_to_matrix npa) idx3 idx4 = npa.(npa_rho_BB).
Proof.
  intro npa. unfold nat_matrix_to_fin5, npa_to_matrix, idx3, idx4.
  simpl. reflexivity.
Qed.

(** rho_AA is at position (1, 2) *)
Lemma npa_rho_AA_position : forall (npa : NPAMomentMatrix),
  nat_matrix_to_fin5 (npa_to_matrix npa) idx1 idx2 = npa.(npa_rho_AA).
Proof.
  intro npa. unfold nat_matrix_to_fin5, npa_to_matrix, idx1, idx2.
  simpl. reflexivity.
Qed.

Lemma quantum_realizable_implies_normalized : forall (npa : NPAMomentMatrix),
  quantum_realizable npa ->
  Rabs (npa.(npa_E00)) <= 1 /\
  Rabs (npa.(npa_E01)) <= 1 /\
  Rabs (npa.(npa_E10)) <= 1 /\
  Rabs (npa.(npa_E11)) <= 1.
Proof.
  intros npa [Hsym Hpsd].
  set (M := nat_matrix_to_fin5 (npa_to_matrix npa)).
  split; [|split; [|split]].
  - (* E00 at (1,3) *)
    rewrite <- npa_E00_position.
    apply PSD5_off_diagonal_bound; auto.
    + rewrite npa_diagonal_one; lra.
    + rewrite npa_diagonal_one; lra.
  - (* E01 at (1,4) *)
    rewrite <- npa_E01_position.
    apply PSD5_off_diagonal_bound; auto.
    + rewrite npa_diagonal_one; lra.
    + rewrite npa_diagonal_one; lra.
  - (* E10 at (2,3) *)
    rewrite <- npa_E10_position.
    apply PSD5_off_diagonal_bound; auto.
    + rewrite npa_diagonal_one; lra.
    + rewrite npa_diagonal_one; lra.
  - (* E11 at (2,4) *)
    rewrite <- npa_E11_position.
    apply PSD5_off_diagonal_bound; auto.
    + rewrite npa_diagonal_one; lra.
    + rewrite npa_diagonal_one; lra.
Qed.

(** The moment matrix is symmetric by construction *)
Lemma npa_to_matrix_symmetric : forall (npa : NPAMomentMatrix),
  symmetric5 (nat_matrix_to_fin5 (npa_to_matrix npa)).
Proof.
  intros npa i j.
  unfold symmetric5, nat_matrix_to_fin5, npa_to_matrix.
  (* The nat-indexed matrix is symmetric by construction *)
  (* Prove by case analysis on all 5×5 index combinations *)
  (* Extract nat indices from Fin5 *)
  destruct (Fin.to_nat i) as [ni Hi].
  destruct (Fin.to_nat j) as [nj Hj].
  simpl.
  (* Now do case analysis on ni and nj, both < 5 *)
  destruct ni as [|[|[|[|[|]]]]]; destruct nj as [|[|[|[|[|]]]]]; try lia; reflexivity.
Qed.

(**
    VERIFICATION SUMMARY - STEP 2

    ✓ NPA operator sequence defined (5 operators for CHSH)
    ✓ Moment matrix structure formalized (5×5 symmetric matrix)
    ✓ CHSH correlations embedded in moment matrix
    ✓ Quantum realizability defined (PSD + symmetric)
    ✓ Bounds: Quantum realizable → correlators normalized

    COMPLETED (via alternate route):
    Tsirelson bound proved in TsirelsonGeneral.v / TsirelsonFromAlgebra.v
    via pure algebra, not NPA optimization. The NPA→Tsirelson path was
    superseded.
    *)
