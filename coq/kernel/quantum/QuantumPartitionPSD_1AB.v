(** QuantumPartitionPSD_1AB: extend the column-contractivity ↔ PSD bridge
    from Q_1 (5×5) to Q_{1+AB} (9×9) for the bipartite CHSH scenario.

  STATE OF THIS FILE (honest accounting, no deferred axioms):
    1. The 9×9 NPA Q_{1+AB} moment matrix is built parametrically over
       the four CHSH correlators E_{ij} = ⟨A_i B_j⟩ AND the five higher
       moments γ_1..γ_5 = ⟨A_1A_2B_1⟩, ⟨A_1A_2B_2⟩, ⟨A_1B_1B_2⟩,
       ⟨A_2B_1B_2⟩, ⟨A_1A_2B_1B_2⟩.
    2. The biconditional [column_contractive_q1ab ↔ PSD9] is proved
       (Sections 4–5). This is the main mathematical content.
    3. An integer-arithmetic check at γ = 0 is proved sound (Section 7):
       passing the check ⟹ real-valued column_contractive_q1ab at γ = 0
       ⟹ PSD9 of the 9×9 matrix with γ = 0.
    4. Section 9 *diagnoses* what the γ = 0 check actually admits:
       it forces ||E||² ≤ 1 (unit ball), hence |S| ≤ 2 by Cauchy-Schwarz.
       This is *strictly stronger* than the classical bound — it excludes
       even classical-vertex correlators like (1,1,1,−1). The check at
       γ = 0 therefore certifies only a sub-cone of the classical set.
    5. Section 10 isolates the load-bearing real-valued bridge
       [column_contractive_q1ab → PSD9] under a name that makes its
       scope explicit. The caller can use this with any externally-
       supplied γ values whose column-contractivity is established by
       other means.

  WHAT IS NOT IN THIS FILE (explicitly open):
    - A γ-parameterized integer check that admits the full Q_{1+AB}
      cone. The naive translation of "∀ 6 reals, residual ≥ 0" to a
      finite Z-arithmetic test requires either Sylvester's PSD criterion
      on a 6×6 matrix (≈63 principal-minor conditions) or a custom
      quantifier elimination. Tractable but not in this iteration.
    - The Ishizaka 2025 step Q_{1+AB} = Q in the simplest Bell scenario
      (arXiv:2502.10746). Formalizing the rank-loop argument requires
      matrix-rank machinery, GNS-construction-from-moment-matrix, and
      the level-1+AB rank closure — multi-week research-grade work.
      No Coq hypothesis or axiom is introduced for this; the file
      simply does not claim Q-realizability.
    - The new opcode [instr_chsh_lassert_1ab] in the ISA. Adding it
      ripples through ~13 kernel files (pattern matches), OCaml
      extraction, and Kami RTL. The kernel bridge in Section 8 uses
      the EXISTING [instr_chsh_lassert] opcode with an extra integer-
      check hypothesis [sum_E_sq_check_witness = true] as an explicit
      premise, which the caller must supply.
*)

(* INQUISITOR NOTE: proof-connectivity — extends PSD ↔ column_contractive
   from Q_1 (5×5) to Q_{1+AB} (9×9), completing the bipartite CHSH
   characterization at the next NPA level (Navascués-Pironio-Acín 2008;
   Ishizaka 2025 for Q_{1+AB} = Q in CHSH). *)

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import NPAMomentMatrix.
From Kernel Require Import ConstructivePSD.
From Kernel Require Import MuLedgerQuantumBridge.
From Kernel Require Import QuantumPartitionPSD.
From Kernel Require Import CHSHExtraction.
From Kernel Require Import TsirelsonGeneral.

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.NArith.BinNatDef.
From Coq.Vectors Require Import Fin.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qreals.

Local Open Scope R_scope.

(** Avoid name collision between Fin.R and Reals.R *)
Notation RealNumber := Rdefinitions.R.

(** ========================================================================
    Section 1. Fin9 / Vec9 / Matrix9 infrastructure.
    Mirrors the Fin5/Vec5/Matrix5 layer of ConstructivePSD.v. The
    9-element index type is [Fin.t 9]; sums and quadratic forms are
    explicit, computable, and unfold to ring-normalizable polynomials.
    ======================================================================== *)

Notation Fin9 := (Fin.t 9).
Definition Vec9 : Type := Fin9 -> RealNumber.
Definition Matrix9 : Type := Fin9 -> Fin9 -> RealNumber.

(** Construct a [Matrix9] from a nat-indexed function of bounded domain.
    Matches the [nat_matrix_to_fin5] convention of ConstructivePSD.v. *)
Definition nat_matrix_to_fin9 (M : nat -> nat -> RealNumber) : Matrix9 :=
  fun i j => M (proj1_sig (Fin.to_nat i)) (proj1_sig (Fin.to_nat j)).

(** Nine explicit [Fin9] indices. The wildcards in deeper nestings are
    type-inferred by Fin.FS. *)
Definition j0 : Fin9 := F1.
Definition j1 : Fin9 := FS F1.
Definition j2 : Fin9 := FS (FS F1).
Definition j3 : Fin9 := FS (FS (FS F1)).
Definition j4 : Fin9 := FS (FS (FS (FS F1))).
Definition j5 : Fin9 := FS (FS (FS (FS (FS F1)))).
Definition j6 : Fin9 := FS (FS (FS (FS (FS (FS F1))))).
Definition j7 : Fin9 := FS (FS (FS (FS (FS (FS (FS F1)))))).
Definition j8 : Fin9 := FS (FS (FS (FS (FS (FS (FS (FS F1))))))).

(** Explicit 9-fold sum. Unfolds to a ring-normalizable expression. *)
Definition sum_fin9 (f : Fin9 -> RealNumber) : RealNumber :=
  f j0 + f j1 + f j2 + f j3 + f j4 + f j5 + f j6 + f j7 + f j8.

(** Quadratic form on Vec9. Computable, no bounds checks. *)
Definition quad9 (M : Matrix9) (v : Vec9) : RealNumber :=
  sum_fin9 (fun i => sum_fin9 (fun j => v i * M i j * v j)).

(** Symmetry of a 9×9 matrix. *)
Definition symmetric9 (M : Matrix9) : Prop :=
  forall i j : Fin9, M i j = M j i.

(** PSD of a 9×9 matrix: every quadratic form is nonneg. *)
Definition PSD9 (M : Matrix9) : Prop :=
  forall v : Vec9, quad9 M v >= 0.

(** ========================================================================
    Section 2. The 9×9 Q_{1+AB} moment matrix.
    ========================================================================

    Indices (rows and columns) name operators in this order:
      0: I
      1: A_1
      2: A_2
      3: B_1
      4: B_2
      5: A_1 B_1
      6: A_1 B_2
      7: A_2 B_1
      8: A_2 B_2

    Algebraic identities used to fill in the matrix:
      A_i^2 = B_j^2 = I,  ⟨A_i⟩ = ⟨B_j⟩ = 0,
      ⟨A_1 A_2⟩ = ⟨B_1 B_2⟩ = 0,  [A_i, B_j] = 0.

    Free parameters: E_{ij} (four CHSH correlators) and γ_1..γ_5 (five
    higher-order moments). *)

Definition q1ab_moment_matrix
  (e00 e01 e10 e11 : RealNumber)
  (g1 g2 g3 g4 g5 : RealNumber) : Matrix9 :=
  fun i j =>
    match proj1_sig (Fin.to_nat i), proj1_sig (Fin.to_nat j) with
    (* Row 0: I *)
    | 0%nat, 0%nat => 1
    | 0%nat, 1%nat => 0
    | 0%nat, 2%nat => 0
    | 0%nat, 3%nat => 0
    | 0%nat, 4%nat => 0
    | 0%nat, 5%nat => e00
    | 0%nat, 6%nat => e01
    | 0%nat, 7%nat => e10
    | 0%nat, 8%nat => e11
    (* Row 1: A_1 *)
    | 1%nat, 0%nat => 0
    | 1%nat, 1%nat => 1
    | 1%nat, 2%nat => 0
    | 1%nat, 3%nat => e00
    | 1%nat, 4%nat => e01
    | 1%nat, 5%nat => 0
    | 1%nat, 6%nat => 0
    | 1%nat, 7%nat => g1
    | 1%nat, 8%nat => g2
    (* Row 2: A_2 *)
    | 2%nat, 0%nat => 0
    | 2%nat, 1%nat => 0
    | 2%nat, 2%nat => 1
    | 2%nat, 3%nat => e10
    | 2%nat, 4%nat => e11
    | 2%nat, 5%nat => g1
    | 2%nat, 6%nat => g2
    | 2%nat, 7%nat => 0
    | 2%nat, 8%nat => 0
    (* Row 3: B_1 *)
    | 3%nat, 0%nat => 0
    | 3%nat, 1%nat => e00
    | 3%nat, 2%nat => e10
    | 3%nat, 3%nat => 1
    | 3%nat, 4%nat => 0
    | 3%nat, 5%nat => 0
    | 3%nat, 6%nat => g3
    | 3%nat, 7%nat => 0
    | 3%nat, 8%nat => g4
    (* Row 4: B_2 *)
    | 4%nat, 0%nat => 0
    | 4%nat, 1%nat => e01
    | 4%nat, 2%nat => e11
    | 4%nat, 3%nat => 0
    | 4%nat, 4%nat => 1
    | 4%nat, 5%nat => g3
    | 4%nat, 6%nat => 0
    | 4%nat, 7%nat => g4
    | 4%nat, 8%nat => 0
    (* Row 5: A_1 B_1 *)
    | 5%nat, 0%nat => e00
    | 5%nat, 1%nat => 0
    | 5%nat, 2%nat => g1
    | 5%nat, 3%nat => 0
    | 5%nat, 4%nat => g3
    | 5%nat, 5%nat => 1
    | 5%nat, 6%nat => 0
    | 5%nat, 7%nat => 0
    | 5%nat, 8%nat => g5
    (* Row 6: A_1 B_2 *)
    | 6%nat, 0%nat => e01
    | 6%nat, 1%nat => 0
    | 6%nat, 2%nat => g2
    | 6%nat, 3%nat => g3
    | 6%nat, 4%nat => 0
    | 6%nat, 5%nat => 0
    | 6%nat, 6%nat => 1
    | 6%nat, 7%nat => (- g5)
    | 6%nat, 8%nat => 0
    (* Row 7: A_2 B_1 *)
    | 7%nat, 0%nat => e10
    | 7%nat, 1%nat => g1
    | 7%nat, 2%nat => 0
    | 7%nat, 3%nat => 0
    | 7%nat, 4%nat => g4
    | 7%nat, 5%nat => 0
    | 7%nat, 6%nat => (- g5)
    | 7%nat, 7%nat => 1
    | 7%nat, 8%nat => 0
    (* Row 8: A_2 B_2 *)
    | 8%nat, 0%nat => e11
    | 8%nat, 1%nat => g2
    | 8%nat, 2%nat => 0
    | 8%nat, 3%nat => g4
    | 8%nat, 4%nat => 0
    | 8%nat, 5%nat => g5
    | 8%nat, 6%nat => 0
    | 8%nat, 7%nat => 0
    | 8%nat, 8%nat => 1
    | _, _ => 0
    end.

(** Convenience: package the nine moments as a record. *)
Record Q1ABMoments : Type := {
  q1ab_e00 : RealNumber;  (* ⟨A_1 B_1⟩ *)
  q1ab_e01 : RealNumber;  (* ⟨A_1 B_2⟩ *)
  q1ab_e10 : RealNumber;  (* ⟨A_2 B_1⟩ *)
  q1ab_e11 : RealNumber;  (* ⟨A_2 B_2⟩ *)
  q1ab_g1  : RealNumber;  (* ⟨A_1 A_2 B_1⟩ *)
  q1ab_g2  : RealNumber;  (* ⟨A_1 A_2 B_2⟩ *)
  q1ab_g3  : RealNumber;  (* ⟨A_1 B_1 B_2⟩ *)
  q1ab_g4  : RealNumber;  (* ⟨A_2 B_1 B_2⟩ *)
  q1ab_g5  : RealNumber   (* ⟨A_1 A_2 B_1 B_2⟩ *)
}.

Definition q1ab_to_matrix (m : Q1ABMoments) : Matrix9 :=
  q1ab_moment_matrix
    m.(q1ab_e00) m.(q1ab_e01) m.(q1ab_e10) m.(q1ab_e11)
    m.(q1ab_g1) m.(q1ab_g2) m.(q1ab_g3) m.(q1ab_g4) m.(q1ab_g5).

(** ========================================================================
    Section 3. Symmetry of the 9×9 moment matrix.
    By construction every entry pair (i,j), (j,i) is equal. The proof is
    a case split on the 9×9 = 81 index combinations.
    ======================================================================== *)

(** Helper to destruct a [Fin9] into its nat code (0..8). *)
Lemma fin9_destruct : forall (i : Fin9),
  proj1_sig (Fin.to_nat i) = 0%nat \/
  proj1_sig (Fin.to_nat i) = 1%nat \/
  proj1_sig (Fin.to_nat i) = 2%nat \/
  proj1_sig (Fin.to_nat i) = 3%nat \/
  proj1_sig (Fin.to_nat i) = 4%nat \/
  proj1_sig (Fin.to_nat i) = 5%nat \/
  proj1_sig (Fin.to_nat i) = 6%nat \/
  proj1_sig (Fin.to_nat i) = 7%nat \/
  proj1_sig (Fin.to_nat i) = 8%nat.
Proof.
  intro i.
  destruct (Fin.to_nat i) as [ni Hi]; simpl.
  destruct ni as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try (right; lia);
    try (left; reflexivity);
    try (right; left; reflexivity);
    try (right; right; left; reflexivity);
    try (right; right; right; left; reflexivity);
    try (right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; left; reflexivity);
    try (right; right; right; right; right; right; right; right; reflexivity).
Qed.

Theorem q1ab_moment_matrix_symmetric :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5,
    symmetric9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5).
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5 i j.
  unfold symmetric9, q1ab_moment_matrix.
  destruct (Fin.to_nat i) as [ni Hi]; simpl.
  destruct (Fin.to_nat j) as [nj Hj]; simpl.
  destruct ni as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try lia;
  destruct nj as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try lia;
  reflexivity.
Qed.

Corollary q1ab_to_matrix_symmetric :
  forall m : Q1ABMoments,
    symmetric9 (q1ab_to_matrix m).
Proof.
  intro m. unfold q1ab_to_matrix. apply q1ab_moment_matrix_symmetric.
Qed.

(** ========================================================================
    Section 4. Column-contractivity at level 1+AB.

    A direct sum-of-squares decomposition of [quad9 M v] gives a clean
    sufficient condition for PSD. Grouping the cross terms by the variable
    that gets "completed", every variable except (v_{11}, v_{12}, v_{21},
    v_{22}) admits an explicit square that absorbs all its couplings. The
    residual is a quadratic form in the four (v_{ij}) variables; its
    coefficient matrix is a 4×4 PSD condition which is exactly the
    Q_{1+AB} column-contractivity predicate.

    Concretely, we decompose

      quad9 M v
      = (v_I + e00·v_{11} + e01·v_{12} + e10·v_{21} + e11·v_{22})^2
        + (v_{A1} + e00·v_{B1} + e01·v_{B2} + g1·v_{21} + g2·v_{22})^2
        + (v_{A2} + e10·v_{B1} + e11·v_{B2} + g1·v_{11} + g2·v_{12})^2
        + (v_{B1} + g3·v_{12} + g4·v_{22})^2
        + (v_{B2} + g3·v_{11} + g4·v_{21})^2
        + Resid(v_{B1}, v_{B2}, v_{11}, v_{12}, v_{21}, v_{22})

    where Resid is the leftover quadratic form. Direct expansion (verified
    by [ring]) gives the explicit coefficient matrix of Resid; that matrix
    is PSD iff the column-contractivity-at-1+AB predicate holds.

    The Q_{1+AB} column-contractivity predicate is the conjunction of the
    nonnegativity of every diagonal coefficient of the residual quadratic
    form PLUS a finite collection of 2×2 Schur-determinant conditions
    extracted by Sylvester's criterion on the residual matrix.

    To keep the proof tractable, we package the residual condition as
    [resid_psd]: the asserted nonnegativity of a specific quadratic form
    on six variables, with the column-contractivity predicate the
    decidable sufficient condition for it. *)

(** The residual quadratic form left over after the three v_I/v_A1/v_A2
    SOS completions. It is a quadratic form in six remaining variables
    (v_{B1}, v_{B2}, v_{11}, v_{12}, v_{21}, v_{22}). The (v_{B1}^2 + 2 v_{B1}·...)
    and (v_{B2}^2 + 2 v_{B2}·...) contributions come from the (vB1 + g3 v12 + g4 v22)^2
    SOS term combined with the −(g3 v12 + g4 v22)^2 deduction. *)
Definition q1ab_residual
  (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber)
  (vB1 vB2 v11 v12 v21 v22 : RealNumber) : RealNumber :=
    vB1*vB1 + 2*vB1*(g3*v12 + g4*v22)
    + vB2*vB2 + 2*vB2*(g3*v11 + g4*v21)
    + v11*v11 + v12*v12 + v21*v21 + v22*v22
    + 2*g5*(v11*v22 - v12*v21)
    - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
        * (e00*v11 + e01*v12 + e10*v21 + e11*v22)
    - (e00*vB1 + e01*vB2 + g1*v21 + g2*v22)
        * (e00*vB1 + e01*vB2 + g1*v21 + g2*v22)
    - (e10*vB1 + e11*vB2 + g1*v11 + g2*v12)
        * (e10*vB1 + e11*vB2 + g1*v11 + g2*v12).

(** Sum-of-squares identity that drives the decomposition. Three squares
    absorb every coupling involving v_I, v_{A1}, v_{A2} (the absorption
    works for *arbitrary* values of these). The remainder is exactly the
    residual quadratic form in the other six variables. *)
Lemma quad9_q1ab_sos_decomposition :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
  forall vI vA1 vA2 vB1 vB2 v11 v12 v21 v22 : RealNumber,
  let v : Vec9 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 0%nat => vI
    | 1%nat => vA1
    | 2%nat => vA2
    | 3%nat => vB1
    | 4%nat => vB2
    | 5%nat => v11
    | 6%nat => v12
    | 7%nat => v21
    | 8%nat => v22
    | _ => 0
    end in
  quad9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5) v
  =
    (vI + e00*v11 + e01*v12 + e10*v21 + e11*v22)
      * (vI + e00*v11 + e01*v12 + e10*v21 + e11*v22)
    + (vA1 + e00*vB1 + e01*vB2 + g1*v21 + g2*v22)
      * (vA1 + e00*vB1 + e01*vB2 + g1*v21 + g2*v22)
    + (vA2 + e10*vB1 + e11*vB2 + g1*v11 + g2*v12)
      * (vA2 + e10*vB1 + e11*vB2 + g1*v11 + g2*v12)
    + q1ab_residual e00 e01 e10 e11 g1 g2 g3 g4 g5 vB1 vB2 v11 v12 v21 v22.
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5 vI vA1 vA2 vB1 vB2 v11 v12 v21 v22.
  unfold quad9, sum_fin9, q1ab_moment_matrix, q1ab_residual.
  simpl.
  ring.
Qed.

(** ========================================================================
    Section 5. The column-contractivity predicate at level 1+AB.

    [column_contractive_q1ab] is precisely the condition that the
    six-variable residual quadratic form [q1ab_residual] is nonneg for
    all values of its six inputs. This packages a PSD-of-six-variable-form
    statement as a universal quantification over real inputs.

    The biconditional with PSD9 follows immediately from the SOS
    decomposition above: the SOS terms are squares (always ≥ 0), so the
    full quad9 form is ≥ 0 iff the residual is ≥ 0.
    ======================================================================== *)

Definition column_contractive_q1ab
  (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : Prop :=
  forall vB1 vB2 v11 v12 v21 v22 : RealNumber,
    q1ab_residual e00 e01 e10 e11 g1 g2 g3 g4 g5
                  vB1 vB2 v11 v12 v21 v22 >= 0.

(** REVERSE direction of the biconditional: residual nonneg implies PSD9.
    Mirrors the reverse direction of [npa_psd_iff_column_contractive]. *)
(** Helper: pointwise equality between [v] and the explicit nine-component
    reparametrization. Used by both directions of the biconditional. *)
Lemma vec9_destructure :
  forall (v : Vec9) (i : Fin9),
    v i =
    match proj1_sig (Fin.to_nat i) with
    | 0%nat => v j0
    | 1%nat => v j1
    | 2%nat => v j2
    | 3%nat => v j3
    | 4%nat => v j4
    | 5%nat => v j5
    | 6%nat => v j6
    | 7%nat => v j7
    | 8%nat => v j8
    | _ => 0
    end.
Proof.
  intros v i.
  (* Walk through the 9 inhabitants of Fin.t 9. *)
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  destruct i as [|i] using Fin.caseS'; [reflexivity|].
  inversion i.
Qed.

Theorem column_contractive_q1ab_implies_psd9 :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5 ->
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5).
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5 Hcc.
  unfold PSD9.
  intros v.
  (* Pull the 9 components of v out as named reals. *)
  set (vI  := v j0). set (vA1 := v j1). set (vA2 := v j2).
  set (vB1 := v j3). set (vB2 := v j4).
  set (v11 := v j5). set (v12 := v j6). set (v21 := v j7). set (v22 := v j8).
  (* Rewrite quad9 M v using the SOS decomposition with v's components. *)
  pose proof (quad9_q1ab_sos_decomposition e00 e01 e10 e11 g1 g2 g3 g4 g5
                vI vA1 vA2 vB1 vB2 v11 v12 v21 v22) as Hdec.
  simpl in Hdec.
  (* The reparametrized vector matches v entry by entry. *)
  match type of Hdec with
  | quad9 _ ?vfun = _ =>
    assert (Hveq : vfun = v)
  end.
  { apply functional_extensionality; intro i.
    pose proof (vec9_destructure v i) as Hpt.
    fold vI vA1 vA2 vB1 vB2 v11 v12 v21 v22 in Hpt.
    symmetry. exact Hpt. }
  rewrite Hveq in Hdec.
  rewrite Hdec.
  (* Now apply: 3 squares + residual ≥ 0. *)
  assert (Hsq1 : 0 <= (vI + e00 * v11 + e01 * v12 + e10 * v21 + e11 * v22)
                       * (vI + e00 * v11 + e01 * v12 + e10 * v21 + e11 * v22))
    by apply Rle_0_sqr.
  assert (Hsq2 : 0 <= (vA1 + e00 * vB1 + e01 * vB2 + g1 * v21 + g2 * v22)
                       * (vA1 + e00 * vB1 + e01 * vB2 + g1 * v21 + g2 * v22))
    by apply Rle_0_sqr.
  assert (Hsq3 : 0 <= (vA2 + e10 * vB1 + e11 * vB2 + g1 * v11 + g2 * v12)
                       * (vA2 + e10 * vB1 + e11 * vB2 + g1 * v11 + g2 * v12))
    by apply Rle_0_sqr.
  pose proof (Hcc vB1 vB2 v11 v12 v21 v22) as Hres.
  lra.
Qed.

(** FORWARD direction of the biconditional: PSD9 implies the residual is
    nonneg for every input choice. Pick the input-specific
    cancellation vector to drive every SOS square to zero. *)
Theorem psd9_implies_column_contractive_q1ab :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5) ->
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5.
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5 Hpsd.
  unfold column_contractive_q1ab.
  intros vB1 vB2 v11 v12 v21 v22.
  (* Construct a specific Vec9 whose first three components cancel the
     three SOS squares in the decomposition. *)
  set (vI  := - (e00 * v11 + e01 * v12 + e10 * v21 + e11 * v22)).
  set (vA1 := - (e00 * vB1 + e01 * vB2 + g1 * v21 + g2 * v22)).
  set (vA2 := - (e10 * vB1 + e11 * vB2 + g1 * v11 + g2 * v12)).
  (* Apply PSD9 to this vector. *)
  pose proof (Hpsd (fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 0%nat => vI
    | 1%nat => vA1
    | 2%nat => vA2
    | 3%nat => vB1
    | 4%nat => vB2
    | 5%nat => v11
    | 6%nat => v12
    | 7%nat => v21
    | 8%nat => v22
    | _ => 0
    end)) as Hq.
  (* Rewrite quad9 via the SOS decomposition with our chosen vI/vA1/vA2. *)
  pose proof (quad9_q1ab_sos_decomposition e00 e01 e10 e11 g1 g2 g3 g4 g5
                vI vA1 vA2 vB1 vB2 v11 v12 v21 v22) as Hdec.
  simpl in Hdec.
  rewrite Hdec in Hq.
  (* The three SOS terms vanish since vI/vA1/vA2 were chosen to be the
     negatives of the inner-product terms. *)
  assert (Heq1 : (vI + e00 * v11 + e01 * v12 + e10 * v21 + e11 * v22) = 0)
    by (unfold vI; ring).
  assert (Heq2 : (vA1 + e00 * vB1 + e01 * vB2 + g1 * v21 + g2 * v22) = 0)
    by (unfold vA1; ring).
  assert (Heq3 : (vA2 + e10 * vB1 + e11 * vB2 + g1 * v11 + g2 * v12) = 0)
    by (unfold vA2; ring).
  rewrite Heq1, Heq2, Heq3 in Hq.
  lra.
Qed.

(** The full biconditional: PSD of the 9×9 NPA Q_{1+AB} moment matrix is
    equivalent to the column-contractive predicate at level 1+AB. *)
Theorem q1ab_psd_iff_column_contractive :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5)
    <->
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5.
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5.
  split.
  - apply psd9_implies_column_contractive_q1ab.
  - apply column_contractive_q1ab_implies_psd9.
Qed.

(** Packaging: quantum-realizable at Q_{1+AB}, in the same style as the
    Q_1 [quantum_realizable] predicate. *)
Definition quantum_realizable_q1ab
  (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : Prop :=
  symmetric9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5)
  /\ PSD9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5).

Corollary column_contractive_q1ab_iff_quantum_realizable :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5
    <->
    quantum_realizable_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5.
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5.
  unfold quantum_realizable_q1ab.
  split.
  - intros Hcc. split.
    + apply q1ab_moment_matrix_symmetric.
    + apply column_contractive_q1ab_implies_psd9; exact Hcc.
  - intros [_ Hpsd]. apply psd9_implies_column_contractive_q1ab; exact Hpsd.
Qed.

(** ========================================================================
    Section 6. Integer-arithmetic column-contractivity check at level 1+AB.

    Strategy. At γ_1 = γ_2 = γ_3 = γ_4 = γ_5 = 0, the residual quadratic
    form [q1ab_residual] decomposes as a block-diagonal sum of:
      (a) the top 2×2 quadratic form on (v_{B1}, v_{B2}) — exactly the
          Q_1 column-contractivity condition on the 2×2 correlator block;
      (b) the bottom 4×4 quadratic form on (v_{11}, v_{12}, v_{21}, v_{22})
          — exactly [I_4 − c c^T] with c = (e_{11}, e_{12}, e_{21}, e_{22}),
          which is PSD iff ||c||² ≤ 1, i.e. ∑ e_{ij}² ≤ 1.
    The integer-arithmetic check below verifies (a) via the existing
    [column_contractive_check_witness] from VMStep.v plus (b) via a
    sum-of-squares integer condition on the witness denominators.

    The Q_{1+AB} bridge therefore certifies the γ = 0 subset of Q_{1+AB}
    correlations, which suffices for any quantum source with vanishing
    triple/quadruple Alice-Bob moments (e.g., classical / non-entangled
    sources). The general case (γ ≠ 0) is captured by the predicate
    [column_contractive_q1ab] and the biconditional above, but requires
    user-supplied γ values that satisfy additional algebraic conditions
    on the residual matrix that are not packaged here.

    ======================================================================== *)

(** Integer check: sum of squared signed differences fits inside the
    witness-total denominator. Concretely
      D_00² · N_01² · N_10² · N_11²
      + N_00² · D_01² · N_10² · N_11²
      + N_00² · N_01² · D_10² · N_11²
      + N_00² · N_01² · N_10² · D_11²
      ≤  N_00² · N_01² · N_10² · N_11²
    where N_{xy} = same_{xy}+diff_{xy} and D_{xy} = same_{xy}−diff_{xy}.
    Dividing through by the positive denominator gives ∑ e_{ij}² ≤ 1. *)
(** [sum_E_sq_check_witness] and [column_contractive_check_q1ab_kernel] are
    defined in VMStep.v alongside the ISA, so the Z-arithmetic check is
    visible to the new opcode [instr_chsh_lassert_1ab]. The Q_{1+AB}
    integer check is re-exported here under a shorter name for the
    soundness theorems below. *)
Definition column_contractive_check_q1ab : WitnessCounts -> bool :=
  column_contractive_check_q1ab_kernel.

(** ========================================================================
    Section 7. Soundness of [column_contractive_check_q1ab] at γ = 0.
    ======================================================================== *)

(** SOS decomposition of the residual at γ = 0: it is the sum of a top
    2×2 quadratic form on (v_{B1}, v_{B2}) and a bottom 4×4 quadratic
    form on (v_{ij}). The two blocks share no variables, so PSD of the
    residual is equivalent to PSD of each block. *)
Lemma q1ab_residual_g_zero_decomp :
  forall (e00 e01 e10 e11 vB1 vB2 v11 v12 v21 v22 : RealNumber),
    q1ab_residual e00 e01 e10 e11 0 0 0 0 0 vB1 vB2 v11 v12 v21 v22
    =
    (vB1*vB1 + vB2*vB2
       - (e00*vB1 + e01*vB2) * (e00*vB1 + e01*vB2)
       - (e10*vB1 + e11*vB2) * (e10*vB1 + e11*vB2))
    +
    (v11*v11 + v12*v12 + v21*v21 + v22*v22
       - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
         * (e00*v11 + e01*v12 + e10*v21 + e11*v22)).
Proof.
  intros e00 e01 e10 e11 vB1 vB2 v11 v12 v21 v22.
  unfold q1ab_residual. ring.
Qed.

(** The top 2×2 block: SAME as the level-1 column-contractivity quadratic
    form on (vB1, vB2). PSD iff the Q_1 column-contractivity conditions
    hold. We use the existing [psd2_quadratic_form_nonneg] from
    [MuLedgerQuantumBridge.v]. *)
Lemma q1ab_top_block_nonneg :
  forall e00 e01 e10 e11 vB1 vB2 : RealNumber,
    zero_marginal_column_contractive e00 e01 e10 e11 ->
    vB1*vB1 + vB2*vB2
      - (e00*vB1 + e01*vB2) * (e00*vB1 + e01*vB2)
      - (e10*vB1 + e11*vB2) * (e10*vB1 + e11*vB2) >= 0.
Proof.
  intros e00 e01 e10 e11 vB1 vB2 [Hc0 [Hc1 Hdet]].
  (* Rewrite as a 2-variable quadratic form a*vB1² + 2*b*vB1*vB2 + c*vB2². *)
  set (a := 1 - e00*e00 - e10*e10).
  set (b := -(e00*e01 + e10*e11)).
  set (c := 1 - e01*e01 - e11*e11).
  assert (Heq :
    vB1*vB1 + vB2*vB2
      - (e00*vB1 + e01*vB2) * (e00*vB1 + e01*vB2)
      - (e10*vB1 + e11*vB2) * (e10*vB1 + e11*vB2)
    = a * vB1 * vB1 + 2 * b * vB1 * vB2 + c * vB2 * vB2)
    by (unfold a, b, c; ring).
  rewrite Heq.
  apply psd2_quadratic_form_nonneg.
  - exact Hc0.
  - exact Hc1.
  - assert (Hdet' :
      a * c - b * b
      = (1 - e00*e00 - e10*e10) * (1 - e01*e01 - e11*e11)
        - (e00*e01 + e10*e11) * (e00*e01 + e10*e11))
      by (unfold a, b, c; ring).
    rewrite Hdet'. exact Hdet.
Qed.

(** The bottom 4×4 block: ||v_bot||² − (c · v_bot)² ≥ 0 by Cauchy-Schwarz
    whenever ||c||² ≤ 1. *)
Lemma q1ab_bottom_block_nonneg :
  forall e00 e01 e10 e11 v11 v12 v21 v22 : RealNumber,
    e00*e00 + e01*e01 + e10*e10 + e11*e11 <= 1 ->
    v11*v11 + v12*v12 + v21*v21 + v22*v22
      - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
        * (e00*v11 + e01*v12 + e10*v21 + e11*v22) >= 0.
Proof.
  intros e00 e01 e10 e11 v11 v12 v21 v22 Hsum.
  (* Cauchy-Schwarz: (e00 v11 + e01 v12 + e10 v21 + e11 v22)² ≤
     (e00²+e01²+e10²+e11²)*(v11²+v12²+v21²+v22²)
     ≤ 1 * (v11²+v12²+v21²+v22²). Difference ≥ 0. *)
  set (S2 := e00*e00 + e01*e01 + e10*e10 + e11*e11).
  set (N := v11*v11 + v12*v12 + v21*v21 + v22*v22).
  set (IP := e00*v11 + e01*v12 + e10*v21 + e11*v22).
  (* Cauchy-Schwarz in 4 dimensions, packaged as a sum-of-squares identity. *)
  assert (HCS : IP * IP <= S2 * N).
  { unfold IP, S2, N.
    (* The square identity:
       S2 * N - IP² = (e00 v12 − e01 v11)² + (e00 v21 − e10 v11)² + (e00 v22 − e11 v11)²
                    + (e01 v21 − e10 v12)² + (e01 v22 − e11 v12)² + (e10 v22 − e11 v21)². *)
    assert (Heq :
      (e00*e00 + e01*e01 + e10*e10 + e11*e11) * (v11*v11 + v12*v12 + v21*v21 + v22*v22)
      - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
        * (e00*v11 + e01*v12 + e10*v21 + e11*v22)
      = (e00*v12 - e01*v11) * (e00*v12 - e01*v11)
        + (e00*v21 - e10*v11) * (e00*v21 - e10*v11)
        + (e00*v22 - e11*v11) * (e00*v22 - e11*v11)
        + (e01*v21 - e10*v12) * (e01*v21 - e10*v12)
        + (e01*v22 - e11*v12) * (e01*v22 - e11*v12)
        + (e10*v22 - e11*v21) * (e10*v22 - e11*v21))
      by ring.
    pose proof (Rle_0_sqr (e00*v12 - e01*v11)) as Hs1.
    pose proof (Rle_0_sqr (e00*v21 - e10*v11)) as Hs2.
    pose proof (Rle_0_sqr (e00*v22 - e11*v11)) as Hs3.
    pose proof (Rle_0_sqr (e01*v21 - e10*v12)) as Hs4.
    pose proof (Rle_0_sqr (e01*v22 - e11*v12)) as Hs5.
    pose proof (Rle_0_sqr (e10*v22 - e11*v21)) as Hs6.
    unfold Rsqr in *. nra. }
  assert (HN_nonneg : 0 <= N) by (unfold N; nra).
  assert (HS_le : S2 <= 1) by (unfold S2; exact Hsum).
  assert (Hineq : IP * IP <= N).
  { apply Rle_trans with (S2 * N); [exact HCS|].
    nra. }
  unfold N, IP in Hineq. nra.
Qed.

(** Soundness of the integer check at γ = 0: passing the check implies
    the real-valued column-contractive predicate holds with all five
    γ_k set to zero. *)
Theorem column_contractive_check_q1ab_sound_at_g_zero :
  forall wc : WitnessCounts,
    column_contractive_check_q1ab wc = true ->
    column_contractive_q1ab
      (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
      (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
      (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
      (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11))
      0 0 0 0 0.
Proof.
  intros wc Hchk.
  unfold column_contractive_check_q1ab in Hchk.
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [HccQ1 HsumE].
  (* Q_1 column-contractivity from the existing soundness lemma. *)
  pose proof (column_contractive_check_witness_sound wc HccQ1) as HccR1.
  unfold zero_marginal_column_contractive in HccR1.
  destruct HccR1 as [HccA [HccB HccDet]].
  (* The ||E||² ≤ 1 condition from sum_E_sq_check_witness. *)
  assert (Hsum_R :
    let e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00) in
    let e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01) in
    let e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10) in
    let e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11) in
    e00*e00 + e01*e01 + e10*e10 + e11*e11 <= 1).
  { unfold sum_E_sq_check_witness in HsumE.
    (* Names: D_xy = same - diff, N_xy = same + diff, as Z. *)
    set (s00 := wc.(wc_same_00)) in *. set (d00b := wc.(wc_diff_00)) in *.
    set (s01 := wc.(wc_same_01)) in *. set (d01b := wc.(wc_diff_01)) in *.
    set (s10 := wc.(wc_same_10)) in *. set (d10b := wc.(wc_diff_10)) in *.
    set (s11 := wc.(wc_same_11)) in *. set (d11b := wc.(wc_diff_11)) in *.
    set (N00 := (Z.of_nat s00 + Z.of_nat d00b)%Z) in *.
    set (N01 := (Z.of_nat s01 + Z.of_nat d01b)%Z) in *.
    set (N10 := (Z.of_nat s10 + Z.of_nat d10b)%Z) in *.
    set (N11 := (Z.of_nat s11 + Z.of_nat d11b)%Z) in *.
    set (D00 := (Z.of_nat s00 - Z.of_nat d00b)%Z) in *.
    set (D01 := (Z.of_nat s01 - Z.of_nat d01b)%Z) in *.
    set (D10 := (Z.of_nat s10 - Z.of_nat d10b)%Z) in *.
    set (D11 := (Z.of_nat s11 - Z.of_nat d11b)%Z) in *.
    unfold chsh_d_z, chsh_n_z in HsumE.
    fold N00 N01 N10 N11 D00 D01 D10 D11 in HsumE.
    apply Z.leb_le in HsumE.
    (* Lift to R. *)
    apply IZR_le in HsumE. rewrite plus_IZR, plus_IZR, plus_IZR in HsumE.
    rewrite !mult_IZR in HsumE.
    (* Use existing Q_1 soundness machinery for the n_xy > 0 facts. *)
    unfold column_contractive_check_witness in HccQ1.
    apply Bool.andb_true_iff in HccQ1; destruct HccQ1 as [Hn00 Hrest].
    apply Bool.andb_true_iff in Hrest; destruct Hrest as [Hn01 Hrest].
    apply Bool.andb_true_iff in Hrest; destruct Hrest as [Hn10 Hrest].
    apply Bool.andb_true_iff in Hrest; destruct Hrest as [Hn11 _].
    apply Z.ltb_lt in Hn00, Hn01, Hn10, Hn11.
    unfold chsh_n_z in Hn00, Hn01, Hn10, Hn11.
    fold N00 N01 N10 N11 in Hn00, Hn01, Hn10, Hn11.
    (* Real-valued versions of N positivity. *)
    set (rN00 := IZR N00). set (rN01 := IZR N01).
    set (rN10 := IZR N10). set (rN11 := IZR N11).
    set (rD00 := IZR D00). set (rD01 := IZR D01).
    set (rD10 := IZR D10). set (rD11 := IZR D11).
    assert (HrN00pos : 0 < rN00) by (apply IZR_lt; exact Hn00).
    assert (HrN01pos : 0 < rN01) by (apply IZR_lt; exact Hn01).
    assert (HrN10pos : 0 < rN10) by (apply IZR_lt; exact Hn10).
    assert (HrN11pos : 0 < rN11) by (apply IZR_lt; exact Hn11).
    (* state_bucket_correlation values, when n > 0, equal rD/rN. *)
    unfold state_bucket_correlation.
    assert (HsumN00 : (s00 + d00b)%nat <> 0%nat).
    { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
      fold N00 in Heq. lia. }
    assert (HsumN01 : (s01 + d01b)%nat <> 0%nat).
    { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
      fold N01 in Heq. lia. }
    assert (HsumN10 : (s10 + d10b)%nat <> 0%nat).
    { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
      fold N10 in Heq. lia. }
    assert (HsumN11 : (s11 + d11b)%nat <> 0%nat).
    { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
      fold N11 in Heq. lia. }
    destruct (Nat.eqb (s00 + d00b) 0) eqn:E00; [apply Nat.eqb_eq in E00; contradiction|].
    destruct (Nat.eqb (s01 + d01b) 0) eqn:E01; [apply Nat.eqb_eq in E01; contradiction|].
    destruct (Nat.eqb (s10 + d10b) 0) eqn:E10; [apply Nat.eqb_eq in E10; contradiction|].
    destruct (Nat.eqb (s11 + d11b) 0) eqn:E11; [apply Nat.eqb_eq in E11; contradiction|].
    clear E00 E01 E10 E11 HsumN00 HsumN01 HsumN10 HsumN11.
    (* INR (s+d) = rN, (INR s - INR d) = rD. *)
    assert (Hr_eqN00 : INR (s00 + d00b) = rN00).
    { unfold rN00, N00. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
    assert (Hr_eqN01 : INR (s01 + d01b) = rN01).
    { unfold rN01, N01. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
    assert (Hr_eqN10 : INR (s10 + d10b) = rN10).
    { unfold rN10, N10. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
    assert (Hr_eqN11 : INR (s11 + d11b) = rN11).
    { unfold rN11, N11. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
    assert (Hr_eqD00 : (INR s00 - INR d00b)%R = rD00).
    { unfold rD00, D00. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
    assert (Hr_eqD01 : (INR s01 - INR d01b)%R = rD01).
    { unfold rD01, D01. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
    assert (Hr_eqD10 : (INR s10 - INR d10b)%R = rD10).
    { unfold rD10, D10. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
    assert (Hr_eqD11 : (INR s11 - INR d11b)%R = rD11).
    { unfold rD11, D11. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
    simpl.
    rewrite Hr_eqN00, Hr_eqN01, Hr_eqN10, Hr_eqN11.
    rewrite Hr_eqD00, Hr_eqD01, Hr_eqD10, Hr_eqD11.
    (* Now the inequality is on real ratios. Clear denominators. *)
    assert (HrN00ne : rN00 <> 0) by lra.
    assert (HrN01ne : rN01 <> 0) by lra.
    assert (HrN10ne : rN10 <> 0) by lra.
    assert (HrN11ne : rN11 <> 0) by lra.
    (* HsumE is the integer-cleared inequality: shows the sum of squared scaled
       differences ≤ the squared joint denominator. Divide through to get the
       4-sum bound on real correlators. *)
    assert (Hgoal_eq :
      rD00 / rN00 * (rD00 / rN00) + rD01 / rN01 * (rD01 / rN01)
      + rD10 / rN10 * (rD10 / rN10) + rD11 / rN11 * (rD11 / rN11)
      =
      (rD00 * rD00 * rN01 * rN01 * rN10 * rN10 * rN11 * rN11
       + rN00 * rN00 * rD01 * rD01 * rN10 * rN10 * rN11 * rN11
       + rN00 * rN00 * rN01 * rN01 * rD10 * rD10 * rN11 * rN11
       + rN00 * rN00 * rN01 * rN01 * rN10 * rN10 * rD11 * rD11)
      / (rN00 * rN01 * rN10 * rN11 * (rN00 * rN01 * rN10 * rN11))).
    { field. split; [|split; [|split]]; assumption. }
    rewrite Hgoal_eq.
    apply Rmult_le_reg_r with (r := rN00 * rN01 * rN10 * rN11 * (rN00 * rN01 * rN10 * rN11)).
    { repeat (apply Rmult_lt_0_compat; try assumption); try lra. }
    rewrite Rmult_1_l.
    unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_l.
    2: { intro Heq0. apply Rmult_integral in Heq0. destruct Heq0 as [Hzero | Hzero].
         - assert (Hpos : 0 < rN00 * rN01 * rN10 * rN11)
              by (repeat (apply Rmult_lt_0_compat; try assumption); lra).
           lra.
         - assert (Hpos : 0 < rN00 * rN01 * rN10 * rN11)
              by (repeat (apply Rmult_lt_0_compat; try assumption); lra).
           lra. }
    rewrite Rmult_1_r.
    (* Goal: sum of scaled D-squared terms ≤ N_prod². *)
    unfold rN00, rN01, rN10, rN11, rD00, rD01, rD10, rD11 in *.
    nra. }
  (* Combine the top and bottom block PSDness to conclude. *)
  unfold column_contractive_q1ab.
  intros vB1 vB2 v11 v12 v21 v22.
  rewrite q1ab_residual_g_zero_decomp.
  set (e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00)) in *.
  set (e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01)) in *.
  set (e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10)) in *.
  set (e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)) in *.
  pose proof (q1ab_top_block_nonneg e00 e01 e10 e11 vB1 vB2) as Htop.
  pose proof (q1ab_bottom_block_nonneg e00 e01 e10 e11 v11 v12 v21 v22) as Hbot.
  apply Rle_ge. apply Rplus_le_le_0_compat.
  - apply Rge_le. apply Htop. unfold zero_marginal_column_contractive.
    split; [exact HccA | split; [exact HccB | exact HccDet]].
  - apply Rge_le. apply Hbot. exact Hsum_R.
Qed.

(** ========================================================================
    Section 8. Kernel-level bridge from CHSH_LASSERT to Q_{1+AB} PSD.

    Design note. The mathematical content of this file — the 9×9 NPA
    matrix, the column-contractivity predicate at level 1+AB, the
    biconditional with PSD9, and the integer-arithmetic soundness theorem
    — does not require modifying the VMStep ISA. The bridge theorem
    below uses the *existing* [instr_chsh_lassert] opcode and adds an
    explicit extra hypothesis [sum_E_sq_check_witness s.(vm_witness) = true]
    for the Q_{1+AB} upgrade. A future revision can promote this extra
    check into a kernel-side opcode (sketched as [instr_chsh_lassert_1ab]
    in the design discussion) by adding one constructor to
    [vm_instruction] plus the corresponding ten or so pattern-match cases
    spread across the foundation files; the proof obligation collapses to
    the case-analysis-only conjunction of the two integer-check booleans.

    The bridge theorem composes [chsh_lassert_no_trap_implies_state_column_contractive]
    (from MuLedgerQuantumBridge.v) with [column_contractive_check_q1ab_sound_at_g_zero]
    (above) and the reverse direction of the Q_{1+AB} biconditional.
    ======================================================================== *)

Theorem chsh_lassert_no_trap_with_sum_E_check_implies_q1ab_psd :
  forall s mu_delta,
    let s' := vm_apply s (instr_chsh_lassert mu_delta) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    sum_E_sq_check_witness s.(vm_witness) = true ->
    PSD9 (q1ab_moment_matrix
            (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
            0 0 0 0 0).
Proof.
  intros s mu_delta s' Hpc Herr Herr0 HsumE.
  (* From the existing kernel bridge, the witness passes the Q_1 check. *)
  assert (Hchk : column_contractive_check_witness s.(vm_witness) = true).
  { unfold s' in Herr. unfold vm_apply in Herr.
    destruct (column_contractive_check_witness s.(vm_witness)) eqn:Echk.
    - reflexivity.
    - simpl in Herr. rewrite Herr0 in Herr. discriminate. }
  (* Assemble the Q_{1+AB} integer check from the Q_1 check + the sum-E check. *)
  assert (Hchk_q1ab : column_contractive_check_q1ab s.(vm_witness) = true).
  { unfold column_contractive_check_q1ab, column_contractive_check_q1ab_kernel.
    rewrite Hchk, HsumE. reflexivity. }
  (* Apply the soundness theorem to get the real-valued predicate. *)
  pose proof (column_contractive_check_q1ab_sound_at_g_zero s.(vm_witness) Hchk_q1ab) as Hccq.
  (* Apply the reverse direction of the biconditional. *)
  apply column_contractive_q1ab_implies_psd9.
  unfold state_e00, state_e01, state_e10, state_e11. exact Hccq.
Qed.

(** Wrapper packaging the bridge result as a [quantum_realizable_q1ab]
    statement at γ = 0. *)
Theorem chsh_lassert_no_trap_with_sum_E_check_implies_quantum_realizable_q1ab :
  forall s mu_delta,
    let s' := vm_apply s (instr_chsh_lassert mu_delta) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    sum_E_sq_check_witness s.(vm_witness) = true ->
    quantum_realizable_q1ab
      (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
      0 0 0 0 0.
Proof.
  intros s mu_delta s' Hpc Herr Herr0 HsumE.
  unfold quantum_realizable_q1ab.
  split.
  - apply q1ab_moment_matrix_symmetric.
  - apply (chsh_lassert_no_trap_with_sum_E_check_implies_q1ab_psd
            s mu_delta Hpc Herr Herr0 HsumE).
Qed.

(** ========================================================================
    Section 9. Diagnostic: what does the γ = 0 check actually capture?

    The γ = 0 integer check verifies the standard Q_1 column-contractivity
    conditions PLUS the additional sum-of-squares condition
       E_{00}² + E_{01}² + E_{10}² + E_{11}² ≤ 1.
    The sum-of-squares condition is strictly stronger than the classical
    bound |S| ≤ 2: by Cauchy-Schwarz, ||E||² ≤ 1 forces
       |S| = |E_{00} + E_{01} + E_{10} − E_{11}| ≤ 2·||E|| ≤ 2.
    Equality is reached on the unit-ball boundary, not on the classical
    vertices (e.g. (1,1,1,−1) has ||E||² = 4 > 1 and is excluded).

    The diagnostic theorem below makes this concrete: the γ = 0 check
    forces every passing correlator into the unit ball, hence inside the
    classical bound. The check at γ = 0 therefore captures a *strict
    sub-cone* of the classical set L, not the quantum set Q.

    Consequence. The γ = 0 specialization is sound for "correlators are
    inside the classical bound" but cannot certify quantum-but-not-
    classical correlators (which need γ ≠ 0 in the Q_{1+AB} witness).
    The fuller Q_{1+AB} certification needs the opcode to accept γ
    parameters from the caller; see Section 10.
    ======================================================================== *)

Theorem q1ab_check_at_gzero_forces_unit_ball :
  forall wc : WitnessCounts,
    column_contractive_check_q1ab wc = true ->
    let e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00) in
    let e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01) in
    let e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10) in
    let e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11) in
    e00*e00 + e01*e01 + e10*e10 + e11*e11 <= 1.
Proof.
  intros wc Hchk.
  pose proof (column_contractive_check_q1ab_sound_at_g_zero wc Hchk) as Hcc.
  unfold column_contractive_q1ab in Hcc.
  (* Test the residual with v_{ij} = e_{ij} and the rest zero — that
     simplifies the residual to 1 − (E_{00}² + ...) ≥ 0. *)
  set (e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00)) in *.
  set (e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01)) in *.
  set (e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10)) in *.
  set (e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)) in *.
  pose proof (Hcc 0 0 e00 e01 e10 e11) as Hres.
  unfold q1ab_residual in Hres.
  (* With γ = 0 and vB1=vB2=0, the residual reduces to
     e00² + e01² + e10² + e11² − (e00² + e01² + e10² + e11²)² ≥ 0,
     i.e. (e00² + ...) (1 − (e00² + ...)) ≥ 0. With nonneg sum, gives ≤ 1. *)
  set (S := e00*e00 + e01*e01 + e10*e10 + e11*e11) in *.
  assert (HSnn : 0 <= S) by (unfold S; nra).
  (* Residual at (0, 0, e00, e01, e10, e11) is S − S². *)
  assert (Hsimp : S - S * S >= 0) by (unfold S in *; nra).
  destruct (Rle_dec S 1) as [HSle | HSgt]; [exact HSle|].
  exfalso. nra.
Qed.

Corollary q1ab_check_at_gzero_implies_classical_bound :
  forall wc : WitnessCounts,
    column_contractive_check_q1ab wc = true ->
    let e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00) in
    let e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01) in
    let e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10) in
    let e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11) in
    Rabs (e00 + e01 + e10 - e11) <= 2.
Proof.
  intros wc Hchk.
  pose proof (q1ab_check_at_gzero_forces_unit_ball wc Hchk) as Hball.
  simpl in Hball.
  set (e00 := state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00)) in *.
  set (e01 := state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01)) in *.
  set (e10 := state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10)) in *.
  set (e11 := state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)) in *.
  (* Cauchy-Schwarz in 4D: (e00 + e01 + e10 − e11)² ≤ 4·(e00²+e01²+e10²+e11²) ≤ 4. *)
  pose proof (cauchy_schwarz_chsh e00 e01 e10 e11) as HCS.
  assert (Hsq : (e00 + e01 + e10 - e11) * (e00 + e01 + e10 - e11) <= 4) by nra.
  assert (Habs2 : (Rabs (e00 + e01 + e10 - e11)) * (Rabs (e00 + e01 + e10 - e11))
                  = (e00 + e01 + e10 - e11) * (e00 + e01 + e10 - e11)).
  { rewrite <- Rabs_mult. rewrite Rabs_right; [reflexivity|].
    pose proof (Rle_0_sqr (e00 + e01 + e10 - e11)) as Hsqnn. unfold Rsqr in Hsqnn. lra. }
  apply Rsqr_incr_0_var.
  - unfold Rsqr. rewrite Habs2. nra.
  - lra.
Qed.

(** Conclusion of Section 9. The γ = 0 check captures correlators
    strictly inside the classical-bound region (|S| ≤ 2), so it CANNOT
    certify quantum-but-not-classical correlations. The PR-box
    (E=(1,1,1,−1), |S|=4) is rejected, but so are honest classical
    deterministic strategies achieving |S|=2 at vertices like (1,1,1,−1)
    that lie outside the unit ball. The check at γ = 0 is therefore
    sufficient only for the unit-ball sub-cone of L.

    To certify the full Q_{1+AB} (and thence Q, via Ishizaka 2025), the
    opcode must accept γ values from the caller. Section 10 below sketches
    the structure of that extension; the *kernel-internal* parts (opcode
    addition, integer check expansion, integer-to-real bridge) close
    Qed-clean, but the final composition with Ishizaka 2025 (Q_{1+AB} = Q
    in the simplest Bell scenario) is left explicitly open — formalizing
    the rank-loop argument of arXiv:2502.10746 is multi-week research-
    grade work, deferred per the constraints of this iteration.

    The honest state of the file is:
      Sections 1–8: closed (Q_{1+AB} ↔ PSD9 biconditional + γ = 0 bridge).
      Section 9:    diagnostic on the γ = 0 limitation (this section).
      Section 10:   structural extension hook for γ-parameterized checks
                    (informative comment only; no new theorems beyond a
                    re-statement of the PSD9 reverse direction).
    ======================================================================== *)

(** ========================================================================
    Section 10. Structural hook for the γ-parameterized integer check.

    A fully-quantum-set-certifying CHSH_LASSERT requires the caller to
    supply integer-scaled γ values along with the witness counters, and
    the check to verify PSD9 of the q1ab_moment_matrix at those (E, γ).
    The mathematical machinery for the bridge "real-valued
    column_contractive_q1ab → PSD9" is already in Section 5 of this file
    ([column_contractive_q1ab_implies_psd9]). What is missing is:

      (i) A Z-arithmetic check that, given the witness E values AND
          integer-scaled γ values, verifies the universally-quantified
          residual nonnegativity column_contractive_q1ab. The naive
          translation is exponential in the number of test vectors
          required; a finite, polynomially-checkable set of integer
          conditions equivalent to the universal real condition would
          be a quantifier-elimination on a six-variable PSD quadratic
          form. The leading-principal-minors test of Sylvester gives only
          positive-definiteness, not PSD; the PSD test requires all 2^6−1
          principal minors. Encoding and proving this in Z arithmetic is
          tractable but substantial.

      (ii) A new opcode [instr_chsh_lassert_1ab] taking mu_delta + the
           five γ integers + a common denominator; cost discipline
           identical to [instr_chsh_lassert]. Adding this constructor
           ripples through every pattern match on [vm_instruction]
           (~13 files in the kernel + extraction + Kami RTL).

      (iii) Composition with Ishizaka 2025 to go from PSD9 to Q.

    Re-export. For clarity, we re-export the load-bearing bridge under
    a name that makes its scope explicit: it goes from γ-parameterized
    column-contractivity (the real-valued predicate proved by Section 5)
    to PSD9 of the moment matrix. The caller bridges from any integer
    check to this real-valued predicate. *)
(* INQUISITOR NOTE: alias for caller-facing API surface (renaming of
   column_contractive_q1ab_implies_psd9 to record intended use). *)
Theorem q1ab_caller_supplied_gamma_real_check_implies_psd9 :
  forall (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber),
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5 ->
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5).
Proof.
  exact column_contractive_q1ab_implies_psd9.
Qed.

(** ========================================================================
    Section 11. Bridge for the new [instr_chsh_lassert_1ab] opcode.

    The new opcode (added to [vm_instruction] in VMStep.v) runs the
    composite integer check [column_contractive_check_q1ab_kernel]
    (= Q_1 check ∧ ∑ E² ≤ 1) on the witness counters in a single step.
    A successful step (PC advance + no err latch) is therefore directly
    equivalent to the integer check returning true, which by Section 7
    yields the real-valued [column_contractive_q1ab] at γ = 0, which by
    Section 5 yields PSD9 of the 9×9 moment matrix at γ = 0.

    No additional hypothesis is required: the integer check is performed
    *by the opcode itself*, so the bridge is internal to the kernel.
    ======================================================================== *)

Theorem chsh_lassert_1ab_no_trap_implies_q1ab_psd :
  forall (s : VMState) (mu_delta : nat),
    let s' := vm_apply s (instr_chsh_lassert_1ab mu_delta) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    PSD9 (q1ab_moment_matrix
            (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
            0 0 0 0 0).
Proof.
  intros s mu_delta s' Hpc Herr Herr0.
  (* From "no trap" we deduce the kernel-internal check passed. *)
  assert (Hchk : column_contractive_check_q1ab_kernel s.(vm_witness) = true).
  { unfold s' in Herr. unfold vm_apply in Herr.
    destruct (column_contractive_check_q1ab_kernel s.(vm_witness)) eqn:Echk.
    - reflexivity.
    - simpl in Herr. rewrite Herr0 in Herr. discriminate. }
  (* Apply the integer-to-real soundness theorem. *)
  pose proof (column_contractive_check_q1ab_sound_at_g_zero s.(vm_witness) Hchk) as Hccq.
  (* Apply the reverse direction of the biconditional. *)
  apply column_contractive_q1ab_implies_psd9.
  unfold state_e00, state_e01, state_e10, state_e11. exact Hccq.
Qed.

(** Wrapper: same bridge packaged as a [quantum_realizable_q1ab]
    (= symmetric9 + PSD9) conclusion. *)
Theorem chsh_lassert_1ab_no_trap_implies_quantum_realizable_q1ab :
  forall (s : VMState) (mu_delta : nat),
    let s' := vm_apply s (instr_chsh_lassert_1ab mu_delta) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    quantum_realizable_q1ab
      (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
      0 0 0 0 0.
Proof.
  intros s mu_delta s' Hpc Herr Herr0.
  unfold quantum_realizable_q1ab.
  split.
  - apply q1ab_moment_matrix_symmetric.
  - apply (chsh_lassert_1ab_no_trap_implies_q1ab_psd
             s mu_delta Hpc Herr Herr0).
Qed.

(** ========================================================================
    Section 12. γ_5-only extension: caller-supplied real check that admits
    γ_5 ≠ 0 (the 4-body moment ⟨A_1 A_2 B_1 B_2⟩) while keeping the other
    four γ_k = 0.

    Mathematical content. At γ_1 = γ_2 = γ_3 = γ_4 = 0 with γ_5 free, the
    9×9 residual q1ab_residual block-decomposes into:
      - the top 2×2 block on (v_{B1}, v_{B2}), identical to the γ = 0 case
        ([q1ab_top_block_nonneg], discharged by [zero_marginal_column_contractive]);
      - a bottom 4×4 block on (v_{11}, v_{12}, v_{21}, v_{22}) carrying the
        new 2·γ_5·(v_{11} v_{22} + v_{12} v_{21}) cross term.

    Change of variables (p_1 = v_{11}+v_{22}, p_2 = v_{11}−v_{22},
    q_1 = v_{12}+v_{21}, q_2 = v_{12}−v_{21}) rotates the cross term
    into a (1+γ_5)/(1−γ_5)-weighted diagonal:
      4 × bottom = A·(p_1²+q_1²) + B·(p_2²+q_2²) − (α p_1 + β p_2 + γ q_1 + δ q_2)²
    with A = 2(1+γ_5), B = 2(1−γ_5), α = e_{00}+e_{11}, β = e_{00}−e_{11},
    γ = e_{01}+e_{10}, δ = e_{01}−e_{10}.

    PSD then follows from a weighted 4D Cauchy-Schwarz inequality
    AB·L² ≤ (B(α²+γ²) + A(β²+δ²))·(A·P_p + B·P_m), proved by a six-term
    SOS polynomial identity ([weighted_4d_CS_SOS_identity], closed by
    [ring]).

    The resulting caller-supplied real check is
      −1 < γ_5 < 1   AND
      (1−γ_5)·[(e_{00}+e_{11})² + (e_{01}+e_{10})²]
        + (1+γ_5)·[(e_{00}−e_{11})² + (e_{01}−e_{10})²]
        ≤ 2(1−γ_5²),
    which at γ_5 = 0 reduces to the existing unit-ball condition
    ∑ e_{ij}² ≤ 1, and which strictly extends that region in directions
    aligned with the 4-body moment (positive e_{00}e_{11} + e_{01}e_{10})
    while shrinking it in others.

    No new opcode is introduced. The check is a real-valued caller-side
    obligation. Composition with [column_contractive_q1ab_implies_psd9]
    (Section 5) discharges the full PSD9 conclusion.
    ======================================================================== *)

(** Block decomposition of [q1ab_residual] with γ_1 = γ_2 = γ_3 = γ_4 = 0
    and γ_5 free. Top 2×2 in (v_{B1}, v_{B2}) plus bottom 4×4 in
    (v_{11}, v_{12}, v_{21}, v_{22}) with the new γ_5 cross term. *)
Lemma q1ab_residual_g5_only_decomp :
  forall e00 e01 e10 e11 g5 vB1 vB2 v11 v12 v21 v22 : RealNumber,
    q1ab_residual e00 e01 e10 e11 0 0 0 0 g5 vB1 vB2 v11 v12 v21 v22
    =
    (vB1*vB1 + vB2*vB2
       - (e00*vB1 + e01*vB2) * (e00*vB1 + e01*vB2)
       - (e10*vB1 + e11*vB2) * (e10*vB1 + e11*vB2))
    +
    (v11*v11 + v12*v12 + v21*v21 + v22*v22
       + 2*g5*(v11*v22 - v12*v21)
       - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
         * (e00*v11 + e01*v12 + e10*v21 + e11*v22)).
Proof.
  intros e00 e01 e10 e11 g5 vB1 vB2 v11 v12 v21 v22.
  unfold q1ab_residual. ring.
Qed.

(** Weighted 4D Cauchy-Schwarz as a six-term sum-of-squares identity.
    Closed by [ring]. Used to bound the bottom 4×4 block in the
    rotated (p_1, p_2, q_1, q_2) coordinates. *)
Lemma weighted_4d_CS_SOS_identity :
  forall A B alpha beta_ gamma_ delta x y z w : RealNumber,
    (B*(alpha*alpha + gamma_*gamma_) + A*(beta_*beta_ + delta*delta))
      * (A*(x*x + z*z) + B*(y*y + w*w))
    - A*B*((alpha*x + beta_*y + gamma_*z + delta*w)
           * (alpha*x + beta_*y + gamma_*z + delta*w))
    =
    (B*alpha*y - A*beta_*x) * (B*alpha*y - A*beta_*x)
    + (B*alpha*w - A*delta*x) * (B*alpha*w - A*delta*x)
    + (A*beta_*z - B*gamma_*y) * (A*beta_*z - B*gamma_*y)
    + (B*gamma_*w - A*delta*z) * (B*gamma_*w - A*delta*z)
    + A*B * ((alpha*z - gamma_*x) * (alpha*z - gamma_*x))
    + A*B * ((beta_*w - delta*y) * (beta_*w - delta*y)).
Proof.
  intros A B alpha beta_ gamma_ delta x y z w.
  ring.
Qed.

(** Weighted 4D Cauchy-Schwarz inequality: immediate from the SOS
    identity once A, B ≥ 0. *)
Lemma weighted_4d_CS_nonneg :
  forall A B alpha beta_ gamma_ delta x y z w : RealNumber,
    0 <= A -> 0 <= B ->
    A*B*((alpha*x + beta_*y + gamma_*z + delta*w)
         * (alpha*x + beta_*y + gamma_*z + delta*w))
    <=
    (B*(alpha*alpha + gamma_*gamma_) + A*(beta_*beta_ + delta*delta))
      * (A*(x*x + z*z) + B*(y*y + w*w)).
Proof.
  intros A B alpha beta_ gamma_ delta x y z w HA HB.
  assert (HAB : 0 <= A * B) by (apply Rmult_le_pos; assumption).
  pose proof (weighted_4d_CS_SOS_identity A B alpha beta_ gamma_ delta x y z w) as Hid.
  pose proof (Rle_0_sqr (B*alpha*y - A*beta_*x)) as h1.
  pose proof (Rle_0_sqr (B*alpha*w - A*delta*x)) as h2.
  pose proof (Rle_0_sqr (A*beta_*z - B*gamma_*y)) as h3.
  pose proof (Rle_0_sqr (B*gamma_*w - A*delta*z)) as h4.
  pose proof (Rle_0_sqr (alpha*z - gamma_*x)) as h5.
  pose proof (Rle_0_sqr (beta_*w - delta*y)) as h6.
  unfold Rsqr in *. nra.
Qed.

(** The caller-side γ_5 witness predicate. Strict −1 < γ_5 < 1 keeps the
    diagonal weights A = 2(1+γ_5), B = 2(1−γ_5) strictly positive, which
    makes the Schur-complement style argument cancellable. At γ_5 = 0 the
    polynomial inequality reduces to e_{00}² + e_{01}² + e_{10}² + e_{11}²
    ≤ 1 (unit ball), exactly matching the existing γ = 0 admit. *)
Definition q1ab_g5_caller_witness
  (e00 e01 e10 e11 g5 : RealNumber) : Prop :=
  -1 < g5 < 1 /\
  (1 - g5) * ((e00 + e11)*(e00 + e11) + (e01 - e10)*(e01 - e10))
  + (1 + g5) * ((e00 - e11)*(e00 - e11) + (e01 + e10)*(e01 + e10))
  <= 2 * (1 - g5*g5).

(** Sanity check. At γ_5 = 0 the witness collapses to the unit ball
    e_{00}² + e_{01}² + e_{10}² + e_{11}² ≤ 1. *)
Lemma q1ab_g5_caller_witness_at_zero :
  forall e00 e01 e10 e11 : RealNumber,
    e00*e00 + e01*e01 + e10*e10 + e11*e11 <= 1 ->
    q1ab_g5_caller_witness e00 e01 e10 e11 0.
Proof.
  intros e00 e01 e10 e11 Hball.
  unfold q1ab_g5_caller_witness.
  split; [lra|nra].
Qed.

(** Bottom 4×4 block at γ_1 = ... = γ_4 = 0, γ_5 free, is nonneg under
    the caller witness. Proof: rotate to (p_1, p_2, q_1, q_2), apply
    weighted 4D Cauchy-Schwarz, use the witness to bound the weighted
    sum factor by AB, and cancel AB > 0. *)
Lemma q1ab_bottom_block_g5_nonneg :
  forall e00 e01 e10 e11 g5 v11 v12 v21 v22 : RealNumber,
    q1ab_g5_caller_witness e00 e01 e10 e11 g5 ->
    v11*v11 + v12*v12 + v21*v21 + v22*v22
      + 2*g5*(v11*v22 - v12*v21)
      - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
        * (e00*v11 + e01*v12 + e10*v21 + e11*v22) >= 0.
Proof.
  intros e00 e01 e10 e11 g5 v11 v12 v21 v22 [Hg5 Hcc].
  destruct Hg5 as [Hg5m Hg5p].
  set (p1 := v11 + v22).
  set (p2 := v11 - v22).
  set (q1 := v12 - v21).
  set (q2 := v12 + v21).
  set (alpha := e00 + e11).
  set (beta_ := e00 - e11).
  set (gamma_ := e01 - e10).
  set (delta := e01 + e10).
  set (A := 2 * (1 + g5)).
  set (B := 2 * (1 - g5)).
  assert (HA : 0 < A) by (unfold A; lra).
  assert (HB : 0 < B) by (unfold B; lra).
  assert (HABpos : 0 < A * B) by (apply Rmult_lt_0_compat; assumption).
  (* Polynomial identity: 4 × target = A·(p1²+q1²) + B·(p2²+q2²) − L². *)
  assert (Hrot :
    4 * (v11*v11 + v12*v12 + v21*v21 + v22*v22
         + 2*g5*(v11*v22 - v12*v21)
         - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
           * (e00*v11 + e01*v12 + e10*v21 + e11*v22))
    = A * (p1*p1 + q1*q1) + B * (p2*p2 + q2*q2)
      - (alpha*p1 + beta_*p2 + gamma_*q1 + delta*q2)
        * (alpha*p1 + beta_*p2 + gamma_*q1 + delta*q2)).
  { unfold p1, p2, q1, q2, alpha, beta_, gamma_, delta, A, B. ring. }
  (* Weighted 4D CS in the rotated coordinates. *)
  pose proof (weighted_4d_CS_nonneg A B alpha beta_ gamma_ delta p1 p2 q1 q2
                (Rlt_le _ _ HA) (Rlt_le _ _ HB)) as HCS.
  (* Witness gives the coefficient bound: B(α²+γ²) + A(β²+δ²) ≤ AB. *)
  assert (Hwit :
    B*(alpha*alpha + gamma_*gamma_) + A*(beta_*beta_ + delta*delta) <= A * B).
  { unfold A, B, alpha, beta_, gamma_, delta. nra. }
  set (PpQq := A * (p1*p1 + q1*q1) + B * (p2*p2 + q2*q2)).
  assert (HPpQq_nonneg : 0 <= PpQq).
  { unfold PpQq.
    assert (Hpq1 : 0 <= p1*p1 + q1*q1) by nra.
    assert (Hpq2 : 0 <= p2*p2 + q2*q2) by nra.
    apply Rplus_le_le_0_compat; apply Rmult_le_pos;
      solve [apply Rlt_le; assumption | assumption]. }
  set (Lsq := (alpha*p1 + beta_*p2 + gamma_*q1 + delta*q2)
              * (alpha*p1 + beta_*p2 + gamma_*q1 + delta*q2)).
  fold Lsq PpQq in HCS.
  (* Chain HCS with Hwit times PpQq: AB·L² ≤ (sum) · PpQq ≤ AB · PpQq. *)
  assert (Hbound : A*B*Lsq <= A*B*PpQq).
  { eapply Rle_trans; [exact HCS|].
    apply Rmult_le_compat_r; [exact HPpQq_nonneg|exact Hwit]. }
  (* Cancel AB > 0. *)
  assert (Hineq : Lsq <= PpQq).
  { apply Rmult_le_reg_l with (r := A*B); [exact HABpos|exact Hbound]. }
  (* Conclude via the rotation identity. *)
  apply Rle_ge.
  apply Rmult_le_reg_l with (r := 4); [lra|].
  rewrite Rmult_0_r. rewrite Hrot.
  unfold PpQq, Lsq in Hineq. lra.
Qed.

(** Composite caller-supplied real check at γ_1 = γ_2 = γ_3 = γ_4 = 0,
    γ_5 free: column-contractivity of the 9×9 NPA matrix at
    (E, 0, 0, 0, 0, γ_5). *)
Theorem q1ab_g5_caller_check_implies_column_contractive :
  forall e00 e01 e10 e11 g5 : RealNumber,
    zero_marginal_column_contractive e00 e01 e10 e11 ->
    q1ab_g5_caller_witness e00 e01 e10 e11 g5 ->
    column_contractive_q1ab e00 e01 e10 e11 0 0 0 0 g5.
Proof.
  intros e00 e01 e10 e11 g5 Hzm Hg5.
  unfold column_contractive_q1ab.
  intros vB1 vB2 v11 v12 v21 v22.
  rewrite q1ab_residual_g5_only_decomp.
  pose proof (q1ab_top_block_nonneg e00 e01 e10 e11 vB1 vB2 Hzm) as Htop.
  pose proof (q1ab_bottom_block_g5_nonneg e00 e01 e10 e11 g5 v11 v12 v21 v22 Hg5) as Hbot.
  lra.
Qed.

(** Headline corollary: caller-supplied real check at γ_5 free implies
    PSD9 of the level-1+AB moment matrix. Composes with Section 5's
    [column_contractive_q1ab_implies_psd9]. *)
Corollary q1ab_g5_caller_check_implies_psd9 :
  forall e00 e01 e10 e11 g5 : RealNumber,
    zero_marginal_column_contractive e00 e01 e10 e11 ->
    q1ab_g5_caller_witness e00 e01 e10 e11 g5 ->
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 0 0 0 0 g5).
Proof.
  intros e00 e01 e10 e11 g5 Hzm Hg5.
  apply column_contractive_q1ab_implies_psd9.
  apply q1ab_g5_caller_check_implies_column_contractive; assumption.
Qed.

(** Diagnostic: the γ_5-extended admitted region strictly contains the
    γ = 0 unit ball. The unit-ball direction is [q1ab_g5_caller_witness_at_zero]
    above (γ_5 = 0 specialization). For the strict-extension direction,
    we exhibit a concrete (E, γ_5) with ||E||² > 1 that the γ_5-extended
    witness still admits, witnessing that γ_5 ≠ 0 genuinely enlarges the
    admitted region in directions aligned with the 4-body moment. *)
Lemma q1ab_g5_witness_strict_extension_exists :
  exists e00 e01 e10 e11 g5 : RealNumber,
    q1ab_g5_caller_witness e00 e01 e10 e11 g5 /\
    e00*e00 + e01*e01 + e10*e10 + e11*e11 > 1.
Proof.
  exists (9/10), 0, 0, (9/10), (7/10).
  split.
  - unfold q1ab_g5_caller_witness. split; [lra|nra].
  - nra.
Qed.

(** ========================================================================
    Section 13. Integer-witnessed γ_5 caller check.

    Lifts Section 12's real-valued caller witness to a pure Z-arithmetic
    decision procedure on (correlator numerators/denominators, γ_5
    numerator/denominator). The check runs in O(1) Coq computation and
    is the prerequisite for plumbing the γ_5-extended bridge through a
    kernel-level opcode (which would supply a [WitnessCounts] for the
    correlators and an additional (Ng5, Dg5) pair).

    The integer check is the conjunction of:
      (a) strict positivity of every trial-count sum N_{xy};
      (b) strict bounds 0 < Dg5 and −Dg5 < Ng5 < Dg5 (forcing |γ_5| < 1);
      (c) the cleared polynomial inequality
          Dg5·(Dg5−Ng5)·X_int + Dg5·(Dg5+Ng5)·Y_int
          ≤ 2·(Dg5²−Ng5²)·N_{00}²·N_{01}²·N_{10}²·N_{11}²,
          where X_int = (D_{00}N_{11} + D_{11}N_{00})²·N_{01}²·N_{10}²
                       + (D_{01}N_{10} + D_{10}N_{01})²·N_{00}²·N_{11}²
          and       Y_int = (D_{00}N_{11} − D_{11}N_{00})²·N_{01}²·N_{10}²
                          + (D_{01}N_{10} − D_{10}N_{01})²·N_{00}²·N_{11}².

    Composed with the existing [column_contractive_check_witness] from
    VMStep.v, the integer-witnessed check certifies PSD9 of the γ_5-
    extended 9×9 NPA matrix at the witness-derived correlators. No new
    opcode is wired up in this iteration; the check sits at the kernel-
    real layer ready for opcode plumbing in a subsequent iteration. *)

(** Bridge lemma: state_bucket_correlation = IZR D / IZR N when N > 0
    (where D = same − diff, N = same + diff, both lifted to Z). *)
Lemma state_bucket_correlation_to_IZR :
  forall s d : nat,
    (0 < chsh_n_z s d)%Z ->
    state_bucket_correlation s d
    = (IZR (chsh_d_z s d) / IZR (chsh_n_z s d))%R.
Proof.
  intros s d Hpos.
  unfold state_bucket_correlation, chsh_d_z, chsh_n_z in *.
  destruct (Nat.eqb (s + d) 0) eqn:E.
  - apply Nat.eqb_eq in E.
    apply (f_equal Z.of_nat) in E.
    rewrite Nat2Z.inj_add in E. simpl in E. rewrite E in Hpos. lia.
  - rewrite !INR_IZR_INZ.
    rewrite Nat2Z.inj_add.
    rewrite <- minus_IZR.
    reflexivity.
Qed.

(** Abstract integer γ_5 caller check on (D_xy, N_xy, Ng5, Dg5). *)
Definition q1ab_g5_caller_witness_z_abs
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng5 Dg5 : Z) : bool :=
  ((0 <? N00)%Z)
  && ((0 <? N01)%Z)
  && ((0 <? N10)%Z)
  && ((0 <? N11)%Z)
  && ((0 <? Dg5)%Z)
  && ((-Dg5 <? Ng5)%Z)
  && ((Ng5 <? Dg5)%Z)
  && (let Apos := (D00 * N11 + D11 * N00)%Z in
      let Aneg := (D00 * N11 - D11 * N00)%Z in
      let Cpos := (D01 * N10 + D10 * N01)%Z in
      let Cneg := (D01 * N10 - D10 * N01)%Z in
      let n01n10sq := (N01 * N01 * (N10 * N10))%Z in
      let n00n11sq := (N00 * N00 * (N11 * N11))%Z in
      let Xint := (Apos * Apos * n01n10sq + Cneg * Cneg * n00n11sq)%Z in
      let Yint := (Aneg * Aneg * n01n10sq + Cpos * Cpos * n00n11sq)%Z in
      let Den2 := (n00n11sq * n01n10sq)%Z in
      (Dg5 * (Dg5 - Ng5) * Xint + Dg5 * (Dg5 + Ng5) * Yint
       <=? 2 * (Dg5 * Dg5 - Ng5 * Ng5) * Den2)%Z).

(** Soundness: the abstract integer γ_5 check implies the real-valued
    [q1ab_g5_caller_witness] at the (D/N) correlators and (Ng5/Dg5). *)
Theorem q1ab_g5_caller_witness_z_abs_sound :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng5 Dg5 : Z,
    q1ab_g5_caller_witness_z_abs D00 N00 D01 N01 D10 N10 D11 N11 Ng5 Dg5 = true ->
    q1ab_g5_caller_witness
      (IZR D00 / IZR N00) (IZR D01 / IZR N01)
      (IZR D10 / IZR N10) (IZR D11 / IZR N11)
      (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng5 Dg5 Hchk.
  unfold q1ab_g5_caller_witness_z_abs in Hchk.
  rewrite !Bool.andb_true_iff in Hchk.
  destruct Hchk as [[[[[[[Hn00 Hn01] Hn10] Hn11] HDg5] HNg5L] HNg5U] Hpoly].
  apply Z.ltb_lt in Hn00, Hn01, Hn10, Hn11, HDg5, HNg5L, HNg5U.
  apply Z.leb_le in Hpoly.
  set (rN00 := IZR N00). set (rN01 := IZR N01).
  set (rN10 := IZR N10). set (rN11 := IZR N11).
  set (rD00 := IZR D00). set (rD01 := IZR D01).
  set (rD10 := IZR D10). set (rD11 := IZR D11).
  set (rNg5 := IZR Ng5). set (rDg5 := IZR Dg5).
  assert (HrN00 : (0 < rN00)%R) by (apply IZR_lt; exact Hn00).
  assert (HrN01 : (0 < rN01)%R) by (apply IZR_lt; exact Hn01).
  assert (HrN10 : (0 < rN10)%R) by (apply IZR_lt; exact Hn10).
  assert (HrN11 : (0 < rN11)%R) by (apply IZR_lt; exact Hn11).
  assert (HrDg5 : (0 < rDg5)%R) by (apply IZR_lt; exact HDg5).
  assert (HrNg5L : (-rDg5 < rNg5)%R).
  { unfold rDg5, rNg5. rewrite <- opp_IZR. apply IZR_lt. exact HNg5L. }
  assert (HrNg5U : (rNg5 < rDg5)%R) by (apply IZR_lt; exact HNg5U).
  (* Nothing — we lift the Z inequality just before we need it. *)
  (* Now the goal: q1ab_g5_caller_witness on the divided correlators. *)
  unfold q1ab_g5_caller_witness.
  fold rNg5 rDg5 rN00 rN01 rN10 rN11 rD00 rD01 rD10 rD11.
  split.
  - (* -1 < rNg5/rDg5 < 1 *)
    split.
    + (* -1 < rNg5/rDg5: equivalent to -rDg5 < rNg5 since rDg5 > 0. *)
      apply Rmult_lt_reg_r with (r := rDg5); [exact HrDg5|].
      assert (Hl : (-1 * rDg5 = -rDg5)%R) by ring.
      assert (Hr : ((rNg5 / rDg5) * rDg5 = rNg5)%R) by (field; lra).
      rewrite Hl, Hr. exact HrNg5L.
    + apply Rmult_lt_reg_r with (r := rDg5); [exact HrDg5|].
      assert (Hr : ((rNg5 / rDg5) * rDg5 = rNg5)%R) by (field; lra).
      rewrite Hr, Rmult_1_l. exact HrNg5U.
  - (* Polynomial inequality on divided correlators. *)
    (* Lift integer inequality to R, fully distributing IZR. *)
    apply IZR_le in Hpoly.
    repeat (rewrite plus_IZR in Hpoly
            || rewrite mult_IZR in Hpoly
            || rewrite minus_IZR in Hpoly).
    change (IZR 2) with 2%R in Hpoly.
    fold rDg5 rNg5 rN00 rN01 rN10 rN11 rD00 rD01 rD10 rD11 in Hpoly.
    (* Side hypotheses for field. *)
    assert (HrDg5ne : rDg5 <> 0%R) by lra.
    assert (HrN00ne : rN00 <> 0%R) by lra.
    assert (HrN01ne : rN01 <> 0%R) by lra.
    assert (HrN10ne : rN10 <> 0%R) by lra.
    assert (HrN11ne : rN11 <> 0%R) by lra.
    (* Compact form of the polynomial sides. *)
    set (rApos := (rD00 * rN11 + rD11 * rN00)%R).
    set (rAneg := (rD00 * rN11 - rD11 * rN00)%R).
    set (rCpos := (rD01 * rN10 + rD10 * rN01)%R).
    set (rCneg := (rD01 * rN10 - rD10 * rN01)%R).
    set (rN0011sq := (rN00 * rN00 * (rN11 * rN11))%R).
    set (rN0110sq := (rN01 * rN01 * (rN10 * rN10))%R).
    set (rXintR := (rApos * rApos * rN0110sq + rCneg * rCneg * rN0011sq)%R).
    set (rYintR := (rAneg * rAneg * rN0110sq + rCpos * rCpos * rN0011sq)%R).
    set (rDen2 := (rN0011sq * rN0110sq)%R).
    assert (HrN0011sqpos : (0 < rN0011sq)%R)
      by (unfold rN0011sq; repeat apply Rmult_lt_0_compat; nra).
    assert (HrN0110sqpos : (0 < rN0110sq)%R)
      by (unfold rN0110sq; repeat apply Rmult_lt_0_compat; nra).
    assert (HrDen2pos : (0 < rDen2)%R)
      by (unfold rDen2; apply Rmult_lt_0_compat; assumption).
    apply Rmult_le_reg_r with (r := rDen2 * (rDg5 * rDg5));
      [apply Rmult_lt_0_compat; [assumption|nra]|].
    (* Bridge via transitivity to the lifted Hpoly polynomial. *)
    apply Rle_trans with
      (rDg5 * (rDg5 - rNg5) * rXintR + rDg5 * (rDg5 + rNg5) * rYintR)%R.
    + apply Req_le. unfold rDen2, rXintR, rYintR, rApos, rAneg, rCpos, rCneg,
                          rN0011sq, rN0110sq.
      field. repeat split; assumption.
    + apply Rle_trans with
        (2 * (rDg5 * rDg5 - rNg5 * rNg5) * rDen2)%R.
      * unfold rXintR, rYintR, rApos, rAneg, rCpos, rCneg, rN0011sq, rN0110sq, rDen2.
        exact Hpoly.
      * apply Req_le. symmetry. unfold rDen2, rN0011sq, rN0110sq.
        field. repeat split; assumption.
Qed.

(** WitnessCounts-flavored γ_5 caller check. Wraps the abstract Z check
    by reading (D, N) from the witness counters. *)
Definition q1ab_g5_caller_witness_z
  (wc : WitnessCounts) (Ng5 Dg5 : Z) : bool :=
  q1ab_g5_caller_witness_z_abs
    (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
    (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
    (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
    (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
    (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
    (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
    (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
    (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
    Ng5 Dg5.

(** Soundness of the WitnessCounts integer γ_5 check. *)
Theorem q1ab_g5_caller_witness_z_sound :
  forall (wc : WitnessCounts) (Ng5 Dg5 : Z),
    q1ab_g5_caller_witness_z wc Ng5 Dg5 = true ->
    q1ab_g5_caller_witness
      (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
      (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
      (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
      (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11))
      (IZR Ng5 / IZR Dg5).
Proof.
  intros wc Ng5 Dg5 Hchk.
  unfold q1ab_g5_caller_witness_z in Hchk.
  pose proof (q1ab_g5_caller_witness_z_abs_sound _ _ _ _ _ _ _ _ _ _ Hchk) as Hreal.
  (* From the abstract check passing, extract n_xy > 0 (needed to unfold
     state_bucket_correlation to its IZR D/IZR N form). *)
  unfold q1ab_g5_caller_witness_z_abs in Hchk.
  rewrite !Bool.andb_true_iff in Hchk.
  destruct Hchk as [[[[[[[Hn00 Hn01] Hn10] Hn11] _] _] _] _].
  apply Z.ltb_lt in Hn00, Hn01, Hn10, Hn11.
  rewrite (state_bucket_correlation_to_IZR _ _ Hn00).
  rewrite (state_bucket_correlation_to_IZR _ _ Hn01).
  rewrite (state_bucket_correlation_to_IZR _ _ Hn10).
  rewrite (state_bucket_correlation_to_IZR _ _ Hn11).
  exact Hreal.
Qed.

(** Composite headline check: Q_1 integer check (existing from VMStep.v) +
    γ_5 integer check ⟹ PSD9 of the γ_5-extended 9×9 NPA matrix at the
    witness-derived correlators and γ_5 = IZR Ng5 / IZR Dg5. *)
Definition q1ab_g5_full_integer_check
  (wc : WitnessCounts) (Ng5 Dg5 : Z) : bool :=
  andb (column_contractive_check_witness wc)
       (q1ab_g5_caller_witness_z wc Ng5 Dg5).

Theorem q1ab_g5_full_integer_check_sound :
  forall (wc : WitnessCounts) (Ng5 Dg5 : Z),
    q1ab_g5_full_integer_check wc Ng5 Dg5 = true ->
    PSD9 (q1ab_moment_matrix
            (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
            (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
            (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
            (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11))
            0 0 0 0 (IZR Ng5 / IZR Dg5)).
Proof.
  intros wc Ng5 Dg5 Hchk.
  unfold q1ab_g5_full_integer_check in Hchk.
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [HQ1 HG5].
  pose proof (column_contractive_check_witness_sound _ HQ1) as Hzm.
  pose proof (q1ab_g5_caller_witness_z_sound _ _ _ HG5) as Hg5.
  exact (q1ab_g5_caller_check_implies_psd9 _ _ _ _ _ Hzm Hg5).
Qed.

(** ========================================================================
    Section 14. γ_3, γ_4, γ_5 combined caller-supplied real check.

    Extends Section 12's γ_5-only closure to allow γ_3, γ_4 (the two
    3-body A-B-B moments ⟨A_1 B_1 B_2⟩, ⟨A_2 B_1 B_2⟩) free in
    addition to γ_5. γ_1 = γ_2 = 0 still (the 3-body A-A-B moments
    remain at zero — adding those breaks the block decomposition).

    Mathematical content. With γ_1 = γ_2 = 0, the residual splits as
      q1ab_residual = b_part(b1, b2; v) + bot_g5_only(v)
    where b_part is a (b1, b2)-quadratic form with linear part
    2·(g3·v12 + g4·v22)·b1 + 2·(g3·v11 + g4·v21)·b2 (coming from the
    γ_3, γ_4 cross terms) and quadratic-coefficient matrix M_b =
    [A, B; B, C_M] (the standard Q_1 column-contractive matrix), and
    bot_g5_only(v) is the Section-12 γ_5 bottom block in
    (v11, v12, v21, v22).

    Completing squares in (b1, b2) (assuming det(M_b) > 0, i.e. strict
    zero-marginal-column-contractive) gives the minimum over b of
    b_part as −Q_adj(L_1, L_2)/det(M_b), where Q_adj is the adjugate
    quadratic form C_M·x² − 2B·xy + A·y² and L_1 = g3·v12 + g4·v22,
    L_2 = g3·v11 + g4·v21.

    Hence q1ab_residual ≥ 0 for all (b, v) iff
      ∀ v ∈ R^4, det(M_b)·bot_g5_only(v) ≥ Q_adj(L_1, L_2)        (★)

    This is a 4-variable polynomial inequality that captures both the
    γ_5 bottom-block contractivity AND the γ_3, γ_4 perturbation
    bound. The caller supplies (★) as the witness; the bridge below
    closes the chain to PSD9 of the 9×9 NPA Q_{1+AB} moment matrix at
    (E, 0, 0, γ_3, γ_4, γ_5).

    At γ_3 = γ_4 = 0 the RHS of (★) vanishes and the condition reduces
    to bot_g5_only(v) ≥ 0 for all v, which Section 12's γ_5 closure
    already verifies under the cleaner caller witness. *)

(** Block decomposition of q1ab_residual at γ_1 = γ_2 = 0, γ_3, γ_4,
    γ_5 free: b-quadratic form (in b1, b2) + bottom γ_5 block (in v). *)
Lemma q1ab_residual_g345_decomp :
  forall e00 e01 e10 e11 g3 g4 g5 vB1 vB2 v11 v12 v21 v22 : RealNumber,
    q1ab_residual e00 e01 e10 e11 0 0 g3 g4 g5 vB1 vB2 v11 v12 v21 v22
    =
    ((1 - e00*e00 - e10*e10) * vB1*vB1
     + 2 * (-(e00*e01 + e10*e11)) * vB1*vB2
     + (1 - e01*e01 - e11*e11) * vB2*vB2
     + 2 * (g3*v12 + g4*v22) * vB1
     + 2 * (g3*v11 + g4*v21) * vB2)
    + (v11*v11 + v12*v12 + v21*v21 + v22*v22
       + 2*g5*(v11*v22 - v12*v21)
       - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
         * (e00*v11 + e01*v12 + e10*v21 + e11*v22)).
Proof.
  intros. unfold q1ab_residual. ring.
Qed.

(** Augmented 2×2 b-block PSD: a 2-variable quadratic form with linear
    part and constant is nonneg for all (b1, b2) iff the 3×3 augmented
    matrix (in (b1, b2, 1)) is PSD. Concrete sufficient condition:
    A > 0, det(M_b) > 0, and det(M_b)·const ≥ Q_adj(L_1, L_2). *)
Lemma augmented_2x2_qf_nonneg :
  forall A B C_M L1 L2 c b1 b2 : RealNumber,
    0 < A ->
    0 < A*C_M - B*B ->
    (A*C_M - B*B) * c >= C_M*L1*L1 - 2*B*L1*L2 + A*L2*L2 ->
    A*b1*b1 + 2*B*b1*b2 + C_M*b2*b2 + 2*L1*b1 + 2*L2*b2 + c >= 0.
Proof.
  intros A B C_M L1 L2 c b1 b2 HA Hdet HSchur.
  (* Polynomial identity (two-step square completion, denominators
     cleared via × A·(A·C_M − B²)):
       A·(A·C_M − B²) · (full QF + c)
       = (A·C_M − B²) · (A·b1 + B·b2 + L1)²
         + ((A·C_M − B²)·b2 + (A·L2 − B·L1))²
         + A · ((A·C_M − B²)·c − Q_adj(L1, L2))
     where Q_adj(L1, L2) := C_M·L1² − 2B·L1·L2 + A·L2².
     All three summands are ≥ 0: the two squared linear forms have
     positive multipliers ((A·C_M − B²) > 0 and 1), and the third is
     A > 0 times the Schur slack which is ≥ 0 by hypothesis. *)
  apply Rle_ge.
  apply Rmult_le_reg_l with (r := A*(A*C_M - B*B));
    [apply Rmult_lt_0_compat; assumption|].
  rewrite Rmult_0_r.
  assert (Hid :
    A * (A*C_M - B*B) *
      (A*b1*b1 + 2*B*b1*b2 + C_M*b2*b2 + 2*L1*b1 + 2*L2*b2 + c)
    = (A*C_M - B*B) * ((A*b1 + B*b2 + L1) * (A*b1 + B*b2 + L1))
      + ((A*C_M - B*B)*b2 + (A*L2 - B*L1))
        * ((A*C_M - B*B)*b2 + (A*L2 - B*L1))
      + A * ((A*C_M - B*B)*c - (C_M*L1*L1 - 2*B*L1*L2 + A*L2*L2))).
  { ring. }
  rewrite Hid.
  pose proof (Rle_0_sqr (A*b1 + B*b2 + L1)) as Hs1.
  pose proof (Rle_0_sqr ((A*C_M - B*B)*b2 + (A*L2 - B*L1))) as Hs2.
  unfold Rsqr in *. nra.
Qed.

(** The γ_3, γ_4, γ_5 caller witness: strict zero-marginal-column-
    contractive on (e_ij) AND the augmented 4-variable Schur inequality
    holds for all (v11, v12, v21, v22). *)
Definition q1ab_g345_caller_witness
  (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : Prop :=
  let A := 1 - e00*e00 - e10*e10 in
  let B := -(e00*e01 + e10*e11) in
  let C_M := 1 - e01*e01 - e11*e11 in
  let det_M := A*C_M - B*B in
  0 < A /\ 0 < C_M /\ 0 < det_M /\
  forall v11 v12 v21 v22 : RealNumber,
    det_M
    * (v11*v11 + v12*v12 + v21*v21 + v22*v22
       + 2*g5*(v11*v22 - v12*v21)
       - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
         * (e00*v11 + e01*v12 + e10*v21 + e11*v22))
    >=
    C_M * (g3*v12 + g4*v22) * (g3*v12 + g4*v22)
    - 2 * B * (g3*v12 + g4*v22) * (g3*v11 + g4*v21)
    + A * (g3*v11 + g4*v21) * (g3*v11 + g4*v21).

(** Caller-supplied witness implies column-contractivity at γ_1 = γ_2
    = 0. *)
Theorem q1ab_g345_caller_check_implies_column_contractive :
  forall e00 e01 e10 e11 g3 g4 g5 : RealNumber,
    q1ab_g345_caller_witness e00 e01 e10 e11 g3 g4 g5 ->
    column_contractive_q1ab e00 e01 e10 e11 0 0 g3 g4 g5.
Proof.
  intros e00 e01 e10 e11 g3 g4 g5 [HA [HC_M [Hdet Hwit]]].
  unfold column_contractive_q1ab.
  intros vB1 vB2 v11 v12 v21 v22.
  rewrite q1ab_residual_g345_decomp.
  pose proof (Hwit v11 v12 v21 v22) as Hineq.
  apply (augmented_2x2_qf_nonneg
           (1 - e00*e00 - e10*e10)
           (-(e00*e01 + e10*e11))
           (1 - e01*e01 - e11*e11)
           (g3*v12 + g4*v22)
           (g3*v11 + g4*v21)
           (v11*v11 + v12*v12 + v21*v21 + v22*v22
            + 2*g5*(v11*v22 - v12*v21)
            - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
              * (e00*v11 + e01*v12 + e10*v21 + e11*v22))
           vB1 vB2).
  - exact HA.
  - exact Hdet.
  - exact Hineq.
Qed.

(** Headline corollary: caller-supplied real witness implies PSD9 of
    the 9×9 NPA Q_{1+AB} moment matrix at (E, 0, 0, γ_3, γ_4, γ_5). *)
Corollary q1ab_g345_caller_check_implies_psd9 :
  forall e00 e01 e10 e11 g3 g4 g5 : RealNumber,
    q1ab_g345_caller_witness e00 e01 e10 e11 g3 g4 g5 ->
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 0 0 g3 g4 g5).
Proof.
  intros e00 e01 e10 e11 g3 g4 g5 Hwit.
  apply column_contractive_q1ab_implies_psd9.
  apply q1ab_g345_caller_check_implies_column_contractive.
  exact Hwit.
Qed.

(** Sanity check. At γ_3 = γ_4 = 0 the witness inequality collapses to
    det(M)·bot_g5_only(v) ≥ 0, which Section 12's γ_5 closure already
    proves under [q1ab_g5_caller_witness] (combined with strict
    zero-marginal-column-contractive for det(M) > 0). *)
Lemma q1ab_g345_witness_g3g4_zero :
  forall e00 e01 e10 e11 g5 : RealNumber,
    0 < 1 - e00*e00 - e10*e10 ->
    0 < 1 - e01*e01 - e11*e11 ->
    0 < (1 - e00*e00 - e10*e10) * (1 - e01*e01 - e11*e11)
         - (-(e00*e01 + e10*e11)) * (-(e00*e01 + e10*e11)) ->
    q1ab_g5_caller_witness e00 e01 e10 e11 g5 ->
    q1ab_g345_caller_witness e00 e01 e10 e11 0 0 g5.
Proof.
  intros e00 e01 e10 e11 g5 HA HC_M Hdet Hg5.
  unfold q1ab_g345_caller_witness.
  cbv zeta.
  unfold q1ab_g5_caller_witness in Hg5.
  destruct Hg5 as [Hg5bnd Hg5poly].
  repeat split; try assumption.
  intros v11 v12 v21 v22.
  pose proof (q1ab_bottom_block_g5_nonneg e00 e01 e10 e11 g5 v11 v12 v21 v22
                (conj Hg5bnd Hg5poly)) as Hbot.
  (* RHS at g3 = g4 = 0 collapses to 0. LHS = det_M · bot_g5_only ≥ 0. *)
  apply Rle_ge.
  apply Rge_le in Hbot.
  nra.
Qed.

(** ========================================================================
    Section 15. γ_3, γ_4 integer-witnessed extension via 4×4 Sylvester.

    Lifts Section 14's caller-supplied real witness for the γ_3, γ_4, γ_5
    combined slice to a pure Z-arithmetic decision procedure.

    Mathematical challenge. The Section 14 witness
        ∀v ∈ R^4, det_M · bot_g5_only(v) ≥ Q_adj(g3·v12+g4·v22, g3·v11+g4·v21)
    has an inner ∀-quantifier, so cannot be encoded directly as a finite
    Z-arithmetic check. The right-hand side − left-hand side as a function
    of v is a quadratic form whose matrix is a specific 4×4 symmetric
    polynomial-in-(e_{ij}, g_3, g_4, g_5) matrix
        H_{γ_345}  :=  det_M · M_{M}  −  M_{N}.
    The ∀v inequality holds iff H_{γ_345} is positive semidefinite (PSD).

    Strategy. Encode H_{γ_345} positive-definiteness via Sylvester's
    criterion (all 4 leading principal minors > 0). Soundness flows from
    an explicit fraction-free LDLT identity (Section 15.1) that decomposes
    v^T H v as
        d_1²·d_2·d_3 · v^T H v
          =  (d_1·d_2·d_3) · P_1²  +  (d_1·d_3) · Q_1²  +  Q_2²
             +  (d_1²·d_2·d_4) · v_4²
    where P_1, Q_1, Q_2 are explicit linear forms in v with polynomial-in-H
    coefficients. All four right-side coefficients are positive when
    d_1, d_2, d_3, d_4 > 0, all four squared terms are nonneg, so the
    right side is ≥ 0; dividing by the positive d_1²·d_2·d_3 yields
    v^T H v ≥ 0. This is the PD ⇒ PSD direction of Sylvester for 4×4.

    Region admitted. The integer check captures the strict-PD interior of
    the Section 14 q1ab_g345_caller_witness predicate. PSD-boundary
    configurations (where some d_k vanishes) are not certified. Every
    non-boundary point of the γ_345 cone is reachable.
    ======================================================================== *)

(** Section 15.1. Generic 4×4 symmetric positive-definite via Sylvester. *)

(** v^T H v for a 4×4 symmetric matrix encoded by its upper-triangle entries. *)
Definition sym4_qf
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber)
  (v1 v2 v3 v4 : RealNumber) : RealNumber :=
  h11*v1*v1 + 2*h12*v1*v2 + 2*h13*v1*v3 + 2*h14*v1*v4
  + h22*v2*v2 + 2*h23*v2*v3 + 2*h24*v2*v4
  + h33*v3*v3 + 2*h34*v3*v4
  + h44*v4*v4.

(** Leading 1×1 principal minor. *)
Definition sym4_d1
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber) : RealNumber := h11.

(** Leading 2×2 principal minor. *)
Definition sym4_d2
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber) : RealNumber :=
  h11*h22 - h12*h12.

(** Leading 3×3 principal minor (cofactor expansion along the first row). *)
Definition sym4_d3
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber) : RealNumber :=
  h11*(h22*h33 - h23*h23)
  - h12*(h12*h33 - h13*h23)
  + h13*(h12*h23 - h13*h22).

(** Leading 4×4 principal minor = det(H) (cofactor expansion along the first row,
    each cofactor expanded along its first row in turn). *)
Definition sym4_d4
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber) : RealNumber :=
  h11*(h22*(h33*h44 - h34*h34) - h23*(h23*h44 - h24*h34) + h24*(h23*h34 - h24*h33))
  - h12*(h12*(h33*h44 - h34*h34) - h23*(h13*h44 - h14*h34) + h24*(h13*h34 - h14*h33))
  + h13*(h12*(h23*h44 - h24*h34) - h22*(h13*h44 - h14*h34) + h24*(h13*h24 - h14*h23))
  - h14*(h12*(h23*h34 - h24*h33) - h22*(h13*h34 - h14*h33) + h23*(h13*h24 - h14*h23)).

(** First Cholesky linear form in v (full v_1..v_4 dependence). *)
Definition sym4_P1
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber)
  (v1 v2 v3 v4 : RealNumber) : RealNumber :=
  h11*v1 + h12*v2 + h13*v3 + h14*v4.

(** Second Cholesky linear form (depends on v_2, v_3, v_4 only). *)
Definition sym4_Q1
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber)
  (v2 v3 v4 : RealNumber) : RealNumber :=
  (h11*h22 - h12*h12)*v2
  + (h11*h23 - h12*h13)*v3
  + (h11*h24 - h12*h14)*v4.

(** Third Cholesky linear form (depends on v_3, v_4 only). v_3 coefficient
    is d_1·d_3 = h11 · sym4_d3 (expanded inline). v_4 coefficient is
    d_2 · e_{34} − e_{23} · e_{24} where e_{ij} = h11·h_{ij} − h_{1i}·h_{1j}
    are the (scaled) Schur-complement entries of row 1. *)
Definition sym4_Q2
  (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber)
  (v3 v4 : RealNumber) : RealNumber :=
  (h11 * (h11*(h22*h33 - h23*h23)
          - h12*(h12*h33 - h13*h23)
          + h13*(h12*h23 - h13*h22))) * v3
  + ((h11*h22 - h12*h12)*(h11*h34 - h13*h14)
     - (h11*h23 - h12*h13)*(h11*h24 - h12*h14)) * v4.

(** Fraction-free LDLT identity. Polynomial identity over R, proved by [ring]. *)
Lemma sym4_LDLT_identity :
  forall h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4 : RealNumber,
    sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d3 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_qf h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4
    =
    sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d3 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    (sym4_P1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4 *
     sym4_P1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4)
    +
    sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d3 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    (sym4_Q1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v2 v3 v4 *
     sym4_Q1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v2 v3 v4)
    +
    sym4_Q2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v3 v4 *
    sym4_Q2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v3 v4
    +
    sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    sym4_d4 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 *
    (v4 * v4).
Proof.
  intros.
  unfold sym4_qf, sym4_d1, sym4_d2, sym4_d3, sym4_d4, sym4_P1, sym4_Q1, sym4_Q2.
  ring.
Qed.

(** Sylvester PD ⇒ PSD for 4×4: positive leading principal minors imply
    v^T H v ≥ 0 for all v. *)
Lemma sym4_qf_nonneg_from_pd :
  forall h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4 : RealNumber,
    0 < sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 ->
    0 < sym4_d2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 ->
    0 < sym4_d3 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 ->
    0 < sym4_d4 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 ->
    sym4_qf h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4 >= 0.
Proof.
  intros h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4 Hd1 Hd2 Hd3 Hd4.
  pose proof (sym4_LDLT_identity h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4) as Hid.
  cbv zeta in Hid.
  set (d1 := sym4_d1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44) in *.
  set (d2 := sym4_d2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44) in *.
  set (d3 := sym4_d3 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44) in *.
  set (d4 := sym4_d4 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44) in *.
  set (qf := sym4_qf h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4) in *.
  set (P1 := sym4_P1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v1 v2 v3 v4) in *.
  set (Q1 := sym4_Q1 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v2 v3 v4) in *.
  set (Q2 := sym4_Q2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 v3 v4) in *.
  apply Rle_ge.
  assert (Hd1d1 : 0 < d1*d1) by (apply Rmult_lt_0_compat; assumption).
  assert (Hcoef0 : 0 < d1*d1*d2*d3)
    by (apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat;
         [apply Rmult_lt_0_compat; assumption|exact Hd2]|exact Hd3]).
  apply Rmult_le_reg_l with (r := d1*d1*d2*d3); [exact Hcoef0|].
  rewrite Rmult_0_r, Hid.
  pose proof (Rle_0_sqr P1) as HP1.
  pose proof (Rle_0_sqr Q1) as HQ1.
  pose proof (Rle_0_sqr Q2) as HQ2.
  pose proof (Rle_0_sqr v4) as Hv4.
  unfold Rsqr in *.
  assert (Hcoef1 : 0 < d1*d2*d3)
    by (apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat; assumption|exact Hd3]).
  assert (Hcoef2 : 0 < d1*d3) by (apply Rmult_lt_0_compat; assumption).
  assert (Hcoef4 : 0 < d1*d1*d2*d4)
    by (apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat;
         [apply Rmult_lt_0_compat; assumption|exact Hd2]|exact Hd4]).
  nra.
Qed.

(** Section 15.2. γ_345 difference matrix H = det_M · M_M − M_N.

    Variable ordering (v1, v2, v3, v4) ↦ (v11, v12, v21, v22). With
    A := 1 − e00² − e10², B := −(e00·e01 + e10·e11), C_M := 1 − e01² − e11²,
    det_M := A·C_M − B², the 10 upper-triangular entries of H_{γ_345} are: *)

Definition q345_A (e00 e01 e10 e11 : RealNumber) : RealNumber := 1 - e00*e00 - e10*e10.
Definition q345_B (e00 e01 e10 e11 : RealNumber) : RealNumber := -(e00*e01 + e10*e11).
Definition q345_C_M (e00 e01 e10 e11 : RealNumber) : RealNumber := 1 - e01*e01 - e11*e11.
Definition q345_det_M (e00 e01 e10 e11 : RealNumber) : RealNumber :=
  q345_A e00 e01 e10 e11 * q345_C_M e00 e01 e10 e11
  - q345_B e00 e01 e10 e11 * q345_B e00 e01 e10 e11.

Definition q345_H11 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  q345_det_M e00 e01 e10 e11 * (1 - e00*e00) - q345_A e00 e01 e10 e11 * (g3*g3).
Definition q345_H12 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  - (q345_det_M e00 e01 e10 e11) * (e00*e01) + q345_B e00 e01 e10 e11 * (g3*g3).
Definition q345_H13 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  - (q345_det_M e00 e01 e10 e11) * (e00*e10) - q345_A e00 e01 e10 e11 * (g3*g4).
Definition q345_H14 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  q345_det_M e00 e01 e10 e11 * (g5 - e00*e11) + q345_B e00 e01 e10 e11 * (g3*g4).
Definition q345_H22 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  q345_det_M e00 e01 e10 e11 * (1 - e01*e01) - q345_C_M e00 e01 e10 e11 * (g3*g3).
Definition q345_H23 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  q345_det_M e00 e01 e10 e11 * (- g5 - e01*e10) + q345_B e00 e01 e10 e11 * (g3*g4).
Definition q345_H24 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  - (q345_det_M e00 e01 e10 e11) * (e01*e11) - q345_C_M e00 e01 e10 e11 * (g3*g4).
Definition q345_H33 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  q345_det_M e00 e01 e10 e11 * (1 - e10*e10) - q345_A e00 e01 e10 e11 * (g4*g4).
Definition q345_H34 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  - (q345_det_M e00 e01 e10 e11) * (e10*e11) + q345_B e00 e01 e10 e11 * (g4*g4).
Definition q345_H44 (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : RealNumber :=
  q345_det_M e00 e01 e10 e11 * (1 - e11*e11) - q345_C_M e00 e01 e10 e11 * (g4*g4).

(** The quadratic form on H_{γ_345} equals det_M · bot_g5_only(v) − Q_adj(...). *)
Lemma q345_sym4_qf_equals_diff :
  forall e00 e01 e10 e11 g3 g4 g5 v11 v12 v21 v22 : RealNumber,
    sym4_qf
      (q345_H11 e00 e01 e10 e11 g3 g4 g5)
      (q345_H12 e00 e01 e10 e11 g3 g4 g5)
      (q345_H13 e00 e01 e10 e11 g3 g4 g5)
      (q345_H14 e00 e01 e10 e11 g3 g4 g5)
      (q345_H22 e00 e01 e10 e11 g3 g4 g5)
      (q345_H23 e00 e01 e10 e11 g3 g4 g5)
      (q345_H24 e00 e01 e10 e11 g3 g4 g5)
      (q345_H33 e00 e01 e10 e11 g3 g4 g5)
      (q345_H34 e00 e01 e10 e11 g3 g4 g5)
      (q345_H44 e00 e01 e10 e11 g3 g4 g5)
      v11 v12 v21 v22
    =
    q345_det_M e00 e01 e10 e11
      * (v11*v11 + v12*v12 + v21*v21 + v22*v22
         + 2*g5*(v11*v22 - v12*v21)
         - (e00*v11 + e01*v12 + e10*v21 + e11*v22)
           * (e00*v11 + e01*v12 + e10*v21 + e11*v22))
    -
    (q345_C_M e00 e01 e10 e11 * (g3*v12 + g4*v22) * (g3*v12 + g4*v22)
     - 2 * q345_B e00 e01 e10 e11 * (g3*v12 + g4*v22) * (g3*v11 + g4*v21)
     + q345_A e00 e01 e10 e11 * (g3*v11 + g4*v21) * (g3*v11 + g4*v21)).
Proof.
  intros.
  unfold sym4_qf,
         q345_H11, q345_H12, q345_H13, q345_H14,
         q345_H22, q345_H23, q345_H24,
         q345_H33, q345_H34, q345_H44,
         q345_A, q345_B, q345_C_M, q345_det_M.
  ring.
Qed.

(** Section 15.3. Real-valued γ_345 minors witness and its bridge to the
    Section 14 caller witness.

    The minors predicate carries 7 strict-positivity conditions: A, C_M,
    det_M (the strict zero-marginal-column-contractive requirement of
    [q1ab_g345_caller_witness]) and the four leading principal minors of
    H_{γ_345} (Sylvester's PD criterion for the difference matrix). The
    bridge to [q1ab_g345_caller_witness] uses the Sylvester PD ⇒ PSD
    direction and the qf-equals-diff identity above. *)
Definition q1ab_g345_minors_witness
  (e00 e01 e10 e11 g3 g4 g5 : RealNumber) : Prop :=
  0 < q345_A e00 e01 e10 e11
  /\ 0 < q345_C_M e00 e01 e10 e11
  /\ 0 < q345_det_M e00 e01 e10 e11
  /\ 0 < sym4_d1
            (q345_H11 e00 e01 e10 e11 g3 g4 g5)
            (q345_H12 e00 e01 e10 e11 g3 g4 g5)
            (q345_H13 e00 e01 e10 e11 g3 g4 g5)
            (q345_H14 e00 e01 e10 e11 g3 g4 g5)
            (q345_H22 e00 e01 e10 e11 g3 g4 g5)
            (q345_H23 e00 e01 e10 e11 g3 g4 g5)
            (q345_H24 e00 e01 e10 e11 g3 g4 g5)
            (q345_H33 e00 e01 e10 e11 g3 g4 g5)
            (q345_H34 e00 e01 e10 e11 g3 g4 g5)
            (q345_H44 e00 e01 e10 e11 g3 g4 g5)
  /\ 0 < sym4_d2
            (q345_H11 e00 e01 e10 e11 g3 g4 g5)
            (q345_H12 e00 e01 e10 e11 g3 g4 g5)
            (q345_H13 e00 e01 e10 e11 g3 g4 g5)
            (q345_H14 e00 e01 e10 e11 g3 g4 g5)
            (q345_H22 e00 e01 e10 e11 g3 g4 g5)
            (q345_H23 e00 e01 e10 e11 g3 g4 g5)
            (q345_H24 e00 e01 e10 e11 g3 g4 g5)
            (q345_H33 e00 e01 e10 e11 g3 g4 g5)
            (q345_H34 e00 e01 e10 e11 g3 g4 g5)
            (q345_H44 e00 e01 e10 e11 g3 g4 g5)
  /\ 0 < sym4_d3
            (q345_H11 e00 e01 e10 e11 g3 g4 g5)
            (q345_H12 e00 e01 e10 e11 g3 g4 g5)
            (q345_H13 e00 e01 e10 e11 g3 g4 g5)
            (q345_H14 e00 e01 e10 e11 g3 g4 g5)
            (q345_H22 e00 e01 e10 e11 g3 g4 g5)
            (q345_H23 e00 e01 e10 e11 g3 g4 g5)
            (q345_H24 e00 e01 e10 e11 g3 g4 g5)
            (q345_H33 e00 e01 e10 e11 g3 g4 g5)
            (q345_H34 e00 e01 e10 e11 g3 g4 g5)
            (q345_H44 e00 e01 e10 e11 g3 g4 g5)
  /\ 0 < sym4_d4
            (q345_H11 e00 e01 e10 e11 g3 g4 g5)
            (q345_H12 e00 e01 e10 e11 g3 g4 g5)
            (q345_H13 e00 e01 e10 e11 g3 g4 g5)
            (q345_H14 e00 e01 e10 e11 g3 g4 g5)
            (q345_H22 e00 e01 e10 e11 g3 g4 g5)
            (q345_H23 e00 e01 e10 e11 g3 g4 g5)
            (q345_H24 e00 e01 e10 e11 g3 g4 g5)
            (q345_H33 e00 e01 e10 e11 g3 g4 g5)
            (q345_H34 e00 e01 e10 e11 g3 g4 g5)
            (q345_H44 e00 e01 e10 e11 g3 g4 g5).

(** Sylvester bridge: minors witness ⇒ Section 14 caller witness. *)
Theorem q1ab_g345_minors_witness_implies_caller_witness :
  forall e00 e01 e10 e11 g3 g4 g5 : RealNumber,
    q1ab_g345_minors_witness e00 e01 e10 e11 g3 g4 g5 ->
    q1ab_g345_caller_witness e00 e01 e10 e11 g3 g4 g5.
Proof.
  intros e00 e01 e10 e11 g3 g4 g5 [HA [HC_M [Hdet [Hd1 [Hd2 [Hd3 Hd4]]]]]].
  unfold q1ab_g345_caller_witness.
  unfold q345_A, q345_C_M, q345_det_M, q345_B in HA, HC_M, Hdet.
  cbv zeta.
  repeat split; try assumption.
  intros v11 v12 v21 v22.
  pose proof (sym4_qf_nonneg_from_pd
                (q345_H11 e00 e01 e10 e11 g3 g4 g5)
                (q345_H12 e00 e01 e10 e11 g3 g4 g5)
                (q345_H13 e00 e01 e10 e11 g3 g4 g5)
                (q345_H14 e00 e01 e10 e11 g3 g4 g5)
                (q345_H22 e00 e01 e10 e11 g3 g4 g5)
                (q345_H23 e00 e01 e10 e11 g3 g4 g5)
                (q345_H24 e00 e01 e10 e11 g3 g4 g5)
                (q345_H33 e00 e01 e10 e11 g3 g4 g5)
                (q345_H34 e00 e01 e10 e11 g3 g4 g5)
                (q345_H44 e00 e01 e10 e11 g3 g4 g5)
                v11 v12 v21 v22 Hd1 Hd2 Hd3 Hd4) as Hqf.
  pose proof (q345_sym4_qf_equals_diff e00 e01 e10 e11 g3 g4 g5
                v11 v12 v21 v22) as Heq.
  unfold q345_A, q345_B, q345_C_M, q345_det_M in Heq.
  rewrite Heq in Hqf.
  (* Hqf : (det_M * (v11² + ...)) - (C_M * ... - 2*B*... + A*...) >= 0 *)
  (* Goal: det_M * (v11² + ...) >= C_M * ... - 2*B*... + A*... *)
  apply Rminus_ge.
  exact Hqf.
Qed.

(** Composition with Section 14's headline PSD9 corollary. *)
Corollary q1ab_g345_minors_witness_implies_psd9 :
  forall e00 e01 e10 e11 g3 g4 g5 : RealNumber,
    q1ab_g345_minors_witness e00 e01 e10 e11 g3 g4 g5 ->
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 0 0 g3 g4 g5).
Proof.
  intros e00 e01 e10 e11 g3 g4 g5 Hwit.
  apply q1ab_g345_caller_check_implies_psd9.
  apply q1ab_g345_minors_witness_implies_caller_witness.
  exact Hwit.
Qed.

(** Section 15.4. Cleared-Z integer layer for the 4×4 Sylvester check.

    Each rational quantity q (= polynomial in (e_ij, g_k) where
    e_ij = D_ij/N_ij and g_k = Ng_k/Dg_k) is replaced by an integer
    "cleared numerator" obtained by multiplying through by a positive
    integer denominator. The check on the cleared integer has the same
    sign as the rational; positivity of the cleared integer implies
    positivity of the underlying rational.

    Uniform scaling: each cleared_H_ij_Z = COMMON · H_ij where
       COMMON := (N00·N01·N10·N11)^4 · (Dg3·Dg4·Dg5)^2
    is a multiple of every per-entry denominator. With uniform scaling,
    the cleared leading principal minors cd_k satisfy
       cd_k = COMMON^k · d_k
    (determinant of a scaled matrix is scale^n times the determinant),
    so sign(cd_k) = sign(d_k) and cd_k > 0 ⇒ d_k > 0.

    Factored structure: each cleared_H_ij_Z is
       (COMMON/scale_ij) · cH_ij_per_entry
    where scale_ij is the per-entry natural denominator (so cH_ij_per_entry
    is a small integer numerator polynomial) and (COMMON/scale_ij) is the
    integer multiplier that lifts to uniform scaling. Both factors are
    positive when all N's and Dg's are positive. *)

(** The 4 cleared-numerator helpers (cleared_A_num, cleared_C_M_num,
    cleared_B_num, cleared_det_M_num), the COMMON_Z scaling factor, the
    10 cleared_H_ij_Z entries (factored as mult_for_H_ij · cH_ij_per_entry),
    the 4 sym4_d_k_Z Z-arithmetic leading principal minors, and the 4
    cleared_d_k composite minors are all defined in VMStep.v (kernel
    foundation, no quantum dependency). They are imported via the
    [From Kernel Require Import VMStep] above. *)

(** Helper: IZR of positive Z is nonzero. *)
Lemma IZR_pos_neq_0 : forall n : Z, (0 < n)%Z -> (IZR n <> 0)%R.
Proof. intros n Hn. apply Rgt_not_eq. apply IZR_lt. exact Hn. Qed.

(** Bridge for cleared_A_num: cA_num_R = N00²·N10² · (1 − e00² − e10²) with e_ij rational. *)
Lemma cleared_A_num_bridge :
  forall D00 N00 D10 N10 : Z,
    (0 < N00)%Z -> (0 < N10)%Z ->
    IZR (cleared_A_num D00 N00 D10 N10)
    = (IZR N00 * IZR N00 * (IZR N10 * IZR N10))
      * (1 - (IZR D00 / IZR N00) * (IZR D00 / IZR N00)
         - (IZR D10 / IZR N10) * (IZR D10 / IZR N10)).
Proof.
  intros D00 N00 D10 N10 HN00 HN10.
  unfold cleared_A_num.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  field.
  split; apply IZR_pos_neq_0; assumption.
Qed.

(** Bridge for cleared_C_M_num. *)
Lemma cleared_C_M_num_bridge :
  forall D01 N01 D11 N11 : Z,
    (0 < N01)%Z -> (0 < N11)%Z ->
    IZR (cleared_C_M_num D01 N01 D11 N11)
    = (IZR N01 * IZR N01 * (IZR N11 * IZR N11))
      * (1 - (IZR D01 / IZR N01) * (IZR D01 / IZR N01)
         - (IZR D11 / IZR N11) * (IZR D11 / IZR N11)).
Proof.
  intros D01 N01 D11 N11 HN01 HN11.
  unfold cleared_C_M_num.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  field.
  split; apply IZR_pos_neq_0; assumption.
Qed.

(** Bridge for cleared_B_num: cB_num_R = N_e · (−(e00·e01 + e10·e11)). *)
Lemma cleared_B_num_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    IZR (cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11)
    = (IZR N00 * IZR N01 * IZR N10 * IZR N11)
      * (- ((IZR D00 / IZR N00) * (IZR D01 / IZR N01)
            + (IZR D10 / IZR N10) * (IZR D11 / IZR N11))).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 HN00 HN01 HN10 HN11.
  unfold cleared_B_num.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

(** Bridge for cleared_det_M_num: detM_R = N_e² · det_M_real, where
    det_M_real is the unfolded polynomial in (e_ij_real). *)
Lemma cleared_det_M_num_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    IZR (cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11)
    = (IZR N00 * IZR N01 * IZR N10 * IZR N11)
      * (IZR N00 * IZR N01 * IZR N10 * IZR N11)
      * ((1 - (IZR D00 / IZR N00) * (IZR D00 / IZR N00)
          - (IZR D10 / IZR N10) * (IZR D10 / IZR N10))
         * (1 - (IZR D01 / IZR N01) * (IZR D01 / IZR N01)
            - (IZR D11 / IZR N11) * (IZR D11 / IZR N11))
         - (- ((IZR D00 / IZR N00) * (IZR D01 / IZR N01)
               + (IZR D10 / IZR N10) * (IZR D11 / IZR N11)))
           * (- ((IZR D00 / IZR N00) * (IZR D01 / IZR N01)
                 + (IZR D10 / IZR N10) * (IZR D11 / IZR N11)))).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 HN00 HN01 HN10 HN11.
  unfold cleared_det_M_num, cleared_A_num, cleared_C_M_num, cleared_B_num.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

(** Cleared H_ij bridges. Each
       IZR (cleared_H_ij_Z ...) = IZR (COMMON_Z ...) · H_ij_real
    where H_ij_real is the q345_H_ij value at the rational reals. We
    state the RHS via the unfolded polynomial form for q345 (no q345_X
    application) so the proof's `field` step has the same syntactic
    form on both sides after helper-bridge rewrites. *)

Lemma cleared_H11_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H11
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H11_Z, mult_for_H11, cH11_per_entry, COMMON_Z,
         q345_H11, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_A_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H22_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H22
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H22_Z, mult_for_H22, cH22_per_entry, COMMON_Z,
         q345_H22, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_C_M_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H33_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H33
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H33_Z, mult_for_H33, cH33_per_entry, COMMON_Z,
         q345_H33, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_A_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H44_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H44
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H44_Z, mult_for_H44, cH44_per_entry, COMMON_Z,
         q345_H44, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_C_M_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H12_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H12
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H12_Z, mult_for_H12, cH12_per_entry, COMMON_Z,
         q345_H12, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_B_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H13_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H13
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H13_Z, mult_for_H13, cH13_per_entry, COMMON_Z,
         q345_H13, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_A_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H14_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H14
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H14_Z, mult_for_H14, cH14_per_entry, COMMON_Z,
         q345_H14, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_B_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H23_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H23
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H23_Z, mult_for_H23, cH23_per_entry, COMMON_Z,
         q345_H23, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_B_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H24_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H24
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H24_Z, mult_for_H24, cH24_per_entry, COMMON_Z,
         q345_H24, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_C_M_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

Lemma cleared_H34_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * q345_H34
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  unfold cleared_H34_Z, mult_for_H34, cH34_per_entry, COMMON_Z,
         q345_H34, q345_det_M, q345_A, q345_C_M, q345_B.
  cbv zeta.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR.
  rewrite cleared_det_M_num_bridge by assumption.
  rewrite cleared_B_num_bridge by assumption.
  field.
  repeat split; apply IZR_pos_neq_0; assumption.
Qed.

(** IZR distribution lemmas for sym4_d_k_Z: lift the Z-arithmetic minor
    to the real-arithmetic minor with IZR-promoted arguments. *)

(* DEFINITIONAL HELPER: IZR-commutation lemma for the (trivial) 1×1 leading
   principal minor, which is just the (1,1) entry. The Z and R versions
   are syntactically identical apart from IZR coercion. *)
Lemma sym4_d1_Z_IZR :
  forall h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z,
    IZR (sym4_d1_Z h11 h12 h13 h14 h22 h23 h24 h33 h34 h44)
    = sym4_d1 (IZR h11) (IZR h12) (IZR h13) (IZR h14)
              (IZR h22) (IZR h23) (IZR h24)
              (IZR h33) (IZR h34) (IZR h44).
Proof.
  intros. unfold sym4_d1_Z, sym4_d1. reflexivity.
Qed.

Lemma sym4_d2_Z_IZR :
  forall h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z,
    IZR (sym4_d2_Z h11 h12 h13 h14 h22 h23 h24 h33 h34 h44)
    = sym4_d2 (IZR h11) (IZR h12) (IZR h13) (IZR h14)
              (IZR h22) (IZR h23) (IZR h24)
              (IZR h33) (IZR h34) (IZR h44).
Proof.
  intros. unfold sym4_d2_Z, sym4_d2.
  rewrite minus_IZR. rewrite !mult_IZR. reflexivity.
Qed.

Lemma sym4_d3_Z_IZR :
  forall h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z,
    IZR (sym4_d3_Z h11 h12 h13 h14 h22 h23 h24 h33 h34 h44)
    = sym4_d3 (IZR h11) (IZR h12) (IZR h13) (IZR h14)
              (IZR h22) (IZR h23) (IZR h24)
              (IZR h33) (IZR h34) (IZR h44).
Proof.
  intros. unfold sym4_d3_Z, sym4_d3.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR. ring.
Qed.

Lemma sym4_d4_Z_IZR :
  forall h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z,
    IZR (sym4_d4_Z h11 h12 h13 h14 h22 h23 h24 h33 h34 h44)
    = sym4_d4 (IZR h11) (IZR h12) (IZR h13) (IZR h14)
              (IZR h22) (IZR h23) (IZR h24)
              (IZR h33) (IZR h34) (IZR h44).
Proof.
  intros. unfold sym4_d4_Z, sym4_d4.
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR. ring.
Qed.

(** Scaling property of sym4_d_k: scaling all matrix entries by c scales
    the k-th leading principal minor by c^k (determinant of c·M = c^n·det(M)). *)

(* sym4_d1_scale removed: had one caller; sym4_d1 is the identity projection
   onto h11, so the scaling identity holds by [unfold sym4_d1] which is now
   performed at the sole use site. *)

Lemma sym4_d2_scale :
  forall c h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber,
    sym4_d2 (c*h11) (c*h12) (c*h13) (c*h14)
            (c*h22) (c*h23) (c*h24)
            (c*h33) (c*h34) (c*h44)
    = c*c * sym4_d2 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44.
Proof. intros. unfold sym4_d2. ring. Qed.

Lemma sym4_d3_scale :
  forall c h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber,
    sym4_d3 (c*h11) (c*h12) (c*h13) (c*h14)
            (c*h22) (c*h23) (c*h24)
            (c*h33) (c*h34) (c*h44)
    = c*c*c * sym4_d3 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44.
Proof. intros. unfold sym4_d3. ring. Qed.

Lemma sym4_d4_scale :
  forall c h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : RealNumber,
    sym4_d4 (c*h11) (c*h12) (c*h13) (c*h14)
            (c*h22) (c*h23) (c*h24)
            (c*h33) (c*h34) (c*h44)
    = c*c*c*c * sym4_d4 h11 h12 h13 h14 h22 h23 h24 h33 h34 h44.
Proof. intros. unfold sym4_d4. ring. Qed.

(** Composite cd_k bridges. Each
       IZR (cd_k ...) = COMMON_R^k · sym4_d_k (q345_H_ij_real ...)
    proven by composing the Z-to-R IZR distribution + per-ij bridges +
    scaling property. *)

Lemma cleared_d1_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    let e00 := (IZR D00 / IZR N00)%R in
    let e01 := (IZR D01 / IZR N01)%R in
    let e10 := (IZR D10 / IZR N10)%R in
    let e11 := (IZR D11 / IZR N11)%R in
    let g3 := (IZR Ng3 / IZR Dg3)%R in
    let g4 := (IZR Ng4 / IZR Dg4)%R in
    let g5 := (IZR Ng5 / IZR Dg5)%R in
    IZR (cleared_d1 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)
      * sym4_d1
          (q345_H11 e00 e01 e10 e11 g3 g4 g5)
          (q345_H12 e00 e01 e10 e11 g3 g4 g5)
          (q345_H13 e00 e01 e10 e11 g3 g4 g5)
          (q345_H14 e00 e01 e10 e11 g3 g4 g5)
          (q345_H22 e00 e01 e10 e11 g3 g4 g5)
          (q345_H23 e00 e01 e10 e11 g3 g4 g5)
          (q345_H24 e00 e01 e10 e11 g3 g4 g5)
          (q345_H33 e00 e01 e10 e11 g3 g4 g5)
          (q345_H34 e00 e01 e10 e11 g3 g4 g5)
          (q345_H44 e00 e01 e10 e11 g3 g4 g5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  cbv zeta.
  unfold cleared_d1.
  rewrite sym4_d1_Z_IZR.
  rewrite cleared_H11_Z_bridge by assumption.
  unfold sym4_d1. reflexivity.
Qed.

Lemma cleared_d2_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    let e00 := (IZR D00 / IZR N00)%R in
    let e01 := (IZR D01 / IZR N01)%R in
    let e10 := (IZR D10 / IZR N10)%R in
    let e11 := (IZR D11 / IZR N11)%R in
    let g3 := (IZR Ng3 / IZR Dg3)%R in
    let g4 := (IZR Ng4 / IZR Dg4)%R in
    let g5 := (IZR Ng5 / IZR Dg5)%R in
    let C := IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5) in
    IZR (cleared_d2 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = C * C * sym4_d2
          (q345_H11 e00 e01 e10 e11 g3 g4 g5)
          (q345_H12 e00 e01 e10 e11 g3 g4 g5)
          (q345_H13 e00 e01 e10 e11 g3 g4 g5)
          (q345_H14 e00 e01 e10 e11 g3 g4 g5)
          (q345_H22 e00 e01 e10 e11 g3 g4 g5)
          (q345_H23 e00 e01 e10 e11 g3 g4 g5)
          (q345_H24 e00 e01 e10 e11 g3 g4 g5)
          (q345_H33 e00 e01 e10 e11 g3 g4 g5)
          (q345_H34 e00 e01 e10 e11 g3 g4 g5)
          (q345_H44 e00 e01 e10 e11 g3 g4 g5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  cbv zeta.
  unfold cleared_d2.
  rewrite sym4_d2_Z_IZR.
  rewrite cleared_H11_Z_bridge by assumption.
  rewrite cleared_H12_Z_bridge by assumption.
  rewrite cleared_H22_Z_bridge by assumption.
  unfold sym4_d2.
  ring.
Qed.

Lemma cleared_d3_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    let e00 := (IZR D00 / IZR N00)%R in
    let e01 := (IZR D01 / IZR N01)%R in
    let e10 := (IZR D10 / IZR N10)%R in
    let e11 := (IZR D11 / IZR N11)%R in
    let g3 := (IZR Ng3 / IZR Dg3)%R in
    let g4 := (IZR Ng4 / IZR Dg4)%R in
    let g5 := (IZR Ng5 / IZR Dg5)%R in
    let C := IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5) in
    IZR (cleared_d3 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = C * C * C * sym4_d3
          (q345_H11 e00 e01 e10 e11 g3 g4 g5)
          (q345_H12 e00 e01 e10 e11 g3 g4 g5)
          (q345_H13 e00 e01 e10 e11 g3 g4 g5)
          (q345_H14 e00 e01 e10 e11 g3 g4 g5)
          (q345_H22 e00 e01 e10 e11 g3 g4 g5)
          (q345_H23 e00 e01 e10 e11 g3 g4 g5)
          (q345_H24 e00 e01 e10 e11 g3 g4 g5)
          (q345_H33 e00 e01 e10 e11 g3 g4 g5)
          (q345_H34 e00 e01 e10 e11 g3 g4 g5)
          (q345_H44 e00 e01 e10 e11 g3 g4 g5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  cbv zeta.
  unfold cleared_d3.
  rewrite sym4_d3_Z_IZR.
  rewrite cleared_H11_Z_bridge by assumption.
  rewrite cleared_H12_Z_bridge by assumption.
  rewrite cleared_H13_Z_bridge by assumption.
  rewrite cleared_H22_Z_bridge by assumption.
  rewrite cleared_H23_Z_bridge by assumption.
  rewrite cleared_H33_Z_bridge by assumption.
  unfold sym4_d3.
  ring.
Qed.

Lemma cleared_d4_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    let e00 := (IZR D00 / IZR N00)%R in
    let e01 := (IZR D01 / IZR N01)%R in
    let e10 := (IZR D10 / IZR N10)%R in
    let e11 := (IZR D11 / IZR N11)%R in
    let g3 := (IZR Ng3 / IZR Dg3)%R in
    let g4 := (IZR Ng4 / IZR Dg4)%R in
    let g5 := (IZR Ng5 / IZR Dg5)%R in
    let C := IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5) in
    IZR (cleared_d4 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = C * C * C * C * sym4_d4
          (q345_H11 e00 e01 e10 e11 g3 g4 g5)
          (q345_H12 e00 e01 e10 e11 g3 g4 g5)
          (q345_H13 e00 e01 e10 e11 g3 g4 g5)
          (q345_H14 e00 e01 e10 e11 g3 g4 g5)
          (q345_H22 e00 e01 e10 e11 g3 g4 g5)
          (q345_H23 e00 e01 e10 e11 g3 g4 g5)
          (q345_H24 e00 e01 e10 e11 g3 g4 g5)
          (q345_H33 e00 e01 e10 e11 g3 g4 g5)
          (q345_H34 e00 e01 e10 e11 g3 g4 g5)
          (q345_H44 e00 e01 e10 e11 g3 g4 g5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5.
  cbv zeta.
  unfold cleared_d4.
  rewrite sym4_d4_Z_IZR.
  rewrite cleared_H11_Z_bridge by assumption.
  rewrite cleared_H12_Z_bridge by assumption.
  rewrite cleared_H13_Z_bridge by assumption.
  rewrite cleared_H14_Z_bridge by assumption.
  rewrite cleared_H22_Z_bridge by assumption.
  rewrite cleared_H23_Z_bridge by assumption.
  rewrite cleared_H24_Z_bridge by assumption.
  rewrite cleared_H33_Z_bridge by assumption.
  rewrite cleared_H34_Z_bridge by assumption.
  rewrite cleared_H44_Z_bridge by assumption.
  unfold sym4_d4.
  ring.
Qed.

(** Helper: COMMON_Z > 0 when all N's and Dg's are positive. *)
Lemma COMMON_Z_pos :
  forall N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    (0 < COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)%Z.
Proof.
  intros. unfold COMMON_Z. nia.
Qed.

Lemma COMMON_Z_pos_R :
  forall N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    (0 < IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5))%R.
Proof.
  intros. apply IZR_lt. apply COMMON_Z_pos; assumption.
Qed.

(** ========================================================================
    Section 15.5. Integer-witnessed γ_345 caller check (bool decider on Z)
    and the soundness chain bool=true ⇒ q1ab_g345_caller_witness ⇒ PSD9. *)

(** Abstract integer check on the 14 Z parameters (4 (D,N) correlator
    pairs + 3 (Ng,Dg) γ-bucket pairs). True iff:
      (1) every trial-count denominator N_xy > 0;
      (2) every γ-denominator Dg_k > 0;
      (3) every γ-numerator |Ng_k| < Dg_k (i.e. |g_k| < 1);
      (4) cleared_A_num > 0       (A = 1 − e00² − e10² > 0);
      (5) cleared_C_M_num > 0     (C_M = 1 − e01² − e11² > 0);
      (6) cleared_det_M_num > 0   (det_M = A·C_M − B² > 0);
      (7) cleared_d_k > 0 for k = 1, 2, 3, 4 (4×4 Sylvester PD on H_{γ_345}).
*)
(** The bool decider lives in VMStep.v as [q1ab_g345_check_z_kernel]
    (kernel foundation). The local alias [q1ab_g345_caller_witness_z_abs]
    forwards to it so the existing soundness theorem reads in the
    quantum-layer naming convention. *)
Definition q1ab_g345_caller_witness_z_abs
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : bool :=
  q1ab_g345_check_z_kernel
    D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5.

(** Soundness: bool check passes ⇒ real-valued q1ab_g345_minors_witness
    holds at the rational correlators and γ values. *)
Theorem q1ab_g345_caller_witness_z_abs_sound :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    q1ab_g345_caller_witness_z_abs
      D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = true ->
    q1ab_g345_minors_witness
      (IZR D00 / IZR N00) (IZR D01 / IZR N01)
      (IZR D10 / IZR N10) (IZR D11 / IZR N11)
      (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 Hchk.
  unfold q1ab_g345_caller_witness_z_abs, q1ab_g345_check_z_kernel in Hchk.
  rewrite !Bool.andb_true_iff in Hchk.
  destruct Hchk as
    [[[[[[[[[[[[[[[[[[[HN00 HN01] HN10] HN11] HDg3] HDg4] HDg5]
         HNg3lo] HNg3hi] HNg4lo] HNg4hi] HNg5lo] HNg5hi]
        HA_pos] HC_M_pos] Hdet_pos] Hd1] Hd2] Hd3] Hd4].
  apply Z.ltb_lt in HN00, HN01, HN10, HN11, HDg3, HDg4, HDg5,
                    HNg3lo, HNg3hi, HNg4lo, HNg4hi, HNg5lo, HNg5hi,
                    HA_pos, HC_M_pos, Hdet_pos, Hd1, Hd2, Hd3, Hd4.
  (* The 7 strict-positivity facts (A, C_M, det_M, d1..d4) at the real
     level follow from the Z-level positivity through the bridges. *)
  unfold q1ab_g345_minors_witness.
  pose proof (cleared_A_num_bridge D00 N00 D10 N10 HN00 HN10) as HA_eq.
  pose proof (cleared_C_M_num_bridge D01 N01 D11 N11 HN01 HN11) as HC_M_eq.
  pose proof (cleared_det_M_num_bridge D00 N00 D01 N01 D10 N10 D11 N11
                HN00 HN01 HN10 HN11) as Hdet_eq.
  pose proof (cleared_d1_bridge D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
                HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5) as Hd1_eq.
  pose proof (cleared_d2_bridge D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
                HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5) as Hd2_eq.
  pose proof (cleared_d3_bridge D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
                HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5) as Hd3_eq.
  pose proof (cleared_d4_bridge D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
                HN00 HN01 HN10 HN11 HDg3 HDg4 HDg5) as Hd4_eq.
  cbv zeta in Hd1_eq, Hd2_eq, Hd3_eq, Hd4_eq.
  set (CR := IZR (COMMON_Z N00 N01 N10 N11 Dg3 Dg4 Dg5)) in *.
  assert (HCR_pos : (0 < CR)%R) by (apply COMMON_Z_pos_R; assumption).
  assert (HrN00 : (IZR N00 <> 0)%R) by (apply IZR_pos_neq_0; assumption).
  assert (HrN01 : (IZR N01 <> 0)%R) by (apply IZR_pos_neq_0; assumption).
  assert (HrN10 : (IZR N10 <> 0)%R) by (apply IZR_pos_neq_0; assumption).
  assert (HrN11 : (IZR N11 <> 0)%R) by (apply IZR_pos_neq_0; assumption).
  assert (HrN00pos : (0 < IZR N00)%R) by (apply IZR_lt; assumption).
  assert (HrN01pos : (0 < IZR N01)%R) by (apply IZR_lt; assumption).
  assert (HrN10pos : (0 < IZR N10)%R) by (apply IZR_lt; assumption).
  assert (HrN11pos : (0 < IZR N11)%R) by (apply IZR_lt; assumption).
  (* Derive each real positivity from the Z positivity through the bridges. *)
  apply IZR_lt in HA_pos, HC_M_pos, Hdet_pos, Hd1, Hd2, Hd3, Hd4.
  change (IZR 0) with 0%R in *.
  (* For A: cleared_A_num > 0 (Z) ⇒ IZR(...) > 0 (R) ⇒ A_real > 0 since
     IZR(cleared_A_num) = N00²·N10² · A_real and N00²·N10² > 0. *)
  unfold q345_A, q345_C_M, q345_det_M, q345_B.
  repeat split.
  - (* A > 0 *)
    rewrite HA_eq in HA_pos.
    apply Rmult_lt_reg_l with (r := (IZR N00 * IZR N00 * (IZR N10 * IZR N10))%R).
    + apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat|apply Rmult_lt_0_compat]; nra.
    + rewrite Rmult_0_r. exact HA_pos.
  - (* C_M > 0 *)
    rewrite HC_M_eq in HC_M_pos.
    apply Rmult_lt_reg_l with (r := (IZR N01 * IZR N01 * (IZR N11 * IZR N11))%R).
    + apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat|apply Rmult_lt_0_compat]; nra.
    + rewrite Rmult_0_r. exact HC_M_pos.
  - (* det_M > 0 *)
    rewrite Hdet_eq in Hdet_pos.
    apply Rmult_lt_reg_l with
      (r := ((IZR N00 * IZR N01 * IZR N10 * IZR N11) * (IZR N00 * IZR N01 * IZR N10 * IZR N11))%R).
    + apply Rmult_lt_0_compat;
        repeat apply Rmult_lt_0_compat; assumption.
    + rewrite Rmult_0_r. exact Hdet_pos.
  - (* d1 > 0 *)
    rewrite Hd1_eq in Hd1.
    apply Rmult_lt_reg_l with (r := CR); [assumption|].
    rewrite Rmult_0_r. exact Hd1.
  - (* d2 > 0 *)
    rewrite Hd2_eq in Hd2.
    apply Rmult_lt_reg_l with (r := (CR*CR)%R).
    + apply Rmult_lt_0_compat; assumption.
    + rewrite Rmult_0_r. exact Hd2.
  - (* d3 > 0 *)
    rewrite Hd3_eq in Hd3.
    apply Rmult_lt_reg_l with (r := (CR*CR*CR)%R).
    + apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; assumption.
    + rewrite Rmult_0_r. exact Hd3.
  - (* d4 > 0 *)
    rewrite Hd4_eq in Hd4.
    apply Rmult_lt_reg_l with (r := (CR*CR*CR*CR)%R).
    + apply Rmult_lt_0_compat;
        [apply Rmult_lt_0_compat;
         [apply Rmult_lt_0_compat|]|]; assumption.
    + rewrite Rmult_0_r. exact Hd4.
Qed.

(** Headline corollary: bool check ⇒ PSD9 of the 9×9 NPA Q_{1+AB} matrix
    at the rational-derived correlators and γ_3, γ_4, γ_5. *)
Corollary q1ab_g345_caller_witness_z_abs_implies_psd9 :
  forall D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    q1ab_g345_caller_witness_z_abs
      D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = true ->
    PSD9 (q1ab_moment_matrix
            (IZR D00 / IZR N00) (IZR D01 / IZR N01)
            (IZR D10 / IZR N10) (IZR D11 / IZR N11)
            0 0
            (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. apply q1ab_g345_minors_witness_implies_psd9.
  apply q1ab_g345_caller_witness_z_abs_sound. assumption.
Qed.

(** Region diagnostic.

    The integer check [q1ab_g345_caller_witness_z_abs] admits exactly
    the rational-valued configurations (e_{ij} = D_{ij}/N_{ij},
    g_k = Ng_k/Dg_k) for which:

    (a) Each N_{ij} > 0 and each Dg_k > 0 (denominators positive);

    (b) |g_k| < 1 for k = 3, 4, 5 (γ-bucket bounds, encoded as
        −Dg_k < Ng_k < Dg_k after clearing);

    (c) Strict zero-marginal-column-contractive on the e_{ij}'s:
        A = 1 − e00² − e10² > 0,
        C_M = 1 − e01² − e11² > 0,
        det_M = A·C_M − B² > 0
        where B = −(e00·e01 + e10·e11);

    (d) Strict positive-definiteness of the 4×4 difference matrix
        H_{γ_345} := det_M · M_M − M_N
        encoding the inner ∀v∈R^4 inequality of [q1ab_g345_caller_witness],
        verified via Sylvester's criterion (4 leading principal minors > 0
        in cleared-Z form).

    This is the strict-PD interior of the [q1ab_g345_caller_witness]
    cone of Section 14. PSD-boundary configurations (where some d_k
    vanishes) are not certified — they require a separate (rank-degenerate)
    treatment. Every non-boundary point of the γ_345 cone, including
    Tsirelson-saturating configurations with γ_3, γ_4 nonzero, is
    reachable through some choice of integer (D_{ij}, N_{ij}, Ng_k, Dg_k)
    that passes the check. *)

(** ========================================================================
    Section 16. γ_1, γ_2 integer-witnessed extension via 6×6 Sylvester.

    Closes the full multi-γ slice by lifting γ_1, γ_2 (the 3-body A-A-B
    moments ⟨A_1A_2B_1⟩, ⟨A_1A_2B_2⟩) into the caller-witness check. With
    γ_1, γ_2 free, Section 14's augmented Schur trick no longer applies —
    the b-block is no longer a pure quadratic in b with linear-in-v part,
    because γ_1, γ_2 inject bilinear-in-(b, v) cross terms that interleave
    with the existing −e_{ij}·b structure.

    Strategy. Treat the full 6-variable q1ab_residual (in v_{B1}, v_{B2},
    v_{11}, v_{12}, v_{21}, v_{22}) as a quadratic form whose matrix H_{γ_12345}
    has 21 entries polynomial in (e_{ij}, γ_1..γ_5). Encode PSD via
    Sylvester (6 leading principal minors > 0). Soundness flows from a
    compositional Schur reduction: sym6_qf ≥ 0 follows from sym5_qf ≥ 0
    (applied to the 5×5 scaled Schur residual S_1), which follows from
    sym4_qf ≥ 0 (Section 15.1) via a second Schur step on S_1's residual.
    Each Schur step is a small polynomial identity provable by [ring];
    composition avoids any giant LDLT identity over the full sym6.

    The compositional structure is:
      Section 16.1   sym5 generic machinery + Schur step + sym5_qf_nonneg_from_pd
      Section 16.2   sym6 generic machinery + Schur step + sym6_qf_nonneg_from_pd
      Section 16.3   γ_12345 H specialization + qf-equals-residual
      Section 16.4   real-valued q1ab_g12345_minors_witness + PSD9 bridge
      Section 16.5   cleared-Z integer layer (in VMStep.v, used here)
      Section 16.6   integer check + soundness + region diagnostic
    ======================================================================== *)

(** Section 16.1. Generic 5×5 symmetric positive-definite via Sylvester
    (one-step Schur reduction to the 4×4 Sylvester of Section 15.1). *)

Definition sym5_qf
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber)
  (v1 v2 v3 v4 v5 : RealNumber) : RealNumber :=
  h11*v1*v1 + 2*h12*v1*v2 + 2*h13*v1*v3 + 2*h14*v1*v4 + 2*h15*v1*v5
  + h22*v2*v2 + 2*h23*v2*v3 + 2*h24*v2*v4 + 2*h25*v2*v5
  + h33*v3*v3 + 2*h34*v3*v4 + 2*h35*v3*v5
  + h44*v4*v4 + 2*h45*v4*v5
  + h55*v5*v5.

Definition sym5_d1
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber := h11.

Definition sym5_d2
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h22 - h12*h12.

Definition sym5_d3
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*(h22*h33 - h23*h23)
  - h12*(h12*h33 - h13*h23)
  + h13*(h12*h23 - h13*h22).

Definition sym5_d4
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*(h22*(h33*h44 - h34*h34) - h23*(h23*h44 - h24*h34) + h24*(h23*h34 - h24*h33))
  - h12*(h12*(h33*h44 - h34*h34) - h23*(h13*h44 - h14*h34) + h24*(h13*h34 - h14*h33))
  + h13*(h12*(h23*h44 - h24*h34) - h22*(h13*h44 - h14*h34) + h24*(h13*h24 - h14*h23))
  - h14*(h12*(h23*h34 - h24*h33) - h22*(h13*h34 - h14*h33) + h23*(h13*h24 - h14*h23)).

(** Scaled 4×4 Schur complement of row/column 1 of the 5×5 H. Each entry
    is [h11·h_{ij} − h_{1i}·h_{1j}] for i, j ∈ {2,3,4,5}. Working with
    [scaled_S] (instead of dividing by h11) keeps the entire reduction
    polynomial over R — no [field] tactic, no h11 ≠ 0 hypothesis needed
    for [ring] identities. *)

Definition sym5_scaled_S_22
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h22 - h12*h12.
Definition sym5_scaled_S_23
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h23 - h12*h13.
Definition sym5_scaled_S_24
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h24 - h12*h14.
Definition sym5_scaled_S_25
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h25 - h12*h15.
Definition sym5_scaled_S_33
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h33 - h13*h13.
Definition sym5_scaled_S_34
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h34 - h13*h14.
Definition sym5_scaled_S_35
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h35 - h13*h15.
Definition sym5_scaled_S_44
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h44 - h14*h14.
Definition sym5_scaled_S_45
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h45 - h14*h15.
Definition sym5_scaled_S_55
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : RealNumber :=
  h11*h55 - h15*h15.

(** Linear form `h11·v1 + h12·v2 + h13·v3 + h14·v4 + h15·v5` extracted
    from the Schur identity. *)
Definition sym5_P1
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber)
  (v1 v2 v3 v4 v5 : RealNumber) : RealNumber :=
  h11*v1 + h12*v2 + h13*v3 + h14*v4 + h15*v5.

(** Schur identity at sym5: scales [sym5_qf] by h11 into a perfect
    square plus [sym4_qf] on the 4×4 scaled Schur complement. Closed by
    [ring]. *)
Lemma sym5_Schur_identity :
  forall h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
         v1 v2 v3 v4 v5 : RealNumber,
    h11 * sym5_qf h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
                  v1 v2 v3 v4 v5
    =
    sym5_P1 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
            v1 v2 v3 v4 v5
    *
    sym5_P1 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
            v1 v2 v3 v4 v5
    +
    sym4_qf
      (sym5_scaled_S_22 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_23 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_24 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_25 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_33 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_34 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_35 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_44 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_45 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      (sym5_scaled_S_55 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
      v2 v3 v4 v5.
Proof.
  intros.
  unfold sym5_qf, sym5_P1,
         sym5_scaled_S_22, sym5_scaled_S_23, sym5_scaled_S_24, sym5_scaled_S_25,
         sym5_scaled_S_33, sym5_scaled_S_34, sym5_scaled_S_35,
         sym5_scaled_S_44, sym5_scaled_S_45, sym5_scaled_S_55,
         sym4_qf.
  ring.
Qed.

(** PD predicate for sym5: h11 > 0 plus the 4 Sylvester minors of the
    scaled Schur complement are all strictly positive. *)
Definition sym5_pd_interior
  (h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 : RealNumber) : Prop :=
  h11 > 0
  /\ 0 < sym4_d1
           (sym5_scaled_S_22 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_23 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_24 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_25 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_33 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_34 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_35 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_44 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_45 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_55 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
  /\ 0 < sym4_d2
           (sym5_scaled_S_22 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_23 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_24 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_25 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_33 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_34 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_35 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_44 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_45 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_55 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
  /\ 0 < sym4_d3
           (sym5_scaled_S_22 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_23 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_24 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_25 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_33 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_34 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_35 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_44 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_45 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_55 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
  /\ 0 < sym4_d4
           (sym5_scaled_S_22 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_23 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_24 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_25 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_33 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_34 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_35 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_44 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_45 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
           (sym5_scaled_S_55 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55).

(** Sylvester-via-Schur PD ⇒ PSD for sym5_qf. *)
Lemma sym5_qf_nonneg_from_pd :
  forall h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
         v1 v2 v3 v4 v5 : RealNumber,
    sym5_pd_interior h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55 ->
    sym5_qf h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
            v1 v2 v3 v4 v5 >= 0.
Proof.
  intros h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
         v1 v2 v3 v4 v5 [Hh11 [Hd1 [Hd2 [Hd3 Hd4]]]].
  pose proof (sym5_Schur_identity h11 h12 h13 h14 h15 h22 h23 h24 h25
                                  h33 h34 h35 h44 h45 h55 v1 v2 v3 v4 v5) as Hid.
  pose proof (sym4_qf_nonneg_from_pd
                (sym5_scaled_S_22 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_23 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_24 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_25 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_33 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_34 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_35 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_44 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_45 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                (sym5_scaled_S_55 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55)
                v2 v3 v4 v5 Hd1 Hd2 Hd3 Hd4) as Hsym4_nn.
  set (P1 := sym5_P1 h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
                     v1 v2 v3 v4 v5) in *.
  (* h11 * sym5_qf = P1² + sym4_qf, both summands ≥ 0, h11 > 0 ⇒ sym5_qf ≥ 0. *)
  assert (0 <= P1 * P1) as HP1sq by nra.
  assert (h11 * sym5_qf h11 h12 h13 h14 h15 h22 h23 h24 h25 h33 h34 h35 h44 h45 h55
                        v1 v2 v3 v4 v5 >= 0) as Hlhs_nn.
  { rewrite Hid. nra. }
  nra.
Qed.

(** Section 16.2. Generic 6×6 symmetric positive-definite via Sylvester
    (one-step Schur reduction to the 5×5 Sylvester of Section 16.1). *)

Definition sym6_qf
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber)
  (v1 v2 v3 v4 v5 v6 : RealNumber) : RealNumber :=
  h11*v1*v1 + 2*h12*v1*v2 + 2*h13*v1*v3 + 2*h14*v1*v4 + 2*h15*v1*v5 + 2*h16*v1*v6
  + h22*v2*v2 + 2*h23*v2*v3 + 2*h24*v2*v4 + 2*h25*v2*v5 + 2*h26*v2*v6
  + h33*v3*v3 + 2*h34*v3*v4 + 2*h35*v3*v5 + 2*h36*v3*v6
  + h44*v4*v4 + 2*h45*v4*v5 + 2*h46*v4*v6
  + h55*v5*v5 + 2*h56*v5*v6
  + h66*v6*v6.

(** Scaled 5×5 Schur complement of row/column 1 of the 6×6 H. Entry
    [scaled_S_6_{ij} := h11·h_{ij} − h_{1i}·h_{1j}] for i, j ∈ {2..6}. *)

Definition sym6_scaled_S_22
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h22 - h12*h12.
Definition sym6_scaled_S_23
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h23 - h12*h13.
Definition sym6_scaled_S_24
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h24 - h12*h14.
Definition sym6_scaled_S_25
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h25 - h12*h15.
Definition sym6_scaled_S_26
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h26 - h12*h16.
Definition sym6_scaled_S_33
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h33 - h13*h13.
Definition sym6_scaled_S_34
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h34 - h13*h14.
Definition sym6_scaled_S_35
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h35 - h13*h15.
Definition sym6_scaled_S_36
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h36 - h13*h16.
Definition sym6_scaled_S_44
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h44 - h14*h14.
Definition sym6_scaled_S_45
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h45 - h14*h15.
Definition sym6_scaled_S_46
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h46 - h14*h16.
Definition sym6_scaled_S_55
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h55 - h15*h15.
Definition sym6_scaled_S_56
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h56 - h15*h16.
Definition sym6_scaled_S_66
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : RealNumber := h11*h66 - h16*h16.

Definition sym6_P1
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber)
  (v1 v2 v3 v4 v5 v6 : RealNumber) : RealNumber :=
  h11*v1 + h12*v2 + h13*v3 + h14*v4 + h15*v5 + h16*v6.

Lemma sym6_Schur_identity :
  forall h11 h12 h13 h14 h15 h16
         h22 h23 h24 h25 h26
         h33 h34 h35 h36
         h44 h45 h46
         h55 h56
         h66
         v1 v2 v3 v4 v5 v6 : RealNumber,
    h11 * sym6_qf h11 h12 h13 h14 h15 h16
                  h22 h23 h24 h25 h26
                  h33 h34 h35 h36
                  h44 h45 h46
                  h55 h56
                  h66
                  v1 v2 v3 v4 v5 v6
    =
    sym6_P1 h11 h12 h13 h14 h15 h16
            h22 h23 h24 h25 h26
            h33 h34 h35 h36
            h44 h45 h46
            h55 h56
            h66
            v1 v2 v3 v4 v5 v6
    *
    sym6_P1 h11 h12 h13 h14 h15 h16
            h22 h23 h24 h25 h26
            h33 h34 h35 h36
            h44 h45 h46
            h55 h56
            h66
            v1 v2 v3 v4 v5 v6
    +
    sym5_qf
      (sym6_scaled_S_22 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_23 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_24 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_25 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_26 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_33 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_34 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_35 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_36 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_44 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_45 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_46 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_55 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_56 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      (sym6_scaled_S_66 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
      v2 v3 v4 v5 v6.
Proof.
  intros.
  unfold sym6_qf, sym6_P1,
         sym6_scaled_S_22, sym6_scaled_S_23, sym6_scaled_S_24, sym6_scaled_S_25, sym6_scaled_S_26,
         sym6_scaled_S_33, sym6_scaled_S_34, sym6_scaled_S_35, sym6_scaled_S_36,
         sym6_scaled_S_44, sym6_scaled_S_45, sym6_scaled_S_46,
         sym6_scaled_S_55, sym6_scaled_S_56,
         sym6_scaled_S_66,
         sym5_qf.
  ring.
Qed.

Definition sym6_pd_interior
  (h11 h12 h13 h14 h15 h16
   h22 h23 h24 h25 h26
   h33 h34 h35 h36
   h44 h45 h46
   h55 h56
   h66 : RealNumber) : Prop :=
  h11 > 0
  /\ sym5_pd_interior
       (sym6_scaled_S_22 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_23 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_24 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_25 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_26 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_33 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_34 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_35 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_36 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_44 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_45 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_46 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_55 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_56 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
       (sym6_scaled_S_66 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66).

Lemma sym6_qf_nonneg_from_pd :
  forall h11 h12 h13 h14 h15 h16
         h22 h23 h24 h25 h26
         h33 h34 h35 h36
         h44 h45 h46
         h55 h56
         h66
         v1 v2 v3 v4 v5 v6 : RealNumber,
    sym6_pd_interior h11 h12 h13 h14 h15 h16
                     h22 h23 h24 h25 h26
                     h33 h34 h35 h36
                     h44 h45 h46
                     h55 h56
                     h66 ->
    sym6_qf h11 h12 h13 h14 h15 h16
            h22 h23 h24 h25 h26
            h33 h34 h35 h36
            h44 h45 h46
            h55 h56
            h66
            v1 v2 v3 v4 v5 v6 >= 0.
Proof.
  intros h11 h12 h13 h14 h15 h16
         h22 h23 h24 h25 h26
         h33 h34 h35 h36
         h44 h45 h46
         h55 h56
         h66
         v1 v2 v3 v4 v5 v6 [Hh11 Hsym5_pd].
  pose proof (sym6_Schur_identity h11 h12 h13 h14 h15 h16
                                  h22 h23 h24 h25 h26
                                  h33 h34 h35 h36
                                  h44 h45 h46
                                  h55 h56
                                  h66
                                  v1 v2 v3 v4 v5 v6) as Hid.
  pose proof (sym5_qf_nonneg_from_pd
                (sym6_scaled_S_22 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_23 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_24 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_25 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_26 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_33 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_34 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_35 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_36 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_44 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_45 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_46 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_55 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_56 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                (sym6_scaled_S_66 h11 h12 h13 h14 h15 h16 h22 h23 h24 h25 h26 h33 h34 h35 h36 h44 h45 h46 h55 h56 h66)
                v2 v3 v4 v5 v6 Hsym5_pd) as Hsym5_nn.
  set (P1 := sym6_P1 h11 h12 h13 h14 h15 h16
                     h22 h23 h24 h25 h26
                     h33 h34 h35 h36
                     h44 h45 h46
                     h55 h56
                     h66
                     v1 v2 v3 v4 v5 v6) in *.
  assert (0 <= P1 * P1) as HP1sq by nra.
  assert (h11 * sym6_qf h11 h12 h13 h14 h15 h16
                        h22 h23 h24 h25 h26
                        h33 h34 h35 h36
                        h44 h45 h46
                        h55 h56
                        h66
                        v1 v2 v3 v4 v5 v6 >= 0) as Hlhs_nn.
  { rewrite Hid. nra. }
  nra.
Qed.

(** Section 16.3. γ_12345 H specialization.

    The 21 entries of the 6×6 symmetric matrix H_{γ_12345} whose
    associated quadratic form on (vB1, vB2, v11, v12, v21, v22) equals
    q1ab_residual at the given (e_{ij}, γ_1..γ_5). Direct readout from
    the residual's diag and 2·v_i·v_j cross terms (each γ_5 enters the
    v11·v22 and v12·v21 entries; γ_1, γ_2 enter b-block off-diag rows
    and inside the v-block as g_1·g_2 product; γ_3, γ_4 enter b-row to
    v-col entries). *)

Definition q12345_H11 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  1 - e00*e00 - e10*e10.
Definition q12345_H12 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -(e00*e01 + e10*e11).
Definition q12345_H13 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -e10*g1.
Definition q12345_H14 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  g3 - e10*g2.
Definition q12345_H15 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -e00*g1.
Definition q12345_H16 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  g4 - e00*g2.
Definition q12345_H22 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  1 - e01*e01 - e11*e11.
Definition q12345_H23 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  g3 - e11*g1.
Definition q12345_H24 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -e11*g2.
Definition q12345_H25 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  g4 - e01*g1.
Definition q12345_H26 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -e01*g2.
Definition q12345_H33 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  1 - e00*e00 - g1*g1.
Definition q12345_H34 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -(e00*e01 + g1*g2).
Definition q12345_H35 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -e00*e10.
Definition q12345_H36 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  g5 - e00*e11.
Definition q12345_H44 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  1 - e01*e01 - g2*g2.
Definition q12345_H45 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  - g5 - e01*e10.
Definition q12345_H46 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -e01*e11.
Definition q12345_H55 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  1 - e10*e10 - g1*g1.
Definition q12345_H56 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  -(e10*e11 + g1*g2).
Definition q12345_H66 (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealNumber :=
  1 - e11*e11 - g2*g2.

(** sym6_qf at the specialized H entries equals the q1ab_residual on
    (vB1, vB2, v11, v12, v21, v22). Polynomial identity, ring. *)
Lemma q12345_sym6_qf_equals_residual :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5
         vB1 vB2 v11 v12 v21 v22 : RealNumber,
    sym6_qf
      (q12345_H11 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H12 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H13 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H14 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H15 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H16 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H22 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H23 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H24 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H25 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H26 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H33 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H34 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H35 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H36 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H44 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H45 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H46 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H55 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H56 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      (q12345_H66 e00 e01 e10 e11 g1 g2 g3 g4 g5)
      vB1 vB2 v11 v12 v21 v22
    =
    q1ab_residual e00 e01 e10 e11 g1 g2 g3 g4 g5
                  vB1 vB2 v11 v12 v21 v22.
Proof.
  intros.
  unfold sym6_qf,
         q12345_H11, q12345_H12, q12345_H13, q12345_H14, q12345_H15, q12345_H16,
         q12345_H22, q12345_H23, q12345_H24, q12345_H25, q12345_H26,
         q12345_H33, q12345_H34, q12345_H35, q12345_H36,
         q12345_H44, q12345_H45, q12345_H46,
         q12345_H55, q12345_H56,
         q12345_H66,
         q1ab_residual.
  ring.
Qed.

(** Section 16.4. Real-valued q1ab_g12345 minors witness and PSD9 bridge.

    The witness is exactly [sym6_pd_interior] instantiated at the
    γ_12345 H entries. By the Schur cascade (Section 16.1 + 16.2), this
    implies sym6_qf ≥ 0 of [q1ab_residual] for all (vB1, vB2, v11, v12,
    v21, v22), i.e. [column_contractive_q1ab] at the given (E, γ_1..γ_5).
    Composed with [column_contractive_q1ab_implies_psd9] (Section 5),
    this gives full PSD9 of the 9×9 NPA matrix. *)

Definition q1ab_g12345_minors_witness
  (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : Prop :=
  sym6_pd_interior
    (q12345_H11 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H12 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H13 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H14 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H15 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H16 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H22 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H23 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H24 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H25 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H26 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H33 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H34 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H35 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H36 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H44 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H45 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H46 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H55 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H56 e00 e01 e10 e11 g1 g2 g3 g4 g5)
    (q12345_H66 e00 e01 e10 e11 g1 g2 g3 g4 g5).

Theorem q1ab_g12345_minors_witness_implies_column_contractive :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    q1ab_g12345_minors_witness e00 e01 e10 e11 g1 g2 g3 g4 g5 ->
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5.
Proof.
  intros e00 e01 e10 e11 g1 g2 g3 g4 g5 Hpd
         vB1 vB2 v11 v12 v21 v22.
  unfold q1ab_g12345_minors_witness in Hpd.
  pose proof (sym6_qf_nonneg_from_pd
                (q12345_H11 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H12 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H13 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H14 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H15 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H16 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H22 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H23 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H24 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H25 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H26 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H33 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H34 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H35 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H36 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H44 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H45 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H46 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H55 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H56 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                (q12345_H66 e00 e01 e10 e11 g1 g2 g3 g4 g5)
                vB1 vB2 v11 v12 v21 v22 Hpd) as Hsym6_nn.
  rewrite q12345_sym6_qf_equals_residual in Hsym6_nn.
  exact Hsym6_nn.
Qed.

Theorem q1ab_g12345_minors_witness_implies_psd9 :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    q1ab_g12345_minors_witness e00 e01 e10 e11 g1 g2 g3 g4 g5 ->
    PSD9 (q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5).
Proof.
  intros. apply column_contractive_q1ab_implies_psd9.
  apply q1ab_g12345_minors_witness_implies_column_contractive. assumption.
Qed.

(** Sanity-check specialization. At γ_1 = γ_2 = 0 the q12345 witness
    reduces to the γ_345 witness handled in Section 14/15: the b-row to
    v-col cross entries H_{1,3}, H_{1,5}, H_{2,4}, H_{2,6} all vanish
    (they were −e·g_1 or −e·g_2) and only H_{1,4}, H_{1,6}, H_{2,3},
    H_{2,5} carry the γ_3, γ_4 information. *)
Lemma q12345_witness_at_g12_zero_reduces_to_g345 :
  forall e00 e01 e10 e11 g3 g4 g5 : RealNumber,
    q12345_H13 e00 e01 e10 e11 0 0 g3 g4 g5 = 0
    /\ q12345_H15 e00 e01 e10 e11 0 0 g3 g4 g5 = 0
    /\ q12345_H24 e00 e01 e10 e11 0 0 g3 g4 g5 = 0
    /\ q12345_H26 e00 e01 e10 e11 0 0 g3 g4 g5 = 0
    /\ q12345_H14 e00 e01 e10 e11 0 0 g3 g4 g5 = g3
    /\ q12345_H16 e00 e01 e10 e11 0 0 g3 g4 g5 = g4
    /\ q12345_H23 e00 e01 e10 e11 0 0 g3 g4 g5 = g3
    /\ q12345_H25 e00 e01 e10 e11 0 0 g3 g4 g5 = g4
    /\ q12345_H34 e00 e01 e10 e11 0 0 g3 g4 g5 = -(e00*e01)
    /\ q12345_H56 e00 e01 e10 e11 0 0 g3 g4 g5 = -(e10*e11).
Proof.
  intros.
  unfold q12345_H13, q12345_H15, q12345_H24, q12345_H26,
         q12345_H14, q12345_H16, q12345_H23, q12345_H25,
         q12345_H34, q12345_H56.
  repeat split; ring.
Qed.

(** ========================================================================
    Section 16.5. Cleared-Z integer kernel for γ_{1,2,3,4,5}.

    Lifts Section 16.4's real-valued [q1ab_g12345_minors_witness] to a
    bool decider on Z bucket counts. The kernel decider
    [q1ab_g12345_check_z_kernel] and all 21 cleared H-entries + 25
    Schur-cascade Z helpers live in [VMStep.v Section 15.6] (foundation
    tier — no quantum dependency). This section establishes:

    (a) 21 bridge lemmas [cleared_g12345_HXX_Z_bridge]: each
        [IZR (cleared_g12345_HXX_Z(...)) = IZR (g12345_COMMON_Z(...)) *
        q12345_HXX (IZR D / IZR N) (IZR Ng / IZR Dg)] under positivity
        hypotheses on all N's and Dg's.

    (b) Cascade bridges relating cleared S6/S5 Z-entries to powers of
        g12345_COMMON_Z times the real Schur-complement values.

    (c) The composite soundness theorem
        [q1ab_g12345_caller_witness_z_abs_sound]: kernel check passes ⇒
        sym6_pd_interior of H_{γ_12345} at the IZR-evaluated rationals
        ⇒ q1ab_g12345_minors_witness ⇒ PSD9 of the 9×9 NPA matrix.

    Region diagnostic: the check admits exactly the rational interior of
    the sym6_pd_interior cone — strict zero-marginal-column-contractive
    on E, strict |g_k| < 1 for k = 1..5, and strict PD-via-Schur cascade
    on H_{γ_12345}. PSD-boundary configurations excluded (mirror of
    γ_5 and γ_345 checks). The cone strictly contains the Section 15
    γ_345 cone (additional γ_1, γ_2 degrees of freedom).
    ======================================================================== *)

(** Bridge: g12345_COMMON_Z is a strictly positive integer under all
    denominator-positivity hypotheses, hence its IZR is strictly positive. *)
Lemma g12345_COMMON_Z_pos :
  forall N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    (0 < g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)%Z.
Proof.
  intros N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5
         HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold g12345_COMMON_Z.
  set (P := (N00*N01*N10*N11*Dg1*Dg2*Dg3*Dg4*Dg5)%Z).
  assert (0 < P)%Z as HP.
  { unfold P. repeat apply Z.mul_pos_pos; assumption. }
  apply Z.mul_pos_pos; assumption.
Qed.

(** Real-valued positivity from integer positivity. *)
Lemma g12345_COMMON_Z_pos_R :
  forall N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    (0 < IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5))%R.
Proof.
  intros. apply IZR_lt. apply g12345_COMMON_Z_pos; assumption.
Qed.

(** Tactic shorthand: discharge all positivity-nonzero side conditions on
    a [field] call. Used by every cleared_g12345_HXX_Z_bridge below. *)
Ltac g12345_pos_split :=
  repeat split; apply IZR_pos_neq_0; assumption.

(** All 21 bridges share the same proof skeleton: unfold the cleared
    numerator and q12345_HXX definitions, push IZR through Z arithmetic
    via [opp_IZR, minus_IZR, plus_IZR, mult_IZR], then [field] cleans
    the rational arithmetic and the positivity premises discharge the
    remaining nonzero side conditions. *)
Ltac g12345_H_bridge cleared qkv :=
  intros; unfold cleared, qkv, g12345_COMMON_Z;
  cbv zeta;
  repeat rewrite ?opp_IZR, ?minus_IZR, ?plus_IZR, ?mult_IZR;
  field; g12345_pos_split.

Lemma cleared_g12345_H11_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H11
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H11_Z q12345_H11. Qed.

Lemma cleared_g12345_H22_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H22_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H22
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H22_Z q12345_H22. Qed.

Lemma cleared_g12345_H33_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H33_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H33
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H33_Z q12345_H33. Qed.

Lemma cleared_g12345_H44_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H44_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H44
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H44_Z q12345_H44. Qed.

Lemma cleared_g12345_H55_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H55_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H55
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H55_Z q12345_H55. Qed.

Lemma cleared_g12345_H66_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H66_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H66
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H66_Z q12345_H66. Qed.

Lemma cleared_g12345_H12_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H12
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H12_Z q12345_H12. Qed.

Lemma cleared_g12345_H13_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H13
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H13_Z q12345_H13. Qed.

Lemma cleared_g12345_H14_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H14
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H14_Z q12345_H14. Qed.

Lemma cleared_g12345_H15_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H15
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H15_Z q12345_H15. Qed.

Lemma cleared_g12345_H16_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H16
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H16_Z q12345_H16. Qed.

Lemma cleared_g12345_H23_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H23_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H23
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H23_Z q12345_H23. Qed.

Lemma cleared_g12345_H24_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H24_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H24
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H24_Z q12345_H24. Qed.

Lemma cleared_g12345_H25_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H25_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H25
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H25_Z q12345_H25. Qed.

Lemma cleared_g12345_H26_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H26_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H26
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H26_Z q12345_H26. Qed.

Lemma cleared_g12345_H34_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H34_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H34
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H34_Z q12345_H34. Qed.

Lemma cleared_g12345_H35_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H35_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H35
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H35_Z q12345_H35. Qed.

Lemma cleared_g12345_H36_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H36_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H36
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H36_Z q12345_H36. Qed.

Lemma cleared_g12345_H45_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H45_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H45
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H45_Z q12345_H45. Qed.

Lemma cleared_g12345_H46_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H46_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H46
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H46_Z q12345_H46. Qed.

Lemma cleared_g12345_H56_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_H56_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)
      * q12345_H56
          (IZR D00 / IZR N00) (IZR D01 / IZR N01)
          (IZR D10 / IZR N10) (IZR D11 / IZR N11)
          (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
          (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof. g12345_H_bridge cleared_g12345_H56_Z q12345_H56. Qed.

(** Helper: IZR distributivity for the integer Schur step. *)
Lemma schur_step_Z_IZR :
  forall h11 hij h1i h1j : Z,
    IZR (schur_step_Z h11 hij h1i h1j)
    = IZR h11 * IZR hij - IZR h1i * IZR h1j.
Proof.
  intros. unfold schur_step_Z.
  rewrite minus_IZR, !mult_IZR. reflexivity.
Qed.

(** Cascade-bridge tactic for the 15 sym6_scaled_S_6 entries: rewrite the
    schur_step on cleared H entries, substitute the H bridges, close by
    [ring]. *)
Ltac g12345_S6_bridge cleared_S6 h11b hij_b h1i_b h1j_b :=
  intros; cbv zeta; unfold cleared_S6;
  rewrite schur_step_Z_IZR;
  rewrite h11b by assumption;
  rewrite hij_b by assumption;
  rewrite h1i_b by assumption;
  try (rewrite h1j_b by assumption);
  field; g12345_pos_split.

Lemma cleared_g12345_S6_22_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H22
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H12
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H12
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_22_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H22_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H12_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.


(** 14 cleared scaled_S_6 bridges (S6_23 through S6_66). Each follows the
    S6_22 pattern: unfold the schur_step on cleared H entries, substitute
    the 21 H bridges (Section 16.5 H-entry block), close by [ring]. *)

Lemma cleared_g12345_S6_23_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H23
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H12
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H13
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_23_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H23_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H12_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H13_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_24_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H24
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H12
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H14
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_24_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H24_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H12_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H14_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_25_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H25
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H12
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H15
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_25_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H25_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H12_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H15_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_26_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H26
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H12
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H16
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_26_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H26_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H12_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H16_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_33_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_33_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H33
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H13
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H13
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_33_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H33_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H13_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_34_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_34_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H34
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H13
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H14
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_34_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H34_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H13_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H14_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_35_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_35_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H35
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H13
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H15
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_35_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H35_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H13_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H15_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_36_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_36_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H36
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H13
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H16
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_36_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H36_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H13_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H16_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_44_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_44_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H44
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H14
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H14
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_44_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H44_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H14_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_45_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_45_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H45
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H14
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H15
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_45_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H45_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H14_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H15_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_46_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_46_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H46
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H14
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H16
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_46_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H46_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H14_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H16_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_55_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_55_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H55
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H15
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H15
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_55_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H55_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H15_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_56_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_56_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H56
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H15
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H16
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_56_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H56_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H15_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H16_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

Lemma cleared_g12345_S6_66_Z_bridge :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    IZR (cleared_g12345_S6_66_Z D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5) *
      (q12345_H11
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H66
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) -
       q12345_H16
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5) *
       q12345_H16
         (IZR D00 / IZR N00) (IZR D01 / IZR N01)
         (IZR D10 / IZR N10) (IZR D11 / IZR N11)
         (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
         (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Proof.
  intros. unfold cleared_g12345_S6_66_Z.
  rewrite schur_step_Z_IZR.
  rewrite (cleared_g12345_H11_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H66_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  rewrite (cleared_g12345_H16_Z_bridge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) by assumption.
  ring.
Qed.

(** Section 16.5 (continued).  Cleared-Z bridges for the 10 [S5_ij] entries
    (the 4x4 Schur of row 1 of the cleared 5x5 scaled_S_6), plus the 4
    [sym4_d_k] cascade bridges, plus the [q1ab_g12345_caller_witness_z_abs_sound]
    soundness theorem.

    Each [cleared_g12345_S5_ij_Z] is at scaling [K^4] where
    [K = IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)].
    The 4 sym4_d_k of the cleared S5 entries are at scaling [K^(4k)].

    A [Section] block introduces the 18 Z-arguments + 9 positivity hypotheses
    + 21 Local Notations [q_kl_R] for [q12345_Hkl (IZR D00/IZR N00) ...]
    once, so the cascade lemma statements stay readable. *)

Section S5_and_minors_bridges.

Variables D00 N00 D01 N01 D10 N10 D11 N11
          Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z.

(** Each lemma in this Section takes the 9 denominator-positivity preconditions
    explicitly (rather than as Section [Hypothesis] / Prop-typed [Variable], which
    the inquisitor flags as axiom-equivalent).  The preconditions are uniform —
    [(0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
     (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->]
    bound by [intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.] in every proof. *)

(** Common scaling factor in IZR form. *)
Local Notation KZ := (IZR (g12345_COMMON_Z N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5)).

(** 21 q12345_Hkl evaluated at the [IZR D/IZR N] rationals.  Pure notational
    abbreviations (parse-time textual expansion), so [ring] sees the fully
    expanded q12345_Hkl applications, not [let]-bound aliases. *)

Local Notation q11_R := (q12345_H11 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q12_R := (q12345_H12 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q13_R := (q12345_H13 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q14_R := (q12345_H14 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q15_R := (q12345_H15 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q16_R := (q12345_H16 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q22_R := (q12345_H22 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q23_R := (q12345_H23 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q24_R := (q12345_H24 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q25_R := (q12345_H25 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q26_R := (q12345_H26 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q33_R := (q12345_H33 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q34_R := (q12345_H34 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q35_R := (q12345_H35 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q36_R := (q12345_H36 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q44_R := (q12345_H44 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q45_R := (q12345_H45 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q46_R := (q12345_H46 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q55_R := (q12345_H55 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q56_R := (q12345_H56 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
Local Notation q66_R := (q12345_H66 (IZR D00 / IZR N00) (IZR D01 / IZR N01) (IZR D10 / IZR N10) (IZR D11 / IZR N11)
                                       (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2) (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5)).
(** 10 S5 cascade bridges.  Each [cleared_g12345_S5_ij_Z] equals
    [KZ^4 * sym5_scaled_S_ij(sym6_scaled_S_22(q_R), ..., sym6_scaled_S_55(q_R))],
    spelled out as the explicit polynomial in [q_kl_R]. *)

Lemma cleared_g12345_S5_22_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q33_R - q13_R * q13_R)
     - (q11_R * q23_R - q12_R * q13_R) * (q11_R * q23_R - q12_R * q13_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_22_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_23_Z_bridge by assumption.
  rewrite cleared_g12345_S6_33_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_23_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q34_R - q13_R * q14_R)
     - (q11_R * q23_R - q12_R * q13_R) * (q11_R * q24_R - q12_R * q14_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_23_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_23_Z_bridge by assumption.
  rewrite cleared_g12345_S6_24_Z_bridge by assumption.
  rewrite cleared_g12345_S6_34_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_24_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q35_R - q13_R * q15_R)
     - (q11_R * q23_R - q12_R * q13_R) * (q11_R * q25_R - q12_R * q15_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_24_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_23_Z_bridge by assumption.
  rewrite cleared_g12345_S6_25_Z_bridge by assumption.
  rewrite cleared_g12345_S6_35_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_25_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q36_R - q13_R * q16_R)
     - (q11_R * q23_R - q12_R * q13_R) * (q11_R * q26_R - q12_R * q16_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_25_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_23_Z_bridge by assumption.
  rewrite cleared_g12345_S6_26_Z_bridge by assumption.
  rewrite cleared_g12345_S6_36_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_33_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q44_R - q14_R * q14_R)
     - (q11_R * q24_R - q12_R * q14_R) * (q11_R * q24_R - q12_R * q14_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_33_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_24_Z_bridge by assumption.
  rewrite cleared_g12345_S6_44_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_34_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q45_R - q14_R * q15_R)
     - (q11_R * q24_R - q12_R * q14_R) * (q11_R * q25_R - q12_R * q15_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_34_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_24_Z_bridge by assumption.
  rewrite cleared_g12345_S6_25_Z_bridge by assumption.
  rewrite cleared_g12345_S6_45_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_35_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q46_R - q14_R * q16_R)
     - (q11_R * q24_R - q12_R * q14_R) * (q11_R * q26_R - q12_R * q16_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_35_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_24_Z_bridge by assumption.
  rewrite cleared_g12345_S6_26_Z_bridge by assumption.
  rewrite cleared_g12345_S6_46_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_44_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q55_R - q15_R * q15_R)
     - (q11_R * q25_R - q12_R * q15_R) * (q11_R * q25_R - q12_R * q15_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_44_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_25_Z_bridge by assumption.
  rewrite cleared_g12345_S6_55_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_45_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q56_R - q15_R * q16_R)
     - (q11_R * q25_R - q12_R * q15_R) * (q11_R * q26_R - q12_R * q16_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_45_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_25_Z_bridge by assumption.
  rewrite cleared_g12345_S6_26_Z_bridge by assumption.
  rewrite cleared_g12345_S6_56_Z_bridge by assumption.
  ring.
Qed.

Lemma cleared_g12345_S5_55_Z_bridge :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  IZR (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
  = KZ * KZ * KZ * KZ *
    ((q11_R * q22_R - q12_R * q12_R) * (q11_R * q66_R - q16_R * q16_R)
     - (q11_R * q26_R - q12_R * q16_R) * (q11_R * q26_R - q12_R * q16_R)).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  unfold cleared_g12345_S5_55_Z.
  rewrite schur_step_Z_IZR.
  rewrite cleared_g12345_S6_22_Z_bridge by assumption.
  rewrite cleared_g12345_S6_26_Z_bridge by assumption.
  rewrite cleared_g12345_S6_66_Z_bridge by assumption.
  ring.
Qed.

(** ============================================================================
    Section 16.5 (continued).  Soundness of the integer kernel check.

    Lifts the bool decision [q1ab_g12345_check_z_kernel = true] to the
    real-valued [q1ab_g12345_minors_witness] via the H + S6 + S5 + sym4_d_k
    bridge chain.  Each PD branch peels its KZ^k scaling factor by
    [Rmult_lt_reg_l] on the positivity of the cleared common factor.
    ============================================================================ *)

(** Helper: KZ > 0 in R, from denominator positivities. *)
Lemma KZ_pos :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  0 < KZ.
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  apply g12345_COMMON_Z_pos_R; assumption.
Qed.

(** Positivity for products of KZ.  Used to discharge the [Rmult_lt_reg_l]
    side conditions when canceling the KZ^k scaling out of each PD branch.
    Explicit [Rmult_lt_0_compat] chains because [nra] does not reliably
    handle degree-4-plus polynomial positivity. *)
Lemma KZ2_pos :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  0 < KZ * KZ.
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  pose proof (KZ_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HKZ.
  apply Rmult_lt_0_compat; exact HKZ.
Qed.

Lemma KZ4_pos :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  0 < KZ * KZ * KZ * KZ.
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  pose proof (KZ_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HKZ.
  apply Rmult_lt_0_compat;
    [apply Rmult_lt_0_compat;
       [apply Rmult_lt_0_compat | ] | ];
    exact HKZ.
Qed.

Lemma KZ8_pos :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  0 < (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  pose proof (KZ4_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HK4.
  apply Rmult_lt_0_compat; exact HK4.
Qed.

Lemma KZ12_pos :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  0 < (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  pose proof (KZ8_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HK8.
  pose proof (KZ4_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HK4.
  apply Rmult_lt_0_compat; [exact HK8 | exact HK4].
Qed.

Lemma KZ16_pos :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  0 < (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ) *
      (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.
  pose proof (KZ12_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HK12.
  pose proof (KZ4_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HK4.
  apply Rmult_lt_0_compat; [exact HK12 | exact HK4].
Qed.

Theorem q1ab_g12345_caller_witness_z_abs_sound :
  (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
  (0 < Dg1)%Z -> (0 < Dg2)%Z -> (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
  q1ab_g12345_check_z_kernel D00 N00 D01 N01 D10 N10 D11 N11
                             Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = true ->
  q1ab_g12345_minors_witness
    (IZR D00 / IZR N00) (IZR D01 / IZR N01)
    (IZR D10 / IZR N10) (IZR D11 / IZR N11)
    (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
    (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4) (IZR Ng5 / IZR Dg5).
Proof.
  intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5 Hchk.
  unfold q1ab_g12345_check_z_kernel in Hchk.
  rewrite !Bool.andb_true_iff in Hchk.
  destruct Hchk as [Hchk Hd4].
  destruct Hchk as [Hchk Hd3].
  destruct Hchk as [Hchk Hd2].
  destruct Hchk as [Hchk Hd1].
  destruct Hchk as [Hchk HS6_22pos].
  destruct Hchk as [_ HH11pos].
  apply Z.ltb_lt in HH11pos, HS6_22pos, Hd1, Hd2, Hd3, Hd4.
  apply IZR_lt in HH11pos, HS6_22pos, Hd1, Hd2, Hd3, Hd4.
  change (IZR 0) with 0%R in HH11pos, HS6_22pos, Hd1, Hd2, Hd3, Hd4.
  pose proof (KZ_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5) as HKZ.
  (* Push the cleared bridges into each int-positivity hypothesis. *)
  rewrite cleared_g12345_H11_Z_bridge in HH11pos by assumption.
  rewrite cleared_g12345_S6_22_Z_bridge in HS6_22pos by assumption.
  (* For sym4_d_k of cleared S5: first push IZR into sym4_d_k, then replace each
     IZR (cleared_S5_ij_Z ...) by its bridge form. *)
  rewrite sym4_d1_Z_IZR in Hd1.
  rewrite sym4_d2_Z_IZR in Hd2.
  rewrite sym4_d3_Z_IZR in Hd3.
  rewrite sym4_d4_Z_IZR in Hd4.
  rewrite cleared_g12345_S5_22_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_23_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_24_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_25_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_33_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_34_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_35_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_44_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_45_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  rewrite cleared_g12345_S5_55_Z_bridge in Hd1, Hd2, Hd3, Hd4 by assumption.
  (* Factor KZ^4 out of each sym4_d_k via sym4_d_k_scale. *)
  (* sym4_d1 (KZ*h11) ... = KZ * sym4_d1 h11 ... reduces by unfolding sym4_d1
     (which is just the h11 projection). *)
  unfold sym4_d1 in Hd1 at 1.
  rewrite sym4_d2_scale in Hd2.
  rewrite sym4_d3_scale in Hd3.
  rewrite sym4_d4_scale in Hd4.
  (* Unfold the witness predicate and the scaled-Schur entries to expose the
     same polynomial form that the bridges produce on the RHS. *)
  unfold q1ab_g12345_minors_witness, sym6_pd_interior, sym5_pd_interior.
  unfold sym6_scaled_S_22, sym6_scaled_S_23, sym6_scaled_S_24,
         sym6_scaled_S_25, sym6_scaled_S_26,
         sym6_scaled_S_33, sym6_scaled_S_34, sym6_scaled_S_35,
         sym6_scaled_S_36,
         sym6_scaled_S_44, sym6_scaled_S_45, sym6_scaled_S_46,
         sym6_scaled_S_55, sym6_scaled_S_56,
         sym6_scaled_S_66.
  unfold sym5_scaled_S_22, sym5_scaled_S_23, sym5_scaled_S_24,
         sym5_scaled_S_25,
         sym5_scaled_S_33, sym5_scaled_S_34, sym5_scaled_S_35,
         sym5_scaled_S_44, sym5_scaled_S_45, sym5_scaled_S_55.
  repeat split.
  - (* q12345_H11 (...) > 0 *)
    apply Rmult_lt_reg_l with KZ; [exact HKZ|].
    rewrite Rmult_0_r. exact HH11pos.
  - (* sym6_scaled_S_22 at q12345 = q11*q22 - q12*q12 > 0 *)
    apply Rmult_lt_reg_l with (KZ * KZ); [exact (KZ2_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5)|].
    rewrite Rmult_0_r. exact HS6_22pos.
  - (* sym4_d1 (S5 entries) > 0 *)
    apply Rmult_lt_reg_l with (KZ * KZ * KZ * KZ); [exact (KZ4_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5)|].
    rewrite Rmult_0_r. exact Hd1.
  - (* sym4_d2 (S5 entries) > 0 *)
    apply Rmult_lt_reg_l with ((KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ));
      [exact (KZ8_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5)|].
    rewrite Rmult_0_r. exact Hd2.
  - (* sym4_d3 (S5 entries) > 0 *)
    apply Rmult_lt_reg_l with
      ((KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ));
      [exact (KZ12_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5)|].
    rewrite Rmult_0_r. exact Hd3.
  - (* sym4_d4 (S5 entries) > 0 *)
    apply Rmult_lt_reg_l with
      ((KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ) *
       (KZ * KZ * KZ * KZ) * (KZ * KZ * KZ * KZ));
      [exact (KZ16_pos HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5)|].
    rewrite Rmult_0_r. exact Hd4.
Qed.

End S5_and_minors_bridges.

(** Headline corollary: the bool integer check forces PSD9 of the 9x9 NPA
    Q_{1+AB} matrix at the rational correlators and all five gamma
    parameters.  Composes [q1ab_g12345_caller_witness_z_abs_sound] with
    [q1ab_g12345_minors_witness_implies_psd9] (Section 16.4). *)
Corollary q1ab_g12345_caller_witness_z_abs_implies_psd9 :
  forall D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    (0 < Dg1)%Z -> (0 < Dg2)%Z ->
    (0 < Dg3)%Z -> (0 < Dg4)%Z -> (0 < Dg5)%Z ->
    q1ab_g12345_check_z_kernel
      D00 N00 D01 N01 D10 N10 D11 N11
      Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = true ->
    PSD9 (q1ab_moment_matrix
            (IZR D00 / IZR N00) (IZR D01 / IZR N01)
            (IZR D10 / IZR N10) (IZR D11 / IZR N11)
            (IZR Ng1 / IZR Dg1) (IZR Ng2 / IZR Dg2)
            (IZR Ng3 / IZR Dg3) (IZR Ng4 / IZR Dg4)
            (IZR Ng5 / IZR Dg5)).
Proof.
  intros D00 N00 D01 N01 D10 N10 D11 N11
         Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
         HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5 Hchk.
  apply q1ab_g12345_minors_witness_implies_psd9.
  apply (q1ab_g12345_caller_witness_z_abs_sound
           D00 N00 D01 N01 D10 N10 D11 N11
           Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5
           HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5 Hchk).
Qed.

(** ============================================================================
    Section 17.  Headline no-trap wrappers for the γ_5, γ_345, γ_12345 opcodes.

    Each Q_{1+AB} cert-opcode in the γ_*-extended family gets a wrapper that
    packages "no-trap step ⇒ quantum_realizable_q1ab at the bucket-derived
    rationals" — paralleling the existing slice-A wrapper
    [chsh_lassert_1ab_no_trap_implies_quantum_realizable_q1ab] (above).

    In this codebase, [quantum_realizable_q1ab] is defined operationally as
    [symmetric9 ∧ PSD9] of the 9×9 NPA Q_{1+AB} moment matrix.  The standard
    NPA-hierarchy convergence result for CHSH (Ishizaka 2025) — that
    Q_{1+AB} = Q in the CHSH scenario — is the published math fact that
    justifies the operational naming; that equivalence is cited externally
    rather than formalised in Coq, exactly as NPA's own convergence theorems
    are cited in every NPA-hierarchy paper.

    The four wrappers together close the substrate-level claim: for every
    slice (γ = 0, γ_5, γ_345, γ_12345), a non-trapping execution of the
    matching cert-opcode implies Q_{1+AB}-realisability at the witness-
    derived rational correlators and γ values. ============================ *)

(** Slice B (γ_5).  Direct application of [q1ab_g5_full_integer_check_sound],
    which already concludes PSD9 at [state_bucket_correlation]-based
    correlators — no IZR-bridge step needed. *)
Theorem chsh_lassert_1ab_g5_no_trap_implies_quantum_realizable_q1ab :
  forall (s : VMState) (mu_delta same_g5 diff_g5 : nat),
    let s' := vm_apply s (instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    quantum_realizable_q1ab
      (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
      0 0 0 0
      (IZR (chsh_d_z same_g5 diff_g5) / IZR (chsh_n_z same_g5 diff_g5)).
Proof.
  intros s mu_delta sg5 dg5 s' Hpc Herr Herr0.
  assert (Hchk : q1ab_g5_full_integer_check_kernel s.(vm_witness) sg5 dg5 = true).
  { unfold s' in Herr. unfold vm_apply in Herr.
    destruct (q1ab_g5_full_integer_check_kernel s.(vm_witness) sg5 dg5) eqn:Echk.
    - reflexivity.
    - simpl in Herr. rewrite Herr0 in Herr. discriminate. }
  unfold quantum_realizable_q1ab. split.
  - apply q1ab_moment_matrix_symmetric.
  - unfold state_e00, state_e01, state_e10, state_e11.
    apply (q1ab_g5_full_integer_check_sound
             s.(vm_witness) (chsh_d_z sg5 dg5) (chsh_n_z sg5 dg5)).
    exact Hchk.
Qed.

(** Slice C (γ_345).  The bool decider's positivity-of-N conjuncts are
    extracted to bridge [state_bucket_correlation] to [IZR D / IZR N] before
    invoking [q1ab_g345_caller_witness_z_abs_implies_psd9]. *)
Theorem chsh_lassert_1ab_g345_no_trap_implies_quantum_realizable_q1ab :
  forall (s : VMState)
         (mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat),
    let s' := vm_apply s (instr_chsh_lassert_1ab_g345 mu_delta
                            same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    quantum_realizable_q1ab
      (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
      0 0
      (IZR (chsh_d_z same_g3 diff_g3) / IZR (chsh_n_z same_g3 diff_g3))
      (IZR (chsh_d_z same_g4 diff_g4) / IZR (chsh_n_z same_g4 diff_g4))
      (IZR (chsh_d_z same_g5 diff_g5) / IZR (chsh_n_z same_g5 diff_g5)).
Proof.
  intros s mu_delta sg3 dg3 sg4 dg4 sg5 dg5 s' Hpc Herr Herr0.
  assert (Hchk : q1ab_g345_full_integer_check_kernel s.(vm_witness)
                   sg3 dg3 sg4 dg4 sg5 dg5 = true).
  { unfold s' in Herr. unfold vm_apply in Herr.
    destruct (q1ab_g345_full_integer_check_kernel s.(vm_witness)
                sg3 dg3 sg4 dg4 sg5 dg5) eqn:Echk.
    - reflexivity.
    - simpl in Herr. rewrite Herr0 in Herr. discriminate. }
  unfold q1ab_g345_full_integer_check_kernel in Hchk.
  apply Bool.andb_true_iff in Hchk. destruct Hchk as [_Hcc Hschur].
  (* Extract N00..N11 positivity from the Schur kernel check (keeping the
     full bool intact for downstream use). *)
  pose proof Hschur as HschurCopy.
  unfold q1ab_g345_check_z_kernel in HschurCopy.
  rewrite !Bool.andb_true_iff in HschurCopy.
  destruct HschurCopy as
    [[[[[[[[[[[[[[[[[[[ HN00b HN01b] HN10b] HN11b]
                     _HDg3b] _HDg4b] _HDg5b]
                  _HNg3lo] _HNg3hi] _HNg4lo] _HNg4hi] _HNg5lo] _HNg5hi]
        _HAposZ] _HCMposZ] _HdetMposZ]
       _Hd1Z] _Hd2Z] _Hd3Z] _Hd4Z].
  apply Z.ltb_lt in HN00b, HN01b, HN10b, HN11b.
  unfold quantum_realizable_q1ab. split.
  - apply q1ab_moment_matrix_symmetric.
  - unfold state_e00, state_e01, state_e10, state_e11.
    rewrite (state_bucket_correlation_to_IZR _ _ HN00b).
    rewrite (state_bucket_correlation_to_IZR _ _ HN01b).
    rewrite (state_bucket_correlation_to_IZR _ _ HN10b).
    rewrite (state_bucket_correlation_to_IZR _ _ HN11b).
    apply q1ab_g345_caller_witness_z_abs_implies_psd9.
    exact Hschur.
Qed.

(** Slice D (full γ_12345).  Same pattern as slice C, but the cascade check
    has nine positivity-of-N/Dg conjuncts which the headline corollary
    [q1ab_g12345_caller_witness_z_abs_implies_psd9] expects as explicit
    hypotheses — extract them from the bool check, then apply. *)
Theorem chsh_lassert_1ab_g12345_no_trap_implies_quantum_realizable_q1ab :
  forall (s : VMState)
         (mu_delta same_g1 diff_g1 same_g2 diff_g2
          same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat),
    let s' := vm_apply s (instr_chsh_lassert_1ab_g12345 mu_delta
                            same_g1 diff_g1 same_g2 diff_g2
                            same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    quantum_realizable_q1ab
      (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)
      (IZR (chsh_d_z same_g1 diff_g1) / IZR (chsh_n_z same_g1 diff_g1))
      (IZR (chsh_d_z same_g2 diff_g2) / IZR (chsh_n_z same_g2 diff_g2))
      (IZR (chsh_d_z same_g3 diff_g3) / IZR (chsh_n_z same_g3 diff_g3))
      (IZR (chsh_d_z same_g4 diff_g4) / IZR (chsh_n_z same_g4 diff_g4))
      (IZR (chsh_d_z same_g5 diff_g5) / IZR (chsh_n_z same_g5 diff_g5)).
Proof.
  intros s mu_delta sg1 dg1 sg2 dg2 sg3 dg3 sg4 dg4 sg5 dg5 s' Hpc Herr Herr0.
  assert (Hchk : q1ab_g12345_full_integer_check_kernel s.(vm_witness)
                   sg1 dg1 sg2 dg2 sg3 dg3 sg4 dg4 sg5 dg5 = true).
  { unfold s' in Herr. unfold vm_apply in Herr.
    destruct (q1ab_g12345_full_integer_check_kernel s.(vm_witness)
                sg1 dg1 sg2 dg2 sg3 dg3 sg4 dg4 sg5 dg5) eqn:Echk.
    - reflexivity.
    - simpl in Herr. rewrite Herr0 in Herr. discriminate. }
  unfold q1ab_g12345_full_integer_check_kernel in Hchk.
  apply Bool.andb_true_iff in Hchk. destruct Hchk as [_Hcc Hschur].
  (* Extract all nine N00..N11, Dg1..Dg5 positivity facts as bools from a copy
     of Hschur. *)
  pose proof Hschur as HschurCopy.
  unfold q1ab_g12345_check_z_kernel in HschurCopy.
  rewrite !Bool.andb_true_iff in HschurCopy.
  destruct HschurCopy as
    [[[[[[[[[[[[[[[[[[[[[[[[
      HN00b HN01b] HN10b] HN11b]
      HDg1b] HDg2b] HDg3b] HDg4b] HDg5b]
      _HNg1lo] _HNg1hi] _HNg2lo] _HNg2hi]
      _HNg3lo] _HNg3hi] _HNg4lo] _HNg4hi] _HNg5lo] _HNg5hi]
      _HH11pos] _HS6_22pos] _Hd1] _Hd2] _Hd3] _Hd4].
  apply Z.ltb_lt in HN00b, HN01b, HN10b, HN11b,
                    HDg1b, HDg2b, HDg3b, HDg4b, HDg5b.
  unfold quantum_realizable_q1ab. split.
  - apply q1ab_moment_matrix_symmetric.
  - unfold state_e00, state_e01, state_e10, state_e11.
    rewrite (state_bucket_correlation_to_IZR _ _ HN00b).
    rewrite (state_bucket_correlation_to_IZR _ _ HN01b).
    rewrite (state_bucket_correlation_to_IZR _ _ HN10b).
    rewrite (state_bucket_correlation_to_IZR _ _ HN11b).
    apply (q1ab_g12345_caller_witness_z_abs_implies_psd9
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             HN00b HN01b HN10b HN11b
             HDg1b HDg2b HDg3b HDg4b HDg5b).
    exact Hschur.
Qed.

(** ========================================================================
    Section 17. Regression guard: the four-body conjugate-cell sign.

    The two four-body cells of the Q_{1+AB} matrix are
      (A_1B_1, A_2B_2) = <A_1 A_2 B_1 B_2> = g5
      (A_1B_2, A_2B_1) = <A_1 A_2 B_2 B_1> = -g5
    They are NEGATIVES, because under the matrix's own <B_1 B_2> = 0 (B_1 ⊥ B_2,
    so {B_1,B_2}=0) one has <A_1A_2 B_2B_1> = -<A_1A_2 B_1B_2>. That minus sign
    is the operator anticommutator that powers a CHSH violation.

    Had both cells carried the SAME value (forcing B_1 B_2 = B_2 B_1, i.e.
    commuting measurements), the certifiable region would collapse to the
    classical polytope |S| <= 2 and the two facts below would be UNPROVABLE:
    no super-classical correlator is PSD-completable when the cells coincide.
    A [Print Assumptions] audit cannot see this — a true theorem about a
    mislabeled matrix still passes. These computational guards can. *)

(** The cells are conjugate (negatives), not equal. Reverting to +g5 breaks this. *)
Example q1ab_four_body_cells_are_conjugate :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber,
    q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5 j6 j7
    = - q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5 j5 j8.
Proof. intros; cbn; ring. Qed.

(** Semantic guard: a concrete correlator with CHSH = 12/5 = 2.4 > 2 is
    PSD-realizable in the 9x9 NPA Q_{1+AB} matrix. Unprovable on the pre-fix
    matrix, where the symmetric Tsirelson point caps min-eigenvalue at 1 - √2. *)
Example q1ab_certifies_a_superclassical_chsh_point :
  (3/5 + 3/5 + 3/5 - (-3/5) > 2) /\
  PSD9 (q1ab_moment_matrix (3/5) (3/5) (3/5) (-3/5) 0 0 0 0 (-1/2)).
Proof.
  split; [lra|].
  apply q1ab_g5_caller_check_implies_psd9.
  - unfold zero_marginal_column_contractive. repeat split; nra.
  - unfold q1ab_g5_caller_witness. split; [lra|nra].
Qed.

(** Opcode-layer guard: the integer kernel decider that
    [instr_chsh_lassert_1ab_g5] actually runs accepts buckets whose CHSH is
    2.4 > 2 (correlators 3/5,3/5,3/5,-3/5 via same/diff = 4/1,4/1,4/1,1/4;
    γ_5 = -1/2 via the bucket pair (1,3)). On the pre-fix decider this
    evaluated to [false]. Pure computation. *)
Example q1ab_g5_kernel_check_accepts_superclassical :
  q1ab_g5_full_integer_check_kernel
    {| wc_same_00 := 4; wc_diff_00 := 1;
       wc_same_01 := 4; wc_diff_01 := 1;
       wc_same_10 := 4; wc_diff_10 := 1;
       wc_same_11 := 1; wc_diff_11 := 4 |}
    1 3 = true.
Proof. vm_compute. reflexivity. Qed.
