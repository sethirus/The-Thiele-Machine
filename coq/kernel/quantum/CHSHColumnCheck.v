(** CHSHColumnCheck: an integer check on CHSH trial counts that implies the
    correlators sit inside the quantum set's zero-marginal slice.

    A CHSH experiment records, for each of the four setting pairs, how many
    trials gave the same outcome and how many gave different outcomes. From
    those eight counts come four correlators [E_xy = (same - diff) / (same +
    diff)]. This file proves three things, with no machine in them.

    - The zero-marginal NPA moment matrix built from four correlators is
      positive semidefinite exactly when the correlators are column
      contractive: two column-norm inequalities and one determinant
      inequality ([column_contractive_iff_npa_psd]).
    - [column_contractive_check_witness] decides those three inequalities on
      the eight counts in integer arithmetic, after clearing the positive
      denominators. If it returns true, the correlators are column
      contractive ([column_contractive_check_witness_sound]), so the NPA
      matrix is positive semidefinite ([column_contractive_check_witness_npa_psd]).
    - [sum_E_sq_check_witness] decides, the same way, that the four squared
      correlators sum to at most one.

    The physical reading, that a positive semidefinite NPA matrix is what
    measurements on a quantum state can produce, comes from the NPA
    hierarchy and is cited, not proved here. *)

From Coq.Vectors Require Import Fin.
From Coq Require Import List Reals QArith Psatz Field ZArith Bool.
Import ListNotations.

From Kernel Require Import ConstructivePSD.
From Kernel Require Import NPAMomentMatrix.

(** * Trial counts *)

(** [WitnessCounts] stores same/different outcome counts for each of the four setting pairs. *)
Record WitnessCounts := {
  wc_same_00 : nat; wc_diff_00 : nat;
  wc_same_01 : nat; wc_diff_01 : nat;
  wc_same_10 : nat; wc_diff_10 : nat;
  wc_same_11 : nat; wc_diff_11 : nat
}.

Definition witness_counts_zero : WitnessCounts :=
  {| wc_same_00 := 0; wc_diff_00 := 0;
     wc_same_01 := 0; wc_diff_01 := 0;
     wc_same_10 := 0; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 0 |}.

Definition witness_total (wc : WitnessCounts) : nat :=
  wc.(wc_same_00) + wc.(wc_diff_00) +
  wc.(wc_same_01) + wc.(wc_diff_01) +
  wc.(wc_same_10) + wc.(wc_diff_10) +
  wc.(wc_same_11) + wc.(wc_diff_11).

(** * The integer checks *)

(** ** Column-contractivity check on the CHSH WitnessCounts buckets

    For each setting pair (x,y) ∈ {0,1}² the WitnessCounts hold a [same] and a
    [diff] bucket. The signed difference [d_xy = same_xy - diff_xy] and the
    sum [n_xy = same_xy + diff_xy] (both interpreted in Z) determine the
    correlator [E_xy = d_xy / n_xy] (in R). The three column-contractivity
    conditions on the correlators
       1 - E_00^2 - E_10^2 >= 0
       1 - E_01^2 - E_11^2 >= 0
       (1 - E_00^2 - E_10^2)(1 - E_01^2 - E_11^2) >= (E_00*E_01 + E_10*E_11)^2
    are equivalent (after clearing denominators by the positive
    [n_00^2*n_01^2*n_10^2*n_11^2]) to three Z-arithmetic inequalities
       A := n_00^2 * n_10^2 - d_00^2 * n_10^2 - d_10^2 * n_00^2 >= 0
       B := n_01^2 * n_11^2 - d_01^2 * n_11^2 - d_11^2 * n_01^2 >= 0
       A * B >= C^2,  where C := d_00*d_01*n_10*n_11 + d_10*d_11*n_00*n_01
    Each n_xy must also be strictly positive (a correlator needs at least
    one trial per setting pair). The check function below is decidable and
    uses only integer arithmetic.

    The bridge theorem below is
    [column_contractive_check_witness_sound]:
        column_contractive_check_witness wc = true
          -> zero_marginal_column_contractive (E_00 wc) (E_01 wc) (E_10 wc) (E_11 wc)
    which combined with [column_contractive_iff_npa_psd]
    (below) gives NPA-PSD on the witness-derived correlators
    whenever the check passes.
*)

Definition chsh_d_z (same diff : nat) : Z :=
  (Z.of_nat same - Z.of_nat diff)%Z.

Definition chsh_n_z (same diff : nat) : Z :=
  (Z.of_nat same + Z.of_nat diff)%Z.

Definition column_contractive_check_witness (wc : WitnessCounts) : bool :=
  let d00 := chsh_d_z wc.(wc_same_00) wc.(wc_diff_00) in
  let n00 := chsh_n_z wc.(wc_same_00) wc.(wc_diff_00) in
  let d01 := chsh_d_z wc.(wc_same_01) wc.(wc_diff_01) in
  let n01 := chsh_n_z wc.(wc_same_01) wc.(wc_diff_01) in
  let d10 := chsh_d_z wc.(wc_same_10) wc.(wc_diff_10) in
  let n10 := chsh_n_z wc.(wc_same_10) wc.(wc_diff_10) in
  let d11 := chsh_d_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n11 := chsh_n_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n00sq := (n00 * n00)%Z in
  let n01sq := (n01 * n01)%Z in
  let n10sq := (n10 * n10)%Z in
  let n11sq := (n11 * n11)%Z in
  let d00sq := (d00 * d00)%Z in
  let d01sq := (d01 * d01)%Z in
  let d10sq := (d10 * d10)%Z in
  let d11sq := (d11 * d11)%Z in
  let A := (n00sq * n10sq - d00sq * n10sq - d10sq * n00sq)%Z in
  let B := (n01sq * n11sq - d01sq * n11sq - d11sq * n01sq)%Z in
  let C := (d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01)%Z in
  andb (Z.ltb 0 n00)
  (andb (Z.ltb 0 n01)
  (andb (Z.ltb 0 n10)
  (andb (Z.ltb 0 n11)
  (andb (Z.leb 0 A)
  (andb (Z.leb 0 B)
        (Z.leb (C * C) (A * B))))))).

(** ** Q_{1+AB} integer check: sum-of-squares bound on the four correlators

    Verifies, in pure Z arithmetic, the additional condition
       E_{00}^2 + E_{01}^2 + E_{10}^2 + E_{11}^2 <= 1
    by clearing denominators. With N_xy = same+diff and D_xy = same-diff,
    the cleared inequality is
       D_00^2 * N_01^2 * N_10^2 * N_11^2
       + N_00^2 * D_01^2 * N_10^2 * N_11^2
       + N_00^2 * N_01^2 * D_10^2 * N_11^2
       + N_00^2 * N_01^2 * N_10^2 * D_11^2
       <=  N_00^2 * N_01^2 * N_10^2 * N_11^2.

    The combined Q_{1+AB} check is
    the conjunction of [column_contractive_check_witness] and
    [sum_E_sq_check_witness]. Soundness for the column-contractive
    predicate at γ = 0 is proved in QuantumPartitionPSD_1AB.v. *)

Definition sum_E_sq_check_witness (wc : WitnessCounts) : bool :=
  let d00 := chsh_d_z wc.(wc_same_00) wc.(wc_diff_00) in
  let n00 := chsh_n_z wc.(wc_same_00) wc.(wc_diff_00) in
  let d01 := chsh_d_z wc.(wc_same_01) wc.(wc_diff_01) in
  let n01 := chsh_n_z wc.(wc_same_01) wc.(wc_diff_01) in
  let d10 := chsh_d_z wc.(wc_same_10) wc.(wc_diff_10) in
  let n10 := chsh_n_z wc.(wc_same_10) wc.(wc_diff_10) in
  let d11 := chsh_d_z wc.(wc_same_11) wc.(wc_diff_11) in
  let n11 := chsh_n_z wc.(wc_same_11) wc.(wc_diff_11) in
  let den := (n00 * n01 * n10 * n11)%Z in
  let den_sq := (den * den)%Z in
  let term00 := (d00 * d00 * n01 * n01 * n10 * n10 * n11 * n11)%Z in
  let term01 := (n00 * n00 * d01 * d01 * n10 * n10 * n11 * n11)%Z in
  let term10 := (n00 * n00 * n01 * n01 * d10 * d10 * n11 * n11)%Z in
  let term11 := (n00 * n00 * n01 * n01 * n10 * n10 * d11 * d11)%Z in
  Z.leb (term00 + term01 + term10 + term11) den_sq.

Definition column_contractive_check_q1ab_kernel (wc : WitnessCounts) : bool :=
  andb (column_contractive_check_witness wc)
       (sum_E_sq_check_witness wc).

(** ** Q_{1+AB} γ_5-aware integer check (abstract on signed correlators).

    Pure Z-arithmetic decider on (D_xy, N_xy, Ng5, Dg5) where:
      D_xy = (same - diff) in Z, N_xy = (same + diff) in Z (Q_1 buckets)
      g_5 = IZR Ng5 / IZR Dg5  with strict |Ng5| < Dg5

    Verifies:
      (a) every N_xy > 0,
      (b) Dg5 > 0 and -Dg5 < Ng5 < Dg5 (so |g_5| < 1 strictly),
      (c) the cleared SOS-witness polynomial inequality
            Dg5*(Dg5 - Ng5)*X_int + Dg5*(Dg5 + Ng5)*Y_int
            <= 2*(Dg5² - Ng5²)*Den2
          where X_int, Y_int, Den2 are integer-built squared sums and
          the denominator product.

    Soundness (in QuantumPartitionPSD_1AB.v): passing this check implies
    PSD9 of the 9x9 NPA Q_{1+AB} matrix at (E, 0, 0, 0, 0, g_5) when
    combined with column_contractive_check_witness for the (E_ij) part. *)
Definition q1ab_g5_check_z_kernel
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

(** Composite Q_{1+AB} γ_5 integer check on a [WitnessCounts] and a γ_5
    nat bucket pair (same_g5, diff_g5). Reads the four CHSH correlator
    buckets from wc, the γ_5 numerator/denominator from the bucket pair,
    and conjoins the existing column_contractive_check_witness with the
    γ_5 SOS check. *)
Definition q1ab_g5_full_integer_check_kernel
  (wc : WitnessCounts) (same_g5 diff_g5 : nat) : bool :=
  let Ng5 := chsh_d_z same_g5 diff_g5 in
  let Dg5 := chsh_n_z same_g5 diff_g5 in
  andb (column_contractive_check_witness wc)
       (q1ab_g5_check_z_kernel
          (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
          (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
          Ng5 Dg5).

(** ** Q_{1+AB} γ_{3,4,5} integer check via 4×4 Sylvester PD.

    Z-arithmetic decider on (D_xy, N_xy, Ng3, Dg3, Ng4, Dg4, Ng5, Dg5). The
    extension over the γ_5-only check encodes the inner ∀v∈R^4 inequality
    of the Section-14 caller witness as positive-definiteness of a 4×4
    symmetric matrix H_{γ_345} = det_M·M_M − M_N. PD is verified by
    Sylvester's criterion (4 leading principal minors > 0 in cleared-Z
    form). Soundness in QuantumPartitionPSD_1AB.v Section 15. *)

(** Cleared (integer-numerator) versions of A, B, C_M, det_M. *)

Definition cleared_A_num (D00 N00 D10 N10 : Z) : Z :=
  (N00*N00*N10*N10 - D00*D00*N10*N10 - D10*D10*N00*N00)%Z.

Definition cleared_C_M_num (D01 N01 D11 N11 : Z) : Z :=
  (N01*N01*N11*N11 - D01*D01*N11*N11 - D11*D11*N01*N01)%Z.

Definition cleared_B_num (D00 N00 D01 N01 D10 N10 D11 N11 : Z) : Z :=
  (- (D00*D01*N10*N11 + D10*D11*N00*N01))%Z.

Definition cleared_det_M_num (D00 N00 D01 N01 D10 N10 D11 N11 : Z) : Z :=
  (cleared_A_num D00 N00 D10 N10 * cleared_C_M_num D01 N01 D11 N11
   - cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11
     * cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11)%Z.

(** Uniform common scaling factor: N_e^4 · D_g^2. *)
Definition COMMON_Z
  (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00*N00*N00*N00 * (N01*N01*N01*N01) * (N10*N10*N10*N10) * (N11*N11*N11*N11)
   * (Dg3*Dg3) * (Dg4*Dg4) * (Dg5*Dg5))%Z.

(** Per-entry cleared numerators (small Z polynomials, one per H_ij). *)

Definition cH11_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let A_n := cleared_A_num D00 N00 D10 N10 in
  (Dg3*Dg3 * detM * (N00*N00 - D00*D00)
   - N00*N00 * N01*N01 * N11*N11 * A_n * (Ng3*Ng3))%Z.

Definition cH22_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let CM_n := cleared_C_M_num D01 N01 D11 N11 in
  (Dg3*Dg3 * detM * (N01*N01 - D01*D01)
   - N00*N00 * N01*N01 * N10*N10 * CM_n * (Ng3*Ng3))%Z.

Definition cH33_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let A_n := cleared_A_num D00 N00 D10 N10 in
  (Dg4*Dg4 * detM * (N10*N10 - D10*D10)
   - N01*N01 * N10*N10 * N11*N11 * A_n * (Ng4*Ng4))%Z.

Definition cH44_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let CM_n := cleared_C_M_num D01 N01 D11 N11 in
  (Dg4*Dg4 * detM * (N11*N11 - D11*D11)
   - N00*N00 * N10*N10 * N11*N11 * CM_n * (Ng4*Ng4))%Z.

Definition cH12_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (- (Dg3*Dg3 * detM * D00 * D01)
   + N00*N00 * N01*N01 * N10 * N11 * B_n * (Ng3*Ng3))%Z.

Definition cH13_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let A_n := cleared_A_num D00 N00 D10 N10 in
  (- (Dg3 * Dg4 * detM * D00 * D10)
   - N00 * N01*N01 * N10 * N11*N11 * A_n * Ng3 * Ng4)%Z.

Definition cH14_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (N00 * N11 * Dg3 * Dg4 * detM * Ng5
   - Dg3 * Dg4 * Dg5 * detM * D00 * D11
   + N00*N00 * N01 * N10 * N11*N11 * Dg5 * B_n * Ng3 * Ng4)%Z.

Definition cH23_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (- (N01 * N10 * Dg3 * Dg4 * detM * Ng5)
   - Dg3 * Dg4 * Dg5 * detM * D01 * D10
   + N00 * N01*N01 * N10*N10 * N11 * Dg5 * B_n * Ng3 * Ng4)%Z.

Definition cH24_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let CM_n := cleared_C_M_num D01 N01 D11 N11 in
  (- (Dg3 * Dg4 * detM * D01 * D11)
   - N00*N00 * N01 * N10*N10 * N11 * CM_n * Ng3 * Ng4)%Z.

Definition cH34_per_entry (D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4 : Z) : Z :=
  let detM := cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11 in
  let B_n := cleared_B_num D00 N00 D01 N01 D10 N10 D11 N11 in
  (- (Dg4*Dg4 * detM * D10 * D11)
   + N00 * N01 * N10*N10 * N11*N11 * B_n * (Ng4*Ng4))%Z.

(** Multipliers (COMMON/scale_ij) lifting per-entry cH to uniform COMMON. *)
Definition mult_for_H11 (N01 N10 N11 Dg4 Dg5 : Z) : Z :=
  (N01*N01 * (N10*N10) * (N11*N11) * (Dg4*Dg4) * (Dg5*Dg5))%Z.
Definition mult_for_H22 (N00 N10 N11 Dg4 Dg5 : Z) : Z :=
  (N00*N00 * (N10*N10) * (N11*N11) * (Dg4*Dg4) * (Dg5*Dg5))%Z.
Definition mult_for_H33 (N00 N01 N11 Dg3 Dg5 : Z) : Z :=
  (N00*N00 * (N01*N01) * (N11*N11) * (Dg3*Dg3) * (Dg5*Dg5))%Z.
Definition mult_for_H44 (N00 N01 N10 Dg3 Dg5 : Z) : Z :=
  (N00*N00 * (N01*N01) * (N10*N10) * (Dg3*Dg3) * (Dg5*Dg5))%Z.
Definition mult_for_H12 (N00 N01 N10 N11 Dg4 Dg5 : Z) : Z :=
  (N00 * N01 * (N10*N10) * (N11*N11) * (Dg4*Dg4) * (Dg5*Dg5))%Z.
Definition mult_for_H13 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00 * (N01*N01) * N10 * (N11*N11) * Dg3 * Dg4 * (Dg5*Dg5))%Z.
Definition mult_for_H14 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00 * (N01*N01) * (N10*N10) * N11 * Dg3 * Dg4 * Dg5)%Z.
Definition mult_for_H23 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00*N00 * N01 * N10 * (N11*N11) * Dg3 * Dg4 * Dg5)%Z.
Definition mult_for_H24 (N00 N01 N10 N11 Dg3 Dg4 Dg5 : Z) : Z :=
  (N00*N00 * N01 * (N10*N10) * N11 * Dg3 * Dg4 * (Dg5*Dg5))%Z.
Definition mult_for_H34 (N00 N01 N10 N11 Dg3 Dg5 : Z) : Z :=
  (N00*N00 * (N01*N01) * N10 * N11 * (Dg3*Dg3) * (Dg5*Dg5))%Z.

(** Cleared H entries (uniform COMMON scaling). *)
Definition cleared_H11_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H11 N01 N10 N11 Dg4 Dg5
   * cH11_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3)%Z.
Definition cleared_H22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H22 N00 N10 N11 Dg4 Dg5
   * cH22_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3)%Z.
Definition cleared_H33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H33 N00 N01 N11 Dg3 Dg5
   * cH33_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4)%Z.
Definition cleared_H44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H44 N00 N01 N10 Dg3 Dg5
   * cH44_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4)%Z.
Definition cleared_H12_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H12 N00 N01 N10 N11 Dg4 Dg5
   * cH12_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3)%Z.
Definition cleared_H13_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H13 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH13_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4)%Z.
Definition cleared_H14_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H14 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH14_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z.
Definition cleared_H23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H23 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH23_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z.
Definition cleared_H24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H24 N00 N01 N10 N11 Dg3 Dg4 Dg5
   * cH24_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4)%Z.
Definition cleared_H34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (mult_for_H34 N00 N01 N10 N11 Dg3 Dg5
   * cH34_per_entry D00 N00 D01 N01 D10 N10 D11 N11 Ng4 Dg4)%Z.

(** Z-arithmetic 4×4 leading principal minors. *)
Definition sym4_d1_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z := h11.
Definition sym4_d2_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z :=
  (h11*h22 - h12*h12)%Z.
Definition sym4_d3_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z :=
  (h11*(h22*h33 - h23*h23)
   - h12*(h12*h33 - h13*h23)
   + h13*(h12*h23 - h13*h22))%Z.
Definition sym4_d4_Z (h11 h12 h13 h14 h22 h23 h24 h33 h34 h44 : Z) : Z :=
  (h11*(h22*(h33*h44 - h34*h34) - h23*(h23*h44 - h24*h34) + h24*(h23*h34 - h24*h33))
   - h12*(h12*(h33*h44 - h34*h34) - h23*(h13*h44 - h14*h34) + h24*(h13*h34 - h14*h33))
   + h13*(h12*(h23*h44 - h24*h34) - h22*(h13*h44 - h14*h34) + h24*(h13*h24 - h14*h23))
   - h14*(h12*(h23*h34 - h24*h33) - h22*(h13*h34 - h14*h33) + h23*(h13*h24 - h14*h23)))%Z.

(** Composite cleared leading principal minors cd_k. *)
Definition cleared_d1
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d1_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).
Definition cleared_d2
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d2_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).
Definition cleared_d3
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d3_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).
Definition cleared_d4
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  sym4_d4_Z
    (cleared_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** Abstract Z-bool decider on 14 integer parameters. *)
Definition q1ab_g345_check_z_kernel
  (D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : bool :=
  ((0 <? N00)%Z)
  && ((0 <? N01)%Z)
  && ((0 <? N10)%Z)
  && ((0 <? N11)%Z)
  && ((0 <? Dg3)%Z)
  && ((0 <? Dg4)%Z)
  && ((0 <? Dg5)%Z)
  && ((-Dg3 <? Ng3)%Z) && ((Ng3 <? Dg3)%Z)
  && ((-Dg4 <? Ng4)%Z) && ((Ng4 <? Dg4)%Z)
  && ((-Dg5 <? Ng5)%Z) && ((Ng5 <? Dg5)%Z)
  && ((0 <? cleared_A_num D00 N00 D10 N10)%Z)
  && ((0 <? cleared_C_M_num D01 N01 D11 N11)%Z)
  && ((0 <? cleared_det_M_num D00 N00 D01 N01 D10 N10 D11 N11)%Z)
  && ((0 <? cleared_d1 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_d2 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_d3 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_d4 D00 N00 D01 N01 D10 N10 D11 N11 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z).

(** Composite Q_{1+AB} γ_{3,4,5} integer check on [WitnessCounts] plus three
    γ-bucket pairs. Reads (D,N) for the 4 CHSH correlators from the witness
    counters and (Ng,Dg) for γ_3, γ_4, γ_5 from the supplied bucket pairs. *)
Definition q1ab_g345_full_integer_check_kernel
  (wc : WitnessCounts)
  (same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat) : bool :=
  let Ng3 := chsh_d_z same_g3 diff_g3 in
  let Dg3 := chsh_n_z same_g3 diff_g3 in
  let Ng4 := chsh_d_z same_g4 diff_g4 in
  let Dg4 := chsh_n_z same_g4 diff_g4 in
  let Ng5 := chsh_d_z same_g5 diff_g5 in
  let Dg5 := chsh_n_z same_g5 diff_g5 in
  andb (column_contractive_check_witness wc)
       (q1ab_g345_check_z_kernel
          (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
          (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
          Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** ============================================================================
    Section 15.6. γ_{1,2,3,4,5} cleared-Z integer kernel (sym6 + Schur cascade).

    Lifts the real-valued [q1ab_g12345_minors_witness] (sym6_pd_interior at
    H_{γ_12345}) to a pure Z-arithmetic decision procedure. The cascade
    computes:

      - 21 cleared H_{ij}-numerators at uniform scaling
        [g12345_COMMON_Z] := (N00·N01·N10·N11·Dg1·Dg2·Dg3·Dg4·Dg5)²;
      - 15 cleared scaled_S_6 entries (4×4 Schur complement of row 1 of
        the sym6 H) at scaling g12345_COMMON_Z²;
      - 10 cleared scaled_S_5 entries (Schur of Schur: 4×4 Schur of row 1
        of the sym5 scaled_S_6) at scaling g12345_COMMON_Z⁴;
      - 4 sym4 Sylvester leading minors of the scaled_S_5 cleared values,
        at scaling g12345_COMMON_Z^(4·k) for k = 1..4.

    The kernel decider [q1ab_g12345_check_z_kernel] tests six positivities:
    cleared_H11 > 0, cleared_scaled_S_6_22 > 0, sym4_d_k of cleared
    scaled_S_5 > 0 for k = 1..4. Soundness in QuantumPartitionPSD_1AB.v
    Section 16.5. *)

(** Uniform common scaling factor for the 21-entry H_{γ_12345} matrix.
    All cleared H entries are at this scaling; cascade levels square it. *)
Definition g12345_COMMON_Z
  (N00 N01 N10 N11 Dg1 Dg2 Dg3 Dg4 Dg5 : Z) : Z :=
  (let P := (N00*N01*N10*N11*Dg1*Dg2*Dg3*Dg4*Dg5)%Z in P*P)%Z.

(** Cleared H_{ij}-numerators at scaling g12345_COMMON_Z. Each is
    [g12345_COMMON_Z · q12345_HXX(D00/N00, ..., Ng5/Dg5)] expressed as a
    pure Z polynomial. *)

Definition cleared_g12345_H11_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* g12345_COMMON_Z · (1 - (D00/N00)² - (D10/N10)²)
     = (N01·N11·Dg1·Dg2·Dg3·Dg4·Dg5)² · (N00²·N10² - D00²·N10² - D10²·N00²) *)
  ((N01*N11*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N01*N11*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N00*N00*N10*N10 - D00*D00*N10*N10 - D10*D10*N00*N00))%Z.

Definition cleared_g12345_H22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N10*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N00*N10*Dg1*Dg2*Dg3*Dg4*Dg5)
   * (N01*N01*N11*N11 - D01*D01*N11*N11 - D11*D11*N01*N01))%Z.

Definition cleared_g12345_H33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_33 = 1 - e00² - g1² = (Dg1²·N00² - Dg1²·D00² - Ng1²·N00²)/(N00²·Dg1²)
     COMMON·H_33 = (N01·N10·N11·Dg2·Dg3·Dg4·Dg5)² · (Dg1²·(N00² - D00²) - Ng1²·N00²) *)
  ((N01*N10*N11*Dg2*Dg3*Dg4*Dg5)
   * (N01*N10*N11*Dg2*Dg3*Dg4*Dg5)
   * (Dg1*Dg1*(N00*N00 - D00*D00) - Ng1*Ng1*N00*N00))%Z.

Definition cleared_g12345_H44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N10*N11*Dg1*Dg3*Dg4*Dg5)
   * (N00*N10*N11*Dg1*Dg3*Dg4*Dg5)
   * (Dg2*Dg2*(N01*N01 - D01*D01) - Ng2*Ng2*N01*N01))%Z.

Definition cleared_g12345_H55_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N01*N11*Dg2*Dg3*Dg4*Dg5)
   * (N00*N01*N11*Dg2*Dg3*Dg4*Dg5)
   * (Dg1*Dg1*(N10*N10 - D10*D10) - Ng1*Ng1*N10*N10))%Z.

Definition cleared_g12345_H66_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  ((N00*N01*N10*Dg1*Dg3*Dg4*Dg5)
   * (N00*N01*N10*Dg1*Dg3*Dg4*Dg5)
   * (Dg2*Dg2*(N11*N11 - D11*D11) - Ng2*Ng2*N11*N11))%Z.

Definition cleared_g12345_H12_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_12 = -(e00·e01 + e10·e11) = -(D00·D01·N10·N11 + D10·D11·N00·N01)/(N00·N01·N10·N11)
     COMMON·H_12 = -(N00·N01·N10·N11)·(Dg1·Dg2·Dg3·Dg4·Dg5)² · (numerator) *)
  ((N00*N01*N10*N11) * (Dg1*Dg2*Dg3*Dg4*Dg5) * (Dg1*Dg2*Dg3*Dg4*Dg5)
   * (-(D00*D01*N10*N11 + D10*D11*N00*N01)))%Z.

Definition cleared_g12345_H13_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_13 = -e10·g1 = -(D10·Ng1)/(N10·Dg1)
     COMMON·H_13 = -(N10·Dg1)·(N00·N01·N11·Dg1·Dg2·Dg3·Dg4·Dg5)·(N00·N01·N10·N11·Dg2·Dg3·Dg4·Dg5)·(D10·Ng1)
     Group: COMMON / (N10·Dg1) = N10·N00²·N01²·N11²·Dg1·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N11*N11*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D10*Ng1)))%Z.

Definition cleared_g12345_H14_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_14 = g3 - e10·g2 = (Ng3·N10·Dg2 - D10·Ng2·Dg3)/(N10·Dg2·Dg3)
     COMMON / (N10·Dg2·Dg3) = N10·N00²·N01²·N11²·Dg1²·Dg2·Dg3·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N11*N11*Dg1*Dg1*Dg2*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (Ng3*N10*Dg2 - D10*Ng2*Dg3))%Z.

Definition cleared_g12345_H15_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_15 = -e00·g1 = -(D00·Ng1)/(N00·Dg1)
     COMMON / (N00·Dg1) = N00·N01²·N10²·N11²·Dg1·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N01*N01*N10*N10*N11*N11*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D00*Ng1)))%Z.

Definition cleared_g12345_H16_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_16 = g4 - e00·g2 = (Ng4·N00·Dg2 - D00·Ng2·Dg4)/(N00·Dg2·Dg4)
     COMMON / (N00·Dg2·Dg4) = N00·N01²·N10²·N11²·Dg1²·Dg2·Dg3²·Dg4·Dg5² *)
  ((N00*N01*N01*N10*N10*N11*N11*Dg1*Dg1*Dg2*Dg3*Dg3*Dg4*Dg5*Dg5)
   * (Ng4*N00*Dg2 - D00*Ng2*Dg4))%Z.

Definition cleared_g12345_H23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_23 = g3 - e11·g1 = (Ng3·N11·Dg1 - D11·Ng1·Dg3)/(N11·Dg1·Dg3)
     COMMON / (N11·Dg1·Dg3) = N11·N00²·N01²·N10²·Dg1·Dg2²·Dg3·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N10*N11*Dg1*Dg2*Dg2*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (Ng3*N11*Dg1 - D11*Ng1*Dg3))%Z.

Definition cleared_g12345_H24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_24 = -e11·g2 = -(D11·Ng2)/(N11·Dg2)
     COMMON / (N11·Dg2) = N11·N00²·N01²·N10²·Dg1²·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N10*N11*Dg1*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D11*Ng2)))%Z.

Definition cleared_g12345_H25_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_25 = g4 - e01·g1 = (Ng4·N01·Dg1 - D01·Ng1·Dg4)/(N01·Dg1·Dg4)
     COMMON / (N01·Dg1·Dg4) = N01·N00²·N10²·N11²·Dg1·Dg2²·Dg3²·Dg4·Dg5² *)
  ((N00*N00*N01*N10*N10*N11*N11*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg5*Dg5)
   * (Ng4*N01*Dg1 - D01*Ng1*Dg4))%Z.

Definition cleared_g12345_H26_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_26 = -e01·g2 = -(D01·Ng2)/(N01·Dg2)
     COMMON / (N01·Dg2) = N01·N00²·N10²·N11²·Dg1²·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N10*N10*N11*N11*Dg1*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D01*Ng2)))%Z.

Definition cleared_g12345_H34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_34 = -(e00·e01 + g1·g2) = -(D00·D01·Dg1·Dg2 + Ng1·Ng2·N00·N01)/(N00·N01·Dg1·Dg2)
     COMMON / (N00·N01·Dg1·Dg2) = N00·N01·N10²·N11²·Dg1·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N01*N10*N10*N11*N11*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D00*D01*Dg1*Dg2 + Ng1*Ng2*N00*N01)))%Z.

Definition cleared_g12345_H35_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_35 = -e00·e10 = -(D00·D10)/(N00·N10)
     COMMON / (N00·N10) = N00·N01²·N10·N11²·Dg1²·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N01*N01*N10*N11*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D00*D10)))%Z.

Definition cleared_g12345_H36_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_36 = g5 - e00·e11 = (Ng5·N00·N11 - D00·D11·Dg5)/(N00·N11·Dg5)
     COMMON / (N00·N11·Dg5) = N00·N01²·N10²·N11·Dg1²·Dg2²·Dg3²·Dg4²·Dg5 *)
  ((N00*N01*N01*N10*N10*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5)
   * (Ng5*N00*N11 - D00*D11*Dg5))%Z.

Definition cleared_g12345_H45_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_45 = -g5 - e01·e10 = (-Ng5·N01·N10 - D01·D10·Dg5)/(N01·N10·Dg5)
     (the conjugate four-body cell ⟨A₁A₂B₂B₁⟩ = -⟨A₁A₂B₁B₂⟩; sign forced by
      {B₁,B₂}=0 under the matrix's ⟨B₁B₂⟩=0 assumption)
     COMMON / (N01·N10·Dg5) = N00²·N01·N10·N11²·Dg1²·Dg2²·Dg3²·Dg4²·Dg5 *)
  ((N00*N00*N01*N10*N11*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5)
   * (- Ng5*N01*N10 - D01*D10*Dg5))%Z.

Definition cleared_g12345_H46_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_46 = -e01·e11 = -(D01·D11)/(N01·N11)
     COMMON / (N01·N11) = N00²·N01·N10²·N11·Dg1²·Dg2²·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N10*N10*N11*Dg1*Dg1*Dg2*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D01*D11)))%Z.

Definition cleared_g12345_H56_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  (* H_56 = -(e10·e11 + g1·g2) = -(D10·D11·Dg1·Dg2 + Ng1·Ng2·N10·N11)/(N10·N11·Dg1·Dg2)
     COMMON / (N10·N11·Dg1·Dg2) = N00²·N01²·N10·N11·Dg1·Dg2·Dg3²·Dg4²·Dg5² *)
  ((N00*N00*N01*N01*N10*N11*Dg1*Dg2*Dg3*Dg3*Dg4*Dg4*Dg5*Dg5)
   * (-(D10*D11*Dg1*Dg2 + Ng1*Ng2*N10*N11)))%Z.

(** Helper: integer Schur step [schur_step_Z h11 hij h1i h1j := h11·hij - h1i·h1j].
    Used inline for each of the 15 scaled_S_6 entries and 10 scaled_S_5
    entries below. *)
Definition schur_step_Z (h11 hij h1i h1j : Z) : Z :=
  (h11 * hij - h1i * h1j)%Z.

(** 15 cleared scaled_S_6_{ij} numerators (4×4 Schur of row 1 of sym6 H),
    each at scaling g12345_COMMON_Z². *)

Definition cleared_g12345_S6_22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_25_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_26_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H12_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_35_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_36_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H36_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H13_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_45_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_46_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H46_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H14_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_55_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_56_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H56_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H15_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S6_66_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H66_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_H16_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** 10 cleared scaled_S_5_{ij} numerators (4×4 Schur of row 1 of the 5×5
    scaled_S_6), each at scaling g12345_COMMON_Z⁴. The "h11" of the 5×5
    is scaled_S_6_22, and rows/cols 2..5 of the 5×5 are scaled_S_6 entries
    indexed (3..6). *)

Definition cleared_g12345_S5_22_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_23_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_24_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_25_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_36_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_33_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_34_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_35_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_46_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_44_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_45_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_56_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Definition cleared_g12345_S5_55_Z
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : Z :=
  schur_step_Z
    (cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_66_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
    (cleared_g12345_S6_26_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

(** Abstract Z-bool decider on 18 integer parameters (4 (D,N) bucket pairs
    for the CHSH correlators + 5 (Ng, Dg) bucket pairs for γ_1..γ_5). The
    six positivity checks come from the sym6 → sym5 → sym4 Schur cascade. *)
Definition q1ab_g12345_check_z_kernel
  (D00 N00 D01 N01 D10 N10 D11 N11
   Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 : Z) : bool :=
  ((0 <? N00)%Z)
  && ((0 <? N01)%Z)
  && ((0 <? N10)%Z)
  && ((0 <? N11)%Z)
  && ((0 <? Dg1)%Z) && ((0 <? Dg2)%Z)
  && ((0 <? Dg3)%Z) && ((0 <? Dg4)%Z) && ((0 <? Dg5)%Z)
  && ((-Dg1 <? Ng1)%Z) && ((Ng1 <? Dg1)%Z)
  && ((-Dg2 <? Ng2)%Z) && ((Ng2 <? Dg2)%Z)
  && ((-Dg3 <? Ng3)%Z) && ((Ng3 <? Dg3)%Z)
  && ((-Dg4 <? Ng4)%Z) && ((Ng4 <? Dg4)%Z)
  && ((-Dg5 <? Ng5)%Z) && ((Ng5 <? Dg5)%Z)
  (* Schur cascade, six PD checks: *)
  && ((0 <? cleared_g12345_H11_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? cleared_g12345_S6_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)%Z)
  && ((0 <? sym4_d1_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z)
  && ((0 <? sym4_d2_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z)
  && ((0 <? sym4_d3_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z)
  && ((0 <? sym4_d4_Z
              (cleared_g12345_S5_22_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_23_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_24_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_25_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_33_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_34_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_35_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_44_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_45_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5)
              (cleared_g12345_S5_55_Z D00 N00 D01 N01 D10 N10 D11 N11 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5))%Z).

(** Composite γ_12345 integer check on a WitnessCounts plus five γ-bucket
    pairs. Reads (D, N) for the four CHSH correlators from the witness
    counters and (Ng, Dg) for γ_1..γ_5 from the supplied bucket pairs. *)
Definition q1ab_g12345_full_integer_check_kernel
  (wc : WitnessCounts)
  (same_g1 diff_g1 same_g2 diff_g2
   same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat) : bool :=
  let Ng1 := chsh_d_z same_g1 diff_g1 in
  let Dg1 := chsh_n_z same_g1 diff_g1 in
  let Ng2 := chsh_d_z same_g2 diff_g2 in
  let Dg2 := chsh_n_z same_g2 diff_g2 in
  let Ng3 := chsh_d_z same_g3 diff_g3 in
  let Dg3 := chsh_n_z same_g3 diff_g3 in
  let Ng4 := chsh_d_z same_g4 diff_g4 in
  let Dg4 := chsh_n_z same_g4 diff_g4 in
  let Ng5 := chsh_d_z same_g5 diff_g5 in
  let Dg5 := chsh_n_z same_g5 diff_g5 in
  andb (column_contractive_check_witness wc)
       (q1ab_g12345_check_z_kernel
          (chsh_d_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_n_z wc.(wc_same_00) wc.(wc_diff_00))
          (chsh_d_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_n_z wc.(wc_same_01) wc.(wc_diff_01))
          (chsh_d_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_n_z wc.(wc_same_10) wc.(wc_diff_10))
          (chsh_d_z wc.(wc_same_11) wc.(wc_diff_11))
          (chsh_n_z wc.(wc_same_11) wc.(wc_diff_11))
          Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5).

Local Open Scope R_scope.

Notation RealNumber := Rdefinitions.R.

(** * Column contractivity and the NPA matrix *)

Definition zero_marginal_column_contractive
  (e00 e01 e10 e11 : RealNumber) : Prop :=
  1 - e00 * e00 - e10 * e10 >= 0 /\
  1 - e01 * e01 - e11 * e11 >= 0 /\
  (1 - e00 * e00 - e10 * e10) *
    (1 - e01 * e01 - e11 * e11) -
    (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0.

Lemma psd2_quadratic_form_nonneg :
  forall a b d u v,
    a >= 0 ->
    d >= 0 ->
    a * d - b * b >= 0 ->
    a * u * u + 2 * b * u * v + d * v * v >= 0.
Proof.
  intros a b d u v Ha Hd Hdet.
  destruct (Req_dec v 0) as [Hv0 | Hv0].
  - subst v. nra.
  - set (t := u / v).
    assert (Hu : u = t * v).
    { unfold t. field. lra. }
    rewrite Hu.
    replace (a * (t * v) * (t * v) + 2 * b * (t * v) * v + d * v * v)
      with ((v * v) * (a * t * t + 2 * b * t + d)) by ring.
    assert (Hv2 : v * v >= 0) by nra.
    assert (Hq : a * t * t + 2 * b * t + d >= 0).
    {
      destruct (Req_dec a 0) as [Ha0 | Ha0].
      * subst a.
        assert (Hb0 : b = 0) by nra.
        subst b.
        nra.
      * assert (Ha_pos : a > 0) by lra.
        replace (a * t * t + 2 * b * t + d) with
          (a * (t + b / a) * (t + b / a) + (a * d - b * b) / a)
          by (field; lra).
        assert (Hsqr : 0 <= (t + b / a) * (t + b / a)).
        {
          apply Rle_0_sqr.
        }
        assert (Hs1 : a * (t + b / a) * (t + b / a) >= 0).
        {
          nra.
        }
        assert (Hs2 : (a * d - b * b) / a >= 0).
        {
          unfold Rdiv.
          assert (Hainv : / a >= 0).
          {
            left. apply Rinv_0_lt_compat. lra.
          }
          nra.
        }
        nra.
    }
    nra.
Qed.

Lemma zero_marginal_npa_column_contractive_implies_psd :
  forall e00 e01 e10 e11,
    1 - e00 * e00 - e10 * e10 >= 0 ->
    1 - e01 * e01 - e11 * e11 >= 0 ->
    (1 - e00 * e00 - e10 * e10) *
      (1 - e01 * e01 - e11 * e11) -
      (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0 ->
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11))).
Proof.
  intros e00 e01 e10 e11 Hc0 Hc1 Hdet v.
  unfold PSD5, quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  set (v0 := v F1).
  set (x0 := v (FS F1)).
  set (x1 := v (FS (FS F1))).
  set (y0 := v (FS (FS (FS F1)))).
  set (y1 := v (FS (FS (FS (FS F1))))).
  assert (Hblock :
    (1 - e00 * e00 - e10 * e10) * y0 * y0 +
    2 * (-(e00 * e01 + e10 * e11)) * y0 * y1 +
    (1 - e01 * e01 - e11 * e11) * y1 * y1 >= 0).
  {
    apply (psd2_quadratic_form_nonneg
      (1 - e00 * e00 - e10 * e10)
      (-(e00 * e01 + e10 * e11))
      (1 - e01 * e01 - e11 * e11)
      y0 y1).
    - exact Hc0.
    - exact Hc1.
    - replace
        ((1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
         (-(e00 * e01 + e10 * e11)) * (-(e00 * e01 + e10 * e11)))
        with
        ((1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
         (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11)) by ring.
      exact Hdet.
  }
  replace
    (v0 * (v0 * 1 + x0 * 0 + x1 * 0 + y0 * 0 + y1 * 0) +
     x0 * (v0 * 0 + x0 * 1 + x1 * 0 + y0 * e00 + y1 * e01) +
     x1 * (v0 * 0 + x0 * 0 + x1 * 1 + y0 * e10 + y1 * e11) +
     y0 * (v0 * 0 + x0 * e00 + x1 * e10 + y0 * 1 + y1 * 0) +
     y1 * (v0 * 0 + x0 * e01 + x1 * e11 + y0 * 0 + y1 * 1))
    with
    (v0 * v0 +
     (x0 + e00 * y0 + e01 * y1) * (x0 + e00 * y0 + e01 * y1) +
     (x1 + e10 * y0 + e11 * y1) * (x1 + e10 * y0 + e11 * y1) +
     (1 - e00 * e00 - e10 * e10) * y0 * y0 +
     2 * (-(e00 * e01 + e10 * e11)) * y0 * y1 +
     (1 - e01 * e01 - e11 * e11) * y1 * y1)
    by ring.
  assert (Hv0_nonneg : 0 <= v0 * v0) by apply Rle_0_sqr.
  assert (Hx0_nonneg : 0 <= (x0 + e00 * y0 + e01 * y1) * (x0 + e00 * y0 + e01 * y1))
    by apply Rle_0_sqr.
  assert (Hx1_nonneg : 0 <= (x1 + e10 * y0 + e11 * y1) * (x1 + e10 * y0 + e11 * y1))
    by apply Rle_0_sqr.
  nra.
Qed.

(** Arithmetic identities for the chosen test vectors. *)

(** Test vector 1: v = [0; −e00; −e10; 1; 0]
    Extracts: quad5 M v = 1 − e00² − e10² *)
Lemma npa_quad5_test_col0 :
  forall e00 e01 e10 e11 : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -e00
    | 2%nat => -e10
    | 3%nat => 1
    | _     => 0
    end in
  quad5 M v = 1 - e00 * e00 - e10 * e10.
Proof.
  intros e00 e01 e10 e11.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  ring.
Qed.

(** Test vector 2: v = [0; −e01; −e11; 0; 1]
    Extracts: quad5 M v = 1 − e01² − e11² *)
Lemma npa_quad5_test_col1 :
  forall e00 e01 e10 e11 : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -e01
    | 2%nat => -e11
    | 4%nat => 1
    | _     => 0
    end in
  quad5 M v = 1 - e01 * e01 - e11 * e11.
Proof.
  intros e00 e01 e10 e11.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  ring.
Qed.

(** Test vector family 3: v(t) = [0; −(e00t+e01); −(e10t+e11); t; 1]
    Extracts: quad5 M v(t) = p·t² − 2s·t + q
    where p = 1−e00²−e10², q = 1−e01²−e11², s = e00·e01+e10·e11 *)
Lemma npa_quad5_test_schur :
  forall e00 e01 e10 e11 t : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -(e00 * t + e01)
    | 2%nat => -(e10 * t + e11)
    | 3%nat => t
    | 4%nat => 1
    | _     => 0
    end in
  quad5 M v =
    (1 - e00*e00 - e10*e10) * t * t
    - 2 * (e00*e01 + e10*e11) * t
    + (1 - e01*e01 - e11*e11).
Proof.
  intros e00 e01 e10 e11 t.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  ring.
Qed.

(** Extract the three column-contractivity inequalities from PSD5. *)

Theorem npa_psd_implies_column_contractive :
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11))) ->
    zero_marginal_column_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11 Hpsd.
  unfold zero_marginal_column_contractive.

  (* ---- Condition 1: 1 − e00² − e10² ≥ 0 -------------------------------- *)
  assert (Hc0 : 1 - e00 * e00 - e10 * e10 >= 0).
  {
    pose proof Hpsd (fun i =>
      match proj1_sig (Fin.to_nat i) with
      | 1%nat => -e00
      | 2%nat => -e10
      | 3%nat => 1
      | _     => 0
      end) as Hv1.
    rewrite npa_quad5_test_col0 in Hv1.
    exact Hv1.
  }

  (* ---- Condition 2: 1 − e01² − e11² ≥ 0 -------------------------------- *)
  assert (Hc1 : 1 - e01 * e01 - e11 * e11 >= 0).
  {
    pose proof Hpsd (fun i =>
      match proj1_sig (Fin.to_nat i) with
      | 1%nat => -e01
      | 2%nat => -e11
      | 4%nat => 1
      | _     => 0
      end) as Hv2.
    rewrite npa_quad5_test_col1 in Hv2.
    exact Hv2.
  }

  (* ---- Condition 3: det(I − C^T C) ≥ 0 --------------------------------- *)
  assert (Hdet : (1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
                 (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0).
  {
    (* The parametric family v(t) gives a quadratic ≥ 0 for all t.
       Apply quadratic_nonneg_discriminant to extract the det condition. *)
    assert (Hquad : forall t : R,
      (1 - e00*e00 - e10*e10) * t * t
      - 2 * (e00*e01 + e10*e11) * t
      + (1 - e01*e01 - e11*e11) >= 0).
    {
      intro t.
      pose proof Hpsd (fun i =>
        match proj1_sig (Fin.to_nat i) with
        | 1%nat => -(e00 * t + e01)
        | 2%nat => -(e10 * t + e11)
        | 3%nat => t
        | 4%nat => 1
        | _     => 0
        end) as Hvt.
      rewrite npa_quad5_test_schur in Hvt.
      exact Hvt.
    }
    (* Rewrite to match quadratic_nonneg_discriminant signature:
       ∀t, a + 2*b*t + c*t² ≥ 0 → b² ≤ a*c
       Here a = (1−e01²−e11²), b = −(e00e01+e10e11), c = (1−e00²−e10²) *)
    assert (Hform : forall t : R,
      (1 - e01*e01 - e11*e11)
      + 2 * (-(e00*e01 + e10*e11)) * t
      + (1 - e00*e00 - e10*e10) * t * t >= 0).
    {
      intro t. specialize (Hquad t). lra.
    }
    apply quadratic_nonneg_discriminant in Hform.
    nra.
  }

  exact (conj Hc0 (conj Hc1 Hdet)).
Qed.

Theorem npa_psd_iff_column_contractive :
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)))
    <->
    zero_marginal_column_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11.
  split.
  - apply npa_psd_implies_column_contractive.
  - intros [Hc0 [Hc1 Hdet]].
    apply zero_marginal_npa_column_contractive_implies_psd;
      assumption.
Qed.

(** Corollary: NPA PSD is equivalent to column contractivity. *)
Corollary column_contractive_iff_npa_psd :
  forall e00 e01 e10 e11 : R,
    zero_marginal_column_contractive e00 e01 e10 e11
    <->
    npa_psd (zero_marginal_npa e00 e01 e10 e11).
Proof.
  intros e00 e01 e10 e11.
  unfold npa_psd.
  split.
  - intros [Hc0 [Hc1 Hdet]].
    split.
    + apply npa_to_matrix_symmetric.
    + apply zero_marginal_npa_column_contractive_implies_psd;
        assumption.
  - intros [_ Hpsd].
    apply npa_psd_implies_column_contractive.
    exact Hpsd.
Qed.

(** * Soundness of the integer check *)

(** Compute bucket correlation: (same - diff) / (same + diff).
    Returns 0 if no trials recorded for this setting pair. *)
Definition state_bucket_correlation (same_count diff_count : nat) : RealNumber :=
  if Nat.eqb (same_count + diff_count)%nat 0%nat then 0%R
  else ((INR same_count - INR diff_count) / INR (same_count + diff_count)%nat)%R.

Lemma column_contractive_check_witness_sound :
  forall (wc : WitnessCounts),
    column_contractive_check_witness wc = true ->
    zero_marginal_column_contractive
      (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
      (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
      (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
      (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)).
Proof.
  intros wc Hchk.
  unfold column_contractive_check_witness in Hchk.
  (* Destructure the seven boolean conjuncts. *)
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [Hn00 Hchk].
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [Hn01 Hchk].
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [Hn10 Hchk].
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [Hn11 Hchk].
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [HA Hchk].
  apply Bool.andb_true_iff in Hchk; destruct Hchk as [HB HC2].
  (* Convert booleans to Z-arithmetic propositions. *)
  apply Z.ltb_lt in Hn00, Hn01, Hn10, Hn11.
  apply Z.leb_le in HA, HB, HC2.
  (* Name the Z values and their R liftings. *)
  set (s00 := wc.(wc_same_00)) in *. set (d00 := wc.(wc_diff_00)) in *.
  set (s01 := wc.(wc_same_01)) in *. set (d01 := wc.(wc_diff_01)) in *.
  set (s10 := wc.(wc_same_10)) in *. set (d10 := wc.(wc_diff_10)) in *.
  set (s11 := wc.(wc_same_11)) in *. set (d11 := wc.(wc_diff_11)) in *.
  set (N00 := (Z.of_nat s00 + Z.of_nat d00)%Z) in *.
  set (N01 := (Z.of_nat s01 + Z.of_nat d01)%Z) in *.
  set (N10 := (Z.of_nat s10 + Z.of_nat d10)%Z) in *.
  set (N11 := (Z.of_nat s11 + Z.of_nat d11)%Z) in *.
  set (D00 := (Z.of_nat s00 - Z.of_nat d00)%Z) in *.
  set (D01 := (Z.of_nat s01 - Z.of_nat d01)%Z) in *.
  set (D10 := (Z.of_nat s10 - Z.of_nat d10)%Z) in *.
  set (D11 := (Z.of_nat s11 - Z.of_nat d11)%Z) in *.
  unfold chsh_d_z, chsh_n_z in Hn00, Hn01, Hn10, Hn11, HA, HB, HC2.
  fold N00 D00 N01 D01 N10 D10 N11 D11 in Hn00, Hn01, Hn10, Hn11, HA, HB, HC2.
  (* n_xy > 0 in Z lifts to (s_xy + d_xy) > 0 in nat. *)
  assert (HsumN00 : (s00 + d00)%nat <> 0%nat).
  { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
    unfold N00 in Hn00. lia. }
  assert (HsumN01 : (s01 + d01)%nat <> 0%nat).
  { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
    unfold N01 in Hn01. lia. }
  assert (HsumN10 : (s10 + d10)%nat <> 0%nat).
  { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
    unfold N10 in Hn10. lia. }
  assert (HsumN11 : (s11 + d11)%nat <> 0%nat).
  { intro Heq. apply (f_equal Z.of_nat) in Heq. rewrite Nat2Z.inj_add in Heq.
    unfold N11 in Hn11. lia. }
  (* Real-valued versions of N_xy > 0 and D_xy. *)
  set (rN00 := IZR N00). set (rN01 := IZR N01).
  set (rN10 := IZR N10). set (rN11 := IZR N11).
  set (rD00 := IZR D00). set (rD01 := IZR D01).
  set (rD10 := IZR D10). set (rD11 := IZR D11).
  assert (HrN00pos : (0 < rN00)%R) by (apply IZR_lt; exact Hn00).
  assert (HrN01pos : (0 < rN01)%R) by (apply IZR_lt; exact Hn01).
  assert (HrN10pos : (0 < rN10)%R) by (apply IZR_lt; exact Hn10).
  assert (HrN11pos : (0 < rN11)%R) by (apply IZR_lt; exact Hn11).
  (* state_bucket_correlation values, unfolded under the positive precondition. *)
  unfold state_bucket_correlation.
  destruct (Nat.eqb (s00 + d00) 0) eqn:E00; [apply Nat.eqb_eq in E00; contradiction|].
  destruct (Nat.eqb (s01 + d01) 0) eqn:E01; [apply Nat.eqb_eq in E01; contradiction|].
  destruct (Nat.eqb (s10 + d10) 0) eqn:E10; [apply Nat.eqb_eq in E10; contradiction|].
  destruct (Nat.eqb (s11 + d11) 0) eqn:E11; [apply Nat.eqb_eq in E11; contradiction|].
  clear E00 E01 E10 E11.
  (* Rewrite (INR s - INR d) and INR (s + d) using IZR. *)
  assert (Hr_eqN00 : INR (s00 + d00) = rN00).
  { unfold rN00, N00. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
  assert (Hr_eqN01 : INR (s01 + d01) = rN01).
  { unfold rN01, N01. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
  assert (Hr_eqN10 : INR (s10 + d10) = rN10).
  { unfold rN10, N10. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
  assert (Hr_eqN11 : INR (s11 + d11) = rN11).
  { unfold rN11, N11. rewrite INR_IZR_INZ. rewrite Nat2Z.inj_add. reflexivity. }
  assert (Hr_eqD00 : (INR s00 - INR d00)%R = rD00).
  { unfold rD00, D00. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
  assert (Hr_eqD01 : (INR s01 - INR d01)%R = rD01).
  { unfold rD01, D01. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
  assert (Hr_eqD10 : (INR s10 - INR d10)%R = rD10).
  { unfold rD10, D10. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
  assert (Hr_eqD11 : (INR s11 - INR d11)%R = rD11).
  { unfold rD11, D11. rewrite !INR_IZR_INZ. rewrite <- minus_IZR. reflexivity. }
  rewrite Hr_eqN00, Hr_eqN01, Hr_eqN10, Hr_eqN11.
  rewrite Hr_eqD00, Hr_eqD01, Hr_eqD10, Hr_eqD11.
  (* Bring the Z arithmetic into R via IZR distribution. *)
  assert (HrA_iz : (0 <= IZR (N00 * N00 * (N10 * N10)
                              - D00 * D00 * (N10 * N10)
                              - D10 * D10 * (N00 * N00)))%R).
  { apply IZR_le. exact HA. }
  rewrite !minus_IZR, !mult_IZR in HrA_iz.
  assert (HrA : (rN00 * rN00 * (rN10 * rN10)
                 - rD00 * rD00 * (rN10 * rN10)
                 - rD10 * rD10 * (rN00 * rN00) >= 0)%R).
  { unfold rN00, rN10, rD00, rD10. apply Rle_ge. exact HrA_iz. }
  assert (HrB_iz : (0 <= IZR (N01 * N01 * (N11 * N11)
                              - D01 * D01 * (N11 * N11)
                              - D11 * D11 * (N01 * N01)))%R).
  { apply IZR_le. exact HB. }
  rewrite !minus_IZR, !mult_IZR in HrB_iz.
  assert (HrB : (rN01 * rN01 * (rN11 * rN11)
                 - rD01 * rD01 * (rN11 * rN11)
                 - rD11 * rD11 * (rN01 * rN01) >= 0)%R).
  { unfold rN01, rN11, rD01, rD11. apply Rle_ge. exact HrB_iz. }
  assert (HrAB_iz : (IZR ((D00 * D01 * N10 * N11 + D10 * D11 * N00 * N01)
                          * (D00 * D01 * N10 * N11 + D10 * D11 * N00 * N01))
                     <= IZR ((N00 * N00 * (N10 * N10)
                              - D00 * D00 * (N10 * N10)
                              - D10 * D10 * (N00 * N00))
                             * (N01 * N01 * (N11 * N11)
                                - D01 * D01 * (N11 * N11)
                                - D11 * D11 * (N01 * N01))))%R).
  { apply IZR_le. exact HC2. }
  rewrite !mult_IZR, !plus_IZR, !minus_IZR, !mult_IZR in HrAB_iz.
  assert (HrAB :
            ((rN00 * rN00 * (rN10 * rN10)
              - rD00 * rD00 * (rN10 * rN10)
              - rD10 * rD10 * (rN00 * rN00))
             * (rN01 * rN01 * (rN11 * rN11)
                - rD01 * rD01 * (rN11 * rN11)
                - rD11 * rD11 * (rN01 * rN01))
             >=
             (rD00 * rD01 * rN10 * rN11 + rD10 * rD11 * rN00 * rN01)
             * (rD00 * rD01 * rN10 * rN11 + rD10 * rD11 * rN00 * rN01))%R).
  { unfold rN00, rN01, rN10, rN11, rD00, rD01, rD10, rD11.
    apply Rle_ge. exact HrAB_iz. }
  (* Goal: zero_marginal_column_contractive (rD00/rN00) (rD01/rN01)
                                            (rD10/rN10) (rD11/rN11) *)
  unfold zero_marginal_column_contractive.
  assert (Hrn00sq : (0 < rN00 * rN00)%R) by nra.
  assert (Hrn01sq : (0 < rN01 * rN01)%R) by nra.
  assert (Hrn10sq : (0 < rN10 * rN10)%R) by nra.
  assert (Hrn11sq : (0 < rN11 * rN11)%R) by nra.
  (* The R-level conditions follow by clearing the n_xy denominators (positive)
     and applying the Z-arithmetic facts HrA, HrB, HrAB. Denominators are cleared
     by asserting a polynomial form of each goal and closing it with nra. *)
  assert (HrN00ne : rN00 <> 0%R) by lra.
  assert (HrN01ne : rN01 <> 0%R) by lra.
  assert (HrN10ne : rN10 <> 0%R) by lra.
  assert (HrN11ne : rN11 <> 0%R) by lra.
  apply Rge_le in HrA, HrB, HrAB.
  split; [|split].
  - (* 1 - (rD00/rN00)^2 - (rD10/rN10)^2 >= 0 *)
    assert (Heqv :
      (1 - rD00 / rN00 * (rD00 / rN00) - rD10 / rN10 * (rD10 / rN10)
         = (rN00 * rN00 * (rN10 * rN10)
              - rD00 * rD00 * (rN10 * rN10)
              - rD10 * rD10 * (rN00 * rN00))
           / (rN00 * rN00 * (rN10 * rN10)))%R).
    { field. split; assumption. }
    rewrite Heqv.
    apply Rle_ge.
    unfold Rdiv. apply Rmult_le_pos; [exact HrA | apply Rlt_le; apply Rinv_0_lt_compat; nra].
  - (* 1 - (rD01/rN01)^2 - (rD11/rN11)^2 >= 0 *)
    assert (Heqv :
      (1 - rD01 / rN01 * (rD01 / rN01) - rD11 / rN11 * (rD11 / rN11)
         = (rN01 * rN01 * (rN11 * rN11)
              - rD01 * rD01 * (rN11 * rN11)
              - rD11 * rD11 * (rN01 * rN01))
           / (rN01 * rN01 * (rN11 * rN11)))%R).
    { field. split; assumption. }
    rewrite Heqv.
    apply Rle_ge.
    unfold Rdiv. apply Rmult_le_pos; [exact HrB | apply Rlt_le; apply Rinv_0_lt_compat; nra].
  - (* Schur-complement determinant. *)
    assert (Heqv :
      ((1 - rD00 / rN00 * (rD00 / rN00) - rD10 / rN10 * (rD10 / rN10))
         * (1 - rD01 / rN01 * (rD01 / rN01) - rD11 / rN11 * (rD11 / rN11))
       - (rD00 / rN00 * (rD01 / rN01) + rD10 / rN10 * (rD11 / rN11))
         * (rD00 / rN00 * (rD01 / rN01) + rD10 / rN10 * (rD11 / rN11))
         = ((rN00 * rN00 * (rN10 * rN10)
              - rD00 * rD00 * (rN10 * rN10)
              - rD10 * rD10 * (rN00 * rN00))
            * (rN01 * rN01 * (rN11 * rN11)
                - rD01 * rD01 * (rN11 * rN11)
                - rD11 * rD11 * (rN01 * rN01))
            - (rD00 * rD01 * rN10 * rN11 + rD10 * rD11 * rN00 * rN01)
              * (rD00 * rD01 * rN10 * rN11 + rD10 * rD11 * rN00 * rN01))
           / (rN00 * rN00 * (rN01 * rN01) * (rN10 * rN10) * (rN11 * rN11)))%R).
    { field. repeat split; assumption. }
    rewrite Heqv.
    apply Rle_ge.
    unfold Rdiv. apply Rmult_le_pos.
    + (* 0 <= RHS_of_HrAB - LHS_of_HrAB, by HrAB which says LHS <= RHS. *)
      lra.
    + apply Rlt_le. apply Rinv_0_lt_compat.
      (* denominator: rN00^2 * rN01^2 * rN10^2 * rN11^2 > 0 *)
      repeat (apply Rmult_lt_0_compat); nra.
Qed.

(** If the integer check passes, the zero-marginal NPA matrix of the
    count-derived correlators is positive semidefinite. *)
Theorem column_contractive_check_witness_npa_psd :
  forall (wc : WitnessCounts),
    column_contractive_check_witness wc = true ->
    npa_psd (zero_marginal_npa
      (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
      (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
      (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
      (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11))).
Proof.
  intros wc Hchk.
  apply column_contractive_iff_npa_psd.
  apply column_contractive_check_witness_sound. exact Hchk.
Qed.
