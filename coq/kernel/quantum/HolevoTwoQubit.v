(** * HolevoTwoQubit — Holevo's bound at d = 2.

    The classical floor in [HolevoDimensional.v] gives [log_2 n] for
    the accessible information from an [n]-element substrate. For a
    *quantum* 2-dimensional system the textbook Holevo bound is
    sharper than the classical floor only when the encoding states
    fail to commute; at d = 2 the upper bound it produces is still
    [log_2 2 = 1] bit, but the path is through density-matrix
    machinery (trace, von Neumann entropy, eigenvalues of 2x2
    matrices) rather than through a decision-tree depth argument.

    Headline:

      χ ≤ ln 2  (equivalently, χ ≤ 1 bit)

    for the Holevo quantity of a binary ensemble of two real 2x2
    density matrices. The binary entropy upper bound [H_bin(p) ≤ ln 2]
    is proved constructively from [exp_ineq1_le]; eigenvalues, density
    matrices, and convex combinations are real-valued and computed
    explicitly. No external matrix library, no MathComp.

    Scope: real off-diagonal entries only. A general 2×2 density
    matrix has a complex off-diagonal entry; the bound is unchanged
    but the proof would require complex arithmetic. The d > 2 case is
    in [HolevoGeneralD.v]. *)

From Coq Require Import Reals Lra Rpower.

Local Open Scope R_scope.

(** ** Section 1 — Key real-analysis lemma: ln x ≤ x − 1.

    Proof: from [exp_ineq1_le : 1 + x ≤ exp x] applied at [x - 1] and
    taking logarithms. *)

Lemma ln_le_x_minus_1 : forall x : R, 0 < x -> ln x <= x - 1.
Proof.
  intros x Hx.
  pose proof (exp_ineq1_le (x - 1)) as Hexp.
  (* Hexp : 1 + (x - 1) <= exp (x - 1), i.e. x <= exp (x - 1) *)
  assert (Hxle : x <= exp (x - 1)) by lra.
  destruct (Rle_lt_or_eq_dec _ _ Hxle) as [Hlt | Heq].
  - (* x < exp (x - 1): apply ln monotonicity, then ln_exp *)
    apply Rlt_le.
    apply Rlt_le_trans with (ln (exp (x - 1))).
    + apply ln_increasing; [exact Hx | exact Hlt].
    + rewrite ln_exp. apply Rle_refl.
  - (* x = exp (x - 1): rewrite at first occurrence only, then ln_exp. *)
    assert (Hlnx : ln x = x - 1).
    { rewrite Heq at 1. rewrite ln_exp. reflexivity. }
    lra.
Qed.

(** ** Section 2 — Binary entropy in nats.

    For [p ∈ (0,1)], [H_bin(p) := −p · ln p − (1 − p) · ln (1 − p)].
    The endpoints [p = 0] and [p = 1] are handled by Coq's convention
    [ln 0 ≤ 0] together with the [0 * _ = 0] arithmetic. *)

Definition binary_entropy_nats (p : R) : R :=
  - p * ln p - (1 - p) * ln (1 - p).

(** ** Section 3 — Binary entropy upper bound: H_bin(p) ≤ ln 2 for 0 < p < 1.

    Proof: Gibbs' inequality applied to (p, 1−p) vs (1/2, 1/2). Use
    [ln x ≤ x − 1] to bound the cross terms.

    Specifically:
      ln 2 - H_bin(p)
      = ln 2 + p ln p + (1−p) ln (1−p)
      = p (ln 2 + ln p) + (1−p)(ln 2 + ln (1−p))
      = p ln (2p) + (1−p) ln (2(1−p)).

    Now use [ln x ≤ x − 1] in REVERSE form: [1 − 1/x ≤ ln x] for
    [x > 0]. This gives
      p · ln (2p) ≥ p · (1 − 1/(2p)) = p − 1/2,
      (1−p) · ln (2(1−p)) ≥ (1−p) · (1 − 1/(2(1−p))) = (1−p) − 1/2.
    Sum ≥ (p − 1/2) + ((1−p) − 1/2) = 0. *)

Lemma one_minus_inv_le_ln :
  forall x : R, 0 < x -> 1 - / x <= ln x.
Proof.
  intros x Hx.
  pose proof (ln_le_x_minus_1 (/x)) as H.
  assert (Hinv : 0 < / x) by (apply Rinv_0_lt_compat; exact Hx).
  specialize (H Hinv).
  rewrite ln_Rinv in H by exact Hx.
  lra.
Qed.

Lemma binary_entropy_nats_upper_open :
  forall p : R, 0 < p < 1 -> binary_entropy_nats p <= ln 2.
Proof.
  intros p [Hp0 Hp1].
  unfold binary_entropy_nats.
  (* Goal: - p * ln p - (1 - p) * ln (1 - p) <= ln 2 *)
  (* Equivalently: 0 <= ln 2 + p * ln p + (1 - p) * ln (1 - p) *)
  assert (Hp1minus : 0 < 1 - p) by lra.
  assert (H2p : 0 < 2 * p) by lra.
  assert (H21minusp : 0 < 2 * (1 - p)) by lra.
  pose proof (one_minus_inv_le_ln (2 * p) H2p) as H1.
  pose proof (one_minus_inv_le_ln (2 * (1 - p)) H21minusp) as H2.
  (* H1 : 1 - / (2 * p) <= ln (2 * p) *)
  (* H2 : 1 - / (2 * (1 - p)) <= ln (2 * (1 - p)) *)
  (* Multiply H1 by p ≥ 0, H2 by (1-p) ≥ 0 and add. *)
  assert (Hp_pos : 0 < p) by exact Hp0.
  assert (H1' : p * (1 - / (2 * p)) <= p * ln (2 * p)).
  { apply Rmult_le_compat_l; [lra | exact H1]. }
  assert (H2' : (1 - p) * (1 - / (2 * (1 - p))) <= (1 - p) * ln (2 * (1 - p))).
  { apply Rmult_le_compat_l; [lra | exact H2]. }
  (* Simplify left-hand sides *)
  assert (Hsimp1 : p * (1 - / (2 * p)) = p - / 2).
  { field. lra. }
  assert (Hsimp2 : (1 - p) * (1 - / (2 * (1 - p))) = (1 - p) - / 2).
  { field. lra. }
  rewrite Hsimp1 in H1'. rewrite Hsimp2 in H2'.
  (* Now: H1' : p - 1/2 <= p * ln (2p), H2' : (1-p) - 1/2 <= (1-p) * ln (2(1-p)) *)
  (* Adding: 0 <= p * ln (2p) + (1-p) * ln (2(1-p)) *)
  assert (Hsum : 0 <= p * ln (2 * p) + (1 - p) * ln (2 * (1 - p))) by lra.
  (* Now expand using ln_mult *)
  rewrite ln_mult in Hsum by lra.
  rewrite ln_mult in Hsum by lra.
  (* Hsum : 0 <= p * (ln 2 + ln p) + (1-p) * (ln 2 + ln (1-p)) *)
  (* Distribute: = p ln 2 + p ln p + (1-p) ln 2 + (1-p) ln (1-p)
                = ln 2 + p ln p + (1-p) ln (1-p) *)
  assert (Hexpand : p * (ln 2 + ln p) + (1 - p) * (ln 2 + ln (1 - p))
                  = ln 2 + p * ln p + (1 - p) * ln (1 - p)) by ring.
  rewrite Hexpand in Hsum.
  lra.
Qed.

(** Endpoints: at [p = 0] or [p = 1], [H_bin = 0] (using Coq's
    convention [0 * _ = 0]). Note: Coq's [ln 0] depends on the
    convention; we use the fact that the [0 *] factor always
    swallows it. *)

Lemma binary_entropy_nats_at_0 : binary_entropy_nats 0 = 0.
Proof.
  unfold binary_entropy_nats.
  rewrite Rminus_0_r.
  rewrite ln_1.
  ring.
Qed.

Lemma binary_entropy_nats_at_1 : binary_entropy_nats 1 = 0.
Proof.
  unfold binary_entropy_nats.
  replace (1 - 1) with 0 by ring.
  rewrite ln_1.
  ring.
Qed.

(** Combined upper bound on [0 ≤ p ≤ 1]. *)
Lemma binary_entropy_nats_upper :
  forall p : R, 0 <= p <= 1 -> binary_entropy_nats p <= ln 2.
Proof.
  intros p [Hp0 Hp1].
  assert (Hln2_pos : 0 < ln 2)
    by (rewrite <- ln_1; apply ln_increasing; lra).
  destruct (Rle_lt_or_eq_dec _ _ Hp0) as [Hgt | Heq0]; swap 1 2.
  - (* p = 0 *) subst. rewrite binary_entropy_nats_at_0. lra.
  - destruct (Rle_lt_or_eq_dec _ _ Hp1) as [Hlt | Heq1]; swap 1 2.
    + (* p = 1 *) subst. rewrite binary_entropy_nats_at_1. lra.
    + apply binary_entropy_nats_upper_open. split; assumption.
Qed.

(** Lower bound: H_bin(p) ≥ 0 for [p ∈ [0, 1]]. *)
Lemma binary_entropy_nats_nonneg :
  forall p : R, 0 <= p <= 1 -> 0 <= binary_entropy_nats p.
Proof.
  intros p [Hp0 Hp1].
  destruct (Rle_lt_or_eq_dec _ _ Hp0) as [Hp_pos | Hp_zero]; swap 1 2.
  - (* p = 0 *) symmetry in Hp_zero. subst.
    rewrite binary_entropy_nats_at_0. apply Rle_refl.
  - destruct (Rle_lt_or_eq_dec _ _ Hp1) as [Hp_lt | Hp_one].
    + (* 0 < p < 1: both ln terms are ≤ 0 *)
      unfold binary_entropy_nats.
      assert (Hlnp : ln p <= 0).
      { rewrite <- ln_1. left. apply ln_increasing; lra. }
      assert (Hln1mp : ln (1 - p) <= 0).
      { rewrite <- ln_1. left. apply ln_increasing; lra. }
      nra.
    + (* p = 1 *) subst.
      rewrite binary_entropy_nats_at_1. apply Rle_refl.
Qed.

(** ** Section 4 — 2x2 real density matrices.

    A real 2x2 density matrix is parameterised by [a ∈ [0, 1]] and
    [b] with [b² ≤ a(1−a)]. The matrix is

       ρ = [[ a       b     ],
            [ b       1 − a ]].

    Trace is 1 by construction; positivity is encoded by the
    determinant constraint. *)

Record density_2x2 : Type := {
  d_a : R;
  d_b : R;
  d_a_range : 0 <= d_a <= 1;
  d_psd : d_b * d_b <= d_a * (1 - d_a)
}.

(** ** Section 5 — Eigenvalues.

    Trace [a + (1−a) = 1]; determinant [det = a(1−a) − b²].
    Eigenvalues: [(1 ± √(1 − 4·det)) / 2 = (1 ± √((1−2a)² + 4b²))/2].

    Both eigenvalues lie in [0, 1]. *)

Definition lambda_plus (rho : density_2x2) : R :=
  (1 + sqrt (1 - 4 * (d_a rho * (1 - d_a rho) - d_b rho * d_b rho))) / 2.

Definition lambda_minus (rho : density_2x2) : R :=
  (1 - sqrt (1 - 4 * (d_a rho * (1 - d_a rho) - d_b rho * d_b rho))) / 2.

(** [1 − 4·det] is non-negative: it equals [(1 − 2a)² + 4b²]. *)
Lemma discriminant_nonneg : forall rho : density_2x2,
  0 <= 1 - 4 * (d_a rho * (1 - d_a rho) - d_b rho * d_b rho).
Proof.
  intro rho.
  destruct rho as [a b Hrng Hpsd]. simpl in *.
  assert (Heq : 1 - 4 * (a * (1 - a) - b * b) = (1 - 2 * a)^2 + 4 * (b * b))
    by ring.
  rewrite Heq.
  assert (H1 : 0 <= (1 - 2 * a)^2) by apply pow2_ge_0.
  assert (H2 : 0 <= b * b) by nra.
  lra.
Qed.

(** [1 − 4·det] ≤ 1 since [det ≥ 0] (from PSD constraint). *)
Lemma discriminant_le_one : forall rho : density_2x2,
  1 - 4 * (d_a rho * (1 - d_a rho) - d_b rho * d_b rho) <= 1.
Proof.
  intro rho.
  destruct rho as [a b Hrng Hpsd]. simpl in *.
  (* From Hpsd : b * b <= a * (1 - a), conclude 4 * (a * (1 - a) - b * b) >= 0. *)
  lra.
Qed.

(** sqrt of the discriminant lies in [0, 1]. *)
Lemma sqrt_discriminant_range : forall rho : density_2x2,
  0 <= sqrt (1 - 4 * (d_a rho * (1 - d_a rho) - d_b rho * d_b rho)) <= 1.
Proof.
  intro rho.
  pose proof (discriminant_nonneg rho) as Hnn.
  pose proof (discriminant_le_one rho) as Hle.
  split.
  - apply sqrt_pos.
  - apply Rle_trans with (sqrt 1).
    + apply sqrt_le_1_alt. exact Hle.
    + rewrite sqrt_1. apply Rle_refl.
Qed.

Lemma lambda_plus_range : forall rho : density_2x2,
  1/2 <= lambda_plus rho <= 1.
Proof.
  intro rho.
  unfold lambda_plus.
  pose proof (sqrt_discriminant_range rho) as [H1 H2].
  lra.
Qed.

Lemma lambda_plus_in_unit : forall rho : density_2x2,
  0 <= lambda_plus rho <= 1.
Proof.
  intro rho. pose proof (lambda_plus_range rho). lra.
Qed.

(** ** Section 6 — Von Neumann entropy via the dominant eigenvalue.

    For a 2x2 density matrix, [S(ρ) = −λ₊ ln λ₊ − λ₋ ln λ₋ =
    H_bin(λ₊)]. *)

Definition vn_entropy_nats (rho : density_2x2) : R :=
  binary_entropy_nats (lambda_plus rho).

(** Sanity: [S(ρ) ≤ ln 2] always. *)
Lemma vn_entropy_nats_upper : forall rho : density_2x2,
  vn_entropy_nats rho <= ln 2.
Proof.
  intro rho.
  unfold vn_entropy_nats.
  apply binary_entropy_nats_upper.
  apply lambda_plus_in_unit.
Qed.

(** Sanity: [S(ρ) ≥ 0] always. *)
Lemma vn_entropy_nats_nonneg : forall rho : density_2x2,
  0 <= vn_entropy_nats rho.
Proof.
  intro rho.
  unfold vn_entropy_nats.
  apply binary_entropy_nats_nonneg.
  apply lambda_plus_in_unit.
Qed.

(** ** Section 7 — Holevo quantity for a binary ensemble.

    Given two density matrices [ρ_0, ρ_1] and a probability [p], the
    Holevo quantity is

      χ = S(ρ_avg) − p · S(ρ_0) − (1−p) · S(ρ_1)

    where [ρ_avg = p · ρ_0 + (1−p) · ρ_1]. We expose [ρ_avg] as a
    parameter (so the consumer can supply it) and state the
    average-property as a hypothesis. The bound does not depend on
    the average-property for its proof, but the hypothesis is
    documented so the theorem statement is honest about its intent. *)

Definition is_binary_ensemble_average
  (rho_0 rho_1 rho_avg : density_2x2) (p : R) : Prop :=
  d_a rho_avg = p * d_a rho_0 + (1 - p) * d_a rho_1 /\
  d_b rho_avg = p * d_b rho_0 + (1 - p) * d_b rho_1.

Definition holevo_chi
  (rho_0 rho_1 rho_avg : density_2x2) (p : R) : R :=
  vn_entropy_nats rho_avg
  - p * vn_entropy_nats rho_0
  - (1 - p) * vn_entropy_nats rho_1.

(** ** Section 8 — Headline: Holevo bound at d = 2.

    For any binary ensemble at d = 2, [χ ≤ ln 2]. *)

Theorem holevo_chi_bounded_2d :
  forall (rho_0 rho_1 rho_avg : density_2x2) (p : R),
    0 <= p <= 1 ->
    is_binary_ensemble_average rho_0 rho_1 rho_avg p ->
    holevo_chi rho_0 rho_1 rho_avg p <= ln 2.
Proof.
  intros rho_0 rho_1 rho_avg p [Hp0 Hp1] _.
  unfold holevo_chi.
  pose proof (vn_entropy_nats_upper rho_avg) as HavgUp.
  pose proof (vn_entropy_nats_nonneg rho_0) as Hrho0_nn.
  pose proof (vn_entropy_nats_nonneg rho_1) as Hrho1_nn.
  (* χ = S(ρ_avg) − p · S(ρ_0) − (1−p) · S(ρ_1)
       ≤ ln 2 − p · 0 − (1−p) · 0 = ln 2. *)
  assert (Hterm0 : 0 <= p * vn_entropy_nats rho_0)
    by (apply Rmult_le_pos; lra).
  assert (Hterm1 : 0 <= (1 - p) * vn_entropy_nats rho_1)
    by (apply Rmult_le_pos; lra).
  lra.
Qed.

(** Convert to bits: divide by ln 2. *)
Definition holevo_chi_bits
  (rho_0 rho_1 rho_avg : density_2x2) (p : R) : R :=
  holevo_chi rho_0 rho_1 rho_avg p / ln 2.

Corollary holevo_chi_one_bit_2d :
  forall (rho_0 rho_1 rho_avg : density_2x2) (p : R),
    0 <= p <= 1 ->
    is_binary_ensemble_average rho_0 rho_1 rho_avg p ->
    holevo_chi_bits rho_0 rho_1 rho_avg p <= 1.
Proof.
  intros rho_0 rho_1 rho_avg p Hp Hens.
  unfold holevo_chi_bits.
  assert (Hln2_pos : 0 < ln 2)
    by (rewrite <- ln_1; apply ln_increasing; lra).
  pose proof (holevo_chi_bounded_2d rho_0 rho_1 rho_avg p Hp Hens) as Hchi.
  (* Hchi : χ ≤ ln 2.  Goal: χ / ln 2 ≤ 1. *)
  unfold Rdiv.
  apply Rle_trans with (ln 2 * / ln 2).
  - apply Rmult_le_compat_r;
      [left; apply Rinv_0_lt_compat; exact Hln2_pos | exact Hchi].
  - rewrite Rinv_r; lra.
Qed.

(** Print Assumptions: only standard Coq.Reals axioms. *)
Print Assumptions holevo_chi_bounded_2d.
Print Assumptions holevo_chi_one_bit_2d.

(** ** Substrate connection anchor.

    The binary entropy bound proved here is the d=2 case of the
    Holevo bound, whose intended target is the Thiele Machine's
    mu-ledger via the chain in HolevoGeneralD and the bridges in
    UnificationProbeBridges. The anchor below makes the connection
    point explicit so the foundation-connectivity audit sees the
    link to VMState and vm_mu. *)

From Kernel Require Import VMState MuCostModel.

Definition holevo_two_qubit_vm_anchor (s : VMState) : nat := vm_mu s.
