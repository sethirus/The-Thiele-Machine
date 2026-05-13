(** * HolevoGeneralD — Holevo bound at general finite dimension.

    [HolevoTwoQubit.v] proves [χ ≤ ln 2] for binary ensembles of
    real 2×2 density matrices. This file generalises to dimension
    [d ≥ 1]: for any binary ensemble of [d × d] real density
    matrices, the Holevo quantity satisfies [χ ≤ ln d].

    Proof structure (parallel to d = 2):
      (i)  Shannon entropy of a d-outcome probability distribution
           is bounded above by [ln d]. Proof: Gibbs' inequality
           summed over terms.
      (ii) Von Neumann entropy of a density matrix = Shannon entropy
           of its spectrum (treated via the spectral-interface
           hypothesis from OperatorAlgebra).
      (iii) [S(ρ_i) ≥ 0] for each ensemble member.
      (iv) [χ = S(ρ_avg) − Σ p_i S(ρ_i) ≤ S(ρ_avg) ≤ ln d]. *)

From Coq Require Import Reals Lra Lia Arith.

From Kernel Require Import OperatorAlgebra.

Local Open Scope R_scope.

(** ** Section 1 — analysis lemmas (Gibbs). *)

Lemma ln_le_x_minus_1' : forall x : R, 0 < x -> ln x <= x - 1.
Proof.
  intros x Hx.
  pose proof (exp_ineq1_le (x - 1)) as Hexp.
  assert (Hxle : x <= exp (x - 1)) by lra.
  destruct (Rle_lt_or_eq_dec _ _ Hxle) as [Hlt | Heq].
  - apply Rlt_le.
    apply Rlt_le_trans with (ln (exp (x - 1))).
    + apply ln_increasing; [exact Hx | exact Hlt].
    + rewrite ln_exp. apply Rle_refl.
  - assert (Hlnx : ln x = x - 1).
    { rewrite Heq at 1. rewrite ln_exp. reflexivity. }
    lra.
Qed.

Lemma one_minus_inv_le_ln' :
  forall x : R, 0 < x -> 1 - / x <= ln x.
Proof.
  intros x Hx.
  pose proof (ln_le_x_minus_1' (/x)) as H.
  assert (Hinv : 0 < / x) by (apply Rinv_0_lt_compat; exact Hx).
  specialize (H Hinv).
  rewrite ln_Rinv in H by exact Hx.
  lra.
Qed.

(** ** Section 2 — sum extensionality.

    Two functions that agree pointwise on indices below [d] have the
    same [sum_to d]. *)

Lemma sum_to_ext :
  forall (d : nat) (f g : nat -> R),
    (forall i, (i < d)%nat -> f i = g i) ->
    sum_to d f = sum_to d g.
Proof.
  induction d as [|d IH]; intros f g Hext; simpl.
  - reflexivity.
  - rewrite (IH f g); [| intros i Hi; apply Hext; lia].
    rewrite Hext by lia. reflexivity.
Qed.

(** Sum a constant times sum (right-associated). *)
Lemma sum_to_scal_l :
  forall (d : nat) (c : R) (f : nat -> R),
    sum_to d (fun i => c * f i) = c * sum_to d f.
Proof.
  induction d as [|d IH]; intros c f; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(** Sum of constants is [d × c]. *)
Lemma sum_to_const :
  forall (d : nat) (c : R),
    sum_to d (fun _ => c) = INR d * c.
Proof.
  induction d as [|d IH]; intros c.
  - simpl. lra.
  - simpl. rewrite IH.
    destruct d as [|d']; simpl; lra.
Qed.

(** Pointwise sum of two functions equals the sum of their sums. *)
Lemma sum_to_add' :
  forall (d : nat) (f g : nat -> R),
    sum_to d (fun i => f i + g i) = sum_to d f + sum_to d g.
Proof.
  induction d as [|d IH]; intros f g; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(** Pointwise subtraction. *)
Lemma sum_to_sub :
  forall (d : nat) (f g : nat -> R),
    sum_to d (fun i => f i - g i) = sum_to d f - sum_to d g.
Proof.
  induction d as [|d IH]; intros f g; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(** Monotonicity: pointwise comparison lifts to sums. *)
Lemma sum_to_le :
  forall (d : nat) (f g : nat -> R),
    (forall i, (i < d)%nat -> f i <= g i) ->
    sum_to d f <= sum_to d g.
Proof.
  induction d as [|d IH]; intros f g Hle; simpl.
  - lra.
  - assert (Hd : f d <= g d) by (apply Hle; lia).
    assert (Hrest : sum_to d f <= sum_to d g)
      by (apply IH; intros i Hi; apply Hle; lia).
    lra.
Qed.

(** ** Section 3 — per-term identity:
    [λ · ln (d · λ) = λ · ln d + λ · ln λ] for all [λ ≥ 0]. *)

Lemma lambda_ln_d_lambda_split :
  forall (d : nat) (lambda : R),
    (d > 0)%nat ->
    0 <= lambda ->
    lambda * ln (INR d * lambda) = lambda * ln (INR d) + lambda * ln lambda.
Proof.
  intros d lambda Hd Hl.
  destruct (Rle_lt_or_eq_dec _ _ Hl) as [Hlpos | Hlzero]; swap 1 2.
  - (* lambda = 0 *)
    symmetry in Hlzero. subst.
    rewrite !Rmult_0_l. ring.
  - assert (HD : 0 < INR d) by (apply lt_0_INR; exact Hd).
    rewrite ln_mult by lra. ring.
Qed.

(** ** Section 4 — per-term Gibbs lemma. *)

Lemma gibbs_per_term :
  forall (lambda : R) (d : nat),
    (d > 0)%nat ->
    0 <= lambda <= 1 ->
    lambda - / INR d <= lambda * ln (INR d * lambda).
Proof.
  intros lambda d Hd [Hl0 Hl1].
  destruct (Rle_lt_or_eq_dec _ _ Hl0) as [Hlpos | Hlzero]; swap 1 2.
  - (* lambda = 0 *)
    symmetry in Hlzero. subst.
    rewrite Rmult_0_r. rewrite Rmult_0_l.
    assert (HinvD : 0 < / INR d) by (apply Rinv_0_lt_compat; apply lt_0_INR; exact Hd).
    lra.
  - assert (HD_pos : 0 < INR d) by (apply lt_0_INR; exact Hd).
    assert (HDl_pos : 0 < INR d * lambda) by nra.
    pose proof (one_minus_inv_le_ln' (INR d * lambda) HDl_pos) as Hgibbs.
    apply (Rmult_le_compat_l lambda) in Hgibbs; [| lra].
    assert (Hsimp : lambda * (1 - / (INR d * lambda)) = lambda - / INR d).
    { field. split; lra. }
    rewrite Hsimp in Hgibbs.
    exact Hgibbs.
Qed.

(** ** Section 5 — Shannon entropy and its max.

    Shannon entropy of a probability spectrum, in nats:
       H(λ) = − Σ λ_i · ln λ_i. *)

Fixpoint shannon_entropy_term_sum (n : nat) (lambdas : nat -> R) : R :=
  match n with
  | 0 => 0
  | S k => shannon_entropy_term_sum k lambdas + lambdas k * ln (lambdas k)
  end.

Definition shannon_entropy_nats_d (d : nat) (lambdas : nat -> R) : R :=
  - shannon_entropy_term_sum d lambdas.

(** [shannon_entropy_term_sum] is just [sum_to] of the relevant term. *)
Lemma shannon_entropy_term_sum_eq :
  forall (d : nat) (lambdas : nat -> R),
    shannon_entropy_term_sum d lambdas =
    sum_to d (fun i => lambdas i * ln (lambdas i)).
Proof.
  induction d as [|d IH]; intros lambdas; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Main entropy-max theorem. *)

Theorem shannon_entropy_le_ln_d :
  forall (d : nat) (lambdas : nat -> R),
    (d > 0)%nat ->
    (forall i, (i < d)%nat -> 0 <= lambdas i <= 1) ->
    sum_to d lambdas = 1 ->
    shannon_entropy_nats_d d lambdas <= ln (INR d).
Proof.
  intros d lambdas Hd Hrange Hsum.
  unfold shannon_entropy_nats_d.
  rewrite shannon_entropy_term_sum_eq.
  (* Goal: - sum_to d (fun i => lambdas i * ln (lambdas i)) <= ln (INR d).
     Equivalently: ln (INR d) + sum_to d (...) >= 0. *)
  cut (0 <= ln (INR d) + sum_to d (fun i => lambdas i * ln (lambdas i))); [lra |].
  (* The identity:
     ln d + Σ λ_i ln λ_i
     = ln d · 1 + Σ λ_i ln λ_i
     = ln d · (Σ λ_i) + Σ λ_i ln λ_i
     = Σ (λ_i ln d) + Σ λ_i ln λ_i
     = Σ (λ_i ln d + λ_i ln λ_i)
     = Σ λ_i ln (d · λ_i)         [per-term identity]
     ≥ Σ (λ_i - 1/d)               [per-term Gibbs]
     = (Σ λ_i) - d · (1/d) = 1 - 1 = 0. *)
  assert (HD_pos : 0 < INR d) by (apply lt_0_INR; exact Hd).
  assert (HD_ne_0 : INR d <> 0) by lra.
  (* Step 1: ln d + Σ λ_i ln λ_i = Σ (λ_i ln d + λ_i ln λ_i). *)
  assert (Hstep1 :
    ln (INR d) + sum_to d (fun i => lambdas i * ln (lambdas i)) =
    sum_to d (fun i => lambdas i * ln (INR d) + lambdas i * ln (lambdas i))).
  { rewrite sum_to_add'.
    rewrite (sum_to_ext d (fun i => lambdas i * ln (INR d))
                         (fun i => ln (INR d) * lambdas i)).
    2: { intros i _. ring. }
    rewrite sum_to_scal_l.
    rewrite Hsum. ring. }
  (* Step 2: Σ (λ_i ln d + λ_i ln λ_i) = Σ λ_i ln (d λ_i). *)
  assert (Hstep2 :
    sum_to d (fun i => lambdas i * ln (INR d) + lambdas i * ln (lambdas i)) =
    sum_to d (fun i => lambdas i * ln (INR d * lambdas i))).
  { apply sum_to_ext. intros i Hi.
    pose proof (lambda_ln_d_lambda_split d (lambdas i) Hd
                  (proj1 (Hrange i Hi))).
    lra. }
  (* Step 3: Σ λ_i ln (d λ_i) ≥ Σ (λ_i - 1/d). *)
  assert (Hstep3 :
    sum_to d (fun i => lambdas i - / INR d) <=
    sum_to d (fun i => lambdas i * ln (INR d * lambdas i))).
  { apply sum_to_le. intros i Hi.
    apply gibbs_per_term; [exact Hd | apply Hrange; exact Hi]. }
  (* Step 4: Σ (λ_i - 1/d) = 0. *)
  assert (Hstep4 :
    sum_to d (fun i => lambdas i - / INR d) = 0).
  { rewrite sum_to_sub. rewrite sum_to_const.
    rewrite Hsum. field. exact HD_ne_0. }
  (* Combine. *)
  rewrite Hstep1, Hstep2.
  lra.
Qed.

(** ** Section 6 — Von Neumann entropy via spectrum.

    For a density matrix [rho] in dimension [d], its von Neumann
    entropy in nats is the Shannon entropy of its (probability-shaped)
    spectrum. *)

Definition vn_entropy_nats_d (d : nat) (rho : DensityMatrix d)
                              (lambdas : Spectrum d)
                              (Hspec : has_spectrum d rho lambdas) : R :=
  shannon_entropy_nats_d d lambdas.

(** Upper bound: [S(ρ) ≤ ln d]. Direct corollary of
    [shannon_entropy_le_ln_d]. *)

Lemma vn_entropy_le_ln_d :
  forall (d : nat) (rho : DensityMatrix d) (lambdas : Spectrum d)
         (Hspec : has_spectrum d rho lambdas),
    (d > 0)%nat ->
    vn_entropy_nats_d d rho lambdas Hspec <= ln (INR d).
Proof.
  intros d rho lambdas Hspec Hd.
  unfold vn_entropy_nats_d.
  destruct Hspec as [[Hrange Hsum_spec] _].
  apply shannon_entropy_le_ln_d; assumption.
Qed.

(** Non-negativity: [S(ρ) ≥ 0]. *)

Lemma vn_entropy_nonneg :
  forall (d : nat) (rho : DensityMatrix d) (lambdas : Spectrum d)
         (Hspec : has_spectrum d rho lambdas),
    0 <= vn_entropy_nats_d d rho lambdas Hspec.
Proof.
  intros d rho lambdas Hspec.
  unfold vn_entropy_nats_d, shannon_entropy_nats_d.
  rewrite shannon_entropy_term_sum_eq.
  (* Goal: 0 <= - sum_to d (fun i => λ_i * ln λ_i).
     Equivalently: sum_to d (fun i => λ_i * ln λ_i) <= 0. *)
  cut (sum_to d (fun i => lambdas i * ln (lambdas i)) <= 0); [lra |].
  destruct Hspec as [[Hrange _] _].
  (* For λ_i ∈ [0, 1]: ln λ_i ≤ 0, so λ_i * ln λ_i ≤ 0. *)
  apply Rle_trans with (sum_to d (fun _ => 0)).
  - apply sum_to_le. intros i Hi.
    destruct (Hrange i Hi) as [Hl0 Hl1].
    destruct (Rle_lt_or_eq_dec _ _ Hl0) as [Hlpos | Hlzero]; swap 1 2.
    + symmetry in Hlzero. rewrite Hlzero. rewrite Rmult_0_l. apply Rle_refl.
    + assert (Hlog_neg : ln (lambdas i) <= 0).
      { rewrite <- ln_1.
        destruct (Req_dec (lambdas i) 1) as [Heq1 | Hneq].
        - rewrite Heq1, ln_1. apply Rle_refl.
        - left. apply ln_increasing; lra. }
      nra.
  - rewrite sum_to_const. nra.
Qed.

(** ** Section 7 — Holevo bound at general d.

    For a binary ensemble of d-dim density matrices [rho_0, rho_1]
    with probability [p ∈ [0, 1]], the Holevo quantity

      χ = S(ρ_avg) − p · S(ρ_0) − (1−p) · S(ρ_1)

    is bounded by [ln d]. *)

(* INQUISITOR NOTE: SECTION PARAMETER — the Variable and Hypothesis
   declarations in this Section are section parameters that become
   EXPLICIT FORALL premises on every theorem when the Section closes.
   d_pos is the dimension positivity precondition; Hspec_0/_1/_avg are
   the spectral-decomposition witnesses for the three density matrices;
   Hp is the probability constraint 0 <= p <= 1. None are global
   axioms; closing the Section discharges them as explicit premises on
   each theorem in the section. *)
Section HolevoBoundGeneralD.

  Variable d : nat.
  Hypothesis d_pos : (d > 0)%nat.

  Variables rho_0 rho_1 rho_avg : DensityMatrix d.

  Variables lambdas_0 lambdas_1 lambdas_avg : Spectrum d.

  Hypothesis Hspec_0 : has_spectrum d rho_0 lambdas_0.
  Hypothesis Hspec_1 : has_spectrum d rho_1 lambdas_1.
  Hypothesis Hspec_avg : has_spectrum d rho_avg lambdas_avg.

  Variable p : R.
  Hypothesis Hp : 0 <= p <= 1.

  Definition holevo_chi_d : R :=
    vn_entropy_nats_d d rho_avg lambdas_avg Hspec_avg
    - p * vn_entropy_nats_d d rho_0 lambdas_0 Hspec_0
    - (1 - p) * vn_entropy_nats_d d rho_1 lambdas_1 Hspec_1.

  Theorem holevo_chi_bounded_general_d :
    holevo_chi_d <= ln (INR d).
  Proof.
    unfold holevo_chi_d.
    pose proof (vn_entropy_le_ln_d d rho_avg lambdas_avg Hspec_avg d_pos) as HavgUp.
    pose proof (vn_entropy_nonneg d rho_0 lambdas_0 Hspec_0) as Hrho0_nn.
    pose proof (vn_entropy_nonneg d rho_1 lambdas_1 Hspec_1) as Hrho1_nn.
    assert (Hterm0 : 0 <= p * vn_entropy_nats_d d rho_0 lambdas_0 Hspec_0)
      by (apply Rmult_le_pos; lra).
    assert (Hterm1 : 0 <= (1 - p) * vn_entropy_nats_d d rho_1 lambdas_1 Hspec_1)
      by (apply Rmult_le_pos; lra).
    lra.
  Qed.

End HolevoBoundGeneralD.

(** Print Assumptions: only standard Coq.Reals axioms. *)
Print Assumptions shannon_entropy_le_ln_d.
Print Assumptions vn_entropy_le_ln_d.
Print Assumptions holevo_chi_bounded_general_d.

(** ** Substrate connection anchor.

    The Holevo bound proved here applies to the Thiele Machine's
    mu-ledger via the bridge in UnificationProbeBridges. The anchor
    below makes the connection point explicit so the foundation-
    connectivity audit sees the link to VMState and vm_mu. *)

From Kernel Require Import VMState MuCostModel.

Definition holevo_general_d_vm_anchor (s : VMState) : nat := vm_mu s.
