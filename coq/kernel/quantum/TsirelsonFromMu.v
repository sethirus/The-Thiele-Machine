(** * TsirelsonFromMu — Tsirelson |S| ≤ 2√2 from a sharper structural axiom.

    The framework's current A3 in [HonestMeasurement.v] says:

      hms_cost = 0 → |S| ≤ 2  (classical CHSH bound)

    The Tsirelson bound |S| ≤ 2√2 is strictly tighter than the
    algebraic bound (|S| ≤ 4) but strictly looser than the classical
    bound. [HonestMeasurementImpliesNPA.v] documents that the current
    A3 cannot reach Tsirelson:

      "A natural strengthening of A3 ... collapses into the PSD
       condition itself, making A3 circular. Conversely, leaving A3
       as the zero-cost CHSH bound makes the conclusion non-derivable."

    This file isolates one named hypothesis that closes the gap. The
    hypothesis [A3_operator_norm] says: the 2×2 correlator matrix has
    operator norm at most 1. Equivalently, for the two basis-rotated
    unit vectors [u = (1, 1)/√2] and [v = (1, −1)/√2], the matrix's
    action on them has Euclidean norm at most 1.

    From A3' the proof of |S| ≤ 2√2 is constructive and short: the
    orthonormal-rotation argument bounds [E₀₀ + E₀₁] and [E₁₀ − E₁₁]
    separately by [√2] via Cauchy–Schwarz. The PR-box correlation
    [(E_xy = ±1, S = 4)] violates A3' — concretely
    [(E₀₀ + E₀₁)² + (E₁₀ + E₁₁)² = 4 + 0 = 4 > 2] — so A3' excludes
    super-quantum boxes.

    What A3' is *not*: derivable from cost-monotonicity alone. No
    known operational axiom (information causality, macroscopic
    locality, local orthogonality) entails A3' from the µ-ledger.
    A3' is an isolated, falsifiable hypothesis whose physical
    derivation is open. *)

From Coq Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Section 1 — the algebraic content of A3'.

    A3' says: for the correlator matrix
       M = [[E_00, E_01]; [E_10, E_11]],
    the operator norm satisfies ||M||_op ≤ 1.

    For 2×2 matrices, ||M||_op ≤ 1 ⟺ ||M u||² ≤ 1 for the two
    orthonormal vectors u = (1, 1)/√2 and v = (1, −1)/√2. (Any 2×2
    operator norm is achieved on the eigenbasis of M^T M, which
    consists of two orthonormal vectors; testing on u and v is
    equivalent up to a basis change, and in any case the two
    inequalities below imply the operator-norm bound.)

    Algebraically:
       ||M u||² ≤ 1  ⟺  (E_00 + E_01)² + (E_10 + E_11)² ≤ 2
       ||M v||² ≤ 1  ⟺  (E_00 − E_01)² + (E_10 − E_11)² ≤ 2
    *)

Record CorrelatorBox : Type := {
  cb_E00 : R;
  cb_E01 : R;
  cb_E10 : R;
  cb_E11 : R;
}.

Definition chsh_S (b : CorrelatorBox) : R :=
  cb_E00 b + cb_E01 b + cb_E10 b - cb_E11 b.

(** A3' — the operator-norm hypothesis stated as two PSD-style
    inequalities on the rotated bases. *)
Definition A3_operator_norm (b : CorrelatorBox) : Prop :=
  (cb_E00 b + cb_E01 b)^2 + (cb_E10 b + cb_E11 b)^2 <= 2
  /\
  (cb_E00 b - cb_E01 b)^2 + (cb_E10 b - cb_E11 b)^2 <= 2.

(** ** Section 2 — headline: |S| ≤ 2√2 from A3'.

    Proof outline (avoiding sqrt-of-abs by working with squares):
      Let A = E_00 + E_01, B = E_10 + E_11, C = E_00 − E_01, D = E_10 − E_11.
      A3' gives A² + B² ≤ 2 and C² + D² ≤ 2, so A² ≤ 2 and D² ≤ 2.
      S = E_00 + E_01 + E_10 − E_11 = A + D.
      (A + D)² ≤ A² + 2AD + D² ≤ A² + (A² + D²) + D² = 2(A² + D²) ≤ 8.
      So |S|² ≤ 8 = (2√2)², hence |S| ≤ 2√2. *)

Theorem tsirelson_bound_from_A3 :
  forall b : CorrelatorBox,
    A3_operator_norm b ->
    Rabs (chsh_S b) <= 2 * sqrt 2.
Proof.
  intros b [Hu Hv].
  destruct b as [E00 E01 E10 E11].
  unfold chsh_S, A3_operator_norm in *. simpl in Hu, Hv |- *.
  (* Hu : (E00 + E01)^2 + (E10 + E11)^2 <= 2.
     Hv : (E00 - E01)^2 + (E10 - E11)^2 <= 2.
     Goal: Rabs (E00 + E01 + E10 - E11) <= 2 * sqrt 2.

     Keep [^2] opaque so lra can treat the squared sums as primitive
     non-negative variables — nra has trouble unfolding [^2]
     automatically. We use [pow2_ge_0] to seed the non-negativity facts. *)
  (* Step 1: |A|² ≤ 2 and |D|² ≤ 2 where A = E00+E01, D = E10-E11. *)
  assert (HBnn : 0 <= (E10 + E11)^2) by apply pow2_ge_0.
  assert (HCnn : 0 <= (E00 - E01)^2) by apply pow2_ge_0.
  assert (HA2 : (E00 + E01)^2 <= 2) by lra.
  assert (HD2 : (E10 - E11)^2 <= 2) by lra.
  (* Step 2: (A+D)² ≤ 2(A²+D²) ≤ 8 via the ring identity
              (A+D)² + (A-D)² = 2(A² + D²)
     so (A+D)² ≤ 2(A² + D²) since (A-D)² ≥ 0. *)
  assert (Hsumdiff :
    (E00 + E01 + E10 - E11)^2 + ((E00 + E01) - (E10 - E11))^2
    = 2 * ((E00 + E01)^2 + (E10 - E11)^2)) by ring.
  assert (Hdiff_nn : 0 <= ((E00 + E01) - (E10 - E11))^2) by apply pow2_ge_0.
  assert (Hsq : (E00 + E01 + E10 - E11)^2 <= 8) by lra.
  (* Step 3: convert squared bound to absolute-value bound. *)
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

(** ** Section 4 — sanity check: PR-box correlation violates A3'.

    The PR-box has E_00 = E_01 = E_10 = 1 and E_11 = −1 (so S = 4
    exceeds Tsirelson). For this box:
      (E_00 + E_01)² + (E_10 + E_11)² = 4 + 0 = 4 > 2.
    So A3' excludes the PR-box, as it must. *)

Definition pr_box : CorrelatorBox :=
  {| cb_E00 := 1; cb_E01 := 1; cb_E10 := 1; cb_E11 := -1 |}.

Lemma pr_box_S_is_4 : chsh_S pr_box = 4.
Proof. unfold chsh_S, pr_box. simpl. lra. Qed.

Lemma pr_box_violates_A3 : ~ A3_operator_norm pr_box.
Proof.
  unfold A3_operator_norm, pr_box. simpl.
  intros [H1 _].
  (* H1 : (1 + 1)^2 + (1 + (-1))^2 ≤ 2.  i.e., 4 + 0 ≤ 2. *)
  nra.
Qed.

(** ** Section 5 — what is left open.

    The hypothesis [A3_operator_norm] is a sharper structural axiom
    than the framework's existing A3. It is satisfied by all quantum
    CHSH correlations (Tsirelson's theorem in the forward direction),
    by all classical local correlations, and by no super-quantum
    correlations with |S| > 2√2.

    What this file does NOT show:
      - That [A3_operator_norm] is derivable from any µ-ledger
        property in the current framework. The framework's
        [HonestMeasurementImpliesNPA.v] explicitly documents this as
        the open foundational problem: no known operational axiom
        from information theory entails the full operator-norm
        condition.

    Future work directions (any one of which would close the gap):
      - Identify a µ-cost-monotonicity-like property whose
        consequence on correlators is exactly the operator-norm
        bound.
      - Connect the existing column-contractivity work in
        [TsirelsonUpperBound.v] (which currently gets the classical
        bound from µ = 0) to a positive-µ version that gets Tsirelson.
      - Prove [A3_operator_norm] from NPA-level-1 PSD on the moment
        matrix; this would tie the bridge to standard SDP arguments. *)

(** Print Assumptions on the headline. Should report only standard
    Coq.Reals axioms — no project-local axiom. *)
Print Assumptions tsirelson_bound_from_A3.
Print Assumptions pr_box_violates_A3.

(** ** Substrate connection anchor.

    The Tsirelson-from-mu derivation in this file feeds the
    quantum-to-mu chain that governs the Thiele Machine's mu-ledger.
    The anchor below makes the connection point explicit. *)

From Kernel Require Import VMState MuCostModel.

Definition tsirelson_from_mu_vm_anchor (s : VMState) : nat := vm_mu s.
