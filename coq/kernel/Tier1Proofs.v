(** =========================================================================
    Tier 1 Proofs: Elementary Correlation Bounds
    =========================================================================

    This file contains COMPLETE PROOFS (no axioms, no admits) for:
    - T1-1: normalized_E_bound - Correlations bounded by 1
    - T1-2: valid_box_S_le_4 - CHSH algebraic maximum is 4

    These replace the Context parameters in BoxCHSH.v.
    Estimated: ~100 lines total. Actual: see below.

    ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

From Kernel Require Import ValidCorrelation.
From Kernel Require Import BoxCHSH.

Local Open Scope Q_scope.
Import ListNotations.

(** Bit sign encoding *)
Definition bit_sign (n : nat) : Q :=
  if Nat.eqb n 0 then 1 else if Nat.eqb n 1 then -1 else 0.

(** Correlation *)
Definition E (B : Box) (x y : nat) : Q :=
  (bit_sign 0%nat * bit_sign 0%nat) * B x y 0%nat 0%nat +
  (bit_sign 0%nat * bit_sign 1%nat) * B x y 0%nat 1%nat +
  (bit_sign 1%nat * bit_sign 0%nat) * B x y 1%nat 0%nat +
  (bit_sign 1%nat * bit_sign 1%nat) * B x y 1%nat 1%nat.

(** CHSH value *)
Definition S (B : Box) : Q :=
  E B 0%nat 0%nat + E B 0%nat 1%nat + E B 1%nat 0%nat - E B 1%nat 1%nat.

(** Helper: Simplify bit_sign values *)
Lemma bit_sign_0 : bit_sign 0%nat = 1.
Proof. reflexivity. Qed.

Lemma bit_sign_1 : bit_sign 1%nat = -1.
Proof. reflexivity. Qed.

(** Helper: E expands to linear combination *)
Lemma E_expand : forall B x y,
  E B x y == B x y 0%nat 0%nat - B x y 0%nat 1%nat - B x y 1%nat 0%nat + B x y 1%nat 1%nat.
Proof.
  intros. unfold E, bit_sign. simpl.
  (* Simplify the boolean comparisons *)
  (* (if 0 =? 0 then 1 else ...) = 1 *)
  (* (if 1 =? 0 then 1 else if 1 =? 1 then -1 else 0) = -1 *)
  (* So: 1*1*B00 + 1*(-1)*B01 + (-1)*1*B10 + (-1)*(-1)*B11 *)
  (* = B00 - B01 - B10 + B11 *)
  field.
Qed.

(** =========================================================================
    TIER 1-1: normalized_E_bound

    Theorem: For normalized, non-negative B, |E(x,y)| ≤ 1.

    Proof strategy:
    1. Expand E = p00 - p01 - p10 + p11
    2. Use normalization: p00 + p01 + p10 + p11 = 1
    3. Derive bounds on the linear combination
    4. Apply Qabs characterization

    ========================================================================= *)

Theorem normalized_E_bound : forall B x y,
  non_negative B ->
  normalized B ->
  Qabs (E B x y) <= 1.
Proof.
  intros B x y Hnn Hnorm.
  rewrite E_expand.

  (* Extract the four probabilities *)
  set (p00 := B x y 0%nat 0%nat).
  set (p01 := B x y 0%nat 1%nat).
  set (p10 := B x y 1%nat 0%nat).
  set (p11 := B x y 1%nat 1%nat).

  (* Gather constraints *)
  assert (H00: 0 <= p00) by (unfold p00; apply Hnn).
  assert (H01: 0 <= p01) by (unfold p01; apply Hnn).
  assert (H10: 0 <= p10) by (unfold p10; apply Hnn).
  assert (H11: 0 <= p11) by (unfold p11; apply Hnn).
  assert (Hsum: p00 + p01 + p10 + p11 == 1) by (unfold p00, p01, p10, p11; apply Hnorm).

  (* The goal is: |p00 - p01 - p10 + p11| <= 1 *)
  (* This is equivalent to: -1 <= p00 - p01 - p10 + p11 <= 1 *)

  (* Use Qabs characterization *)
  apply Qabs_case; intros Hcase.

  - (* Case: p00 - p01 - p10 + p11 >= 0, so Qabs(...) = p00 - p01 - p10 + p11 *)
    (* Need: p00 - p01 - p10 + p11 <= 1 *)
    (* From Hsum: p00 + p01 + p10 + p11 == 1 *)
    (* We have: p00, p01, p10, p11 >= 0 *)
    (* This is linear Q arithmetic - psatz can solve it *)
    psatz Q 4.

  - (* Case: p00 - p01 - p10 + p11 < 0, so Qabs(...) = -(p00 - p01 - p10 + p11) *)
    (* Need: -(p00 - p01 - p10 + p11) <= 1 *)
    (* From Hsum: p00 + p01 + p10 + p11 == 1 *)
    (* We have: p00, p01, p10, p11 >= 0 *)
    (* This is linear Q arithmetic - psatz can solve it *)
    psatz Q 4.
Qed.

(** =========================================================================
    TIER 1-2: valid_box_S_le_4

    Theorem: For valid box B, |S(B)| ≤ 4.

    Proof strategy:
    1. S = E00 + E01 + E10 - E11
    2. Apply triangle inequality: |S| ≤ |E00| + |E01| + |E10| + |-E11|
    3. Use |−x| = |x|
    4. Each |Eij| ≤ 1 from normalized_E_bound
    5. Sum: 1 + 1 + 1 + 1 = 4

    ========================================================================= *)

(** Helper: Triangle inequality for Q sums *)
Lemma Qabs_triangle_4 : forall a b c d,
  Qabs (a + b + c + d) <= Qabs a + Qabs b + Qabs c + Qabs d.
Proof.
  intros.
  (* Step by step: |a+b+c+d| <= |a+b| + |c+d| <= |a|+|b| + |c|+|d| *)
  assert (H1: a + b + c + d == (a + b) + (c + d)) by field.
  assert (H2: Qabs a + Qabs b + Qabs c + Qabs d == (Qabs a + Qabs b) + (Qabs c + Qabs d)) by field.
  setoid_rewrite H1.
  setoid_rewrite H2.
  eapply Qle_trans.
  { apply Qabs_triangle. }
  apply Qplus_le_compat.
  - apply Qabs_triangle.
  - apply Qabs_triangle.
Qed.

Theorem valid_box_S_le_4 : forall B,
  valid_box B ->
  Qabs (S B) <= 4.
Proof.
  intros B [Hnn [Hnorm Hns]].
  unfold S.

  (* Rewrite S as sum of 4 terms *)
  assert (HSrewrite: E B 0%nat 0%nat + E B 0%nat 1%nat + E B 1%nat 0%nat - E B 1%nat 1%nat ==
                      E B 0%nat 0%nat + E B 0%nat 1%nat + E B 1%nat 0%nat + (- E B 1%nat 1%nat)) by field.
  setoid_rewrite HSrewrite.

  (* Apply triangle inequality *)
  apply Qle_trans with (Qabs (E B 0%nat 0%nat) + Qabs (E B 0%nat 1%nat) +
                         Qabs (E B 1%nat 0%nat) + Qabs (- E B 1%nat 1%nat)).
  { apply Qabs_triangle_4. }

  (* Use |−x| = |x| *)
  rewrite Qabs_opp.

  (* Apply normalized_E_bound to each term *)
  assert (H00: Qabs (E B 0%nat 0%nat) <= 1) by (apply normalized_E_bound; assumption).
  assert (H01: Qabs (E B 0%nat 1%nat) <= 1) by (apply normalized_E_bound; assumption).
  assert (H10: Qabs (E B 1%nat 0%nat) <= 1) by (apply normalized_E_bound; assumption).
  assert (H11: Qabs (E B 1%nat 1%nat) <= 1) by (apply normalized_E_bound; assumption).

  (* Sum the bounds: 1 + 1 + 1 + 1 = 4 *)
  psatz Q 4.
Qed.


(** =========================================================================
    NOTE: Additional Tier 1 theorems (local_box_S_le_2, pr_box_no_extension)

    These theorems are handled as Context parameters in BoxCHSH.v and
    TestTripartite.v using the Section/Context pattern. This allows:

    1. Explicit parameterization of hard assumptions
    2. Clear documentation of proof obligations
    3. No global axioms (maintains INQUISITOR clean status)

    T1-3 (local_box_S_le_2): Classical CHSH inequality for local boxes
      - Requires ~200 lines of Q arithmetic via Fine's theorem
      - Already parameterized in BoxCHSH.v:110
      - Proof structure: deterministic strategies all give |S| ≤ 2,
        local boxes are convex combinations, convexity preserves bound

    T1-4 (pr_box_no_extension): PR box tripartite monogamy
      - Requires ~300 lines of contradiction derivation
      - Already parameterized in TestTripartite.v
      - Proof structure: marginal constraints from x=y=0 and x=y=1
        are incompatible, systematic case elimination

    For production use, these remain as documented assumptions.
    For research verification, they can be proven independently and
    instantiated via Section parameters.

    ========================================================================= *)

(** =========================================================================
    VERIFICATION: Print Assumptions

    Run `Print Assumptions normalized_E_bound.` to verify zero axioms.
    Run `Print Assumptions valid_box_S_le_4.` to verify zero axioms.
    Run `Print Assumptions local_box_S_le_2.` to see remaining assumption.
    Run `Print Assumptions pr_box_no_extension.` to see remaining assumption.

    Expected: T1-1 and T1-2 closed, T1-3 and T1-4 show "deferred"

    ========================================================================= *)

(* Print Assumptions normalized_E_bound. *)
(* Print Assumptions valid_box_S_le_4. *)
(* Print Assumptions local_box_S_le_2. *)
(* Print Assumptions pr_box_no_extension. *)
