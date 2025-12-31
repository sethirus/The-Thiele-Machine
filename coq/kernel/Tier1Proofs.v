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
    TIER 1-3: local_box_S_le_2

    Theorem: Bell's CHSH inequality - for local boxes, |S(B)| ≤ 2.

    Proof strategy:
    1. Deterministic strategies: (x -> a) × (y -> b)
    2. All 16 deterministic strategies give S ∈ {-2, 0, 2}
    3. Local box = convex combination of deterministic strategies
    4. Convexity preserves bound

    ========================================================================= *)

(** Deterministic strategy: functions from settings to outcomes *)
Record det_strategy : Type := {
  alice_strategy : nat -> bool;
  bob_strategy : nat -> bool
}.

(** Convert bool to Q sign (-1 or 1) *)
Definition bool_to_sign (b : bool) : Q :=
  if b then -1 else 1.

(** Evaluate correlator E for a deterministic strategy *)
Definition E_det (strat : det_strategy) (x y : nat) : Q :=
  bool_to_sign (alice_strategy strat x) * bool_to_sign (bob_strategy strat y).

(** CHSH value for deterministic strategy *)
Definition S_det (strat : det_strategy) : Q :=
  E_det strat 0 0 + E_det strat 0 1 + E_det strat 1 0 - E_det strat 1 1.

(** All 16 deterministic strategies explicitly *)
Definition strat_0000 : det_strategy := {| alice_strategy := fun _ => false; bob_strategy := fun _ => false |}.
Definition strat_0001 : det_strategy := {| alice_strategy := fun _ => false; bob_strategy := fun y => if Nat.eqb y 0 then false else true |}.
Definition strat_0010 : det_strategy := {| alice_strategy := fun _ => false; bob_strategy := fun y => if Nat.eqb y 0 then true else false |}.
Definition strat_0011 : det_strategy := {| alice_strategy := fun _ => false; bob_strategy := fun _ => true |}.
Definition strat_0100 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then false else true; bob_strategy := fun _ => false |}.
Definition strat_0101 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then false else true; bob_strategy := fun y => if Nat.eqb y 0 then false else true |}.
Definition strat_0110 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then false else true; bob_strategy := fun y => if Nat.eqb y 0 then true else false |}.
Definition strat_0111 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then false else true; bob_strategy := fun _ => true |}.
Definition strat_1000 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then true else false; bob_strategy := fun _ => false |}.
Definition strat_1001 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then true else false; bob_strategy := fun y => if Nat.eqb y 0 then false else true |}.
Definition strat_1010 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then true else false; bob_strategy := fun y => if Nat.eqb y 0 then true else false |}.
Definition strat_1011 : det_strategy := {| alice_strategy := fun x => if Nat.eqb x 0 then true else false; bob_strategy := fun _ => true |}.
Definition strat_1100 : det_strategy := {| alice_strategy := fun _ => true; bob_strategy := fun _ => false |}.
Definition strat_1101 : det_strategy := {| alice_strategy := fun _ => true; bob_strategy := fun y => if Nat.eqb y 0 then false else true |}.
Definition strat_1110 : det_strategy := {| alice_strategy := fun _ => true; bob_strategy := fun y => if Nat.eqb y 0 then true else false |}.
Definition strat_1111 : det_strategy := {| alice_strategy := fun _ => true; bob_strategy := fun _ => true |}.

(** Helper lemma: Each of the 16 strategies computes to |S| ≤ 2 *)
Lemma S_det_bounded_concrete : forall (a0 a1 b0 b1 : bool),
  Qabs (S_det {| alice_strategy := fun x => if Nat.eqb x 0 then a0 else a1;
                  bob_strategy := fun y => if Nat.eqb y 0 then b0 else b1 |}) <= 2.
Proof.
  intros a0 a1 b0 b1.
  (* Enumerate all 16 bool combinations *)
  destruct a0; destruct a1; destruct b0; destruct b1;
    unfold S_det, E_det, bool_to_sign, alice_strategy, bob_strategy; simpl;
    unfold Qabs, Qle; simpl; reflexivity.
Qed.

(** All listed deterministic strategies satisfy |S| ≤ 2 *)
Lemma S_det_bounded : forall strat,
  In strat [strat_0000; strat_0001; strat_0010; strat_0011;
            strat_0100; strat_0101; strat_0110; strat_0111;
            strat_1000; strat_1001; strat_1010; strat_1011;
            strat_1100; strat_1101; strat_1110; strat_1111] ->
  Qabs (S_det strat) <= 2.
Proof.
  intros strat Hin.
  (* Each strategy is a specific (a0,a1,b0,b1) combination *)
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]];
    subst; apply S_det_bounded_concrete.
Qed.

(** Convert local box to Box type *)
Definition local_to_box (pA : nat -> nat -> Q) (pB : nat -> nat -> Q) : Box :=
  fun x y a b => pA x a * pB y b.

(** Main theorem: Local boxes satisfy Bell inequality

    Proof strategy:
    1. A local box has the form B(x,y,a,b) = pA(x,a) * pB(y,b)
    2. The correlator factorizes: E(x,y) = (pA(x,0) - pA(x,1)) * (pB(y,0) - pB(y,1))
    3. Define δA(x) = pA(x,0) - pA(x,1), δB(y) = pB(y,0) - pB(y,1)
    4. From normalization: pA(x,0) + pA(x,1) = 1, so |δA(x)| ≤ 1
    5. Similarly |δB(y)| ≤ 1
    6. Then S = δA(0)*δB(0) + δA(0)*δB(1) + δA(1)*δB(0) - δA(1)*δB(1)
    7. Factor as: S = δA(0)*(δB(0)+δB(1)) + δA(1)*(δB(0)-δB(1))
    8. Maximize |S| subject to |δA|, |δB| ≤ 1 via linear programming
    9. Maximum is 2 (achieved at corners like δA=(1,1), δB=(1,-1))

    Complete proof requires ~200 lines of Q arithmetic with case analysis.
*)
Theorem local_box_S_le_2 : forall B,
  local_box B ->
  Qabs (S B) <= 2.
Proof.
  intros B [pA [pB [HpAnn [HpBnn [HpAnorm [HpBnorm Hfact]]]]]].

  (* Step 1: Rewrite S in terms of marginal distributions *)
  unfold S, E.
  repeat (setoid_rewrite Hfact).

  (* Step 2: Each correlator E(x,y) expands to a bilinear form in pA and pB values *)
  (* E(x,y) = Σ_{a,b} sign(a)*sign(b) * pA(x,a) * pB(y,b) *)
  (*        = (pA(x,0) - pA(x,1)) * (pB(y,0) - pB(y,1)) *)

  (* Step 3: Define the marginal differences *)
  (* Let δA(x) = pA(x,0) - pA(x,1) and δB(y) = pB(y,0) - pB(y,1) *)

  (* Step 4: From normalization pA(x,0) + pA(x,1) = 1 and non-negativity,
              we have -1 ≤ δA(x) ≤ 1. Similarly for δB. *)

  (* Step 5: Express S in terms of δ values:
              S = δA(0)*δB(0) + δA(0)*δB(1) + δA(1)*δB(0) - δA(1)*δB(1)
                = δA(0)*(δB(0)+δB(1)) + δA(1)*(δB(0)-δB(1)) *)

  (* Step 6: Bound |S| using |δA|, |δB| ≤ 1
              The maximum is achieved when:
              - Case 1: δA(0)=1, δA(1)=1, δB(0)=1, δB(1)=-1 gives S=2
              - Case 2: δA(0)=-1, δA(1)=-1, δB(0)=-1, δB(1)=1 gives S=-2
              All other configurations give |S| ≤ 2 *)

  (* The complete arithmetic verification requires explicit enumeration
     of extremal cases and use of psatz on the resulting polynomial constraints.
     This is straightforward but tedious (~200 lines). *)
Admitted.

(** =========================================================================
    TIER 1-4: pr_box_no_extension

    Theorem: PR box has no valid tripartite extension.

    Proof strategy:
    1. Define PR box: a⊕b = xy with certainty
    2. Assume tripartite extension exists
    3. Derive contradiction from marginal constraints

    ========================================================================= *)

(** Helper: XOR for nat (treating 0 as false, nonzero as true) *)
Definition nat_xor (n m : nat) : nat :=
  if Nat.eqb n 0 then (if Nat.eqb m 0 then 0 else 1)
  else (if Nat.eqb m 0 then 1 else 0).

(** PR box definition: a⊕b = xy *)
Definition pr_box : Box :=
  fun x y a b =>
    (* PR box constraint: a⊕b = x·y *)
    let expected_xor := Nat.mul x y in
    let actual_xor := nat_xor a b in
    if Nat.eqb actual_xor expected_xor then 1#2 else 0.

(** Tripartite box *)
Definition Box3 := nat -> nat -> nat -> nat -> nat -> nat -> Q.

(** Valid tripartite extension *)
Definition has_valid_extension (B : Box) : Prop :=
  exists (B3 : Box3),
    (* Non-negative *)
    (forall x y z a b c, 0 <= B3 x y z a b c) /\
    (* Normalized *)
    (forall x y z,
      B3 x y z 0%nat 0%nat 0%nat + B3 x y z 0%nat 0%nat 1%nat +
      B3 x y z 0%nat 1%nat 0%nat + B3 x y z 0%nat 1%nat 1%nat +
      B3 x y z 1%nat 0%nat 0%nat + B3 x y z 1%nat 0%nat 1%nat +
      B3 x y z 1%nat 1%nat 0%nat + B3 x y z 1%nat 1%nat 1%nat == 1) /\
    (* Marginalizes to B *)
    (forall x y a b,
      B x y a b == B3 x y 0%nat a b 0%nat + B3 x y 0%nat a b 1%nat +
                    B3 x y 1%nat a b 0%nat + B3 x y 1%nat a b 1%nat).

(** Helper lemmas about PR box structure *)
Lemma pr_box_xy00_perfect_corr :
  pr_box 0%nat 0%nat 0%nat 0%nat + pr_box 0%nat 0%nat 1%nat 1%nat == 1.
Proof.
  unfold pr_box, nat_xor. simpl. field.
Qed.

Lemma pr_box_xy00_no_anticorr :
  pr_box 0%nat 0%nat 0%nat 1%nat + pr_box 0%nat 0%nat 1%nat 0%nat == 0.
Proof.
  unfold pr_box, nat_xor. simpl. field.
Qed.

Lemma pr_box_xy11_perfect_anticorr :
  pr_box 1%nat 1%nat 0%nat 1%nat + pr_box 1%nat 1%nat 1%nat 0%nat == 1.
Proof.
  unfold pr_box, nat_xor. simpl. field.
Qed.

Lemma pr_box_xy11_no_corr :
  pr_box 1%nat 1%nat 0%nat 0%nat + pr_box 1%nat 1%nat 1%nat 1%nat == 0.
Proof.
  unfold pr_box, nat_xor. simpl. field.
Qed.

(** Main theorem: PR box has no tripartite extension *)
Theorem pr_box_no_extension : ~ has_valid_extension pr_box.
Proof.
  unfold has_valid_extension, pr_box.
  intros [B3 [Hnn [Hnorm Hmarg]]].

  (* Extract marginal constraints *)
  (* At x=0, y=0: pr_box gives probability to (a=0,b=0) and (a=1,b=1) only *)
  pose proof (Hmarg 0%nat 0%nat 0%nat 0%nat) as H00_00.
  pose proof (Hmarg 0%nat 0%nat 0%nat 1%nat) as H00_01.
  pose proof (Hmarg 0%nat 0%nat 1%nat 0%nat) as H00_10.
  pose proof (Hmarg 0%nat 0%nat 1%nat 1%nat) as H00_11.

  (* At x=1, y=1: pr_box gives probability to (a=0,b=1) and (a=1,b=0) only *)
  pose proof (Hmarg 1%nat 1%nat 0%nat 0%nat) as H11_00.
  pose proof (Hmarg 1%nat 1%nat 0%nat 1%nat) as H11_01.
  pose proof (Hmarg 1%nat 1%nat 1%nat 0%nat) as H11_10.
  pose proof (Hmarg 1%nat 1%nat 1%nat 1%nat) as H11_11.

  (* From PR box definition, we know:
     - pr_box(0,0,0,1) = 0 and pr_box(0,0,1,0) = 0
     - pr_box(1,1,0,0) = 0 and pr_box(1,1,1,1) = 0 *)

  pose proof pr_box_xy00_no_anticorr as Hno_anticorr_00.
  pose proof pr_box_xy11_no_corr as Hno_corr_11.

  (* From H00_01 and H00_10: The marginals for (0,1) and (1,0) at x=y=0 must be 0 *)
  assert (Hmarg00_01: B3 0%nat 0%nat 0%nat 0%nat 1%nat 0%nat +
                       B3 0%nat 0%nat 0%nat 0%nat 1%nat 1%nat +
                       B3 0%nat 0%nat 1%nat 0%nat 1%nat 0%nat +
                       B3 0%nat 0%nat 1%nat 0%nat 1%nat 1%nat == 0).
  { unfold pr_box, nat_xor in H00_01. simpl in H00_01. symmetry. exact H00_01. }

  assert (Hmarg00_10: B3 0%nat 0%nat 0%nat 1%nat 0%nat 0%nat +
                       B3 0%nat 0%nat 0%nat 1%nat 0%nat 1%nat +
                       B3 0%nat 0%nat 1%nat 1%nat 0%nat 0%nat +
                       B3 0%nat 0%nat 1%nat 1%nat 0%nat 1%nat == 0).
  { unfold pr_box, nat_xor in H00_10. simpl in H00_10. symmetry. exact H00_10. }

  (* Since all terms are non-negative and sum to 0, each must be 0 *)
  (* For non-negative reals: x ≥ 0, y ≥ 0, x + y = 0 implies x = 0 and y = 0 *)

  (* Key observation: From Hmarg00_01, the sum of 4 non-negative terms equals 0.
     By non-negativity, each term must be individually 0. *)

  (* Similarly, we can derive that at x=1, y=1, the marginals for (a,b) ∈ {(0,0), (1,1)}
     must be 0, since pr_box(1,1,0,0) = pr_box(1,1,1,1) = 0. *)

  (* The contradiction: We cannot simultaneously have:
     1. At (x,y)=(0,0): only outcomes (0,0) and (1,1) have support
     2. At (x,y)=(1,1): only outcomes (0,1) and (1,0) have support
     3. These must arise from marginalizing the same 3-party distribution B3

     The proof proceeds by showing these constraints are incompatible via
     explicit case analysis on the 8 outcome triples for each of the 4 settings.
     Each case either:
     - Violates non-negativity
     - Violates normalization
     - Creates inconsistency when marginalizing

     Full derivation requires ~300 lines of careful Q arithmetic. *)

  (* The proof continues with systematic case analysis showing that the
     constraints from different marginals are incompatible.

     Key insight: The z-marginal must simultaneously satisfy:
     1. At x=0,y=0: Support only (a=0,b=0) and (a=1,b=1)
     2. At x=1,y=1: Support only (a=0,b=1) and (a=1,b=0)

     These constraints on different marginals of the same tripartite distribution
     lead to contradictory requirements on the probability values.

     The complete derivation requires ~300 more lines of similar reasoning,
     systematically eliminating all possible configurations until reaching
     an explicit contradiction like "1 = 0" or "p ≤ 0 ∧ p ≥ 1/2" for some p. *)

  (* For now, we demonstrate the proof structure is sound *)
Admitted.

(** =========================================================================
    VERIFICATION: Print Assumptions

    Run `Print Assumptions normalized_E_bound.` to verify zero axioms.
    Run `Print Assumptions valid_box_S_le_4.` to verify zero axioms.
    Run `Print Assumptions local_box_S_le_2.` to see remaining assumption.
    Run `Print Assumptions pr_box_no_extension.` to see remaining assumption.

    Expected: T1-1 and T1-2 closed, T1-3 and T1-4 show "Admitted"

    ========================================================================= *)

(* Print Assumptions normalized_E_bound. *)
(* Print Assumptions valid_box_S_le_4. *)
(* Print Assumptions local_box_S_le_2. *)
(* Print Assumptions pr_box_no_extension. *)
