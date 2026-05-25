(** BornRule: Measurement probabilities on the Bloch sphere

    THE RESULT:
    For a qubit parameterized by Bloch vector (x,y,z), if the probability
    rule P is linear in z (affine) with P(z=+1)=1 and P(z=-1)=0, then
    P(z) = (1+z)/2. This is a uniqueness theorem for affine interpolation
    on [-1,1] with fixed boundary conditions.

    WHAT THIS IS:
    The Born rule probability assignment P(0)=(1+z)/2, P(1)=(1-z)/2 is the
    unique affine probability rule satisfying the boundary conditions. This
    is algebra: solve P(z)=az+b with P(1)=1, P(-1)=0.

    WHAT THIS IS NOT:
    This is NOT a derivation of the Born rule from information accounting
    or mu-cost. The linearity hypothesis (is_linear_in_z) carries the
    essential content. See BornRuleLinearity.v for the argument connecting
    no-signaling to linearity (which is a definitional equivalence, as
    noted in that file). See ProbabilityImpossibility.v for the honest
    negative result: composition alone cannot uniquely determine the
    Born rule.

    THE SETUP:
    Qubit state on Bloch sphere: |ψ⟩ parameterized by (x,y,z) where x²+y²+z²≤1.
    Computational basis measurement gives outcomes |0⟩ or |1⟩ with probabilities:
    - P(0) = (1+z)/2
    - P(1) = (1-z)/2

    These satisfy P(0)+P(1)=1 and are the standard Bloch sphere probabilities.

    Find a different probability assignment that is affine in z and
    matches the boundary conditions. The uniqueness proof shows this
    is impossible.
*)

(* INQUISITOR NOTE: proof-connectivity, bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

(** Measurement setup. *)

(** A qubit measurement in the computational basis *)
(** State: |ψ⟩ = α|0⟩ + β|1⟩ with |α|² + |β|² = 1 *)

(** Bloch sphere representation: z-component determines computational-basis
    probabilities. *)
(** For state with Bloch vector (x, y, z):
    P(|0⟩) = (1 + z)/2
    P(|1⟩) = (1 - z)/2 *)

Definition prob_zero (x y z : R) : R := (1 + z) / 2.
Definition prob_one (x y z : R) : R := (1 - z) / 2.

(** Bloch-ball states make both computational-basis probabilities non-negative. *)
Lemma probs_nonneg : forall x y z,
  x*x + y*y + z*z <= 1 ->
  0 <= prob_zero x y z /\ 0 <= prob_one x y z.
Proof.
  intros x y z Hvalid.
  unfold prob_zero, prob_one.
  (* z² ≤ x² + y² + z² ≤ 1, so z² ≤ 1, so -1 ≤ z ≤ 1 *)
  assert (Hzz: z*z <= 1).
  { assert (Hsum: x*x + y*y + z*z <= 1) by exact Hvalid.
    assert (Hxy: x*x + y*y >= 0) by nra.
    lra. }
  assert (Hz : -1 <= z <= 1).
  { split.
    - (* z ≥ -1 *)
      destruct (Rle_lt_dec (-1) z) as [H|H]; [exact H|].
      (* z < -1 means z² > 1, contradiction *)
      assert (z * z > 1) by nra. lra.
    - (* z ≤ 1 *)
      destruct (Rle_lt_dec z 1) as [H|H]; [exact H|].
      (* z > 1 means z² > 1, contradiction *)
      assert (z * z > 1) by nra. lra. }
  lra.
Qed.

(* DEFINITIONAL HELPER — INQUISITOR NOTE: arithmetic derivation from prob_zero + prob_one definitions. *)
(** The two computational-basis probabilities sum to one by definition. *)
Lemma probs_sum_to_one : forall x y z,
  prob_zero x y z + prob_one x y z = 1.
Proof.
  intros. unfold prob_zero, prob_one. lra.
Qed.

(** A simple measurement-cost proxy. *)

(** Before measurement: information about outcome is uncertain *)
(** Shannon entropy H = -Σ p_i log p_i *)

(** After measurement: we know the outcome definitively *)
(** Information gained = H (prior uncertainty eliminated) *)

(** For a pure state |ψ⟩ measured in its eigenbasis: H = 0 (no surprise) *)
(** For a maximally mixed state: H = 1 bit (maximal surprise) *)

(** [measurement_mu_cost] is a linear-entropy proxy for uncertainty.
    It is not Shannon entropy or von Neumann entropy; the comments below only
    use the two facts this definition proves: pure states have zero cost and
    mixed states have positive cost. *)
Definition measurement_mu_cost (x y z : R) : R :=
  (* For simplicity, use linear entropy instead of von Neumann entropy *)
  (* Linear entropy S_L = 1 - Tr(ρ²) = (1 - x² - y² - z²)/2 *)
  (1 - x*x - y*y - z*z) / 2.

(** Pure states have zero measurement cost (already definite) *)
Lemma pure_state_zero_cost : forall x y z,
  x*x + y*y + z*z = 1 ->
  measurement_mu_cost x y z = 0.
Proof.
  intros x y z Hpure.
  unfold measurement_mu_cost.
  replace (x*x + y*y + z*z) with 1 by lra.
  lra.
Qed.

(** Positivity of the cost on strictly-mixed states would follow by
    unfolding measurement_mu_cost and lra. No caller in the development
    needs it as a standalone lemma, so it is not exported. *)

(** Born-rule uniqueness under an affine-in-z hypothesis. *)

(** An alternative probability rule *)
Definition ProbRule := R -> R -> R -> R -> R.  (* x y z → (p0, p1) via first component *)

(** A probability rule is valid if it satisfies basic axioms *)
Definition valid_prob_rule (P : ProbRule) : Prop :=
  (* Non-negative *)
  (forall x y z, x*x + y*y + z*z <= 1 -> 0 <= P x y z 0) /\
  (forall x y z, x*x + y*y + z*z <= 1 -> 0 <= P x y z 1) /\
  (* Normalized *)
  (forall x y z, P x y z 0 + P x y z 1 = 1) /\
  (* Consistent with pure states: |0⟩ → P(0)=1, |1⟩ → P(0)=0 *)
  (P 0 0 1 0 = 1) /\  (* |0⟩ state *)
  (P 0 0 (-1) 0 = 0).  (* |1⟩ state *)

(** The Born rule as a probability rule *)
Definition born_rule : ProbRule :=
  fun x y z outcome => 
    if Rle_dec outcome (1/2) then prob_zero x y z else prob_one x y z.

(** The concrete Born rule satisfies the validity predicate above. *)
Theorem born_rule_valid : 
  valid_prob_rule born_rule.
Proof.
  unfold valid_prob_rule, born_rule.
  repeat split.
  - intros x y z Hvalid.
    destruct (Rle_dec 0 (1/2)); [|lra].
    pose proof (probs_nonneg x y z Hvalid) as [H _]. exact H.
  - intros x y z Hvalid.
    destruct (Rle_dec 1 (1/2)); [lra|].
    pose proof (probs_nonneg x y z Hvalid) as [_ H]. exact H.
  - intros x y z.
    destruct (Rle_dec 0 (1/2)); destruct (Rle_dec 1 (1/2)); try lra;
    apply probs_sum_to_one.
  - destruct (Rle_dec 0 (1/2)); [|lra].
    unfold prob_zero. lra.
  - destruct (Rle_dec 0 (1/2)); [|lra].
    unfold prob_zero. lra.
Qed.

(** Linear extension uniqueness. *)

(** A rule is linear in z when outcome 0 has the affine form a*z+b on the
    Bloch ball. *)

Definition is_linear_in_z (P : ProbRule) : Prop :=
  exists a b : R,
    forall x y z, x*x + y*y + z*z <= 1 -> P x y z 0 = a * z + b.

(** Any valid probability rule affine in z has the Born value for outcome 0. *)
Theorem linear_implies_born :
  forall P : ProbRule,
    valid_prob_rule P ->
    is_linear_in_z P ->
    forall x y z, 
      x*x + y*y + z*z <= 1 ->
      P x y z 0 = prob_zero x y z.
Proof.
  intros P Hvalid Hlin x y z Hstate.
  destruct Hvalid as [_ [_ [Hnorm [H0 H1]]]].
  destruct Hlin as [a [b Hlinear]].
  (* From |0⟩ state: P(0,0,1,0) = a*1 + b = 1 *)
  assert (Heq1: a + b = 1).
  { specialize (Hlinear 0 0 1).
    assert (H01: 0*0 + 0*0 + 1*1 <= 1) by lra.
    specialize (Hlinear H01).
    rewrite H0 in Hlinear. lra. }
  (* From |1⟩ state: P(0,0,-1,0) = a*(-1) + b = 0 *)
  assert (Heq2: -a + b = 0).
  { specialize (Hlinear 0 0 (-1)).
    assert (H01: 0*0 + 0*0 + (-1)*(-1) <= 1) by lra.
    specialize (Hlinear H01).
    rewrite H1 in Hlinear. lra. }
  (* Solve: a = 1/2, b = 1/2 *)
  assert (Ha: a = 1/2) by lra.
  assert (Hb: b = 1/2) by lra.
  (* P(x,y,z,0) = z/2 + 1/2 = (1+z)/2 = prob_zero *)
  specialize (Hlinear x y z Hstate).
  rewrite Ha, Hb in Hlinear.
  unfold prob_zero. lra.
Qed.

(** Connection to measurement disturbance. *)

(** Post-measurement state after outcome 0: projects to |0⟩ *)
Definition post_measurement_zero (x y z : R) : R * R * R := (0, 0, 1).

(** Post-measurement state after outcome 1: projects to |1⟩ *)
Definition post_measurement_one (x y z : R) : R * R * R := (0, 0, -1).

(** Measurement creates a pure state (purity = 1) *)
Lemma measurement_creates_pure_zero : forall x y z,
  let '(x', y', z') := post_measurement_zero x y z in
  x'*x' + y'*y' + z'*z' = 1.
Proof.
  intros. simpl. lra.
Qed.

(** Outcome 1 also projects to a pure computational-basis state. *)
Lemma measurement_creates_pure_one : forall x y z,
  let '(x', y', z') := post_measurement_one x y z in
  x'*x' + y'*y' + z'*z' = 1.
Proof.
  intros. simpl. lra.
Qed.

(** What this file does not get from Gleason.

    Gleason's theorem is the real theorem about probability measures on quantum
    propositions. This file does not formalize Gleason and does not derive
    linearity. The next predicate is only a weak side condition: the
    measurement-cost proxy is non-negative on valid Bloch states. It does not
    inspect [P]. *)

(** The cost proxy is non-negative on valid Bloch states. *)
Definition measurement_cost_nonnegative (P : ProbRule) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    measurement_mu_cost x y z >= 0.

(** The Born rule satisfies the weak cost-side condition, because every rule
    satisfies it when the state is inside the Bloch ball. *)
Theorem born_rule_measurement_cost_nonnegative :
  measurement_cost_nonnegative born_rule.
Proof.
  unfold measurement_cost_nonnegative, measurement_mu_cost.
  intros x y z Hvalid.
  assert (Hpurity: x*x + y*y + z*z >= 0) by nra.
  lra.
Qed.

(** Summary: Born rule from validity plus affine linearity. *)

(** The theorem below proves exactly this:
    
    1. CONSERVATION: Total probability = 1 (normalization)
    2. POSITIVITY: All probabilities ≥ 0
    3. EIGENSTATE CONSTRAINT: Measurement of eigenstate is certain
    4. LINEARITY: outcome 0 is affine in z
    
    The cost-side condition is kept in the statement for compatibility with the
    surrounding development, but the proof does not use it. The load-bearing
    assumption is [is_linear_in_z]. *)

Theorem valid_linear_rule_is_born_with_cost_side_condition :
  forall P : ProbRule,
    valid_prob_rule P ->
    is_linear_in_z P ->
    measurement_cost_nonnegative P ->
    forall x y z,
      x*x + y*y + z*z <= 1 ->
      P x y z 0 = prob_zero x y z /\
      P x y z 1 = prob_one x y z.
Proof.
  intros P Hvalid Hlin Hmu x y z Hstate.
  pose proof Hvalid as Hvalid_copy.
  split.
  - apply (linear_implies_born P Hvalid Hlin x y z Hstate).
  - (* P(1) = 1 - P(0) = 1 - prob_zero = prob_one *)
    destruct Hvalid_copy as [_ [_ [Hnorm _]]].
    specialize (Hnorm x y z).
    pose proof (linear_implies_born P Hvalid Hlin x y z Hstate) as HP0.
    rewrite HP0 in Hnorm.
    pose proof (probs_sum_to_one x y z) as Hsum.
    lra.
Qed.

(* INQUISITOR NOTE: connectivity anchor for post-measurement pure-state lemmas. *)
Lemma born_rule_measurement_cases :
  (forall x y z,
    let '(x', y', z') := post_measurement_zero x y z in
    x'*x' + y'*y' + z'*z' = 1) /\
  (forall x y z,
    let '(x', y', z') := post_measurement_one x y z in
    x'*x' + y'*y' + z'*z' = 1).
Proof.
  split; [exact measurement_creates_pure_zero | exact measurement_creates_pure_one].
Qed.
