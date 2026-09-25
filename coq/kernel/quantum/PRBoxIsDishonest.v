(** PRBoxIsDishonest: the deterministic PR-box realization signals.

    SCOPE.
    ------
    We construct a deterministic [CorrelatedResource] whose outcomes
    realize the PR-box algebra (A XOR B = x AND y), and prove:
    1. It is free ([prbox_is_free]).
    2. It satisfies the standard 2-to-1 RAC protocol on every input
       ([prbox_rac_succeeds]).
    3. It is therefore signalling ([prbox_resource_signals]), as forced
       by [rac_success_implies_signalling] in MeasurementExtraction.v.

    All three statements are closed under the global context.

    The result is about the [CorrelatedResource] interface and its
    [cr_no_signalling] predicate.

    It does not rule out the separate relational construction in
    [MeasurementExtraction.relational_prbox_is_consistent], because that is not
    the deterministic resource defined here.

    The conclusion is therefore a deterministic no-signalling impossibility in
    this formal interface, not a general physical claim about every PR-box model.

    PROOF SCOPE: standalone algebra; any VM correspondence is supplied by a
    separate bridge theorem.
*)

From Coq Require Import Bool Arith.PeanoNat Lia.
From Kernel Require Import MeasurementExtraction.

(** *** The PR-box realization.

    Shared state is a single bool [sigma] (irrelevant for the algebra).
    Outcomes:
      A = sigma
      B = sigma XOR (x AND y)
    Constraint: A XOR B = sigma XOR sigma XOR (x AND y) = x AND y.

    Note: B depends on x. The resource therefore violates the formal
    [cr_no_signalling] predicate by construction. The general deterministic
    no-signalling impossibility is supplied by [MeasurementExtraction.v]. *)

Definition prbox_outcomes (s : bool) (x y : bool) : bool * bool :=
  (s, xorb s (andb x y)).

Definition prbox_resource : CorrelatedResource :=
  mk_correlated_resource
    bool                (* cr_state *)
    false               (* cr_init  *)
    prbox_outcomes      (* cr_outcomes *)
    (fun _ => 0)        (* cr_cost identically 0 *).

(** prbox_resource is free by construction. *)
Lemma prbox_is_free : cr_is_free prbox_resource.
Proof.
  intro x. reflexivity.
Qed.

(** The PR-box constraint A XOR B = x AND y holds on this realization. *)
Lemma prbox_constraint :
  forall (s x y : bool),
    xorb (cr_alice prbox_resource s x y)
         (cr_bob   prbox_resource s x y)
    = andb x y.
Proof.
  intros s x y.
  unfold cr_alice, cr_bob, prbox_resource, prbox_outcomes; simpl.
  destruct s, x, y; reflexivity.
Qed.

(** Main algebraic lemma. The RAC protocol output for this realization
    equals a_y on every input. *)
Lemma prbox_protocol_calculation :
  forall (a0 a1 y : bool),
    let x := xorb a0 a1 in
    let A := cr_alice prbox_resource (cr_init prbox_resource) x y in
    let B := cr_bob   prbox_resource (cr_init prbox_resource) x y in
    let c := xorb a0 A in
    xorb c B = (if y then a1 else a0).
Proof.
  intros a0 a1 y.
  unfold cr_alice, cr_bob, prbox_resource, prbox_outcomes, cr_init; simpl.
  destruct a0, a1, y; reflexivity.
Qed.

(** This resource makes the formal RAC protocol succeed on every input. *)
Theorem prbox_rac_succeeds : rac_protocol_succeeds prbox_resource.
Proof.
  intros a0 a1 y. apply prbox_protocol_calculation.
Qed.

(** *** Main result: the deterministic realization signals in this model.

    Proved by combining the imported RAC implication
    [rac_success_implies_signalling] from MeasurementExtraction.v with
    [prbox_rac_succeeds] above. No axioms. *)
Theorem prbox_resource_signals :
  ~ cr_no_signalling prbox_resource.
Proof.
  apply rac_success_implies_signalling. exact prbox_rac_succeeds.
Qed.

(** Direct, calculational form: Bob's outcome on this realization
    explicitly depends on Alice's input x.

    Set s = false, y = true. Then Bob's outcome at x = false is
    false XOR (false AND true) = false, but Bob's outcome at x = true is
    false XOR (true AND true) = true. The two differ.

    This is the explicit dependence on x that violates the formal
    no-signalling predicate. *)
Theorem prbox_bob_depends_on_x :
  cr_bob prbox_resource false false true
  <> cr_bob prbox_resource false true  true.
Proof.
  unfold cr_bob, prbox_resource, prbox_outcomes; simpl. discriminate.
Qed.

(** First lifting: any CorrelatedResource whose outcomes universally
    satisfy the PR-box constraint makes the RAC protocol succeed. *)
Lemma prbox_relation_implies_rac_success :
  forall (CR : CorrelatedResource),
    (forall (s : cr_state CR) (x y : bool),
       xorb (cr_alice CR s x y) (cr_bob CR s x y) = andb x y) ->
    rac_protocol_succeeds CR.
Proof.
  intros CR Hrel a0 a1 y.
  cbv zeta.
  remember (cr_alice CR (cr_init CR) (xorb a0 a1) y) as A.
  remember (cr_bob   CR (cr_init CR) (xorb a0 a1) y) as B.
  assert (HAB : xorb A B = andb (xorb a0 a1) y).
  { subst A B. apply Hrel. }
  destruct a0, a1, y, A, B; simpl in HAB; try discriminate; reflexivity.
Qed.

(** Universal corollary: any deterministic resource realizing the PR-box
    constraint signals. Carrier-independent statement of the same
    underlying fact. *)
Corollary prbox_relation_implies_signalling :
  forall (CR : CorrelatedResource),
    (forall (s : cr_state CR) (x y : bool),
       xorb (cr_alice CR s x y) (cr_bob CR s x y) = andb x y) ->
    ~ cr_no_signalling CR.
Proof.
  intros CR Hrel.
  apply rac_success_implies_signalling.
  apply prbox_relation_implies_rac_success.
  exact Hrel.
Qed.

(** *** Quantitative: this realization saturates the formal RAC count at 8/8.

    The formal no-signalling bound is 6/8 successes
    ([MeasurementExtraction.classical_rac_bound]). This signaling realization
    achieves 8/8, giving the stated gap in the count model. *)
Theorem prbox_rac_success_count :
  rac_success_count prbox_resource = 8.
Proof.
  unfold rac_success_count, rac_succeeds_at, prbox_resource,
         cr_alice, cr_bob, prbox_outcomes, cr_init.
  cbn. reflexivity.
Qed.

(** Combined statement: this realization achieves 8/8, while the formal no-signalling
    bound is 6/8, giving a gap of 2. *)
Theorem prbox_strictly_beats_classical :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    rac_success_count CR + 2 <= rac_success_count prbox_resource.
Proof.
  intros CR Hns.
  rewrite prbox_rac_success_count.
  pose proof (classical_rac_bound CR Hns) as H.
  lia.
Qed.

(** *** This realization reaches the formal CHSH-style match count.

    PR-box hits 4/4, classical caps at 3/4. Same statement as
    [prbox_strictly_beats_classical] but in CHSH normalization. *)
Theorem prbox_match_count_is_four :
  prbox_match_count prbox_resource = 4.
Proof.
  reflexivity.
Qed.

(** Strict count gap: this match count exceeds every formal no-signalling resource
    by at least 1. *)
Theorem prbox_chsh_strict_gap :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    prbox_match_count CR + 1 <= prbox_match_count prbox_resource.
Proof.
  intros CR Hns.
  rewrite prbox_match_count_is_four.
  pose proof (prbox_match_classical_bound CR Hns) as H.
  lia.
Qed.

(** *** LITERAL SKETCH TARGET: the PR-box correlation cannot be wrapped
    as an HonestMeasurementSystem.

    The PR-box correlation has correlators (E_00, E_01, E_10, E_11) =
    (+1, +1, +1, -1) at zero cost. Any attempt to construct an
    HonestMeasurementSystem with those values must discharge the [hms_a3]
    obligation, which requires |S| <= 2 at zero cost. The PR-box has
    |S| = 4 > 2, so the obligation cannot be discharged: no
    HonestMeasurementSystem with PR-box correlators at zero cost
    exists. *)

From Coq Require Import Reals Lra.
From Kernel Require Import HonestMeasurement.

Local Open Scope R_scope.

(** No HMS realizes the PR-box correlation pattern at zero cost. *)
Theorem pr_box_correlation_not_HMS :
  ~ exists (H : HonestMeasurementSystem),
       hms_E00 H = 1
    /\ hms_E01 H = 1
    /\ hms_E10 H = 1
    /\ hms_E11 H = -1
    /\ hms_cost H = 0%nat.
Proof.
  intros [H [HE00 [HE01 [HE10 [HE11 Hcost]]]]].
  pose proof (hms_a3_S H Hcost) as Hbound.
  unfold hms_S in Hbound.
  rewrite HE00, HE01, HE10, HE11 in Hbound.
  (* hms_S H = 1 + 1 + 1 - (-1) = 4. Rabs 4 = 4 > 2. *)
  rewrite Rabs_right in Hbound by lra.
  lra.
Qed.

(** Cleaner statement variant: forbid construction at the more honest
    level — given the PR-box specifically, asking for an HMS that
    produces it (with hms_cost = 0) is impossible. *)
Corollary no_zero_cost_HMS_with_chsh_S_of_4 :
  ~ exists (H : HonestMeasurementSystem),
      hms_cost H = 0%nat /\ hms_S H = 4.
Proof.
  intros [H [Hcost HS]].
  pose proof (hms_a3_S H Hcost) as Hbound.
  rewrite HS in Hbound.
  (* Rabs 4 = 4 > 2. *)
  rewrite Rabs_right in Hbound by lra.
  lra.
Qed.

(** ** Scope of the result.

    This file is standalone algebra. Its theorems concern the specified
    correlated-resource and honest-measurement predicates; they do not
    mention VMState or vm_mu. Any connection to the VM ledger must be made by
    a separate theorem that supplies that correspondence explicitly. *)
