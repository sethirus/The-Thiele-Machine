(** * F2_PerMinorFromCostCoherent: per-minor coherence from cost axioms

    Each of the four NPA-1 minor inequalities is individually
    derivable from [cost_coherent] alone (no additional structural
    premise), with a per-minor [t] or [s] witness chosen as a product
    of the correlator components. This is a strictly weaker positive
    result than [F2_MinorFromWitnessLocality], which needs
    witness-locality and produces a shared [t, s] for all four minors
    simultaneously (i.e. algebraic-coherence proper).

    Quantifier order:
    - algebraic-coherence:  ∃ t s, ∀ i ∈ {1..4}, minor_i(t, s) ≥ 0
    - per-minor (this file): ∀ i ∈ {1..4}, ∃ t (or s), minor_i(t) ≥ 0

    The per-minor existence is strictly weaker (the witnesses can
    differ across minors), but the per-minor existence form IS
    derivable from cost-axioms alone — and that derivation is what
    this file establishes.

    Algebraic identity: at t = a · b (the product of correlators in the
    minor), minor_3x3 t a b = (1 - a²)(1 - b²). Since |a|, |b| ≤ 1
    implies a², b² ≤ 1, both factors are non-negative, so the minor
    is non-negative.

    OP-QM scope refinement:
    - cost-axioms alone do NOT entail algebraically_coherent (F2 R1).
    - cost-axioms + per-minor existence form (this file) is
      derivable but strictly weaker than algebraic-coherence.
    - cost-axioms + witness-locality DO entail algebraically_coherent
      (F2 R2). Witness-locality is the precise strengthening that
      promotes per-minor existence to shared-witness existence.

    The F2 closure now has THREE rungs of precision: cost-axioms (no
    minors), cost-axioms + per-minor (each minor satisfiable), and
    cost-axioms + witness-locality (algebraic-coherence proper). *)

From Coq Require Import List Arith.PeanoNat Lia Bool ZArith QArith QArith.Qabs.
Require Import Psatz.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep AlgebraicCoherence.
From Kernel Require Import F2_MinorIndependence.

(** [cost_coherent c]: the cost-axiomatic conjunct of
    [algebraically_coherent], namely |E_xy| ≤ 1 for all four xy-pairs.
    In the Thiele framework this is the trivial bound from witness
    counts being non-negative integers. *)

Definition cost_coherent (c : Correlators) : Prop :=
  Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
  Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1.

Lemma max_trace_cost_coherent : cost_coherent max_trace.
Proof.
  unfold cost_coherent. simpl.
  repeat split; vm_compute; intro; discriminate.
Qed.

(** ** Algebraic identity: at t = a · b, the minor factors as
       (1 - a²)(1 - b²). *)

Lemma minor_3x3_at_product :
  forall a b : Q,
    minor_3x3 (a * b) a b == (1 - a*a) * (1 - b*b).
Proof.
  intros a b. unfold minor_3x3. ring.
Qed.

(** ** |x| ≤ 1 implies x² ≤ 1, hence 1 - x² ≥ 0. *)

Lemma sq_le_1_of_abs_le_1 :
  forall x : Q, Qabs x <= 1 -> x * x <= 1.
Proof.
  intros x Hx.
  pose proof (Qabs_nonneg x) as Hnn.
  apply Qabs_Qle_condition in Hx. destruct Hx as [Hxlo Hxhi].
  nra.
Qed.

Lemma one_minus_sq_nonneg :
  forall x : Q, Qabs x <= 1 -> 0 <= 1 - x * x.
Proof.
  intros. pose proof (sq_le_1_of_abs_le_1 x H) as Hsq. lra.
Qed.

(** ** Each minor is non-negative at the product-of-correlators witness. *)

Lemma minor_nonneg_at_product :
  forall a b : Q,
    Qabs a <= 1 -> Qabs b <= 1 ->
    0 <= minor_3x3 (a * b) a b.
Proof.
  intros a b Ha Hb.
  rewrite minor_3x3_at_product.
  pose proof (one_minus_sq_nonneg a Ha) as H1.
  pose proof (one_minus_sq_nonneg b Hb) as H2.
  nra.
Qed.

(** ** F2 R3 HEADLINE.

    Each of the four NPA-1 minor inequalities is individually
    satisfiable for any cost-coherent correlator c. Each minor uses
    its own t (or s) witness, chosen as the product of the relevant
    correlators. *)

Theorem cost_coherent_implies_per_minor_nonneg :
  forall c : Correlators,
    cost_coherent c ->
    (exists t : Q, 0 <= minor_3x3 t (E00 c) (E10 c)) /\
    (exists t : Q, 0 <= minor_3x3 t (E01 c) (E11 c)) /\
    (exists s : Q, 0 <= minor_3x3 s (E00 c) (E01 c)) /\
    (exists s : Q, 0 <= minor_3x3 s (E10 c) (E11 c)).
Proof.
  intros c [H00 [H01 [H10 H11]]].
  repeat split.
  - exists (E00 c * E10 c). apply minor_nonneg_at_product; assumption.
  - exists (E01 c * E11 c). apply minor_nonneg_at_product; assumption.
  - exists (E00 c * E01 c). apply minor_nonneg_at_product; assumption.
  - exists (E10 c * E11 c). apply minor_nonneg_at_product; assumption.
Qed.

(** ** Strict-weakness of the per-minor existence vs algebraic-coherence.

    The PR-box has cost-coherent correlators (|E_xy| = 1). By the
    above theorem, each minor is INDIVIDUALLY satisfiable. But the
    PR-box is NOT algebraically-coherent (no SHARED t, s makes all
    four simultaneously non-negative) — proven by
    [algebraic_max_not_coherent].

    Therefore the per-minor existence form is strictly weaker than
    algebraic-coherence: cost-coherent implies the former, but not
    the latter. *)

Theorem per_minor_strictly_weaker_than_algebraic_coherence :
  exists c : Correlators,
    cost_coherent c /\
    (exists t : Q, 0 <= minor_3x3 t (E00 c) (E10 c)) /\
    (exists t : Q, 0 <= minor_3x3 t (E01 c) (E11 c)) /\
    (exists s : Q, 0 <= minor_3x3 s (E00 c) (E01 c)) /\
    (exists s : Q, 0 <= minor_3x3 s (E10 c) (E11 c)) /\
    ~ algebraically_coherent c.
Proof.
  exists max_trace.
  pose proof max_trace_cost_coherent as Hcost.
  pose proof (cost_coherent_implies_per_minor_nonneg max_trace Hcost)
       as [H1 [H2 [H3 H4]]].
  split; [exact Hcost |].
  split; [exact H1 |].
  split; [exact H2 |].
  split; [exact H3 |].
  split; [exact H4 |].
  exact algebraic_max_not_coherent.
Qed.

(** ** Per-minor + ALSO satisfying minor #2 with SAME t requires more.

    For the PR-box specifically: at t = E_00 * E_10 = 1, minor #1 is
    satisfied. But minor #2 with the SAME t = 1 fails:
      minor_3x3 1 (E_01) (E_11) = minor_3x3 1 1 (-1)
                                = 1 - 1 - 1 - 1 + 2*1*1*(-1) = -4 < 0.

    The "shared-t" requirement of algebraic-coherence is what fails
    on the PR-box. The per-minor result is satisfied on the PR-box
    because each minor can pick its own t. *)

Lemma pr_box_minor_2_fails_at_minor_1_witness :
  ~ (0 <= minor_3x3 (E00 max_trace * E10 max_trace)
                    (E01 max_trace) (E11 max_trace)).
Proof.
  unfold max_trace. simpl.
  unfold minor_3x3. simpl. lra.
Qed.

(** ** Print Assumptions sanity.

    All theorems above close under the global context. The per-minor
    derivation uses pure rational arithmetic (ring + lra/nra) plus the
    cost_coherent definition from F2_MinorIndependence. No bypass
    markers. F2 R3 establishes the strictly-weaker positive result;
    closing OP-QM at the FULL algebraic-coherence level still requires
    the witness-locality strengthening (F2 R2). *)
