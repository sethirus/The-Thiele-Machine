(** Rational CHSH ceiling predicates and their ordering.

    [satisfies_rational_chsh_ceiling] combines a supplied no-signaling
    proposition with the one-sided bound S <= 5657/2000. This rational
    ceiling exceeds 2*sqrt(2); it is not a characterization of physical
    quantum correlations. The results below are arithmetic and predicate
    introduction/elimination. Full correlator membership is represented by
    [ElliptopeCompletion.elliptope_realizable]. *)

From Coq Require Import List Bool Arith.PeanoNat QArith Lia.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import CHSHExtraction MuCostModel.
From Kernel Require Import ClassicalBound TsirelsonUpperBound.

Record AbstractCorrelation : Type := {
  satisfies_no_signaling : Prop;
  chsh_value : Q
}.

Definition classical_bound : Q := 2.

Definition tsirelson_bound : Q := (5657 # 2000)%Q.

Definition satisfies_rational_chsh_ceiling (ac : AbstractCorrelation) : Prop :=
  ac.(satisfies_no_signaling) /\ ac.(chsh_value) <= tsirelson_bound.

Definition certifiable_with_mu_zero (ac : AbstractCorrelation) : Prop :=
  exists fuel trace s_init,
    mu_cost_of_trace fuel trace 0 = 0%nat /\
    chsh_from_vm_trace fuel trace s_init = ac.(chsh_value) /\
    ac.(satisfies_no_signaling).

Definition rational_chsh_ceiling_bound
  (ac : AbstractCorrelation) (Hq : satisfies_rational_chsh_ceiling ac) :
  ac.(chsh_value) <= tsirelson_bound :=
  match Hq with conj _ Hbound => Hbound end.

Definition zero_cost_trace_no_signaling
  (ac : AbstractCorrelation) (Hcert : certifiable_with_mu_zero ac) :
  ac.(satisfies_no_signaling) :=
  match Hcert with
  | ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj _ (conj _ Hns)))) => Hns
  end.

Definition rational_chsh_ceiling_bound_projection
  (ac : AbstractCorrelation) (Hq : satisfies_rational_chsh_ceiling ac) :
  ac.(chsh_value) <= tsirelson_bound :=
  rational_chsh_ceiling_bound ac Hq.

Lemma classical_bound_implies_rational_ceiling :
  forall ac,
    ac.(satisfies_no_signaling) ->
    ac.(chsh_value) <= classical_bound ->
    satisfies_rational_chsh_ceiling ac.
Proof.
  intros ac Hns Hclass.
  unfold satisfies_rational_chsh_ceiling.
  split; [exact Hns |].
  unfold tsirelson_bound, tsirelson_bound, classical_bound in *.

  apply (Qle_trans _ 2).
  - exact Hclass.
  - unfold Qle. simpl. lia.
Qed.

Definition rational_bound_ordering : Prop :=

  forall ac, ac.(chsh_value) <= classical_bound ->
             ac.(chsh_value) <= tsirelson_bound.

Theorem classical_bound_below_rational_ceiling : rational_bound_ordering.
Proof.
  unfold rational_bound_ordering.
  intros ac Hclass.
  apply (Qle_trans _ classical_bound).
  - exact Hclass.
  - unfold classical_bound, tsirelson_bound.
    unfold Qle. simpl. lia.
Qed.

Definition rational_chsh_ceiling_spec : Prop :=
  forall ac,
    satisfies_rational_chsh_ceiling ac <->
    (ac.(satisfies_no_signaling) /\ ac.(chsh_value) <= tsirelson_bound).

Theorem rational_chsh_ceiling_unfolds : rational_chsh_ceiling_spec.
Proof.
  unfold rational_chsh_ceiling_spec, satisfies_rational_chsh_ceiling.
  intro ac. split; intro H; exact H.
Qed.

Definition rational_bound_summary : Prop :=

  rational_bound_ordering /\
  rational_chsh_ceiling_spec.

Theorem rational_bound_summary_holds : rational_bound_summary.
Proof.
  unfold rational_bound_summary.
  split.
  - exact classical_bound_below_rational_ceiling.
  - exact rational_chsh_ceiling_unfolds.
Qed.

Theorem rational_bound_ordering_and_spec :
  rational_bound_ordering /\
  rational_chsh_ceiling_spec.
Proof.
  split.
  - exact classical_bound_below_rational_ceiling.
  - exact rational_chsh_ceiling_unfolds.
Qed.

Theorem rational_chsh_ceiling_intro :
  forall ac,
    ac.(satisfies_no_signaling) ->
    ac.(chsh_value) <= tsirelson_bound ->
    satisfies_rational_chsh_ceiling ac.
Proof.
  intros ac Hns Hbound.
  unfold satisfies_rational_chsh_ceiling.
  split; assumption.
Qed.

Theorem above_ceiling_fails_rational_bound :
  forall ac,
    ac.(chsh_value) > tsirelson_bound ->
    ~(satisfies_rational_chsh_ceiling ac).
Proof.
  intros ac Hgt Hqm.
  unfold satisfies_rational_chsh_ceiling in Hqm.
  destruct Hqm as [_ Hbound].

  apply Qlt_not_le in Hgt.
  contradiction.
Qed.

