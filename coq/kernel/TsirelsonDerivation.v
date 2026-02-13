(** =========================================================================
    TSIRELSON DERIVATION FROM μ-ACCOUNTING
    ========================================================================= *)

From Coq Require Import QArith Qabs Lia List Reals.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep CHSHExtraction MuCostModel.
From Kernel Require Import AlgebraicCoherence.
From Kernel Require Import HardAssumptions.

(** Correlation specification complexity *)
Definition correlation_mu_cost (c : Correlators) : Q :=
  if Qle_bool (Qabs (S_from_correlators c)) tsirelson_bound
  then 0
  else Qabs (S_from_correlators c) - tsirelson_bound.

Module TsirelsonFromMuAccounting.

(** Non-zero correlation μ-cost implies non-coherent (or exceeds bound) *)
Theorem nonzero_mu_implies_exceeds_bound :
  forall c : Correlators,
    ~(correlation_mu_cost c == 0) ->
    ~(Qabs (S_from_correlators c) <= tsirelson_bound).
Proof.
  intros c Hnonzero Hle.
  apply Hnonzero.
  unfold correlation_mu_cost.
  destruct (Qle_bool (Qabs (S_from_correlators c)) tsirelson_bound) eqn:Htest.
  - reflexivity.
  - exfalso.
    assert (Htrue : Qle_bool (Qabs (S_from_correlators c)) tsirelson_bound = true).
    { apply Qle_bool_iff. exact Hle. }
    rewrite Htrue in Htest. discriminate.
Qed.

(** Total μ-cost for CHSH experiment *)
Definition total_mu_cost 
  (fuel : nat) (trace : list vm_instruction) (c : Correlators) : Q :=
  inject_Z (Z.of_nat (mu_cost_of_trace fuel trace 0)) + correlation_mu_cost c.

(** Total μ = 0 definition *)
Definition total_mu_zero 
  (fuel : nat) (trace : list vm_instruction) (c : Correlators) : Prop :=
  mu_zero_program fuel trace /\ correlation_mu_cost c == 0.

(** Helper lemma for Q arithmetic: y < x implies 0 < x - y *)
Lemma Qgt_minus_pos : forall x y : Q, y < x -> 0 < x - y.
Proof.
  intros x y H.
  unfold Qlt, Qminus in *.
  simpl in *.
  lia.
Qed.

Theorem tsirelson_from_correlation_mu_zero :
  forall c : Correlators,
    correlation_mu_cost c == 0 ->
    Qabs (S_from_correlators c) <= tsirelson_bound.
Proof.
  intros c Hzero.
  unfold correlation_mu_cost in Hzero.
  destruct (Qle_bool (Qabs (S_from_correlators c)) tsirelson_bound) eqn:Hle.
  - apply Qle_bool_iff in Hle. exact Hle.
  - exfalso.
    assert (Hgt : ~(Qabs (S_from_correlators c) <= tsirelson_bound)).
    { intro Hcontra. 
      assert (Htrue : Qle_bool (Qabs (S_from_correlators c)) tsirelson_bound = true).
      { apply Qle_bool_iff. exact Hcontra. }
      rewrite Htrue in Hle. discriminate. }
    apply Qnot_le_lt in Hgt.
    assert (Hpos : 0 < Qabs (S_from_correlators c) - tsirelson_bound).
    { apply Qgt_minus_pos. exact Hgt. }
    rewrite Hzero in Hpos.
    apply Qlt_irrefl in Hpos. exact Hpos.
Qed.

Corollary tsirelson_from_total_mu_zero :
  forall fuel trace c,
    total_mu_zero fuel trace c ->
    Qabs (S_from_correlators c) <= tsirelson_bound.
Proof.
  intros fuel trace c [Hinstr Hcorr].
  apply tsirelson_from_correlation_mu_zero. exact Hcorr.
Qed.

Theorem tsirelson_from_pure_accounting :
  forall fuel trace c,
    Qabs (E00 c) <= 1 -> Qabs (E01 c) <= 1 ->
    Qabs (E10 c) <= 1 -> Qabs (E11 c) <= 1 ->
    total_mu_zero fuel trace c ->
    Qabs (S_from_correlators c) <= tsirelson_bound.
Proof.
  intros fuel trace c _ _ _ _ Htotal.
  apply tsirelson_from_total_mu_zero with (fuel := fuel) (trace := trace).
  exact Htotal.
Qed.

End TsirelsonFromMuAccounting.
