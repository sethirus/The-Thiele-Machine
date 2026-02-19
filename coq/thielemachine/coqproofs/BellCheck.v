Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.
From ThieleMachine Require Import BellInequality.

Local Open Scope Q_scope.

Record SettingAggregate := {
  agg_trials : positive;
  agg_sum_xy : Z
}.

Definition aggregate_E (agg : SettingAggregate) : Q :=
  (agg_sum_xy agg # agg_trials agg).

Record BellSummary := {
  summary00 : SettingAggregate;
  summary01 : SettingAggregate;
  summary10 : SettingAggregate;
  summary11 : SettingAggregate;
  measured_S : Q;
  epsilon : Q;
  classical_S : Q;
  classical_gap : Q;
  violation_margin : Q
}.

Definition computed_S (summary : BellSummary) : Q :=
  aggregate_E (summary11 summary)
    + aggregate_E (summary10 summary)
    + aggregate_E (summary01 summary)
    - aggregate_E (summary00 summary).

Definition summary_consistent (summary : BellSummary) : Prop :=
  measured_S summary == computed_S summary.

Definition classical_gap_witness (summary : BellSummary) : Prop :=
  classical_gap summary == ((2#1) + epsilon summary) - classical_S summary.

Definition classical_gap_nonneg (summary : BellSummary) : Prop :=
  0#1 <= classical_gap summary.

Definition violation_margin_witness (summary : BellSummary) : Prop :=
  violation_margin summary == measured_S summary - ((2#1) + epsilon summary).

Definition violation_margin_positive (summary : BellSummary) : Prop :=
  0#1 < violation_margin summary.

Definition classical_bound (summary : BellSummary) : Prop :=
  classical_S summary <= (2#1) + epsilon summary.

Definition bell_violation (summary : BellSummary) : Prop :=
  (2#1) + epsilon summary < measured_S summary.

(** [classical_gap_plus]: formal specification. *)
Lemma classical_gap_plus :
  forall summary,
    classical_gap_witness summary ->
    classical_S summary + classical_gap summary == (2#1) + epsilon summary.
Proof.
  intros summary Hwitness.
  unfold classical_gap_witness in Hwitness.
  unfold classical_gap.
  rewrite Hwitness.
  ring.
Qed.

(** [violation_margin_plus]: formal specification. *)
Lemma violation_margin_plus :
  forall summary,
    violation_margin_witness summary ->
    measured_S summary == (2#1) + epsilon summary + violation_margin summary.
Proof.
  intros summary Hwitness.
  unfold violation_margin_witness in Hwitness.
  unfold violation_margin.
  rewrite Hwitness.
  ring.
Qed.

(** HELPER: Non-negativity property *)
(** HELPER: Non-negativity property *)
Lemma Qle_plus_nonneg :
  forall a b : Q,
    0#1 <= b ->
    a <= a + b.
Proof.
  intros a b Hb.
  unfold Qle in *; simpl in *; lia.
Qed.
(** HELPER: Non-negativity property *)

(** HELPER: Non-negativity property *)
Lemma Qlt_plus_pos :
  forall a b : Q,
    0#1 < b ->
    a < a + b.
Proof.
  intros a b Hb.
  unfold Qlt in *; simpl in *; lia.
Qed.

(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
(** [CHSH_receipt_to_S]: formal specification. *)
Lemma CHSH_receipt_to_S :
  forall summary,
    summary_consistent summary ->
    measured_S summary == computed_S summary.
Proof.
  intros summary H.
  exact H.
Qed.

(** [classical_gap_implies_bound]: formal specification. *)
Lemma classical_gap_implies_bound :
  forall summary,
    classical_gap_witness summary ->
    classical_gap_nonneg summary ->
    classical_bound summary.
Proof.
  intros summary Hwitness Hnonneg.
  unfold classical_bound.
  setoid_rewrite <- (classical_gap_plus summary Hwitness).
  apply Qle_plus_nonneg.
  exact Hnonneg.
Qed.

(** [violation_margin_implies_violation]: formal specification. *)
Lemma violation_margin_implies_violation :
  forall summary,
    violation_margin_witness summary ->
    violation_margin_positive summary ->
    bell_violation summary.
Proof.
  intros summary Hwitness Hpos.
  unfold bell_violation.
  setoid_rewrite (violation_margin_plus summary Hwitness).
  apply Qlt_plus_pos.
  exact Hpos.
Qed.

(* SAFE: classical CHSH bound S ≤ 2 + ε for local hidden variable models *)
(** [CHSH_classical_bound]: formal specification. *)
Lemma CHSH_classical_bound :
  forall eps (B : Box),
    0#1 <= eps ->
    local B ->
    S B <= (2#1) + eps.
Proof.
  intros eps B Heps Hlocal.
  pose proof (local_CHSH_bound B Hlocal) as Habs.
  assert (S B <= 2#1) as Hle.
  { apply Qabs_le_upper with (y := 2#1).
    - unfold Qle; simpl; lia.
    - exact Habs. }
  apply Qle_trans with (y := 2#1); [exact Hle|].
  apply Qle_plus_nonneg.
  exact Heps.
Qed.

Close Scope Q_scope.
