Require Import Coq.QArith.QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Lia.

Local Open Scope Q_scope.

Record HeadToHeadSummary := {
  hh_sighted_mu : Q;
  hh_blind_mu : Q;
  hh_gap : Q
}.

Definition head_to_head_consistent (summary : HeadToHeadSummary) : Prop :=
  hh_gap summary == hh_blind_mu summary - hh_sighted_mu summary.

Definition head_to_head_gap_positive (summary : HeadToHeadSummary) : Prop :=
  0#1 < hh_gap summary.

Definition head_to_head_sighted_better (summary : HeadToHeadSummary) : Prop :=
  hh_sighted_mu summary < hh_blind_mu summary.

(** [Qlt_plus_pos]: formal specification. *)
Lemma Qlt_plus_pos :
  forall a b : Q,
    0#1 < b ->
    a < a + b.
Proof.
  intros a b Hb.
  unfold Qlt in *; simpl in *; lia.
Qed.

(** [head_to_head_gap_cancel]: formal specification. *)
Lemma head_to_head_gap_cancel :
  forall summary,
    hh_sighted_mu summary + (hh_blind_mu summary - hh_sighted_mu summary)
    == hh_blind_mu summary.
Proof.
  intros summary.
  unfold Qminus.
  rewrite Qplus_assoc.
  rewrite (Qplus_comm (hh_sighted_mu summary) (hh_blind_mu summary)).
  rewrite <- Qplus_assoc.
  rewrite Qplus_opp_r.
  rewrite Qplus_0_r.
  reflexivity.
Qed.

(** [head_to_head_gap_implies_better]: formal specification. *)
Lemma head_to_head_gap_implies_better :
  forall summary,
    head_to_head_consistent summary ->
    head_to_head_gap_positive summary ->
    head_to_head_sighted_better summary.
Proof.
  intros summary Hconsistent Hpositive.
  unfold head_to_head_consistent in Hconsistent.
  unfold head_to_head_gap_positive in Hpositive.
  unfold head_to_head_sighted_better.
  unfold Qminus in *.
  apply (Qlt_plus_pos (hh_sighted_mu summary) (hh_gap summary)) in Hpositive.
  setoid_rewrite Hconsistent in Hpositive.
  setoid_replace (hh_sighted_mu summary + (hh_blind_mu summary - hh_sighted_mu summary))
    with (hh_blind_mu summary) in Hpositive by apply head_to_head_gap_cancel.
  exact Hpositive.
Qed.

Close Scope Q_scope.
