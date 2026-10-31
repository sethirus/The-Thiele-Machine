(** NecFQuant: the floor raised to a threshold, at its limit.

    The appendix theorem: in a quantitative certification system, a run from
    a state with witness 0 (A6) to a state reading yes costs at least N.

    - A2 plays no part, and neither does a start reading no: the floor holds
      for any step, cost, reading and witness meeting A3 and A5
      ([nec_f_qfloor_raw]); the repo theorem is a corollary
      ([nec_f_repo_quantitative_from_raw]).
    - A6 can be weakened to nothing: in general the run costs at least
      N minus the starting witness ([nec_f_qfloor_from_any_witness]).
    - A6 is needed: a quantitative certification system meeting every field
      has a run of cost 1 from a witness-1 state to yes with N = 2
      ([nec_f_quant_needs_a6]).
    - A3 is needed ([nec_f_quant_needs_a3]) and A5 is needed
      ([nec_f_quant_needs_a5]); both counterexamples meet A2.
    - The bound N is attained for every N ([nec_f_quant_tight]). *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import QuantitativeNoFI.
From Kernel Require Import CostSemanticsComparison.

Section Raw.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable cert : S -> bool.
Variable w : S -> nat.
Variable N : nat.

Notation run := (CostSemanticsComparison.run S I step).
Notation total := (CostSemanticsComparison.total I cost).

Definition nec_f_a3 : Prop := forall s i, w s + cost i >= w (step s i).
Definition nec_f_a5 : Prop := forall s, cert s = true -> w s >= N.

Lemma nec_f_raw_telescoping :
  nec_f_a3 -> forall t s, w s + total t >= w (run t s).
Proof.
  intros H3 t. induction t as [| i t IH]; intros s; simpl; [lia |].
  specialize (IH (step s i)). specialize (H3 s i). lia.
Qed.

(** From any start, the run costs at least N minus the starting witness. *)
Theorem nec_f_qfloor_from_any_witness :
  nec_f_a3 -> nec_f_a5 ->
  forall t s, cert (run t s) = true -> total t >= N - w s.
Proof.
  intros H3 H5 t s Hc. pose proof (nec_f_raw_telescoping H3 t s).
  pose proof (H5 _ Hc). lia.
Qed.

(** With A6, the floor is N; no A2 and no start reading no are used. *)
Theorem nec_f_qfloor_raw :
  nec_f_a3 -> nec_f_a5 ->
  forall t s, w s = 0 -> cert (run t s) = true -> total t >= N.
Proof.
  intros H3 H5 t s H0 Hc. pose proof (nec_f_qfloor_from_any_witness H3 H5 t s Hc). lia.
Qed.

End Raw.

Lemma nec_f_cs_run_eq :
  forall CS t s, cs_run CS t s = CostSemanticsComparison.run _ _ (cs_step CS) t s.
Proof. intros CS t. induction t as [| i t IH]; intros s; simpl; [reflexivity | apply IH]. Qed.

Lemma nec_f_cs_total_eq :
  forall CS t, cs_total_cost CS t = CostSemanticsComparison.total _ (cs_cost CS) t.
Proof. intros CS t. induction t as [| i t IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** The repo theorem follows from the raw one. *)
Corollary nec_f_repo_quantitative_from_raw :
  forall (QCS : QuantitativeCertificationSystem) trace s0,
    qcs_witness QCS s0 = 0 ->
    cs_cert (qcs_base QCS) (cs_run (qcs_base QCS) trace s0) = true ->
    cs_total_cost (qcs_base QCS) trace >= qcs_threshold QCS.
Proof.
  intros QCS trace s0 H0 Hc. rewrite nec_f_cs_total_eq.
  rewrite nec_f_cs_run_eq in Hc.
  apply (nec_f_qfloor_raw _ _ (cs_step (qcs_base QCS)) (cs_cost (qcs_base QCS))
           (cs_cert (qcs_base QCS)) (qcs_witness QCS) (qcs_threshold QCS)
           (qcs_cost_bounds_witness QCS) (qcs_cert_threshold_witness QCS) trace s0 H0 Hc).
Qed.

(** * A counter with threshold N: one INC at a time, each costing one *)

Inductive NecFInc := NecFIncOne.

Definition nec_f_inc_step (n : nat) (_ : NecFInc) : nat := S n.
Definition nec_f_inc_cost (_ : NecFInc) : nat := 1.

Definition nec_f_inc_cs (N : nat) : CertificationSystem.
Proof.
  refine {| cs_state := nat; cs_instr := NecFInc; cs_step := nec_f_inc_step;
            cs_cost := nec_f_inc_cost; cs_cert := fun n => Nat.leb N n |}.
  intros s i _ _. unfold nec_f_inc_cost. lia.
Defined.

Definition nec_f_inc_qcs (N : nat) : QuantitativeCertificationSystem.
Proof.
  refine {| qcs_base := nec_f_inc_cs N; qcs_witness := fun n => n; qcs_threshold := N |}.
  - intros s i. simpl. unfold nec_f_inc_cost, nec_f_inc_step. lia.
  - intros s H. simpl in H. apply Nat.leb_le in H. lia.
Defined.

Lemma nec_f_inc_run : forall N k s, cs_run (nec_f_inc_cs N) (repeat NecFIncOne k) s = k + s.
Proof. intros N k. induction k as [| k IH]; intros s; simpl; [reflexivity | rewrite IH; unfold nec_f_inc_step; lia]. Qed.

Lemma nec_f_inc_total : forall N k, cs_total_cost (nec_f_inc_cs N) (repeat NecFIncOne k) = k.
Proof. intros N k. induction k as [| k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** The bound N is attained for every N: N INCs from witness 0 cost N. *)
Theorem nec_f_quant_tight :
  forall N,
    qcs_witness (nec_f_inc_qcs N) 0 = 0 /\
    cs_cert (qcs_base (nec_f_inc_qcs N)) (cs_run (qcs_base (nec_f_inc_qcs N)) (repeat NecFIncOne N) 0) = true /\
    cs_total_cost (qcs_base (nec_f_inc_qcs N)) (repeat NecFIncOne N) = N /\
    qcs_threshold (nec_f_inc_qcs N) = N.
Proof.
  intro N. split; [reflexivity |]. split.
  - simpl. rewrite nec_f_inc_run. apply Nat.leb_le. lia.
  - split; [apply nec_f_inc_total | reflexivity].
Qed.

(** A6 is needed: start from witness 1 with threshold 2; one INC, cost 1. The
    start reads no, so even the plain floor's premise holds. *)
Theorem nec_f_quant_needs_a6 :
  qcs_witness (nec_f_inc_qcs 2) 1 = 1 /\
  cs_cert (qcs_base (nec_f_inc_qcs 2)) 1 = false /\
  cs_cert (qcs_base (nec_f_inc_qcs 2)) (cs_run (qcs_base (nec_f_inc_qcs 2)) [NecFIncOne] 1) = true /\
  cs_total_cost (qcs_base (nec_f_inc_qcs 2)) [NecFIncOne] < qcs_threshold (nec_f_inc_qcs 2).
Proof. repeat split; simpl; lia. Qed.

(** A3 is needed: a jump to N for one unit. Threshold 2, witness = state;
    A2 and A5 hold, A3 fails, and the run costs 1 < 2. *)
Definition nec_f_jump_step (n : nat) (_ : NecFInc) : nat := 2.

Theorem nec_f_quant_needs_a3 :
  CostSemanticsComparison.a2 nat NecFInc nec_f_jump_step nec_f_inc_cost (fun n => Nat.leb 2 n) /\
  nec_f_a5 nat (fun n => Nat.leb 2 n) (fun n => n) 2 /\
  ~ nec_f_a3 nat NecFInc nec_f_jump_step nec_f_inc_cost (fun n => n) /\
  CostSemanticsComparison.run nat NecFInc nec_f_jump_step [NecFIncOne] 0 = 2 /\
  CostSemanticsComparison.total NecFInc nec_f_inc_cost [NecFIncOne] < 2.
Proof.
  split; [intros s i _ _; unfold nec_f_inc_cost; lia |].
  split; [intros s H; apply Nat.leb_le in H; lia |].
  split; [intro H; specialize (H 0 NecFIncOne); unfold nec_f_jump_step, nec_f_inc_cost in H; lia |].
  split; [reflexivity | simpl; lia].
Qed.

(** A5 is needed: the reading says yes at witness 1 while the threshold is 2;
    A2 and A3 hold, and one INC from 0 costs 1 < 2. *)
Theorem nec_f_quant_needs_a5 :
  CostSemanticsComparison.a2 nat NecFInc nec_f_inc_step nec_f_inc_cost (fun n => Nat.leb 1 n) /\
  nec_f_a3 nat NecFInc nec_f_inc_step nec_f_inc_cost (fun n => n) /\
  ~ nec_f_a5 nat (fun n => Nat.leb 1 n) (fun n => n) 2 /\
  (fun n => Nat.leb 1 n) (CostSemanticsComparison.run nat NecFInc nec_f_inc_step [NecFIncOne] 0) = true /\
  CostSemanticsComparison.total NecFInc nec_f_inc_cost [NecFIncOne] < 2.
Proof.
  split; [intros s i _ _; unfold nec_f_inc_cost; lia |].
  split; [intros s i; unfold nec_f_inc_cost, nec_f_inc_step; lia |].
  split; [intro H; specialize (H 1 eq_refl); cbn in H; lia |].
  split; [reflexivity | simpl; lia].
Qed.

Print Assumptions nec_f_qfloor_from_any_witness.
Print Assumptions nec_f_qfloor_raw.
Print Assumptions nec_f_repo_quantitative_from_raw.
Print Assumptions nec_f_quant_tight.
Print Assumptions nec_f_quant_needs_a6.
Print Assumptions nec_f_quant_needs_a3.
Print Assumptions nec_f_quant_needs_a5.
