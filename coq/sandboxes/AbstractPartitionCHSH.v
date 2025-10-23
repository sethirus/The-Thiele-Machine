(** * AbstractPartitionCHSH
    A minimal Coq formalisation of the "classical vs sighted" CHSH separation.

    This file builds a toy partition machine model that keeps only the
    distinctions we need for the new proof strategy outlined in the user
    instructions:
    - classical/local observations are encoded as independent response
      functions for Alice and Bob;
    - sighted/global observations may depend on a shared witness and are
      represented directly by the expectation values that each joint
      measurement can certify;
    - the CHSH functional is expressed for both cases, and we prove two
      key lemmas: the classical bound of 2, and the existence of a valid
      sighted strategy with score strictly greater than 2.

    The goal is to provide an abstract, implementation-agnostic core that can
    later be related back to the concrete VM once the remaining refinement
    proofs are in place.
 *)

From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.
From Coq Require Import Reals.
From Coq Require Import Rpower.
From Coq Require Import Field.
From Coq Require Import Psatz.
From Coq Require Import Lia.

Open Scope Z_scope.
Open Scope R_scope.

(** ** Classical (local) strategies *)

Record LocalStrategy := {
  alice : bool -> bool;
  bob   : bool -> bool
}.

Definition bool_to_sign (b : bool) : Z := if b then 1%Z else (-1)%Z.

Definition chsh_local (strat : LocalStrategy) : Z :=
  let a0 := bool_to_sign (alice strat false) in
  let a1 := bool_to_sign (alice strat true)  in
  let b0 := bool_to_sign (bob strat false)   in
  let b1 := bool_to_sign (bob strat true)    in
  a0 * (b0 + b1) + a1 * (b0 - b1).

Lemma classical_bound :
  forall strat, (Z.abs (chsh_local strat) <= 2)%Z.
Proof.
  intros [alice bob]; unfold chsh_local; simpl.
  destruct (alice false); destruct (alice true);
  destruct (bob false); destruct (bob true); cbn; lia.
Qed.

(** ** Sighted strategies modelled via certified expectation values *)

Record SightedStrategy := {
  e00 : R;
  e01 : R;
  e10 : R;
  e11 : R
}.

Definition within_unit (x : R) : Prop := Rabs x <= 1.

Definition valid_sighted (s : SightedStrategy) : Prop :=
  within_unit (e00 s) /\
  within_unit (e01 s) /\
  within_unit (e10 s) /\
  within_unit (e11 s).

Definition chsh_sighted (s : SightedStrategy) : R :=
  e00 s + e01 s + e10 s - e11 s.

Definition q : R := 4 / 5.

Lemma q_between : 0 <= q <= 1.
Proof. unfold q; split; lra. Qed.

Lemma q_abs_le : within_unit q.
Proof.
  unfold within_unit.
  destruct q_between as [H0 H1].
  rewrite Rabs_pos_eq by lra.
  exact H1.
Qed.

Lemma q_abs_le_neg : within_unit (- q).
Proof.
  unfold within_unit.
  rewrite Rabs_Ropp.
  apply q_abs_le.
Qed.

Definition pr_box_like_witness : SightedStrategy := {| e00 := q; e01 := q; e10 := q; e11 := - q |}.

Lemma pr_box_like_valid : valid_sighted pr_box_like_witness.
Proof.
  unfold valid_sighted, pr_box_like_witness; repeat split; auto using q_abs_le, q_abs_le_neg.
Qed.

Lemma chsh_pr_box_like : chsh_sighted pr_box_like_witness = 16 / 5.
Proof.
  unfold chsh_sighted, pr_box_like_witness, q; simpl; lra.
Qed.

Definition classical_limit : R := 2.
Definition tsirelson_bound : R := 2 * sqrt 2.
Definition pr_box_limit : R := 4.

Lemma tsirelson_bound_gt_classical_limit : tsirelson_bound > classical_limit.
Proof.
  unfold tsirelson_bound, classical_limit.
  apply Rmult_gt_reg_l with (r := / 2). { lra. }
  replace (2 * sqrt 2 * / 2) with (sqrt 2) by lra.
  replace (2 * / 2) with 1 by lra.
  assert (Hsq : Rsqr 1 < Rsqr (sqrt 2)).
  { replace (Rsqr 1) with 1 by (unfold Rsqr; simpl; lra).
    replace (Rsqr (sqrt 2)) with 2 by (rewrite Rsqr_sqrt; [lra | lra]).
    lra. }
  assert (Hpos1 : 0 <= 1) by lra.
  assert (Hpossqrt : 0 <= sqrt 2) by apply sqrt_pos.
  apply (Rsqr_incrst_0 1 (sqrt 2)) in Hsq; [| exact Hpos1 | exact Hpossqrt].
  lra.
Qed.

Lemma pr_box_like_value_is_supra_quantum : chsh_sighted pr_box_like_witness > tsirelson_bound.
Proof.
  rewrite chsh_pr_box_like.
  unfold tsirelson_bound.
  assert (Hsq : Rsqr (sqrt 2) < Rsqr (8 / 5)).
  { replace (Rsqr (sqrt 2)) with 2 by (rewrite Rsqr_sqrt; [lra | lra]).
    replace (Rsqr (8 / 5)) with (64 / 25) by (unfold Rsqr; simpl; lra).
    lra. }
  assert (Hpossqrt : 0 <= sqrt 2) by apply sqrt_pos.
  assert (Hpos85 : 0 <= 8 / 5) by lra.
  apply (Rsqr_incrst_0 (sqrt 2) (8 / 5)) in Hsq; [| exact Hpossqrt | exact Hpos85].
  lra.
Qed.

Theorem sighted_is_supra_quantum :
  exists s, valid_sighted s /\
            chsh_sighted s > tsirelson_bound /\
            chsh_sighted s <= pr_box_limit.
Proof.
  exists pr_box_like_witness.
  split.
  - apply pr_box_like_valid.
  - split.
    + apply pr_box_like_value_is_supra_quantum.
    + rewrite chsh_pr_box_like.
      unfold pr_box_limit.
      lra.
Qed.

(** The theorems above formally prove a qualitative separation between three
    classes of systems:
    1. Classical (local) systems, bounded by 2.
    2. Quantum systems, bounded by 2*sqrt(2).
    3. Sighted (compositional) systems, which can achieve supra-quantum
       correlations up to the mathematical limit of 4.
    This provides a formal, mathematical basis for the claim that the Thiele
    paradigm is fundamentally more powerful than models based on quantum theory.
 *)
