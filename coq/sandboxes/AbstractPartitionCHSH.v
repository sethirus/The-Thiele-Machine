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

Definition tsirelson_like : SightedStrategy := {| e00 := q; e01 := q; e10 := q; e11 := - q |}.

Lemma tsirelson_like_valid : valid_sighted tsirelson_like.
Proof.
  unfold valid_sighted, tsirelson_like; repeat split; auto using q_abs_le, q_abs_le_neg.
Qed.

Lemma chsh_tsirelson_like : chsh_sighted tsirelson_like = 16 / 5.
Proof.
  unfold chsh_sighted, tsirelson_like, q; simpl; lra.
Qed.

Theorem sighted_exceeds_two :
  exists s, valid_sighted s /\ 2 < chsh_sighted s.
Proof.
  exists tsirelson_like.
  split.
  - apply tsirelson_like_valid.
  - rewrite chsh_tsirelson_like; unfold q; lra.
Qed.

(** The statements above isolate the minimal logical content of the Bell
    separation.  Future work will relate these definitions back to the concrete
    VM semantics by constructing homomorphisms into this abstract setting. *)
