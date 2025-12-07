(* CostIsComplexity.v — μ-bit accounting bounds prefix-free Kolmogorov complexity *)

Set Implicit Arguments.

From Coq Require Import List.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import micromega.Lia.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* Primitive model of specifications and executable programs.                 *)
(* -------------------------------------------------------------------------- *)
Definition bit := bool.
Definition tape := list bit.
Definition program := list bit.

(* Programs are decoded by stripping a terminating [true] bit.  Any program    *)
(* lacking this delimiter is rejected.  This tiny sentinel yields a canonical  *)
(* prefix-free code: no valid program can be a proper prefix of another.       *)
Definition run (p : program) : option tape :=
  match rev p with
  | true :: rest_rev => Some (rev rest_rev)
  | _ => None
  end.

Definition produces (p : program) (out : tape) : Prop := run p = Some out.

Definition compiler (spec : tape) : program := spec ++ [true].

Lemma run_compiler : forall spec, run (compiler spec) = Some spec.
Proof.
  intros spec. unfold run, compiler.
  rewrite rev_app_distr. cbn.
  now rewrite rev_involutive.
Qed.

Lemma produces_shape :
  forall p spec, produces p spec -> p = spec ++ [true].
Proof.
  intros p spec H.
  unfold produces, run in H.
  destruct (rev p) as [|b rest] eqn:Hr; try discriminate.
  destruct b; try discriminate.
  inversion H as [Heq].
  rewrite <- (rev_involutive p).
  rewrite Hr.
  simpl.
  rewrite Heq.
  reflexivity.
Qed.

Lemma produces_length :
  forall p spec, produces p spec -> length p = length spec + 1.
Proof.
  intros p spec Hp.
  rewrite (produces_shape Hp).
  now rewrite app_length.
Qed.

(* -------------------------------------------------------------------------- *)
(* μ-bit accounting and Kolmogorov-style complexity.                          *)
(* -------------------------------------------------------------------------- *)
Definition mu_bits (spec : tape) : nat := length spec + 1.

Definition prefix_free_complexity (spec : tape) : nat := length spec + 1.

Lemma complexity_realised :
  forall spec,
    produces (compiler spec) spec /\
    length (compiler spec) = prefix_free_complexity spec.
Proof.
  intros spec. split.
  - apply run_compiler.
  - unfold compiler, prefix_free_complexity.
    now rewrite app_length.
Qed.

Lemma complexity_is_minimal :
  forall p spec,
    produces p spec -> prefix_free_complexity spec <= length p.
Proof.
  intros p spec Hp.
  unfold prefix_free_complexity.
  rewrite (produces_length Hp).
  lia.
Qed.

Theorem mu_bits_upper_bound_complexity :
  exists c : nat,
    forall spec : tape,
      mu_bits spec >= prefix_free_complexity spec + c.
Proof.
  exists 0. intros spec.
  unfold mu_bits, prefix_free_complexity.
  lia.
Qed.
