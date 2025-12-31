(* Kernel-level simple box definitions (nat-indexed)
   This file defines a raw Box type usable in kernel reasoning and proofs.
   Intended to be minimal and independent from the higher-level `Box` record
   used in `thielemachine/coqproofs/BellInequality.v`.
*)

Require Import Coq.QArith.QArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Lia.

Local Open Scope Q_scope.

Definition Box := nat -> nat -> nat -> nat -> Q.

Definition non_negative (B : Box) : Prop :=
  forall x y a b, 0#1 <= B x y a b.

Definition normalized (B : Box) : Prop :=
  forall x y,
    B x y 0%nat 0%nat + B x y 0%nat 1%nat + B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1#1.

Definition no_signaling (B : Box) : Prop :=
  (* Alice's marginal independent of y *)
  (forall x a, (B x 0%nat a 0%nat + B x 0%nat a 1%nat) == (B x 1%nat a 0%nat + B x 1%nat a 1%nat)) /\
  (* Bob's marginal independent of x *)
  (forall y b, (B 0%nat y 0%nat b + B 0%nat y 1%nat b) == (B 1%nat y 0%nat b + B 1%nat y 1%nat b)).

Definition valid_box (B : Box) : Prop :=
  non_negative B /\ normalized B /\ no_signaling B.

(* Local-box (factorizable) definition with marginals normalized and nonneg
   pA : x -> a -> Q, pB : y -> b -> Q such that pA and pB are distributions
   over {0,1} for each setting. *)
Definition local_box (B : Box) : Prop :=
  exists (pA : nat -> nat -> Q) (pB : nat -> nat -> Q),
    (forall x a, 0#1 <= pA x a) /\ (forall y b, 0#1 <= pB y b) /\
    (forall x, pA x 0%nat + pA x 1%nat == 1#1) /\ (forall y, pB y 0%nat + pB y 1%nat == 1#1) /\
    (forall x y a b, B x y a b == pA x a * pB y b).

(* A deterministic/local-deterministic variant could be added later. *)

(* Expose some common helper lemmas later in BoxCHSH.v *)

(* End of ValidCorrelation.v *)
