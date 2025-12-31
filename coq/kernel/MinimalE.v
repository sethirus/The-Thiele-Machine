Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.Init.Nat.
Require Import Lia.
Require Import Lra.

Local Open Scope Q_scope.

(* local bit_sign for minimal repro *)
Definition bit_sign (n : nat) : Q := if Nat.eqb n 0%nat then 1#1 else if Nat.eqb n 1%nat then (-1)#1 else 0#1.

Lemma minimal_normalized_E_bound:
  forall p00 p01 p10 p11 : Q,
    0#1 <= p00 -> 0#1 <= p01 -> 0#1 <= p10 -> 0#1 <= p11 ->
    p00 + p01 + p10 + p11 == 1#1 ->
    Qabs (p00 - p01 - p10 + p11) <= 1#1.
Proof.
  intros p00 p01 p10 p11 Hp00 Hp01 Hp10 Hp11 Hsum.
  apply Qabs_case with (P := fun q : Q => q <= 1#1).
  - intros Hge.
    unfold Qle; simpl; lra.
  - intros Hle.
    unfold Qle; simpl; lra.
Qed.

Close Scope Q_scope.
