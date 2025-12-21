Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Coq.micromega.Lra.
Open Scope Q_scope.

Goal forall x : Q, (1#2) * x == x / (2#1).
Proof.
  intros.
  field.
Qed.
