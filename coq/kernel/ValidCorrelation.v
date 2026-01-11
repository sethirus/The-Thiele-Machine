Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Lists.List.
Require Import Psatz.

Local Open Scope Q_scope.

Definition Box := nat -> nat -> nat -> nat -> Q.

Definition non_negative (B : Box) : Prop :=
  forall x y a b, 0 <= B x y a b.

Definition normalized (B : Box) : Prop :=
  forall x y, (B x y 0%nat 0%nat + B x y 0%nat 1%nat + B x y 1%nat 0%nat + B x y 1%nat 1%nat) == 1.

Definition marginal_a (B : Box) (x y a : nat) : Q :=
  B x y a 0%nat + B x y a 1%nat.

Definition marginal_b (B : Box) (x y b : nat) : Q :=
  B x y 0%nat b + B x y 1%nat b.

Definition no_signaling (B : Box) : Prop :=
  (forall x y1 y2 a, marginal_a B x y1 a == marginal_a B x y2 a) /\
  (forall x1 x2 y b, marginal_b B x1 y b == marginal_b B x2 y b).

Definition deterministic_box (B : Box) : Prop :=
  exists (fA fB : nat -> nat),
    forall x y a b, B x y a b == (if (Nat.eqb a (fA x)) && (Nat.eqb b (fB y)) then 1 else 0).

Definition local_box (B : Box) : Prop :=
  exists (weights : list Q) (det_boxes : list Box),
    (forall db, In db det_boxes -> deterministic_box db) /\
    (forall w, In w weights -> 0 <= w) /\
    (length weights = length det_boxes) /\
    (fold_right Qplus 0 weights == 1) /\
    (forall x y a b, B x y a b == fold_right Qplus 0 
      (map (fun '(w, db) => w * db x y a b) (combine weights det_boxes))).

Theorem bell_math_deterministic : forall (gA gB : nat -> Q),
  (forall x, gA x == 1 \/ gA x == -1) ->
  (forall y, gB y == 1 \/ gB y == -1) ->
  Qabs (gA 0%nat * gB 0%nat + gA 0%nat * gB 1%nat + gA 1%nat * gB 0%nat - gA 1%nat * gB 1%nat) <= 2.
Proof.
  intros gA gB HgA HgB.
  destruct (HgA 0%nat) as [A0 | A0]; destruct (HgA 1%nat) as [A1 | A1];
  destruct (HgB 0%nat) as [B0 | B0]; destruct (HgB 1%nat) as [B1 | B1];
  rewrite A0, A1, B0, B1; try field_simplify; try apply Qabs_case; nra.
Qed.
