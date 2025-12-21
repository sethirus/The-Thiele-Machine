Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Setoid.
Require Import Coq.micromega.Lra.
Require Import Coq.QArith.Qfield.

Import ListNotations.

Open Scope Q_scope.
Open Scope Z_scope.

Definition coef_a_a : Q := (1000000 # 1000000%positive).
Definition coef_a_b : Q := (0 # 1000000).
Definition coef_a_lap_b : Q := (-5000 # 1000000).
Definition coef_a_Vb : Q := (10000 # 1000000).

Definition coef_b_b : Q := (1000000 # 1000000).
Definition coef_b_a : Q := (0 # 1000000).
Definition coef_b_lap_a : Q := (5000 # 1000000).
Definition coef_b_Va : Q := (-10000 # 1000000).

Definition extracted_mass : Q := (1000000 # 1000000).
Definition extracted_inv_2m : Q := (500000 # 1000000).
Definition extracted_dt : Q := (10000 # 1000000).

Definition schrodinger_update_a (a b lap_b Vb : Q) : Q :=
  coef_a_a * a + coef_a_b * b + coef_a_lap_b * lap_b + coef_a_Vb * Vb.

Definition target_update_a (a lap_b Vb : Q) : Q :=
  a + extracted_dt * (-(extracted_inv_2m) * lap_b + Vb).

Goal forall (a b lap_a lap_b Va Vb : Q),
    Qeq (schrodinger_update_a a b lap_b Vb) (target_update_a a lap_b Vb).
Proof.
  intros.
  unfold schrodinger_update_a, target_update_a.
  unfold coef_a_a, coef_a_b, coef_a_lap_b, coef_a_Vb.
  unfold extracted_dt, extracted_inv_2m.
  ring.
Qed.
