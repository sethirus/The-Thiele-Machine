From Coq Require Import QArith.
From Coq Require Import Qring.
From Coq Require Import ZArith.
From Coq Require Import Lia.

From ThieleMachine Require Import BellInequality.

Local Open Scope Q_scope.

(** =======================================================================
    Artifact Isomorphism: supra_quantum_16_5.csv
    =======================================================================

    This module pins the executable artifact
      artifacts/bell/supra_quantum_16_5.csv
    to a Coq-level Box, and proves it agrees with the canonical Coq
    definition `SupraQuantum` from `BellInequality.v`.

    Goal: prevent silent drift between:
    - the checked-in CSV used by Python verification
    - the Coq `supra_quantum_p` definition used in proofs
*)

Definition csv_supra_quantum_p (a b x y : Bit) : Q :=
  match x, y, a, b with
  | B0, B0, B0, B0 => 1#5
  | B0, B0, B0, B1 => 3#10
  | B0, B0, B1, B0 => 3#10
  | B0, B0, B1, B1 => 1#5

  | B0, B1, B0, B0 => 1#2
  | B0, B1, B0, B1 => 0#1
  | B0, B1, B1, B0 => 0#1
  | B0, B1, B1, B1 => 1#2

  | B1, B0, B0, B0 => 1#2
  | B1, B0, B0, B1 => 0#1
  | B1, B0, B1, B0 => 0#1
  | B1, B0, B1, B1 => 1#2

  | B1, B1, B0, B0 => 1#2
  | B1, B1, B0, B1 => 0#1
  | B1, B1, B1, B0 => 0#1
  | B1, B1, B1, B1 => 1#2
  end.

Lemma csv_supra_quantum_p_nonneg :
  forall a b x y,
    0#1 <= csv_supra_quantum_p a b x y.
Proof.
  intros a b x y.
  destruct x, y, a, b; simpl; unfold Qle; simpl; lia.
Qed.

Lemma csv_supra_quantum_p_norm :
  forall x y,
    sum_bit2 (fun a b => csv_supra_quantum_p a b x y) == 1#1.
Proof.
  intros x y.
  destruct x, y; vm_compute; reflexivity.
Qed.

Lemma csv_supra_quantum_p_nosig_A :
  forall x y1 y2 a,
    sum_bit (fun b => csv_supra_quantum_p a b x y1) ==
    sum_bit (fun b => csv_supra_quantum_p a b x y2).
Proof.
  intros x y1 y2 a.
  destruct x, y1, y2, a; vm_compute; reflexivity.
Qed.

Lemma csv_supra_quantum_p_nosig_B :
  forall y x1 x2 b,
    sum_bit (fun a => csv_supra_quantum_p a b x1 y) ==
    sum_bit (fun a => csv_supra_quantum_p a b x2 y).
Proof.
  intros y x1 x2 b.
  destruct y, x1, x2, b; vm_compute; reflexivity.
Qed.

Lemma csv_supra_quantum_p_eq :
  forall a b x y,
    csv_supra_quantum_p a b x y = supra_quantum_p a b x y.
Proof.
  intros a b x y.
  destruct x, y, a, b; reflexivity.
Qed.

Lemma csv_supra_quantum_p_Qeq :
  forall a b x y,
    csv_supra_quantum_p a b x y == supra_quantum_p a b x y.
Proof.
  intros a b x y.
  rewrite csv_supra_quantum_p_eq.
  reflexivity.
Qed.

Definition CsvSupraQuantum : Box := {|
  p := csv_supra_quantum_p;
  norm := csv_supra_quantum_p_norm;
  nonneg := csv_supra_quantum_p_nonneg;
  nosig_A := csv_supra_quantum_p_nosig_A;
  nosig_B := csv_supra_quantum_p_nosig_B
|}.

(* ----------------------------------------------------------------------- *)
(*  Derived: the artifact CHSH equals the Coq SupraQuantum CHSH             *)
(* ----------------------------------------------------------------------- *)

Lemma E_csv_supra_quantum :
  forall x y,
    E CsvSupraQuantum x y == E SupraQuantum x y.
Proof.
  intros x y.
  unfold E.
  apply sum_bit2_ext.
  intros a b.
  simpl.
  rewrite csv_supra_quantum_p_eq.
  reflexivity.
Qed.

Theorem S_CsvSupraQuantum : S CsvSupraQuantum == 16#5.
Proof.
  unfold S.
  repeat rewrite E_csv_supra_quantum.
  apply S_SupraQuantum.
Qed.

Close Scope Q_scope.
