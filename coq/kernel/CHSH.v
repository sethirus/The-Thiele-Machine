From Coq Require Import List Bool Arith.PeanoNat ZArith QArith Lia.
Require Import Coq.QArith.Qabs.
Import ListNotations.
Open Scope Q_scope.

Require Import VMStep.

(** * CHSH from kernel receipts

    This file defines a concrete CHSH statistic over the kernel’s
    non-forgeable receipt channel [instr_chsh_trial x y a b].

    Convention matches tools/verify_supra_quantum.py and the Coq convention:
      S = E(1,1) + E(1,0) + E(0,1) - E(0,0)

    where E(x,y) is the empirical expectation of sign(a)*sign(b).

    STATUS (Dec 16, 2025): VERIFIED (no axioms, no admits)
*)

Module KernelCHSH.

Import VMStep.VMStep.

Record Trial : Type := {
  t_x : nat;
  t_y : nat;
  t_a : nat;
  t_b : nat;
}.

Definition is_trial_instr (i : vm_instruction) : option Trial :=
  match i with
  | instr_chsh_trial x y a b _ =>
      if chsh_bits_ok x y a b then Some {| t_x := x; t_y := y; t_a := a; t_b := b |}
      else None
  | _ => None
  end.

Fixpoint trials_of_receipts (rs : list vm_instruction) : list Trial :=
  match rs with
  | [] => []
  | i :: tl =>
      match is_trial_instr i with
      | Some t => t :: trials_of_receipts tl
      | None => trials_of_receipts tl
      end
  end.

Definition sign_z (bit : nat) : Z :=
  if Nat.eqb bit 1 then 1%Z else (-1)%Z.

Definition trial_value_z (t : Trial) : Z :=
  (sign_z t.(t_a) * sign_z t.(t_b))%Z.

Fixpoint count_setting (x y : nat) (ts : list Trial) : nat :=
  match ts with
  | [] => 0
  | t :: tl =>
      (if (Nat.eqb t.(t_x) x && Nat.eqb t.(t_y) y)%bool then 1 else 0)
        + count_setting x y tl
  end.

Fixpoint sum_setting_z (x y : nat) (ts : list Trial) : Z :=
  match ts with
  | [] => 0%Z
  | t :: tl =>
      (if (Nat.eqb t.(t_x) x && Nat.eqb t.(t_y) y)%bool then trial_value_z t else 0%Z)
        + sum_setting_z x y tl
  end.

Definition expectation (x y : nat) (ts : list Trial) : Q :=
  match count_setting x y ts with
  | 0%nat => 0
  | S n' => (sum_setting_z x y ts) # (Pos.of_succ_nat n')
  end.

Definition chsh (ts : list Trial) : Q :=
  expectation 1 1 ts + expectation 1 0 ts + expectation 0 1 ts - expectation 0 0 ts.

(** ------------------------------------------------------------------------- *)
(** Local deterministic strategies (one response table each)

    We package a *fully explicit* local strategy as four bits A0,A1,B0,B1.
    The associated “one trial per setting” dataset must satisfy |S| ≤ 2.
*)

Record LocalStrategy : Type := {
  a0 : nat;
  a1 : nat;
  b0 : nat;
  b1 : nat;
}.

Definition trial_of_local (s : LocalStrategy) (x y : nat) : Trial :=
  {| t_x := x;
     t_y := y;
     t_a := if Nat.eqb x 0 then s.(a0) else s.(a1);
     t_b := if Nat.eqb y 0 then s.(b0) else s.(b1) |}.

Definition trials_of_local (s : LocalStrategy) : list Trial :=
  [ trial_of_local s 0 0;
    trial_of_local s 0 1;
    trial_of_local s 1 0;
    trial_of_local s 1 1 ].

Definition local_bits_ok (s : LocalStrategy) : Prop :=
  is_bit s.(a0) = true /\ is_bit s.(a1) = true /\
  is_bit s.(b0) = true /\ is_bit s.(b1) = true.

Lemma is_bit_true_cases :
  forall n, is_bit n = true -> n = 0%nat \/ n = 1%nat.
Proof.
  intros n H.
  unfold is_bit in H.
  destruct n as [|n].
  - left. reflexivity.
  - destruct n as [|n].
    + right. reflexivity.
    + simpl in H. discriminate.
Qed.

Lemma count_setting_trials_of_local :
  forall s (x y : nat),
    (x = 0%nat \/ x = 1%nat) ->
    (y = 0%nat \/ y = 1%nat) ->
    count_setting x y (trials_of_local s) = 1%nat.
Proof.
  intros s x y Hx Hy.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy]; subst; vm_compute; reflexivity.
Qed.

Lemma expectation_trials_of_local :
  forall s (x y : nat),
    (x = 0%nat \/ x = 1%nat) ->
    (y = 0%nat \/ y = 1%nat) ->
    expectation x y (trials_of_local s) = (sum_setting_z x y (trials_of_local s))#1.
Proof.
  intros s x y Hx Hy.
  unfold expectation.
  rewrite (count_setting_trials_of_local s x y Hx Hy).
  simpl.
  reflexivity.
Qed.

(** Classical CHSH bound for deterministic local strategies.

    Proof is by finite enumeration of the 16 possible response tables.
*)
Definition chsh_local_z (s : LocalStrategy) : Z :=
  let A0 := sign_z s.(a0) in
  let A1 := sign_z s.(a1) in
  let B0 := sign_z s.(b0) in
  let B1 := sign_z s.(b1) in
  (A1 * B1 + A1 * B0 + A0 * B1 - A0 * B0)%Z.

Theorem local_strategy_chsh_between_neg2_2 :
  forall s,
    local_bits_ok s ->
    (-2 <= chsh_local_z s <= 2)%Z.
Proof.
  intros [A0 A1 B0 B1] Hbits.
  unfold local_bits_ok in Hbits.
  destruct Hbits as [Ha0 [Ha1 [Hb0 Hb1]]].

  (* Reduce each response bit to the concrete 0/1 cases using the proven classifier. *)
  destruct (is_bit_true_cases A0 Ha0) as [HA0|HA0];
  destruct (is_bit_true_cases A1 Ha1) as [HA1|HA1];
  destruct (is_bit_true_cases B0 Hb0) as [HB0|HB0];
  destruct (is_bit_true_cases B1 Hb1) as [HB1|HB1];
  (* Avoid computing inside [Z.le] (which unfolds to compares). Compute the CHSH value separately. *)
  set (v := chsh_local_z {| a0 := A0; a1 := A1; b0 := B0; b1 := B1 |});
  subst A0 A1 B0 B1;
  change (-2 <= v <= 2)%Z;
  assert (Hv : v = 2%Z \/ v = (-2)%Z)
    by (unfold v; vm_compute; first [left; reflexivity | right; reflexivity]);
  destruct Hv as [Hv|Hv]; rewrite Hv; split; lia.
Qed.

Corollary local_strategy_chsh_abs_le_2_z :
  forall s,
    local_bits_ok s ->
    (Z.abs (chsh_local_z s) <= 2)%Z.
Proof.
  intros s Hbits.
  pose proof (local_strategy_chsh_between_neg2_2 s Hbits) as Hbounds.
  apply (proj2 (Z.abs_le (chsh_local_z s) 2)).
  exact Hbounds.
Qed.

End KernelCHSH.
