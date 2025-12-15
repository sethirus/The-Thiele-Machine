From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMStep.

Import ListNotations.

(* A minimal algebraic interface for any would-be "frequency" / "probability weight"
   over traces, abstracting the plan's "composition consistency" requirement.

   We deliberately keep this purely algebraic so it does not smuggle in extra axioms.
*)

Definition Weight := list vm_instruction -> nat.

Definition weight_compositional (w : Weight) : Prop :=
  w [] = 0 /\
  forall t1 t2, w (t1 ++ t2) = w t1 + w t2.

Definition w_len : Weight := fun t => length t.
Definition w_len2 : Weight := fun t => 2 * length t.

Lemma w_len_compositional : weight_compositional w_len.
Proof.
  split.
  - reflexivity.
  - intros t1 t2. unfold w_len.
    rewrite app_length. lia.
Qed.

Lemma w_len2_compositional : weight_compositional w_len2.
Proof.
  split.
  - reflexivity.
  - intros t1 t2. unfold w_len2.
    rewrite app_length. lia.
Qed.

Theorem Born_Rule_Unique_Fails_Without_More_Structure :
  exists w1 w2,
    weight_compositional w1 /\
    weight_compositional w2 /\
    (exists t, w1 t <> w2 t).
Proof.
  exists w_len, w_len2.
  split.
  - exact w_len_compositional.
  - split.
    + exact w_len2_compositional.
    + exists [instr_halt 0].
      simpl. discriminate.
Qed.
