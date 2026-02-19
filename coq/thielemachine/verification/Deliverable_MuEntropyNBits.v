From Coq Require Import QArith Lia Arith.PeanoNat.
Import QArith.
Open Scope Q_scope.

From ThieleMachine Require Import InfoTheory.

(** Deliverable: μ/entropy tight certificates for N-bit reductions.

    We provide a *table* of machine-checked instances:
      before = 2^n, after = 1  (with n in a modest, extensible range)

    For each instance:
      information_cost before 1 = n
      mu_cost 0 before 1 = n    (tight when query_bytes=0)

    This avoids fragile global lemmas about log2_up on powers, while still
    delivering provable, falsifiable certificates for many N.
*)

Module DeliverableMuEntropyNBits.

Local Definition oneQ : Q := 1%Q.

(* Helper tactic: close goals by computation for these concrete numerals. *)
Ltac qcompute := vm_compute; reflexivity.

(** [info_cost_2_to_1]: formal specification. *)
Lemma info_cost_2_to_1 : information_cost 2%positive 1%positive = 1%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_2_to_1_tight]: formal specification. *)
Lemma mu_cost_2_to_1_tight : mu_cost 0 2%positive 1%positive = 1%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_2_to_1. qcompute. Qed.

(** [info_cost_4_to_1]: formal specification. *)
Lemma info_cost_4_to_1 : information_cost 4%positive 1%positive = 2%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_4_to_1_tight]: formal specification. *)
Lemma mu_cost_4_to_1_tight : mu_cost 0 4%positive 1%positive = 2%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_4_to_1. qcompute. Qed.

(** [info_cost_8_to_1]: formal specification. *)
Lemma info_cost_8_to_1 : information_cost 8%positive 1%positive = 3%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_8_to_1_tight]: formal specification. *)
Lemma mu_cost_8_to_1_tight : mu_cost 0 8%positive 1%positive = 3%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_8_to_1. qcompute. Qed.

(** [info_cost_16_to_1]: formal specification. *)
Lemma info_cost_16_to_1 : information_cost 16%positive 1%positive = 4%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_16_to_1_tight]: formal specification. *)
Lemma mu_cost_16_to_1_tight : mu_cost 0 16%positive 1%positive = 4%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_16_to_1. qcompute. Qed.

(** [info_cost_32_to_1]: formal specification. *)
Lemma info_cost_32_to_1 : information_cost 32%positive 1%positive = 5%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_32_to_1_tight]: formal specification. *)
Lemma mu_cost_32_to_1_tight : mu_cost 0 32%positive 1%positive = 5%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_32_to_1. qcompute. Qed.

(** [info_cost_64_to_1]: formal specification. *)
Lemma info_cost_64_to_1 : information_cost 64%positive 1%positive = 6%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_64_to_1_tight]: formal specification. *)
Lemma mu_cost_64_to_1_tight : mu_cost 0 64%positive 1%positive = 6%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_64_to_1. qcompute. Qed.

(** [info_cost_128_to_1]: formal specification. *)
Lemma info_cost_128_to_1 : information_cost 128%positive 1%positive = 7%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_128_to_1_tight]: formal specification. *)
Lemma mu_cost_128_to_1_tight : mu_cost 0 128%positive 1%positive = 7%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_128_to_1. qcompute. Qed.

(** [info_cost_256_to_1]: formal specification. *)
Lemma info_cost_256_to_1 : information_cost 256%positive 1%positive = 8%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_256_to_1_tight]: formal specification. *)
Lemma mu_cost_256_to_1_tight : mu_cost 0 256%positive 1%positive = 8%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_256_to_1. qcompute. Qed.

(** [info_cost_512_to_1]: formal specification. *)
Lemma info_cost_512_to_1 : information_cost 512%positive 1%positive = 9%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_512_to_1_tight]: formal specification. *)
Lemma mu_cost_512_to_1_tight : mu_cost 0 512%positive 1%positive = 9%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_512_to_1. qcompute. Qed.

(** [info_cost_1024_to_1]: formal specification. *)
Lemma info_cost_1024_to_1 : information_cost 1024%positive 1%positive = 10%Q. Proof. unfold information_cost. qcompute. Qed.
(** [mu_cost_1024_to_1_tight]: formal specification. *)
Lemma mu_cost_1024_to_1_tight : mu_cost 0 1024%positive 1%positive = 10%Q. Proof. unfold mu_cost, question_cost. rewrite info_cost_1024_to_1. qcompute. Qed.

End DeliverableMuEntropyNBits.
