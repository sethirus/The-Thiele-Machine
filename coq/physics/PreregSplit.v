From Coq Require Import List Arith Lia.

Import ListNotations.

Module PreregSplit.

Section SplitTail.
  Context {A : Type}.

  (* Split a list into (train, test) where test is the last [test_n] elements.
     This matches the prereg C "chronological tail" policy. *)
  Definition split_tail (test_n : nat) (l : list A) : list A * list A :=
    let k := length l - test_n in
    (firstn k l, skipn k l).

  Lemma split_tail_app (test_n : nat) (l : list A) :
      l = fst (split_tail test_n l) ++ snd (split_tail test_n l).
  Proof.
    unfold split_tail.
    set (k := length l - test_n).
    simpl.
    rewrite firstn_skipn.
    reflexivity.
  Qed.

  Lemma split_tail_lengths (test_n : nat) (l : list A) :
      length (fst (split_tail test_n l)) + length (snd (split_tail test_n l)) = length l.
  Proof.
    rewrite <- app_length.
    rewrite <- split_tail_app.
    reflexivity.
  Qed.

  Lemma split_tail_test_length_exact (test_n : nat) (l : list A) :
      test_n <= length l -> length (snd (split_tail test_n l)) = test_n.
  Proof.
    intro Hle.
    unfold split_tail.
    set (k := length l - test_n).
    simpl.
    rewrite skipn_length.
    (* length l - k = test_n when test_n <= length l and k = length l - test_n *)
    subst k.
    lia.
  Qed.

  Lemma split_tail_train_length_exact (test_n : nat) (l : list A) :
      test_n <= length l -> length (fst (split_tail test_n l)) = length l - test_n.
  Proof.
    intro Hle.
    unfold split_tail.
    set (k := length l - test_n).
    simpl.
    rewrite firstn_length.
    subst k.
    (* min (length l - test_n) (length l) = length l - test_n *)
    rewrite Nat.min_l.
    - reflexivity.
    - lia.
  Qed.

End SplitTail.

End PreregSplit.
