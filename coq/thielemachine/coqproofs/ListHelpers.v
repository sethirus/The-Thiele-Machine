Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Small, focused list lemmas needed by the Bell inequality development.
   Keep this file minimal and proof-focused so we can test combinatorial
   lemmas in isolation from the rest of the development. *)

Section ListHelpers.
  Context {A : Type}.

  (* Chunk a list into pairs [alice; bob] :: rest -> (alice,bob) :: chunk_pairs rest *)
  Fixpoint chunk_pairs (frames : list A) : list (A * A) :=
    match frames with
    | x :: y :: rest => (x, y) :: chunk_pairs rest
    | _ => []
    end.

  Lemma chunk_pairs_repeat :
    forall alice bob n,
      chunk_pairs (concat (repeat [alice; bob] n)) = repeat (alice, bob) n.
  Proof.
    intros alice bob n; induction n as [| n IH]; simpl; auto.
    now rewrite IH.
  Qed.

  Lemma chunk_pairs_firstn_repeat_general :
    forall alice bob n m,
      chunk_pairs (firstn m (concat (repeat [alice; bob] n))) =
      repeat (alice, bob) (Nat.min (Nat.div2 m) n).
  Proof.
    intros alice bob n.
    induction n as [| n IH]; intros m; simpl.
    - rewrite firstn_nil.
      rewrite Nat.min_0_r.
      reflexivity.
    - destruct m as [| m]; simpl.
      + reflexivity.
      + destruct m as [| m]; simpl.
        * reflexivity.
        * rewrite IH.
          simpl.
          change ((alice, bob)
            :: repeat (alice, bob) (Nat.min (Nat.div2 m) n)) with
            (repeat (alice, bob)
              (Nat.succ (Nat.min (Nat.div2 m) n))).
          simpl.
          reflexivity.
  Qed.

  Lemma double_succ :
    forall k : nat, Nat.mul 2 (Nat.succ k) = Nat.succ (Nat.succ (Nat.mul 2 k)).
  Proof.
    intro k.
    rewrite Nat.mul_succ_r.
    simpl.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.

  Lemma chunk_pairs_firstn_repeat :
    forall alice bob n k,
      chunk_pairs (firstn (Nat.mul 2 k) (concat (repeat [alice; bob] n))) =
      firstn k (repeat (alice, bob) n).
  Proof.
    intros alice bob n k.
    revert n.
    induction k as [| k IH]; intros n.
    - reflexivity.
    - destruct n as [| n].
      + reflexivity.
      + rewrite double_succ.
        simpl.
        f_equal.
        apply IH.
  Qed.

  (* Utilities about firstn on app when the first component is fully included. *)
  Lemma firstn_app_ge :
    forall (l1 l2 : list A) n,
      (length l1 <= n)%nat ->
      firstn n (l1 ++ l2) = l1 ++ firstn (n - length l1) l2.
  Proof.
    intros l1 l2 n Hlen.
    rewrite firstn_app.
    rewrite firstn_all2 by exact Hlen.
    reflexivity.
  Qed.

  Lemma repeat_app :
    forall (x : A) k q,
      repeat x (k + q) = repeat x k ++ repeat x q.
  Proof.
    intros x k q; induction k as [| k IH]; simpl; [reflexivity|].
    now rewrite IH.
  Qed.

  


  (* TODO: add robust filter_firstn_concat lemmas here in a follow-up step. *)

End ListHelpers.
