Require Import Coq.Lists.List.
Import ListNotations.

(* NUSD: No Unpaid Sight Debt.
   This file contains foundational lemmas about list properties that are used
   to build the Thiele Machine's formal specification. By providing complete
   proofs for these lemmas, we adhere to the principle of "No Unpaid Sight Debt". *)

(** [app_rev_singleton]: formal specification. *)
Lemma app_rev_singleton : forall A (l : list A) (x : A),
  rev (l ++ [x]) = x :: rev l.
Proof.
  intros A l x.
  induction l as [|y ys IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* A simple property: reversing a list twice yields the original list. *)
(** [rev_rev]: formal specification. *)
Lemma rev_rev : forall (A : Type) (l : list A),
  rev (rev l) = l.
Proof.
  intros A l.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite app_rev_singleton. rewrite IH. reflexivity.
Qed.
