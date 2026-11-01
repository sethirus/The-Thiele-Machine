(* SCOPE NOTE: standalone proof scope.
   Standalone three-state counterexample to deriving an entry toll
   from source-dependent collision coverage. It deliberately does not satisfy
   the stronger Thiele entry-toll axiom and is not a native-machine instance. *)

(* A state-dependent collision charge need not charge the entry transition. *)
From Coq Require Import Arith Lia.
Inductive state := unfinished | first_held | final_held.
Definition step (s : state) :=
  match s with unfinished => first_held | _ => final_held end.
Definition reading (s : state) :=
  match s with unfinished => false | _ => true end.
Definition charge (s : state) :=
  match s with first_held => 1 | _ => 0 end.
Definition ledger (s : state) :=
  match s with final_held => 1 | _ => 0 end.

Theorem permanence : forall s, reading s = true -> reading (step s) = true.
Proof. destruct s; reflexivity. Qed.

Theorem exact_accounting : forall s, ledger (step s) = ledger s + charge s.
Proof. destruct s; reflexivity. Qed.

Theorem every_collision_has_paid_source : forall x y,
  x <> y -> step x = step y -> 1 <= charge x + charge y.
Proof. destruct x,y; cbn; intros; try congruence; lia. Qed.

Theorem entry_is_free : reading unfinished = false /\
  reading (step unfinished) = true /\ charge unfinished = 0.
Proof. repeat split; reflexivity. Qed.

Theorem entry_has_no_competing_source : forall s,
  step s = step unfinished -> s = unfinished.
Proof. destruct s; cbn; intros; congruence. Qed.

Print Assumptions permanence.
Print Assumptions exact_accounting.
Print Assumptions every_collision_has_paid_source.
Print Assumptions entry_is_free.
Print Assumptions entry_has_no_competing_source.
