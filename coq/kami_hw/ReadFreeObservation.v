(** A decoded action with no register reads cannot observe the pre-state. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ActionEvaluator ActionObservation.
From Coq Require Import String.

Fixpoint read_free_action {k} (a : ActionT type k) : Prop :=
  match a with
  | Let_ _ cont => forall v, read_free_action (cont v)
  | WriteReg _ _ cont => read_free_action cont
  | Assert_ _ cont => read_free_action cont
  | Displ _ cont => read_free_action cont
  | Return _ => True
  | _ => False
  end.

Theorem observe_read_free_action : forall k (a : ActionT type k),
  read_free_action a -> forall old old' key,
  observe_action_write old key a = observe_action_write old' key a.
Proof.
  intros k a. induction a; cbn [read_free_action]; intros Hfree old old' key;
    try contradiction; cbn [observe_action_write]; try reflexivity.
  - apply H. apply Hfree.
  - destruct (string_dec key r); [reflexivity|]. apply IHa. exact Hfree.
  - apply IHa. exact Hfree.
  - apply IHa. exact Hfree.
Qed.

Theorem eval_read_free_action : forall k (a : ActionT type k),
  read_free_action a -> forall old old',
  eval_linear_action old a = eval_linear_action old' a.
Proof.
  intros k a. induction a; cbn [read_free_action]; intros Hfree old old';
    try contradiction; cbn [eval_linear_action]; try reflexivity.
  - apply H. apply Hfree.
  - rewrite (IHa Hfree old old'). reflexivity.
  - destruct (evalExpr e); [apply IHa; exact Hfree|reflexivity].
  - apply IHa. exact Hfree.
Qed.
