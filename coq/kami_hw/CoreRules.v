(** Supported action syntax of every actual CPU rule. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore ActionEvaluator.
From Coq Require Import List.

Definition cpu_rule := Attribute (Action Void).

Lemma cpu_rules_linear :
  Forall (fun r : cpu_rule => linear_action (attrType r type)) (getRules thieleCore).
Proof.
  cbn [getRules].
  repeat (apply Forall_cons;
    [cbn [attrType]; repeat (cbn [linear_action]; intro); exact I|]).
  apply Forall_nil.
Qed.

