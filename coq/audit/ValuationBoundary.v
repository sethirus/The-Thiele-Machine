(* SCOPE NOTE: standalone proof scope.
   Standalone finite counterexample to treating an arbitrary
   Boolean reading as an autonomous quotient. Its toll and permanence are
   proved directly; it is not the native earned-chain example. *)

(* A Boolean observation need not be a quotient transition system. *)
From Coq Require Import Bool Arith Lia.
Inductive state := low | middle | high.
Definition step (s : state) :=
  match s with low => middle | _ => high end.
Definition reading (s : state) :=
  match s with high => true | _ => false end.
Definition price := 1.

Theorem toll_and_permanence :
  (forall s, reading s = false -> reading (step s) = true -> 1 <= price) /\
  (forall s, reading s = true -> reading (step s) = true).
Proof. split; destruct s; cbn; intros; try discriminate; auto. Qed.

Theorem no_boolean_shadow_rule :
  ~ exists g : bool -> bool, forall s, reading (step s) = g (reading s).
Proof.
  intros [g H]. pose proof (H low) as H0. pose proof (H middle) as H1.
  cbn in H0,H1; congruence.
Qed.

Print Assumptions toll_and_permanence.
Print Assumptions no_boolean_shadow_rule.
