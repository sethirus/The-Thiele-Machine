(** VMUnboundedLedger: the ledger and certification facts for the unbounded
    VM sibling [vm_apply_u].

    [vm_apply_u] is [vm_apply] with unmasked arithmetic. Its ledger and
    certification behave the same way: each step adds exactly the
    instruction's cost to [vm_mu], only [CERTIFY] can switch
    [vm_certified] on, nothing switches it off, and [CERTIFY] costs at least
    one. These are the facts [StructuralCore] needs to treat the unbounded
    VM as a record-carrying machine. *)

From Coq Require Import List Arith.PeanoNat Lia.
From Kernel Require Import VMState VMStep VMUnboundedStep.

Lemma vm_apply_u_mu : forall s i,
  (vm_apply_u s i).(vm_mu) = s.(vm_mu) + instruction_cost i.
Proof.
  intros s i. destruct i; simpl;
    repeat match goal with
           | |- context [if ?b then _ else _] => destruct b
           | |- context [match ?x with _ => _ end] => destruct x
           end;
    reflexivity.
Qed.

Lemma vm_apply_u_certified : forall s i,
  (vm_apply_u s i).(vm_certified) =
  match i with instr_certify _ => true | _ => s.(vm_certified) end.
Proof.
  intros s i. destruct i; simpl;
    repeat match goal with
           | |- context [if ?b then _ else _] => destruct b
           | |- context [match ?x with _ => _ end] => destruct x
           end;
    reflexivity.
Qed.

Lemma vm_apply_u_certified_permanent : forall s i,
  s.(vm_certified) = true -> (vm_apply_u s i).(vm_certified) = true.
Proof.
  intros s i H. rewrite vm_apply_u_certified. destruct i; auto.
Qed.

Lemma vm_apply_u_no_free_certification : forall s i,
  s.(vm_certified) = false -> (vm_apply_u s i).(vm_certified) = true ->
  instruction_cost i >= 1.
Proof.
  intros s i H0 H1. rewrite vm_apply_u_certified in H1.
  destruct i; try congruence. simpl. lia.
Qed.
