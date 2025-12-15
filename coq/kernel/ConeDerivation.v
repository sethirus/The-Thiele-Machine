From Coq Require Import List.
From Coq Require Import FunctionalExtensionality.

From Kernel Require Import VMStep KernelPhysics.

Import ListNotations.

Definition cone_like (f : list vm_instruction -> list nat) : Prop :=
  f [] = [] /\
  (forall i rest, f (i :: rest) = instr_targets i ++ f rest).

Theorem Cone_Structure_Unique :
  forall f,
    cone_like f ->
    forall trace, f trace = causal_cone trace.
Proof.
  intros f [Hnil Hcons] trace.
  induction trace as [|i rest IH].
  - rewrite Hnil. reflexivity.
  - rewrite Hcons. simpl. rewrite IH. reflexivity.
Qed.

Theorem cone_monotone :
  forall trace1 trace2 x,
    In x (causal_cone trace1) -> In x (causal_cone (trace1 ++ trace2)).
Proof.
  intros trace1 trace2 x Hin.
  eapply cone_monotonic; eauto.
Qed.
