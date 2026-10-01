(** Closed execution and Rice outcomes adjacent to the blocked fixed point. *)

From Coq Require Import List.
Import ListNotations.
From Kernel Require Import VMState VMUnboundedStep VMSelfGuest VMSelfRun.
From Kernel Require Import VMSelfRice VMSelfRiceUndec VMRecursionTarget.

Theorem vm_guest_execution_is_actual : forall p amb tl n c,
  g_wf_program p ->
  run_vm_u n (g_program p) (gc_state amb tl c) =
  gc_state amb tl (g_run n p c).
Proof. exact g_run_is_run_vm_u. Qed.

Theorem vm_guest_rice_holds : vm_guest_rice.
Proof. exact self_rice. Qed.

Theorem identity_transformer_representable :
  g_represents_transformer [] (fun p => p).
Proof.
  split; [constructor |].
  intros p Hwf.
  exists {| gr0 := guest_program_code p; gr1 := 0; gr2 := 0; gr3 := 0 |}, 0.
  split; [| reflexivity].
  exists 0. unfold g_terminal, g_input. simpl. auto.
Qed.

Print Assumptions vm_guest_execution_is_actual.
Print Assumptions vm_guest_rice_holds.
Print Assumptions identity_transformer_representable.
