(** Exact recursion-theorem and Rice targets for the self-interpreted guest. *)

From Coq Require Import List.
From Undecidability.Synthetic Require Import Undecidability.
From Kernel Require Import VMInstructionEncoding VMSelfGuest VMSelfRice VMSelfRiceUndec.

Definition guest_program_code (p : list GInstr) : nat :=
  program_to_nat (g_program p).

Definition g_represents_transformer
    (D : list GInstr) (F : list GInstr -> list GInstr) : Prop :=
  g_wf_program D /\
  forall p, g_wf_program p ->
    exists g mu, g_beh D (guest_program_code p) g mu /\
      gr0 g = guest_program_code (F p).

Definition vm_guest_recursion_theorem : Prop :=
  forall (F : list GInstr -> list GInstr) (D : list GInstr),
    (forall p, g_wf_program p -> g_wf_program (F p)) ->
    g_represents_transformer D F ->
    exists p, g_wf_program p /\ g_equiv p (F p).

Definition vm_guest_rice : Prop :=
  forall (Pr : list GInstr -> Prop) (w : list GInstr),
    g_extensional Pr -> g_wf_program w -> Pr w -> ~ Pr g_bottom ->
    undecidable (fun p => g_wf_program p /\ Pr p).

