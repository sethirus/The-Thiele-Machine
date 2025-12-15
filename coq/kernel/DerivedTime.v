From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import SpacetimeEmergence.

Import ListNotations.

Definition trace_equiv_region (s : VMState) (t1 t2 : list vm_instruction) : Prop :=
  forall s1 s2,
    exec_trace s t1 s1 ->
    exec_trace s t2 s2 ->
    forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

Definition Derived_Time (s : VMState) : Type :=
  { t : list vm_instruction | True }.

Lemma mdlacc_preserves_all_regions :
  forall s module cost s',
    vm_step s (instr_mdlacc module cost) s' ->
    forall mid, ObservableRegion s mid = ObservableRegion s' mid.
Proof.
  intros s module cost s' Hstep mid.
  inversion Hstep; subst; simpl.
  unfold ObservableRegion.
  reflexivity.
Qed.

Theorem Time_Is_Not_Fundamental :
  forall s module cost,
    exists s',
      exec_trace s [] s /\
      exec_trace s [instr_mdlacc module cost] s' /\
      (forall mid, ObservableRegion s mid = ObservableRegion s' mid) /\
      [] <> [instr_mdlacc module cost].
Proof.
  intros s module cost.
  exists (advance_state s (instr_mdlacc module cost) (vm_graph s) (vm_csrs s) (vm_err s)).
  split.
  - constructor.
  - split.
    + eapply exec_trace_cons.
      * apply step_mdlacc.
      * constructor.
    + split.
      * intro mid.
        apply mdlacc_preserves_all_regions with (module := module) (cost := cost).
        apply step_mdlacc.
      * discriminate.
Qed.

Theorem trace_equiv_region_stutter :
  forall s module cost,
    trace_equiv_region s [] [instr_mdlacc module cost].
Proof.
  intros s module cost s1 s2 Hnil Hone mid.
  inversion Hnil; subst.
  inversion Hone; subst.
  repeat match goal with
         | H : exec_trace _ [] _ |- _ => inversion H; subst; clear H
         end.
  match goal with
  | Hstep : vm_step _ (instr_mdlacc _ _) _ |- _ =>
      eapply mdlacc_preserves_all_regions; eauto
  end.
Qed.
