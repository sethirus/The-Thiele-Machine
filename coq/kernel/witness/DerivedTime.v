From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import SpacetimeEmergence.

Import ListNotations.

(* SCOPE NOTE: foundation connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** DerivedTime: observational trace time in this VM.

  This file compares traces under one named observation relation.
  An [instr_mdlacc] step can change the ledger while leaving every
  [ObservableRegion] unchanged.
  The empty trace and a singleton [instr_mdlacc] trace are therefore different
  instruction lists with equal observations under the relation used here.

  This is a statement about the VM transition system.
  It is not a claim about time in physics or about the philosophical status of
  time outside this model.

  The boundary is the observation relation itself.
  A stronger observation could distinguish the traces, and a theorem requiring
  a primitive time field would need a different interface.
*)

(** trace_equiv_region: observational equivalence.
  Two traces are equivalent when, from the same starting state, they produce
  final states with identical observable regions in every memory module. This
  is the operational meaning of "same outcome."
*)
Definition trace_equiv_region (s : VMState) (t1 t2 : list vm_instruction) : Prop :=
  forall s1 s2,
    exec_trace s t1 s1 ->
    exec_trace s t2 s2 ->
    forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

(** Derived_Time: time represented by traces.
  Time is not primitive here. It is represented as the type of traces with a
  trivial witness. The file deliberately does not quotient by
  trace_equiv_region, because doing that too early would hide the main point.
  Instead it keeps syntactic distinctions and then proves that distinct traces
  can still be observationally equivalent.
*)
Definition Derived_Time (s : VMState) : Type :=
  { t : list vm_instruction | True }.

(** mdlacc_preserves_all_regions: the named observation is unchanged.
  [mdlacc] updates the cost ledger but does not modify an [ObservableRegion].
  The proof inverts [vm_step] and unfolds [ObservableRegion].
  This lemma says nothing about observations that include the ledger itself.
*)
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

(** Time_Is_Not_Fundamental: a named-observation stutter witness.
  The theorem exhibits the empty trace and a singleton [mdlacc] trace as
  syntactically different lists with equal [ObservableRegion] values.
  It does not say that every observer treats the traces as equal.
*)
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

(** trace_equiv_region_stutter: explicit observational equivalence.
  This restates the same stutter result directly in the language of
  trace_equiv_region. The previous theorem provides the existential witness;
  this one proves the equivalence predicate itself by inverting the two
  exec_trace hypotheses and applying mdlacc_preserves_all_regions.
*)
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
