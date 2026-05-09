From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import SpacetimeEmergence.

Import ListNotations.

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** DerivedTime: time is not fundamental.

  The claim here is that time is not a fundamental parameter of the universe
  inside this VM semantics. It is derived from equivalence classes of traces
  under observational indistinguishability.

  The key move is stutter equivalence. You can insert mdlacc instructions,
  which record structural information cost, without changing any observable.
  The traces [] and [instr_mdlacc m c] are syntactically different and have
  different lengths, but they are observationally identical.

  This is the usual ghost-step story from formal verification. It is analogous
  to the "problem of time" discussion in quantum gravity, but it is not a
  claimed resolution of that problem. It is a statement about this VM's
  transition system.

  To falsify the idea, find an observable that distinguishes [] from
  [instr_mdlacc m c], show that trace length is measurable independently of
  computational structure, or show that some indispensable physics theorem
  genuinely requires time as a primitive rather than a derived trace notion.
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

(** mdlacc_preserves_all_regions: mdlacc is a ghost instruction.
  mdlacc updates the structural cost ledger but does not modify any
  observable region. It tracks bookkeeping about computational work without
  changing memory, graph topology, or any measurement outcome. The proof is
  just inversion on vm_step followed by unfolding ObservableRegion.

  A falsification would be any memory region whose observable value changes
  after mdlacc, because that would mean the μ-ledger is entangled with the
  observable physics instead of cleanly separated from it.
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

(** Time_Is_Not_Fundamental: the stutter theorem.
  The theorem shows that syntactically different traces, namely [] and a
  singleton mdlacc trace, can be observationally identical. The proof is
  simple: the empty trace is identity, the mdlacc trace performs a state
  transition, mdlacc_preserves_all_regions gives observational equality, and
  the two traces are syntactically distinct.

  The physical interpretation is that ghost steps can be inserted without
  changing measurements. Trace length is therefore not itself an observable;
  what matters is computational structure. A falsification would show that
  step count is measurable independently of content, or produce an observable
  that separates zero-length traces from finite traces with the same memory
  content.
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
