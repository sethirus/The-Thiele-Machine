(** TableInvariantsReachable.v: the reachable-state invariants of C1/C2.

    [TableInvariants.hwb_table_invariants_reset] gives a boundary at the reset
    state carrying [hwb_table_invariants]. [TableInvariantsPreserved.
    hwb_table_invariants_preserved] carries it across one [Retire] step of an
    admitted instruction. [AdmittedRun] chains such steps, and
    [hwb_table_invariants_run] carries the invariant along a whole chain by
    induction. [hwb_table_invariants_reachable] is the same at the reset
    boundary: every state reachable from reset by admitted, retiring
    instructions satisfies the invariants, which are exactly the table
    premises the MORPH/COMPOSE retirement theorems already require.

    The same "chain [Retire] steps, carrying an invariant" induction is the
    skeleton the [fsm_retirement_refinement] trace-composition obligation
    needs. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep Kernel.CertCheck.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval
  StepWordFacts StepFields StepRefineCommon StepRefine StepFieldsMorph StepRefineMorph
  ImplementationContract Abstraction EmbedStep NormalizationSteps NormalizationLoop NormalizationRetirement MorphLoading
  RuleEnabled FsmDecoded ChshDecoded ChshRun ChshStepFields ChshRetire
  LassertSpec LassertWord LassertStepFields LassertRetire CouplingFsmEnds CouplingFsmRun
  CouplingMorphRich CouplingMorphKami CouplingMorphRetire
  CouplingComposeRun CouplingComposeKami CouplingComposeRetire CouplingFaults
  BoundaryRun RetireRuns RetireRunsFsm RetireRunsOps RetireMaster
  DispatchReset DispatchExecution StepFaults TableInvariants TableInvariantsPreserved.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** A chain of admitted instructions, each retiring from the boundary the
    previous one reached. *)
Inductive AdmittedRun : HWB -> list vm_instruction -> HWB -> Prop :=
| ar_nil : forall b, AdmittedRun b nil b
| ar_cons : forall b i is d d',
    admitted b i -> Retire b i d -> AdmittedRun d is d' -> AdmittedRun b (i :: is) d'.

(** The invariants carry along a whole chain. *)
Theorem hwb_table_invariants_run : forall b is d,
  hwb_table_invariants b -> AdmittedRun b is d -> hwb_table_invariants d.
Proof.
  intros b is d Hinv Hrun. induction Hrun as [b|b i is d d' Hadm HR Htail IH].
  - exact Hinv.
  - exact (IH (hwb_table_invariants_preserved b i d Hinv Hadm HR)).
Qed.

(** Every state reachable from the reset boundary by an admitted chain
    carries the invariants. The reset boundary is the one
    [TableInvariants.hwb_table_invariants_reset] exhibits, so the statement
    does not need the record projection to be injective. *)
Theorem hwb_table_invariants_reachable :
  exists b0, hwb_regs b0 = dispatch_reset_state /\
    forall is d, AdmittedRun b0 is d -> hwb_table_invariants d.
Proof.
  destruct hwb_table_invariants_reset as [br [Hbr Hinv]].
  exists br. split; [exact Hbr|].
  intros is d Hrun. exact (hwb_table_invariants_run br is d Hinv Hrun).
Qed.

(** The invariants hold of [d] along any chain, given the invariants hold of
    the chain's start. *)
Corollary hwb_table_invariants_reachable_head : forall b0 is d,
  hwb_table_invariants b0 -> AdmittedRun b0 is d -> hwb_table_invariants d.
Proof. intros b0 is d. exact (hwb_table_invariants_run b0 is d). Qed.

(** * Trace composition

    Chaining the per-instruction retirement executions gives one actual Kami
    execution of the whole chain, and the chain's final boundary observes the
    kernel's own run of the same instruction list. This is the
    [fsm_retirement_refinement] trace-composition obligation, at the level of
    the admitted chains the invariants are carried along. *)

Theorem admitted_run_multistep : forall b is d, AdmittedRun b is d ->
  exists l, Multistep thieleCore (hwb_regs b) (hwb_regs d) l.
Proof.
  intros b is d Hrun. induction Hrun as [b|b i is d d' Hadm HR Htail IH].
  - exists (@nil LabelT). apply NilMultistep. reflexivity.
  - destruct (retire_multistep b i d HR) as [l1 H1].
    destruct IH as [l2 H2].
    exists (List.app l2 l1). exact (normalization_multistep_trans _ _ _ _ _ H1 H2).
Qed.

(** The kernel's own run of an instruction list, in order. *)
Fixpoint kami_run_list (is : list vm_instruction) (ks : KamiSnapshot) : KamiSnapshot :=
  match is with
  | nil => ks
  | i :: is' => kami_run_list is' (kami_step ks i)
  end.

(** The chain's final boundary observes the kernel's run of the same
    instruction list, starting from the chain's start. *)
Theorem admitted_run_snapshot : forall b is d, AdmittedRun b is d ->
  hwb_snapshot d = kami_run_list is (hwb_snapshot b).
Proof.
  intros b is d Hrun. induction Hrun as [b|b i is d d' Hadm HR Htail IH].
  - reflexivity.
  - cbn [kami_run_list].
    destruct HR as [_ [_ [_ Hsnap]]].
    rewrite <- Hsnap. exact IH.
Qed.

(** The composed statement C1/C2 asks for: an admitted chain from the reset
    boundary is an actual Kami execution whose final state carries the table
    invariants and observes the kernel's run of the same instructions. *)
Theorem fsm_retirement_refinement :
  exists b0, hwb_regs b0 = dispatch_reset_state /\
    forall is d, AdmittedRun b0 is d ->
      hwb_table_invariants d /\
      hwb_snapshot d = kami_run_list is (hwb_snapshot b0) /\
      (exists l, Multistep thieleCore (hwb_regs b0) (hwb_regs d) l).
Proof.
  destruct hwb_table_invariants_reset as [br [Hbr Hinv]].
  exists br. split; [exact Hbr|].
  intros is d Hrun. split; [exact (hwb_table_invariants_run br is d Hinv Hrun)|].
  split; [exact (admitted_run_snapshot br is d Hrun)|].
  exact (admitted_run_multistep br is d Hrun).
Qed.

