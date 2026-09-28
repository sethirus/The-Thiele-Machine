(** RetireProgress.v: progress to retirement under the concrete scheduler.

    [RetireMaster.admitted_retires] gives a retirement boundary for every
    admitted instruction, and [retire_runs] below shows the concrete scheduler
    reaches it ([Runs] is exactly "successive firings of the rule the actual
    priority order picks"). [admitted_progress] composes them: from a boundary
    at which an instruction is admitted, the rule runner reaches a boundary
    observing the kernel's step for that instruction, in a bounded number of
    firings, and the whole firing sequence is one actual Kami execution. That
    is the "progress to retirement" half of C1/C2, stated against the real
    scheduler rather than an abstract relation.

    [admitted_run_progress] extends it along an admitted chain, so a whole
    admitted trace is realized by one concrete runner prefix and still carries
    the table invariants. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep Kernel.CertCheck.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval
  StepWordFacts StepFields StepRefineCommon StepRefine StepFieldsMorph StepRefineMorph
  ImplementationContract Abstraction EmbedStep NormalizationSteps NormalizationLoop NormalizationRetirement
  MorphLoading RuleEnabled FsmDecoded ChshDecoded ChshRun ChshStepFields ChshRetire
  LassertSpec LassertWord LassertStepFields LassertRetire CouplingFsmEnds CouplingFsmRun
  CouplingMorphRich CouplingMorphKami CouplingMorphRetire
  CouplingComposeRun CouplingComposeKami CouplingComposeRetire CouplingFaults
  BoundaryRun RetireRuns RetireRunsFsm RetireRunsOps RetireMaster
  DispatchReset DispatchExecution StepFaults TableInvariants TableInvariantsPreserved
  TableInvariantsReachable.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** An admitted instruction retires: the concrete scheduler runs from the
    boundary to the retirement boundary in a bounded number of firings. *)
Theorem retire_runs : forall b i d, Retire b i d -> exists k, Runs b d k.
Proof.
  intros b i d [Hlive [[n Hn] _]].
  pose proof (live_step_runs b Hlive) as H1.
  exists (1 + n).
  exact (runs_trans b (step_next b) 1 H1 d n (busy_runs_runs _ _ _ Hn)).
Qed.

(** The same, with the runner equation, the kernel observation and the actual
    Kami execution. *)
Theorem admitted_progress : forall b i d, Retire b i d ->
  exists k, fst (run_boundary_rules k b) = d /\
    hwb_snapshot d = kami_step (hwb_snapshot b) i /\
    (exists l, Multistep thieleCore (hwb_regs b) (hwb_regs d) l).
Proof.
  intros b i d HR.
  destruct (retire_runs b i d HR) as [k Hk].
  destruct (retire_multistep b i d HR) as [l Hl].
  destruct HR as [_ [_ [_ Hsnap]]].
  exact (ex_intro _ k (conj (runs_runner_exact _ _ _ Hk) (conj Hsnap (ex_intro _ l Hl)))).
Qed.

(** From an admitted instruction alone: the runner fires a bounded number of
    times and the result observes the kernel step. This is the statement
    C1/C2 calls progress to retirement. *)
Theorem admitted_instruction_progress : forall b i,
  admitted b i ->
  exists d k, fst (run_boundary_rules k b) = d /\
    hwb_snapshot d = kami_step (hwb_snapshot b) i /\
    (exists l, Multistep thieleCore (hwb_regs b) (hwb_regs d) l).
Proof.
  intros b i Hadm.
  destruct (admitted_retires b i Hadm) as [d HR].
  destruct (admitted_progress b i d HR) as [k [Hk [Hs Hm]]].
  exact (ex_intro _ d (ex_intro _ k (conj Hk (conj Hs Hm)))).
Qed.

(** Progress along a whole admitted chain: one concrete runner prefix reaches
    the end boundary, the end boundary observes the kernel's own run of the
    same instruction list, and the whole chain is one actual Kami execution. *)
Theorem admitted_run_progress : forall b is d, AdmittedRun b is d ->
  exists k, Runs b d k /\
    hwb_snapshot d = kami_run_list is (hwb_snapshot b) /\
    (exists l, Multistep thieleCore (hwb_regs b) (hwb_regs d) l).
Proof.
  intros b is d Hrun. induction Hrun as [b|b i is d d' Hadm HR Htail IH].
  - exists 0. split; [apply runs_done|].
    split; [reflexivity|]. exists (@nil LabelT). apply NilMultistep. reflexivity.
  - destruct (retire_runs b i d HR) as [k1 Hk1].
    destruct IH as [k2 [Hk2 [Hs [l2 Hl2]]]].
    destruct (retire_multistep b i d HR) as [l1 Hl1].
    destruct HR as [_ [_ [_ Hsnap]]].
    exists (k1 + k2). split; [exact (runs_trans _ _ _ Hk1 _ _ Hk2)|].
    split.
    + cbn [kami_run_list]. rewrite <- Hsnap. exact Hs.
    + exists (List.app l2 l1).
      exact (normalization_multistep_trans _ _ _ _ _ Hl1 Hl2).
Qed.

(** The runner-prefix form of the chain statement. *)
Corollary admitted_run_progress_runner : forall b is d, AdmittedRun b is d ->
  exists k, fst (run_boundary_rules k b) = d.
Proof.
  intros b is d Hrun.
  destruct (admitted_run_progress b is d Hrun) as [k [Hk _]].
  exact (ex_intro _ k (runs_runner_exact _ _ _ Hk)).
Qed.

(** An admitted chain from a boundary carrying the invariants is realized by
    the runner, ends in a state carrying them, and observes the kernel's run
    of the same instructions. *)
Theorem admitted_run_progress_invariants : forall b is d,
  hwb_table_invariants b -> AdmittedRun b is d ->
  exists k, fst (run_boundary_rules k b) = d /\
    hwb_table_invariants d /\
    hwb_snapshot d = kami_run_list is (hwb_snapshot b).
Proof.
  intros b is d Hinv Hrun.
  destruct (admitted_run_progress b is d Hrun) as [k [Hk [Hs _]]].
  exact (ex_intro _ k (conj (runs_runner_exact _ _ _ Hk)
    (conj (hwb_table_invariants_run b is d Hinv Hrun) Hs))).
Qed.
