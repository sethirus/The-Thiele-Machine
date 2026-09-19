(** VMSelfLimitative.v: B3, part 6: applicability of the self-interpreter.

    Composition: pinned MM2 halting -> CM2 guest -> guest fragment program
    [cm2_compile] -> the fixed host program [U].  The host input is data
    only: packed code, width, guest pc, guest ledger 0 and the two counters
    in guest registers 0 and 1.  Halting of the actual host run is the
    host's own termination condition ([vm_pc] reaching [U_END]).

    The limitative statement uses the upstream synthetic [undecidable]
    notion unchanged: a Boolean decider for host halting would co-enumerate
    SBTM halting.  It is not restated as a negation of decider existence. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
From Kernel Require Import VMState VMUnboundedStep.
From Kernel Require Import VMUnboundedCM2Interpreter VMUnboundedCM2Correctness VMUnboundedCM2Bridge.
From Kernel Require Import VMSelfGuest VMSelfProgram VMSelfCorrect VMSelfRun VMSelfUniversal.

Definition zero_hs : HScratch :=
  {| hs4 := 0; hs5 := 0; hs6 := 0; hs7 := 0; hs8 := 0; hs10 := 0; hs15 := 0 |}.

(** Executable total input encoding E(p, x) for any guest program. *)
Definition self_input (amb : VMState) (gp : list GInstr) (pc : nat) (g : GRegs) : VMState :=
  hb amb 0 (g_code (g_width gp) gp) (g_width gp) pc 0 g zero_hs.

Definition self_host_halts (s : VMState) : Prop :=
  exists F, (run_vm_u F U s).(vm_pc) = U_END.

Definition self_mm2_input (amb : VMState) (problem : MM2_PROBLEM) : VMState :=
  let '(p, a, b) := problem in
  self_input amb (cm2_compile (mm2_guest_program p)) 5
    {| gr0 := a; gr1 := b; gr2 := 0; gr3 := 0 |}.

Theorem self_mm2_halting_iff : forall amb problem,
  MM2_HALTING problem <-> self_host_halts (self_mm2_input amb problem).
Proof.
  intros amb [[p a] b]. unfold MM2_HALTING, self_mm2_input, self_input, self_host_halts.
  rewrite mm2_termination_guest_iff.
  set (P := cm2_compile (mm2_guest_program p)).
  set (g0 := {| gr0 := a; gr1 := b; gr2 := 0; gr3 := 0 |}).
  set (c0 := {| gc_pc := 5; gc_mu := 0; gc_g := g0 |}).
  assert (Hc : crel (mm2_guest_config (1, (a, b))) c0) by (unfold crel; cbn; lia).
  pose proof (cm2_compile_wf (mm2_guest_program p)) as Hwf.
  pose proof (g_width_fits P) as Hfit.
  change (hb amb 0 (g_code (g_width P) P) (g_width P) 5 0 g0 zero_hs)
    with (hbc amb 0 (g_width P) P c0 zero_hs).
  split.
  - intros (final & Hh).
    destruct (cm2_compile_complete _ _ _ _ Hh Hc) as (n & Ht & _).
    destruct (self_interpreter_complete amb 0 (g_width P) P Hwf Hfit n c0 zero_hs Ht)
      as (F & HF & _).
    exists F. exact HF.
  - intros (F & HF).
    destruct (self_interpreter_sound amb 0 (g_width P) P Hwf Hfit F c0 zero_hs HF)
      as (n & Ht & _).
    destruct (cm2_compile_sound _ n _ _ Hc Ht) as (final & Hh & _).
    exists final. exact Hh.
Qed.

Theorem mm2_to_self_host : forall amb : VMState,
  MM2_HALTING ⪯ self_host_halts.
Proof.
  intro amb. exists (self_mm2_input amb). intro problem. apply self_mm2_halting_iff.
Qed.

Theorem self_host_synthetic_undecidability : forall amb : VMState,
  undecidable self_host_halts.
Proof.
  intro amb. apply (undecidability_from_reducibility MM2_HALTING_undec).
  apply mm2_to_self_host, amb.
Qed.
