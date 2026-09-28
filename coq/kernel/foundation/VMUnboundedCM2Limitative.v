(** Applicable reduction theorem for actual unbounded host halting.
    The upstream synthetic [undecidable] notion is printed and preserved:
    it means that a total Boolean decider would co-enumerate SBTM halting.
    This file does not silently replace that with [~ decidable]. *)
From Coq Require Import List.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
From Kernel Require Import VMState VMUnboundedCM2Bridge.

Theorem mm2_to_actual_unbounded_host : forall ambient : VMState,
  MM2_HALTING ⪯ cm2_host_halts.
Proof.
  intro ambient. exists (mm2_host_input ambient).
  intro problem. apply mm2_halting_host_iff.
Qed.

Theorem actual_unbounded_host_synthetic_undecidability : forall ambient : VMState,
  undecidable cm2_host_halts.
Proof.
  intro ambient. apply (undecidability_from_reducibility MM2_HALTING_undec).
  apply (mm2_to_actual_unbounded_host ambient).
Qed.
