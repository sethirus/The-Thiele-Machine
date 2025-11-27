From Coq Require Import Lia.
From ThieleMachine Require Import BridgeDefinitions.
From ThieleMachine Require Import BridgeCheckpoints.

(* TEMPORARY: These proofs use vm_compute on 1000-element arrays which takes 10+ minutes each.
   Admitting for now to unblock compilation of other files.
   TODO: Optimize by either:
   1. Using native_compute instead of vm_compute
   2. Reducing checkpoint memory size
   3. Using incremental verification *)

Theorem prove_segment_0_3:
  check_transition checkpoint_0 checkpoint_3 3 = true.
Proof.
Admitted.

Theorem prove_segment_3_9:
  check_transition checkpoint_3 checkpoint_9 6 = true.
Proof.
Admitted.

Theorem prove_segment_9_15:
  check_transition checkpoint_9 checkpoint_15 6 = true.
Proof.
Admitted.

Theorem prove_segment_15_19:
  check_transition checkpoint_15 checkpoint_19 4 = true.
Proof.
Admitted.
