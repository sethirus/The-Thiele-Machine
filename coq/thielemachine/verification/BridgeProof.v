From Coq Require Import Lia.
From ThieleMachine Require Import BridgeDefinitions.
From ThieleMachine Require Import BridgeCheckpoints.

(* CREATIVE OPTIMIZATION: Using native_compute instead of vm_compute for massive speedup.
   Native compilation of the computation is 10-100x faster than vm_compute.
   These proofs verify CPU execution via computational reflection on concrete states. *)

Theorem prove_segment_0_3:
  check_transition checkpoint_0 checkpoint_3 3 = true.
Proof.
  native_compute. reflexivity.
Qed.

Theorem prove_segment_3_9:
  check_transition checkpoint_3 checkpoint_9 6 = true.
Proof.
  native_compute. reflexivity.
Qed.

Theorem prove_segment_9_15:
  check_transition checkpoint_9 checkpoint_15 6 = true.
Proof.
  native_compute. reflexivity.
Qed.

Theorem prove_segment_15_19:
  check_transition checkpoint_15 checkpoint_19 4 = true.
Proof.
  native_compute. reflexivity.
Qed.
