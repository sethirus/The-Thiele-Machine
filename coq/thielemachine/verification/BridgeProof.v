From Coq Require Import Lia.
From ThieleUniversal Require Import TM UTM_Program UTM_Encode.
From ThieleMachineVerification Require Import BridgeDefinitions.
From ThieleMachineVerification Require Import BridgeCheckpoints.

(* CREATIVE OPTIMIZATION: Using native_compute instead of vm_compute for massive speedup.
   Native compilation of the computation is 10-100x faster than vm_compute.
   These proofs verify CPU execution via computational reflection on concrete states. *)

(** [prove_segment_0_3]: formal specification. *)
Theorem prove_segment_0_3:
  check_transition checkpoint_0 checkpoint_3 3 = true.
Proof.
  native_compute. reflexivity.
Qed.

(** [prove_segment_3_9]: formal specification. *)
Theorem prove_segment_3_9:
  check_transition checkpoint_3 checkpoint_9 6 = true.
Proof.
  native_compute. reflexivity.
Qed.

(** [prove_segment_9_15]: formal specification. *)
Theorem prove_segment_9_15:
  check_transition checkpoint_9 checkpoint_15 6 = true.
Proof.
  native_compute. reflexivity.
Qed.

(** [prove_segment_15_19]: formal specification. *)
Theorem prove_segment_15_19:
  check_transition checkpoint_15 checkpoint_19 4 = true.
Proof.
  native_compute. reflexivity.
Qed.

(* General isomorphism proof - setup_state correctly encodes a TM configuration *)
(** [cpu_tm_general_isomorphism]: formal specification. *)
Theorem cpu_tm_general_isomorphism : forall tm conf,
  length program <= UTM_Program.RULES_START_ADDR ->
  length (UTM_Encode.encode_rules tm.(tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR ->
  let st := setup_state tm conf in
  CPU.read_reg CPU.REG_Q st = fst (fst conf) /\
  CPU.read_reg CPU.REG_HEAD st = snd conf /\
  tape_window_ok st (snd (fst conf)).
Proof.
  apply cpu_tm_isomorphism.
Qed.
