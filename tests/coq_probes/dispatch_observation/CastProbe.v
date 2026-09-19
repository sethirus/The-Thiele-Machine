Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import DispatchObservation.

(** A minimal reproduction with no FMap or CPU rule at all. *)
Example zero_extend_four_bit_one :
  evalZeroExtendTrunc 4 (natToWord 4 1) = natToWord 4 1.
Proof.
  vm_compute.
  (* The residual dependent cast prevents definitional equality. *)
  Fail reflexivity.
  clear_concrete_word_casts.
  reflexivity.
Qed.
Print Assumptions zero_extend_four_bit_one.
