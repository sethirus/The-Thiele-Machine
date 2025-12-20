From Coq Require Import QArith Lia.
Import QArith.
Open Scope Q_scope.

(* Kernel receipt-level CHSH statistic *)
Require Import CHSH.

(* Machine-level CHSH boxes and bounds *)
From ThieleMachine Require Import TsirelsonBoundBridge.
From ThieleMachine Require Import QuantumAdmissibilityTsirelson.
From ThieleMachine Require Import BellReceiptLocalBound.
From ThieleMachine Require Import BellInequality.

(** Deliverable: classical vs quantum-admissible vs partition/supra witness.

    This module is intentionally *thin*: it re-exports the already-proven
    components and supplies the small ordering lemmas that make the separation
    immediately usable.
*)

Module DeliverableCHSHSeparation.

(** Numeric strict ordering: 2 < 5657/2000 < 16/5 *)

Lemma classical_bound_strict_lt_tsirelson : (2#1) < kernel_tsirelson_bound_q.
Proof.
  unfold kernel_tsirelson_bound_q.
  unfold Qlt. simpl. lia.
Qed.

Lemma tsirelson_bound_strict_lt_partition : kernel_tsirelson_bound_q < (16#5).
Proof.
  unfold kernel_tsirelson_bound_q.
  unfold Qlt. simpl. lia.
Qed.

(** Classical (local) end-to-end receipt bound *)

Definition classical_local_receipts_CHSH_le_2 :=
  local_fragment_CHSH_le_2_end_to_end.

(** Quantum-admissible box bound (machine-level boxes, not receipt programs) *)

Theorem quantum_admissible_box_CHSH_le_tsirelson :
  forall B,
    quantum_admissible_box B ->
    Qabs (S B) <= kernel_tsirelson_bound_q.
Proof.
  exact quantum_admissible_implies_CHSH_le_tsirelson.
Qed.

(** Concrete supra-quantum witness at the kernel receipt CHSH level *)

Theorem witness_supra_16_5_CHSH :
  S SupraQuantum == 16#5.
Proof.
  exact S_SupraQuantum.
Qed.

Corollary witness_exceeds_tsirelson :
  kernel_tsirelson_bound_q < (16#5).
Proof.
  exact tsirelson_bound_strict_lt_partition.
Qed.

End DeliverableCHSHSeparation.
