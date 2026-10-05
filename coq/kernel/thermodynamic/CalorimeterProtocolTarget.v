(** Two-state calorimeter definitions. *)

From Coq Require Import Reals.
Local Open Scope R_scope.

(* SCOPE NOTE: standalone proof scope.  The parameters are physical inputs;
   no machine ledger fixes their units. *)

Definition two_state_hamiltonian (Delta : R) (excited : bool) : R :=
  if excited then Delta else 0.

Definition mean_register_energy (Delta p_excited : R) : R :=
  Delta * p_excited.

Definition master_next
    (dt k01 k10 p_excited : R) : R :=
  p_excited + dt * (k01 * (1 - p_excited) - k10 * p_excited).

Definition bath_heat_fixed_hamiltonian
    (Delta p_before p_after : R) : R :=
  mean_register_energy Delta p_before - mean_register_energy Delta p_after.

Definition canonical_reset_before : R := / 2.
(* SAFE: a completed reset leaves the register in the ground state, so the
   excited-state probability after the step is zero. *)
Definition canonical_reset_after : R := 0.
Definition canonical_reset_dt : R := 1.
(* SAFE: the reset protocol drives only the downward transition; the upward
   rate is zero by construction of the protocol. *)
Definition canonical_reset_k01 : R := 0.
Definition canonical_reset_k10 : R := 1.
Definition canonical_reset_mu : nat := 1.
