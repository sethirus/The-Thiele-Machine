(** Exact energy bookkeeping and its dimensional boundary for the
    two-state calorimeter protocol. *)

(* SCOPE NOTE: standalone proof scope. The two-state calorimeter protocol
   is a physical model with its own parameters; no machine ledger fixes its
   units. *)

From Coq Require Import Reals Lra Lia.
From Kernel Require Import CalorimeterProtocolTarget.

Local Open Scope R_scope.

Theorem canonical_reset_satisfies_master_equation :
  master_next canonical_reset_dt canonical_reset_k01 canonical_reset_k10
    canonical_reset_before = canonical_reset_after.
Proof.
  unfold master_next, canonical_reset_dt, canonical_reset_k01,
    canonical_reset_k10, canonical_reset_before, canonical_reset_after.
  field.
Qed.

Theorem canonical_reset_heat_exact : forall Delta,
  bath_heat_fixed_hamiltonian Delta canonical_reset_before
    canonical_reset_after = Delta / 2.
Proof.
  intro Delta.
  unfold bath_heat_fixed_hamiltonian, mean_register_energy,
    canonical_reset_before, canonical_reset_after.
  field.
Qed.

Theorem selected_gap_gives_landauer_heat : forall k_B T,
  bath_heat_fixed_hamiltonian (2 * k_B * T * ln 2)
    canonical_reset_before canonical_reset_after = k_B * T * ln 2.
Proof.
  intros k_B T. rewrite canonical_reset_heat_exact. field.
Qed.

Lemma ln_two_positive : 0 < ln 2.
Proof.
  rewrite <- ln_1. apply ln_increasing; lra.
Qed.

Theorem smaller_gap_refutes_unconditional_landauer_floor : forall k_B T,
  0 < k_B -> 0 < T ->
  bath_heat_fixed_hamiltonian (k_B * T * ln 2)
    canonical_reset_before canonical_reset_after < k_B * T * ln 2.
Proof.
  intros k_B T Hk HT.
  rewrite canonical_reset_heat_exact.
  assert (Hscale : 0 < k_B * T * ln 2).
  { apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; assumption.
    - exact ln_two_positive. }
  lra.
Qed.

(** The population dynamics are identical for both gaps, while the exact
    energy transfer differs. *)
Theorem master_equation_does_not_fix_heat_scale :
  exists Delta1 Delta2,
    Delta1 <> Delta2 /\
    master_next canonical_reset_dt canonical_reset_k01 canonical_reset_k10
      canonical_reset_before = canonical_reset_after /\
    master_next canonical_reset_dt canonical_reset_k01 canonical_reset_k10
      canonical_reset_before = canonical_reset_after /\
    bath_heat_fixed_hamiltonian Delta1 canonical_reset_before
      canonical_reset_after <>
    bath_heat_fixed_hamiltonian Delta2 canonical_reset_before
      canonical_reset_after.
Proof.
  exists 1, 2. repeat split.
  - lra.
  - exact canonical_reset_satisfies_master_equation.
  - exact canonical_reset_satisfies_master_equation.
  - rewrite !canonical_reset_heat_exact. lra.
Qed.

Lemma canonical_reset_is_one_mu : canonical_reset_mu = 1%nat.
Proof. reflexivity. Qed.

Print Assumptions canonical_reset_satisfies_master_equation.
Print Assumptions canonical_reset_heat_exact.
Print Assumptions selected_gap_gives_landauer_heat.
Print Assumptions smaller_gap_refutes_unconditional_landauer_floor.
Print Assumptions master_equation_does_not_fix_heat_scale.
