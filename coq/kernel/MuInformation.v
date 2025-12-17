From Coq Require Import ZArith Lia List.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.
Require Import MuLedgerConservation.

(** * μ-information (quantitative accounting)

    This file exposes a small, reusable API for the kernel’s resource ledger.

    The kernel semantics maintains a monotone counter [vm_mu] that increases
    exactly by the declared [instruction_cost] at each executed step.

    Here we package the standard “information injected” quantity:

      Δμ := μ_final − μ_init

    and connect it to the proven ledger conservation theorem.

    STATUS (Dec 16, 2025): VERIFIED (no axioms, no admits)
*)

Definition mu_total (s : VMState) : nat := s.(vm_mu).

(** Integer-valued μ-difference, always nonnegative for actual executions. *)
Definition mu_info_z (s_init s_final : VMState) : Z :=
  (Z.of_nat (mu_total s_final) - Z.of_nat (mu_total s_init))%Z.

(** Natural μ-difference (truncated subtraction). Prefer [mu_info_z] unless you
    already have a proof that [mu_total s_final >= mu_total s_init]. *)
Definition mu_info_nat (s_init s_final : VMState) : nat :=
  mu_total s_final - mu_total s_init.

Lemma mu_info_z_vm_apply :
  forall s instr,
    mu_info_z s (vm_apply s instr) = Z.of_nat (instruction_cost instr).
Proof.
  intros s instr.
  unfold mu_info_z, mu_total.
  rewrite vm_apply_mu.
  lia.
Qed.

(** The “ground truth” quantity for a bounded execution is exactly the ledger sum. *)
Definition mu_info_run_vm (fuel : nat) (trace : list vm_instruction) (s : VMState)
  : nat := ledger_sum (ledger_entries fuel trace s).

Theorem run_vm_mu_total_decomposes :
  forall fuel trace s,
    mu_total (run_vm fuel trace s) = mu_total s + mu_info_run_vm fuel trace s.
Proof.
  intros fuel trace s.
  unfold mu_total, mu_info_run_vm.
  rewrite run_vm_mu_conservation.
  reflexivity.
Qed.

Theorem mu_info_z_run_vm_is_ledger_sum :
  forall fuel trace s,
    mu_info_z s (run_vm fuel trace s) = Z.of_nat (mu_info_run_vm fuel trace s).
Proof.
  intros fuel trace s.
  unfold mu_info_z.
  rewrite run_vm_mu_total_decomposes.
  unfold mu_total.
  lia.
Qed.

Corollary mu_info_z_run_vm_nonneg :
  forall fuel trace s,
    (0 <= mu_info_z s (run_vm fuel trace s))%Z.
Proof.
  intros fuel trace s.
  rewrite mu_info_z_run_vm_is_ledger_sum.
  lia.
Qed.

Corollary run_vm_mu_total_monotone :
  forall fuel trace s,
    mu_total (run_vm fuel trace s) >= mu_total s.
Proof.
  intros fuel trace s.
  rewrite run_vm_mu_total_decomposes.
  unfold mu_info_run_vm.
  lia.
Qed.
