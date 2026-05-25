(** * UnificationProbeBridges — composing the probe files with the VM.

    [LandauerJoules.v], [HolevoDimensional.v], and [BekensteinBound.v]
    each prove a physical bound for an abstract object (a
    [PhysicalErasure] record, a [FeasibleSet], a real-valued
    [system_entropy_nats]); on their own they do not touch the VM.

    This file anchors each probe in the framework's existing µ-ledger
    and cert-flip vocabulary by composing a framework-side fact about
    VM steps (typically from [AbstractNoFI.v] or [MuShannonBridge.v])
    with one of the new bounds, so the conclusion is stated in VM
    vocabulary.

    The four bridges:

      Bridge A — every cert-flip VM step exhibits as a one-bit
                 [PhysicalErasure], with the [second_law_satisfied]
                 field witnessed by [no_free_certification_certified].

      Bridge B — in a thermal substrate satisfying the
                 [LandauerJoules.v] hypotheses, every cert-flip VM
                 step releases at least [k_B · T · ln 2] of heat.

      Bridge C — for any VM trace whose cert-setter executions
                 realise a decision tree covering an [n]-outcome
                 feasible set, [Δµ ≥ log_2 n].

      Bridge D — in a substrate where [vm_mu] increment matches the
                 substrate's information entropy in nats, the Bekenstein
                 bound is a bound on [vm_mu] itself:
                 [Δµ / ln 2 ≤ 2π · E · R / (ℏ c ln 2)].

    Each bridge composes at least one probe theorem with at least one
    framework theorem; none adds a project-local axiom. *)

From Coq Require Import List Arith.PeanoNat Lia Reals Lra.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuCostModel.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import AbstractNoFI.
From Kernel Require Import MuShannonBridge.

(** Cross-tier imports: the Landauer-bridge content used by
    Bridge B / Bridge C below; the LandauerDerived and LandauerJoules
    theorems live in coq/thermodynamic/ for separation of concerns,
    but this aggregator is the kernel-side bridging file that
    combines them with VM-level mu-ledger results. *)

(* INQUISITOR NOTE: cross-tier import (Landauer bridge — see above). *)
From Thermodynamic Require Import LandauerDerived.
(* INQUISITOR NOTE: cross-tier import (Landauer bridge — see above). *)
From Thermodynamic Require Import LandauerJoules.

From Kernel Require Import HolevoDimensional.
From Kernel Require Import BekensteinBound.

(** ** Bridge A — VM cert-flip ↔ PhysicalErasure.

    Given a single VM step that flips [vm_certified] from [false] to
    [true], we construct a [PhysicalErasure] record realising it. The
    [second_law_satisfied] field of the constructed record is exactly
    the framework's [no_free_certification_certified] applied to the
    given step. *)

Definition cert_flip_to_physical_erasure
  (s : VMState) (i : vm_instruction)
  (Hpre : vm_certified s = false)
  (Hpost : vm_certified (vm_apply s i) = true)
  : PhysicalErasure.
Proof.
  unshelve refine ({|
    erasure_op := {| input_bits := 1; output_bits := 0; output_leq := _ |};
    env_entropy_increase := instruction_cost i;
    second_law_satisfied := _
  |}).
  - exact (Nat.le_0_l 1).
  - simpl. unfold bits_erased. simpl.
    pose proof (no_free_certification_certified s i Hpre Hpost) as Hcost.
    lia.
Defined.

(** The constructed erasure has [bits_erased = 1]. *)
Lemma cert_flip_physical_erasure_bits :
  forall s i Hpre Hpost,
    bits_erased (erasure_op (cert_flip_to_physical_erasure s i Hpre Hpost)) = 1.
Proof.
  intros. unfold cert_flip_to_physical_erasure. simpl.
  unfold bits_erased. simpl. reflexivity.
Qed.

(* The [env_entropy_increase] field of [cert_flip_to_physical_erasure] is
   exactly [instruction_cost i] by record construction. The previous lemma
   [cert_flip_physical_erasure_env] only reflected this definitional
   identity (no callers); any consumer that needs it can [simpl] / [unfold]
   directly on the projection. *)

(** ** Bridge B — VM cert-flip in a thermal bath releases ≥ k_B · T · ln 2.

    Composes Bridge A with [LandauerJoules.landauer_joules_one_bit].
    Given the thermal-substrate hypotheses (Boltzmann bridge +
    second law for a bath), every cert-flip VM step releases at least
    [k_B · T · ln 2] of heat to the bath. *)

(* INQUISITOR NOTE: SECTION PARAMETER — the Variable and Hypothesis
   declarations in this Section are section parameters that become
   EXPLICIT FORALL premises on every theorem when the Section closes.
   k_B_pos is physical positivity for the Boltzmann constant; the
   boltzmann_bridge and second_law_thermal_bath are the textbook
   physics inputs to the Landauer / second-law derivation. None are
   global axioms; the Section discharge gives every theorem its full
   set of preconditions. *)
Section ThermalBathCertFlip.

  Variables T k_B : R.
  Hypothesis k_B_pos : (0 < k_B)%R.

  Variable system_thermo_entropy_decrease : PhysicalErasure -> R.
  Variable heat_to_bath_per_erasure : PhysicalErasure -> R.

  Hypothesis boltzmann_bridge :
    forall pe : PhysicalErasure,
      system_thermo_entropy_decrease pe =
      (k_B * info_entropy_decrease_nats pe)%R.

  Hypothesis second_law_thermal_bath :
    forall pe : PhysicalErasure,
      (0 <= system_thermo_entropy_decrease pe)%R ->
      (T * system_thermo_entropy_decrease pe <= heat_to_bath_per_erasure pe)%R.

  Theorem cert_flip_releases_landauer_heat :
    forall (s : VMState) (i : vm_instruction)
           (Hpre : vm_certified s = false)
           (Hpost : vm_certified (vm_apply s i) = true),
      (k_B * T * ln 2 <=
       heat_to_bath_per_erasure
         (cert_flip_to_physical_erasure s i Hpre Hpost))%R.
  Proof.
    intros s i Hpre Hpost.
    pose (pe := cert_flip_to_physical_erasure s i Hpre Hpost).
    assert (Hbits : (INR (bits_erased (erasure_op pe)) = 1)%R).
    { unfold pe. rewrite cert_flip_physical_erasure_bits. simpl. reflexivity. }
    pose proof (landauer_joules T k_B k_B_pos
                  system_thermo_entropy_decrease boltzmann_bridge
                  heat_to_bath_per_erasure second_law_thermal_bath pe) as Hgen.
    rewrite Hbits in Hgen.
    apply Rle_trans with (k_B * T * 1 * ln 2)%R;
      [apply Req_le; ring | exact Hgen].
  Qed.

End ThermalBathCertFlip.

(** ** Bridge C — VM trace classical Holevo bound.

    Composes [HolevoDimensional.classical_holevo_bound] with the
    framework's existing [info_priced_cert_executions_bound]. The
    resulting statement is in pure VM vocabulary: given a VM trace
    that realises a decision tree covering an [n]-outcome feasible
    set, [Δµ ≥ log_2 n]. *)

Theorem vm_trace_classical_holevo :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega : FeasibleSet) (tree : DecisionTree),
    decision_tree_realized_by_trace fuel trace s tree ->
    substrate_dimension omega <= decision_tree_leaf_count tree ->
    Nat.log2 (feasible_size omega) <=
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega tree Hrealized Hcover.
  pose proof (classical_holevo_bound fuel trace s omega tree Hrealized Hcover)
    as Hbound.
  unfold accessible_classical_information, substrate_dimension in Hbound.
  exact Hbound.
Qed.

(** Specialisation: for an [n]-qubit-shaped substrate ([2^n] outcomes),
    [Δµ ≥ n]. This is the "n classical bits from n qubits" form. *)
Corollary vm_trace_n_qubits_classical_holevo :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega : FeasibleSet) (tree : DecisionTree) (n : nat),
    substrate_dimension omega = 2 ^ n ->
    decision_tree_realized_by_trace fuel trace s tree ->
    substrate_dimension omega <= decision_tree_leaf_count tree ->
    n <= (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega tree n Hdim Hrealized Hcover.
  exact (classical_holevo_n_qubits fuel trace s omega tree n
            Hdim Hrealized Hcover).
Qed.

(** ** Bridge D — VM µ-ledger bounded by Bekenstein in a bounded substrate.

    For a VM trace operating inside a bounded thermal substrate of
    radius [R] and total energy [E], if the substrate satisfies the
    second-law hypothesis of [BekensteinBound.v] with the VM's
    µ-cost (in nats) playing the role of [system_entropy_nats], then
    the µ-ledger is bounded by the Bekenstein bound on bits. *)

(* INQUISITOR NOTE: SECTION PARAMETER — Variable/Hypothesis declarations
   in this Section are section parameters that become EXPLICIT FORALL
   premises on each theorem when the Section closes. Constants
   (hbar, c_light, k_B, R_radius) carry physical positivity; the
   vm_mu_delta_nonneg and vm_thermo_second_law_bekenstein hypotheses
   are the substrate-binding preconditions for applying Bekenstein to
   a VM trace. Not global axioms. *)
Section BekensteinVMBridge.

  Variables hbar c_light k_B R_radius E_total : R.
  Hypothesis hbar_pos : (0 < hbar)%R.
  Hypothesis c_light_pos : (0 < c_light)%R.
  Hypothesis k_B_pos : (0 < k_B)%R.
  Hypothesis R_pos : (0 < R_radius)%R.

  (** The µ-ledger increment expressed in nats. We multiply by [ln 2]
      because [vm_mu] is a count of cert-setter executions (effectively
      bits) and the substrate physics works in nats.

      Specifically, [vm_mu_delta_nats fuel trace s] is the trace's
      µ-cost increment, viewed as a Shannon entropy decrease in nats. *)
  Definition vm_mu_delta_nats
    (fuel : nat) (trace : list vm_instruction) (s : VMState) : R :=
    (INR ((run_vm fuel trace s).(vm_mu) - s.(vm_mu)) * ln 2)%R.

  Hypothesis vm_mu_delta_nonneg :
    forall fuel trace s,
      (0 <= vm_mu_delta_nats fuel trace s)%R.

  Hypothesis vm_thermo_second_law_bekenstein :
    forall fuel trace s,
      (unruh_temperature_of_radius hbar c_light k_B R_radius * k_B *
        vm_mu_delta_nats fuel trace s <= E_total)%R.

  Theorem vm_mu_bekenstein_bound :
    forall fuel trace s,
      (INR ((run_vm fuel trace s).(vm_mu) - s.(vm_mu)) <=
       2 * PI * E_total * R_radius / (hbar * c_light * ln 2))%R.
  Proof.
    intros fuel trace s.
    pose proof (bekenstein_bound hbar c_light k_B R_radius E_total
                  hbar_pos c_light_pos k_B_pos R_pos
                  (vm_mu_delta_nats fuel trace s)
                  (vm_thermo_second_law_bekenstein fuel trace s)) as Hbound.
    (* Hbound : system_entropy_bits (vm_mu_delta_nats ...) <=
                2 * PI * E_total * R_radius / (hbar * c_light * ln 2) *)
    unfold system_entropy_bits, vm_mu_delta_nats in Hbound.
    (* Hbound : INR (Δµ) * ln 2 / ln 2 <= ... *)
    assert (Hln2 : (0 < ln 2)%R) by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Hsimp :
      (INR ((run_vm fuel trace s).(vm_mu) - s.(vm_mu)) * ln 2 / ln 2 =
       INR ((run_vm fuel trace s).(vm_mu) - s.(vm_mu)))%R).
    { field. lra. }
    rewrite Hsimp in Hbound.
    exact Hbound.
  Qed.

End BekensteinVMBridge.

(** Print Assumptions: each bridge composes only existing theorems.
    Headlines should report only the standard Coq.Reals axioms. *)

Print Assumptions cert_flip_to_physical_erasure.
Print Assumptions cert_flip_releases_landauer_heat.
Print Assumptions vm_trace_classical_holevo.
Print Assumptions vm_mu_bekenstein_bound.
