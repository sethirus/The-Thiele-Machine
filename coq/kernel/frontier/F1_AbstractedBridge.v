(** * F1_AbstractedBridge: factoring the F1 Landauer derivation

    The headline theorem in [F1_LogicalErasure.v]
    ([A2_from_physical_reversibility_real]) factored A2 through a
    Landauer bridge whose body and conclusion both mentioned
    [instruction_cost] specifically. This file factors that bridge
    one step further: the bridge body and conclusion are stated over
    an abstract cost function [phys_cost : vm_instruction -> nat],
    with no occurrence of [instruction_cost] anywhere in the headline
    theorem statement.

    ** Honest scope

    What this file is:

      - An abstraction of the Landauer bridge over arbitrary cost
        functions [vm_instruction -> nat]. The headline theorem
        [F1_factored_through_abstract_cost] never names
        [instruction_cost]; [instruction_cost] is recovered only by
        instantiation in the composition corollary.

    What this file is NOT:

      - F1 strong-form closure. The bridge body still has cost-floor
        shape ([phys_cost i >= mu_bit]); the abstraction shifts that
        shape from a specific cost to an arbitrary cost, but does not
        eliminate it. The strong form of F1 would require the bridge
        to be statable in operationally-defined physical vocabulary
        (real-valued thermodynamic dissipation in joules, or
        class-collapse counts on macrostates defined by physical
        operations) without a generic ≥-inequality on a [nat]-valued
        cost. That remains open.

    What this buys (narrow but real):

    - The mathematical content of A2 is shown to be cost-function-
      independent: any system whose cost function satisfies the
      Landauer-bridge shape obtains the same A2 conclusion. Thiele's
      [instruction_cost] is one realisation among the universe of cost
      functions that could realise it, not a privileged load-bearer.
    - Separates "Landauer bridge has cost-floor shape" (universal /
      abstract) from "Thiele's [instruction_cost] satisfies the bridge"
      (framework-specific witness). The conceptual factorisation is
      cleaner.

    Bridge is a Prop hypothesis at the theorem level; no project-local
    axiom is added. No bypass markers. Print Assumptions returns
    "Closed under the global context" for every theorem below.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool.

From Kernel Require Import VMState VMStep SimulationProof PrimeAxiom AbstractNoFI.
From Kernel Require Import F1_LogicalErasure.

(** ** Headline — A2's argument over an abstract cost function.

    For any [phys_cost : vm_instruction -> nat] satisfying the Landauer
    bridge (universal-[P] form, with cost-floor [phys_cost i >= mu_bit]
    on every class-collapsing step) at [mu_bit >= 1], the cert-flip
    cost-floor [phys_cost i >= 1] follows.

    Theorem statement contains no occurrence of [instruction_cost]. The
    proof composes the [F1_LogicalErasure] structural lemma (cert-flip
    implies class-collapse on [vm_certified]) with the universally-
    quantified Landauer bridge, then closes with [lia] on the calibration
    [mu_bit >= 1]. Three independent ingredients, no unfold-apply. *)

Theorem F1_factored_through_abstract_cost :
  forall (phys_cost : vm_instruction -> nat) (mu_bit : nat),
    mu_bit >= 1 ->
    (forall (P : bool_macro_property) (i : vm_instruction),
        step_collapses_bool_classes P i ->
        phys_cost i >= mu_bit) ->
    forall (s : VMState) (i : vm_instruction),
      vm_certified s = false ->
      vm_certified (vm_apply s i) = true ->
      phys_cost i >= 1.
Proof.
  intros phys_cost mu Hcal HLandauer s i Hf Ht.
  pose proof (cert_flip_collapses_cert_classes s i Hf Ht) as Hcollapse.
  pose proof (HLandauer vm_certified i Hcollapse) as Hcost.
  lia.
Qed.

(** ** Composition (sanity) — instantiate to [instruction_cost].

    Specialising [F1_factored_through_abstract_cost] to
    [phys_cost := instruction_cost] and [mu_bit := 1] recovers
    [A2_from_physical_reversibility_real]'s conclusion, given the
    same universal-[P] bridge as a hypothesis. This shows the
    abstract theorem has the original as an instance.

    NOTE: this corollary takes the universal-[P] bridge for
    [instruction_cost] as a hypothesis. The framework's existing cost
    law ([no_free_certification_certified] in [AbstractNoFI.v])
    discharges only the cert-only sub-case ([P = vm_certified] at
    [mu_bit = 1]); the universal-[P] version is the physical-
    reversibility *premise* the F1 derivation imports. The corollary
    therefore does not close F1 — it only confirms the abstract
    theorem instantiates correctly. *)

Corollary A2_via_abstract_landauer_universal_bridge :
  (forall (P : bool_macro_property) (i : vm_instruction),
      step_collapses_bool_classes P i ->
      instruction_cost i >= 1) ->
  forall (s : VMState) (i : vm_instruction),
    vm_certified s = false ->
    vm_certified (vm_apply s i) = true ->
    instruction_cost i >= 1.
Proof.
  intros Huniv s i Hf Ht.
  apply (F1_factored_through_abstract_cost
           instruction_cost 1 (le_n 1) Huniv s i Hf Ht).
Qed.

(** ** Print Assumptions sanity.

    All three theorems above are [Closed under the global context]. The
    abstract cost parameter [phys_cost] and the universal-[P] bridge
    are theorem-level Prop hypotheses — neither is a Coq [Axiom],
    [Parameter], or [Hypothesis]. The kernel's zero-project-local-
    axioms invariant is preserved.

    F1 strong-form residual: the bridge body still has cost-floor
    shape ([phys_cost i >= mu_bit]). Closing F1's strong form would
    require restating the bridge in operationally-defined physical
    vocabulary (e.g., real-valued dissipation in joules, or
    thermodynamic class-collapse counts on macrostates defined by
    physical operations) such that the bridge body cannot be unfolded
    back to a generic ≥-inequality on a [nat]-valued cost function.
    That direction needs a real-valued physics formalisation pass that
    is not provided here. *)
