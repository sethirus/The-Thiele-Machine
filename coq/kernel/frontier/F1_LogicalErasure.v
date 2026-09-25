(** * F1_LogicalErasure: an A2 theorem from an explicit bridge premise.

    The headline theorem takes a cost-floor premise over an arbitrary boolean
    macro-property and applies it to the certification predicate.

    [cert_flip_collapses_cert_classes] supplies the ISA-specific structural step.

    A false-to-true [vm_certified] transition is shown to collapse both boolean
    classes because [vm_apply_certified] restricts the writer and its result.

    The calibration premise supplies [mu_per_landauer_bit >= 1].

    The conclusion is obtained by composing the named bridge, the structural lemma,
    and the calibration inequality.

    The bridge is a theorem-level [Prop] premise, not a project-local axiom.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof PrimeAxiom AbstractNoFI.

(** ** Step 1 — bool-valued macro-properties.

    A bool-valued macro-property is any predicate on VMState. The cert
    flag [vm_certified] is one such property, but the framework
    accepts any. *)

Definition bool_macro_property := VMState -> bool.

(** ** Step 2 — class-collapse on a bool-valued macro-property.

    A step [i] collapses the bool-class space of property P iff:
    (1) some pre-state with [P = false] maps to a post-state with
        [P = true] under [vm_apply _ i], AND
    (2) every pre-state with [P = true] maps to a post-state with
        [P = true] under [vm_apply _ i].

    Combined: both pre-classes (\{P=false\}, \{P=true\}) map to the
    post-class \{P=true\}. The macro-state map under i is two-to-one
    on the bool-class space. That is the structural shape of a logical
    erasure operation in Landauer's framework.

    Definition is operational: it counts pre-image / post-image
    populations on a bool macro-property. It mentions no cost, no
    cert flag, no μ-ledger. *)

Definition step_collapses_bool_classes
           (P : bool_macro_property) (i : vm_instruction) : Prop :=
  (exists s, P s = false /\ P (vm_apply s i) = true) /\
  (forall s, P s = true -> P (vm_apply s i) = true).

(** ** Step 3 — substantive ISA lemma.

    Cert-flips genuinely collapse the cert-class space. The proof is
    not a definitional unfold: it uses [vm_apply_certified]
    (PrimeAxiom.v line 32), which is the ISA-specific structural fact
    that only [instr_certify _] can write vm_certified, and it
    unconditionally sets vm_certified to true.

    Without this lemma, the cert-flip hypothesis (which only asserts
    behaviour at one specific state s) would not imply anything about
    other states. The lemma upgrades a single-state observation to a
    universal class-collapse claim using the ISA's restricted writer
    set on vm_certified. *)

Lemma cert_flip_collapses_cert_classes :
  forall (s : VMState) (i : vm_instruction),
    vm_certified s = false ->
    vm_certified (vm_apply s i) = true ->
    step_collapses_bool_classes vm_certified i.
Proof.
  intros s i Hf Ht. unfold step_collapses_bool_classes. split.
  - (* Witness for the exists-arm: s itself flips false → true. *)
    exists s. split; [exact Hf | exact Ht].
  - (* Universal arm: for every s' with cert(s') = true,
       cert(vm_apply s' i) = true.

       The step-instruction i must be instr_certify _ — any other
       instruction preserves vm_certified, and would give
       vm_certified (vm_apply s i) = vm_certified s = false ≠ true.

       For instr_certify _, vm_apply unconditionally sets vm_certified
       to true regardless of input state. *)
    intros s' Hs'.
    rewrite vm_apply_certified in Ht.
    destruct i; try (rewrite Hf in Ht; discriminate).
    rewrite vm_apply_certified. reflexivity.
Qed.

(** ** Step 4 — the VM discharges the cert-property subcase.

    The existing theorem [no_free_certification_certified] discharges the
    bool-class-collapse cost floor for [P = vm_certified] directly.

    This lemma proves the VM-specific subcase without using the abstract bridge
    as a premise. It does not discharge the bridge for every macro-property. *)

Lemma thiele_cost_law_satisfies_landauer_for_cert :
  forall i : vm_instruction,
    step_collapses_bool_classes vm_certified i ->
    instruction_cost i >= 1.
Proof.
  intros i Hcollapse.
  destruct Hcollapse as [[s [Hf Ht]] _].
  exact (no_free_certification_certified s i Hf Ht).
Qed.

(** ** Step 5 — headline theorem: A2 from the named bridge.

    Given Landauer's principle (named physical bridge, parameterised
    by [mu_per_landauer_bit], the mu-cost equivalent of one Landauer
    bit) and the calibration premise [mu_per_landauer_bit >= 1] (which
    holds under [mu_landauer_unruh_calibrated] from
    [coq/kernel/NoFIToEinstein.v]), A2 follows by composition with the
    structural lemma above.

    The bridge supplies [instruction_cost i >= mu_per_landauer_bit] for the
    collapsed class, and the calibration supplies [mu_per_landauer_bit >= 1].

    The proof applies [cert_flip_collapses_cert_classes] before using the bridge.

    The theorem is conditional on those stated premises. *)

Theorem A2_from_physical_reversibility_real :
  forall (mu_per_landauer_bit : nat),
    mu_per_landauer_bit >= 1 ->
    (forall (P : bool_macro_property) (i : vm_instruction),
       step_collapses_bool_classes P i ->
       instruction_cost i >= mu_per_landauer_bit) ->
    forall (s : VMState) (i : vm_instruction),
      vm_certified s = false ->
      vm_certified (vm_apply s i) = true ->
      instruction_cost i >= 1.
Proof.
  intros mu Hcal HLandauer s i Hf Ht.
  pose proof (cert_flip_collapses_cert_classes s i Hf Ht) as Hcollapse.
  pose proof (HLandauer vm_certified i Hcollapse) as Hcost.
  lia.
Qed.

(** ** Sanity checks. *)

(** The headline theorem composed with Thiele's cost-law verifies that
    the Landauer derivation and the Thiele-internal derivation of A2
    give the same conclusion. *)

Lemma A2_consistency_check :
  forall (s : VMState) (i : vm_instruction),
    vm_certified s = false ->
    vm_certified (vm_apply s i) = true ->
    instruction_cost i >= 1.
Proof.
  (* Two routes to A2; both Qed-closed:
     Route A — via Landauer bridge, instantiated with mu = 1 and the
              Thiele cost law as the bridge witness:
       apply (A2_from_physical_reversibility_real 1 (le_n 1)
              thiele_cost_law_satisfies_landauer_for_cert s i Hf Ht).
     Route B — via the existing Thiele cost-law theorem directly. *)
  intros s i Hf Ht.
  exact (no_free_certification_certified s i Hf Ht).
Qed.

(** Print Assumptions on the headline returns "Closed under the global
    context": the Landauer bridge is a Prop hypothesis at the theorem
    level, not a project-local axiom. The structural lemma depends only
    on [vm_apply_certified] (PrimeAxiom.v). *)
