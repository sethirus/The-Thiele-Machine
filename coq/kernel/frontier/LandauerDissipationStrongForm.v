(** * F1_StrongForm: a factored cost implication, with an applicability failure

    The Landauer-style premise below prices every bool-class collapse;
    the calibration bounds that price by the VM instruction-cost schedule.
    Their composition is a valid implication, but the two premises cannot
    hold together for the current ISA. A zero-cost JUMP to PC 1 collapses
    the macro-property PC = 1. The first premise requires positive
    dissipation, while the calibration bounds it by zero.

    [F1_physical_premises_incompatible] makes that obstruction explicit.
    Consequently this file does not provide an applicable physical
    derivation of A2 for the current VM. A2 is already proved directly
    from the instruction semantics in [no_free_certification_certified].

    Repairing the physical model requires choosing a suitable domain of
    operations/properties and a justified cost/dissipation relationship,
    then exhibiting an inhabitant of the resulting premises. No physical
    identification is established by the factored implication alone.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool.

From Kernel Require Import VMState VMStep SimulationProof PrimeAxiom AbstractNoFI.
From Kernel Require Import F1_LogicalErasure MuInitiality.

(** ** Landauer's principle, abstract dissipation form.

    [phys_dissipation_in_landauer_quanta i] is, by intent, the dissipation
    associated with executing instruction [i], measured in multiples of
    [k_B · T · ln 2] (one Landauer quantum). The function is supplied
    externally (by physical measurement, by a thermodynamic model, etc.).
    The kernel does not constrain how it is computed; it appears only as
    a theorem-level parameter.

    Landauer's principle, in dissipation vocabulary: any step that
    collapses bool-class structure on any bool macro-property dissipates
    at least one Landauer quantum. The bridge body mentions class
    collapse and dissipation; not cost. *)

(** ** Named bridge — [cost_dissipation_calibrated].

    The framework-physics interface, packaged as an explicit named bridge
    predicate in the same trust-ledger style as
    [mu_landauer_unruh_calibrated] from [NoFIToEinstein.v]. Operationally:
    each integer μ-unit in [instruction_cost] pays for at most one
    Landauer quantum of dissipation. Equivalently: the framework's cost
    ledger upper-bounds physical dissipation in Landauer quanta.

    The bridge is named so the trust ledger ([README.md] §"Trust-boundary
    scope") can list it alongside [mu_landauer_unruh_calibrated]:
    a falsifiable, externally-supplied calibration whose role and shape
    are explicit. To break it empirically, take any concrete physical
    implementation of the VM and measure dissipation per instruction in
    Landauer quanta; if it ever exceeds the integer [instruction_cost]
    for that instruction, the bridge fails for that implementation. *)

Definition cost_dissipation_calibrated
           (phys_dissipation_in_landauer_quanta : vm_instruction -> nat) : Prop :=
  forall (i : vm_instruction),
    instruction_cost i >= phys_dissipation_in_landauer_quanta i.

(** ** Headline (universal-[P] form).

    Given Landauer's principle in dissipation vocabulary and the
    [cost_dissipation_calibrated] bridge, every class-collapsing step
    has [instruction_cost i >= 1].

    This is a conditional implication only: the
    derivation factors through (i) a substantive physical premise stated
    in physics vocabulary (Landauer's principle, no cost-ledger
    primitive in the bridge body) and (ii) a named, externally-supplied
    calibration playing the unit-conversion role that any formal
    physical theory needs (cf. force ↔ Newtons, entropy ↔ kT). The
    Landauer bridge and calibration are jointly incompatible on the current
    ISA, as proved below; this implication has no physical instance here. *)

Theorem F1_strong_form_universal :
  forall (phys_dissipation_in_landauer_quanta : vm_instruction -> nat),
    (* Landauer's principle, bridge body in dissipation vocabulary:
       class-collapsing step → at least one Landauer quantum dissipated.
       No cost-ledger primitive in this premise. *)
    (forall (P : bool_macro_property) (i : vm_instruction),
        step_collapses_bool_classes P i ->
        phys_dissipation_in_landauer_quanta i >= 1) ->
    (* Named calibration bridge (trust-ledger entry). *)
    cost_dissipation_calibrated phys_dissipation_in_landauer_quanta ->
    (* Conclusion: A2 universal over class-collapsing steps. *)
    forall (P : bool_macro_property) (i : vm_instruction),
      step_collapses_bool_classes P i ->
      instruction_cost i >= 1.
Proof.
  intros phys_diss Hlandauer Hcalib P i Hcollapse.
  pose proof (Hlandauer P i Hcollapse) as Hdiss.
  unfold cost_dissipation_calibrated in Hcalib.
  pose proof (Hcalib i) as Hcal.
  lia.
Qed.

(** ** A2 corollary — cert-flip specialisation.

    Composes the universal-[P] strong-form theorem with the structural
    lemma [cert_flip_collapses_cert_classes] from [F1_LogicalErasure.v]:
    a cert-flip step is one specific class-collapsing step (on the
    [vm_certified] macro-property), so the strong-form bound applies. *)

Corollary A2_via_physical_landauer :
  forall (phys_dissipation_in_landauer_quanta : vm_instruction -> nat),
    (forall (P : bool_macro_property) (i : vm_instruction),
        step_collapses_bool_classes P i ->
        phys_dissipation_in_landauer_quanta i >= 1) ->
    cost_dissipation_calibrated phys_dissipation_in_landauer_quanta ->
    forall (s : VMState) (i : vm_instruction),
      vm_certified s = false ->
      vm_certified (vm_apply s i) = true ->
      instruction_cost i >= 1.
Proof.
  intros phys_diss Hlandauer Hcalib s i Hf Ht.
  pose proof (cert_flip_collapses_cert_classes s i Hf Ht) as Hcollapse.
  exact (F1_strong_form_universal phys_diss Hlandauer Hcalib
                                   vm_certified i Hcollapse).
Qed.

(** Removing a line from a tactic script does not establish logical
    independence of a premise. In particular, A2 for this fixed VM follows
    from its existing cost law without either physical premise.

    More strongly, the full premise pair below is uninhabited. *)

Definition f1_pc_is_one (s : VMState) : bool := Nat.eqb (vm_pc s) 1.

Lemma f1_zero_cost_jump_collapses :
  step_collapses_bool_classes f1_pc_is_one (instr_jump 1 0).
Proof.
  split.
  - exists MuInitiality.init_state. split; reflexivity.
  - intros s _. reflexivity.
Qed.

Theorem F1_physical_premises_incompatible :
  ~ exists dissipation : vm_instruction -> nat,
      (forall P i, step_collapses_bool_classes P i -> dissipation i >= 1) /\
      cost_dissipation_calibrated dissipation.
Proof.
  intros [dissipation [Hlandauer Hcalibration]].
  pose proof (Hlandauer f1_pc_is_one (instr_jump 1 0)
    f1_zero_cost_jump_collapses) as Hpositive.
  pose proof (Hcalibration (instr_jump 1 0)) as Hzero.
  cbn [instruction_cost] in Hzero. lia.
Qed.

(** No project-local axioms are introduced. Closed assumption reports do
    not establish satisfiability of a theorem's explicit hypotheses. *)
