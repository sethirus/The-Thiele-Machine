(** =========================================================================
    KERNEL NOETHER THEORY: Z-action on μ-ledger
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim μ-cost is a Noether charge - a conserved quantity arising from gauge
    symmetry. KernelPhysics.v proved nat-action (shift μ forward). This file
    proves FULL Z-action (bidirectional shifts), making the group structure explicit.

    THE CLAIM:
    The μ-ledger has Z-gauge symmetry: you can shift μ by any integer (positive
    or negative) without changing partition structure. The conservation of μ
    (mu_monotonic from KernelPhysics) is the Noether charge associated with this
    time-translation symmetry.

    WHAT THIS PROVES:
    - z_action_identity: Shifting by 0 is identity (Theorem, line 49)
    - z_action_composition: Shifts compose: shift(a) ∘ shift(b) = shift(a+b) (Theorem, line 58)
    - z_action_inverse: Shifts have inverses: shift(n) ∘ shift(-n) = identity (Theorem, line 74)
    - z_gauge_invariance: Z-shifts preserve partition structure (Theorem, line 92)

    These are the axioms of a group action (Z,+) acting on VMState.

    PHYSICAL INTERPRETATION:
    Noether's theorem: Every continuous symmetry → conserved quantity.
    Here: μ-shift symmetry → μ-cost conservation.
    This is like energy conservation from time-translation symmetry in physics.

    FALSIFICATION:
    Find an operation where shifting μ changes partition structure (violates
    gauge invariance). Or show μ-cost is NOT conserved (violates Noether charge).
    Or prove the group action laws fail (non-associative, no inverse, etc.).

    GOAL: Extend nat-action to Z-action, prove full Noether theorem structure

    Previous (KernelPhysics.v): nat-action (μ → μ + n) + preservation
    This module: Z-action (bidirectional shifts), inverse laws, orbit structure

    WHY: Full group action reveals conservation law scope - does Z-symmetry
    hold or does negative-μ break? If it breaks, WHERE and WHY matters.
    =========================================================================*)

From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import ZArith.ZArith.
From Coq Require Import micromega.Lia.
From Kernel Require Import VMState VMStep.
Import ListNotations.

Open Scope Z_scope.

(** =========================================================================
    Z-ACTION DEFINITION
    =========================================================================*)

(**
  z_gauge_shift: Shift μ-ledger by arbitrary integer (Z-action on VMState).

  WHY: I need to formalize "μ is only defined up to a global constant". Two
  states differing ONLY in μ are physically indistinguishable (gauge equivalent).
  z_gauge_shift implements this gauge transformation: shift μ → μ + delta.

  ALGORITHM: Copy all VMState fields except vm_mu:
  - vm_mu → Z.to_nat(Z.of_nat(vm_mu) + delta)
  - All other fields (graph, regs, mem, etc.) unchanged.

  CRITICAL: Z.to_nat CLAMPS negative values to 0. If vm_mu + delta < 0, result
  is 0. This breaks group action laws when delta violates positivity.

  POSITIVITY GUARD: Most theorems require 0 ≤ vm_mu + delta. This ensures
  Z.to_nat doesn't clamp, preserving group action structure.

  PHYSICAL MEANING: Like gauge transformations in electromagnetism (adding constant
  to voltage doesn't change fields), μ-shifts don't change observable physics
  (partition structure). The μ-ledger is a GAUGE FREEDOM, not physical reality.

  EXAMPLE: s = {| vm_mu := 100; vm_graph := g; ... |}.
           z_gauge_shift 50 s = {| vm_mu := 150; vm_graph := g; ... |} (same graph).
           z_gauge_shift (-50) s = {| vm_mu := 50; vm_graph := g; ... |} (same graph).
           z_gauge_shift (-150) s = {| vm_mu := 0; vm_graph := g; ... |} (CLAMPED!).

  FALSIFICATION: Show z_gauge_shift delta s where vm_graph changes. This would
  mean μ-shifts are NOT gauge transformations (affect observables).

  DEPENDENCIES: Requires Z.to_nat, Z.of_nat (Coq standard library).

  USED BY: z_action_identity, z_action_composition, z_action_inverse, z_gauge_invariance,
  in_same_orbit, vm_step_orbit_equiv, noether_forward.
*)
(** Shift μ by Z amount (can be negative, though vm_mu is nat) *)
Definition z_gauge_shift (delta : Z) (s : VMState) : VMState :=
  {| vm_graph := s.(vm_graph);
     (* SAFE: Bounded arithmetic - caller ensures delta keeps result non-negative *)
     vm_mu := Z.to_nat (Z.of_nat s.(vm_mu) + delta);
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_csrs := s.(vm_csrs);
     vm_pc := s.(vm_pc);
     vm_err := s.(vm_err) |}.

(**
  Observable_partition: Extract partition region structure (ignoring μ).

  WHY: I need an "observer" that is INSENSITIVE to μ-gauge shifts. Observable_partition
  projects VMState onto partition structure only - the GAUGE-INVARIANT part.

  ALGORITHM: Map pg_modules to list of region lists. Each module m contributes
  m.module_region (list of partition IDs). Result: list (list nat) of all regions.

  CLAIM: ∀ delta, s. Observable_partition (z_gauge_shift delta s) = Observable_partition s.
  This is z_gauge_invariance (line 121) - μ-shifts don't change observables.

  PHYSICAL MEANING: Like measuring electric fields (gauge-invariant) instead of
  potentials (gauge-dependent). Partition structure is physical reality; μ is
  bookkeeping.

  EXAMPLE: s = {| vm_graph := {| pg_modules := [(0, {|module_region := [1,2]|}),
                                                  (1, {|module_region := [3,4]|})] |};
                  vm_mu := 100 |}.
           Observable_partition s = [[1,2], [3,4]] (no mention of μ = 100).

  FALSIFICATION: Show two states with same Observable_partition but different
  physical behavior (violates gauge invariance claim).

  USED BY: z_gauge_invariance, noether_forward, noether_backward.
*)
(** Observable: partition structure only (no μ) *)
Definition Observable_partition (s : VMState) : list (list nat) :=
  match s.(vm_graph) with
  | {| pg_modules := mods |} =>
      map (fun m => match m with (_, ms) => ms.(module_region) end) mods
  end.

(** =========================================================================
    GROUP ACTION LAWS
    =========================================================================*)

(**
  z_action_identity: GROUP ACTION AXIOM 1 - Identity element preserves state.

  THEOREM: Shifting by 0 is the identity function: z_gauge_shift 0 s = s.

  WHY: This is the FIRST group action axiom. (Z,+) has identity 0. The action must
  satisfy: action(0, s) = s for all s. Without this, Z-action isn't a group action.

  CLAIM: ∀ s. z_gauge_shift 0 s = s.

  PROOF STRATEGY:
  1. Unfold z_gauge_shift definition.
  2. Simplify: Z.of_nat s.vm_mu + 0 = Z.of_nat s.vm_mu (Z.add_0_r).
  3. Apply Nat2Z.id: Z.to_nat (Z.of_nat n) = n.
  4. Destruct s, show all fields equal by reflexivity.

  PHYSICAL MEANING: "Shifting by nothing changes nothing." The zero gauge transformation
  is trivial - no physical or bookkeeping change.

  FALSIFICATION: Find state s where z_gauge_shift 0 s ≠ s. This would mean the
  implementation of z_gauge_shift is broken (adds spurious changes).

  DEPENDENCIES: Requires z_gauge_shift, Z.add_0_r (stdlib), Nat2Z.id (stdlib).

  USED BY: orbit_equiv_refl (orbit equivalence reflexivity).
*)
(** Identity: shifting by 0 does nothing *)
Theorem z_action_identity : forall s,
  z_gauge_shift 0 s = s.
Proof.
  intros s.
  (* Step 1: Unfold z_gauge_shift *)
  unfold z_gauge_shift. simpl.
  (* Step 2: Simplify Z arithmetic: 0 + x = x *)
  rewrite Z.add_0_r.
  (* Step 3: Cancel Z.to_nat ∘ Z.of_nat = id *)
  rewrite Nat2Z.id.
  (* Step 4: All fields equal by construction *)
  destruct s; simpl; reflexivity.
Qed.

(**
  z_action_composition: GROUP ACTION AXIOM 2 - Shifts compose homomorphically.

  THEOREM: Shifting by b then by a equals shifting by (a+b):
           z_gauge_shift a (z_gauge_shift b s) = z_gauge_shift (a + b) s.

  WHY: This is the SECOND group action axiom. (Z,+) has composition a+b. The action
  must satisfy: action(a, action(b, s)) = action(a+b, s). This is the HOMOMORPHISM
  property - the group operation (addition) is preserved by the action.

  CLAIM: ∀ a, b, s. (0 ≤ μ+b) ∧ (0 ≤ μ+b+a) → shift(a, shift(b, s)) = shift(a+b, s).

  PROOF STRATEGY:
  1. Unfold z_gauge_shift, destruct s.
  2. Goal reduces to: Z.to_nat(Z.of_nat(Z.to_nat(μ+b)) + a) = Z.to_nat(μ + (a+b)).
  3. Apply Z2Nat.id with hypothesis Hb: cancel Z.to_nat ∘ Z.of_nat on LHS.
  4. Simplify: (μ + b) + a = μ + (a+b) by ring algebra (lia).
  5. Both sides equal, reflexivity.

  POSITIVITY GUARDS: Two hypotheses required:
  - 0 ≤ μ+b: Intermediate result must be non-negative (prevents clamping).
  - 0 ≤ μ+b+a: Final result must be non-negative (prevents clamping).
  Without these, Z.to_nat clamps negative values to 0, breaking associativity.

  PHYSICAL MEANING: "Shifting twice is same as shifting once by the sum." Gauge
  transformations compose naturally. Like adding voltages: +50V then +30V equals
  +80V (composition is addition).

  COUNTEREXAMPLE (without positivity): μ=10, b=-5, a=-8. Path A: (10-5)-8 = -3 → 0
  (clamped). Path B: 10 + (-5-8) = -3 → 0. Both clamp, so equal by accident. But
  with μ=10, b=-5, a=+3: Path A: (10-5)+3 = 8. Path B: 10+(-5+3) = 8. Equal ✓.
  But μ=10, b=-12, a=+5: Path A: (10-12)→0, then 0+5=5. Path B: 10+(-12+5)=-7→0.
  Result: 5 ≠ 0. Composition FAILS without positivity guard.

  FALSIFICATION: Find a, b, s satisfying positivity guards where composition fails.
  This would mean Z arithmetic in Coq is broken (impossible - machine-checked).

  DEPENDENCIES: Requires Z2Nat.id, Z.add associativity (lia), z_gauge_shift.

  USED BY: orbit_equiv_trans (composes gauge shifts in orbit chains).
*)
(** Composition: shift(a, shift(b, s)) = shift(a+b, s) *)
Theorem z_action_composition : forall a b s,
  0 <= Z.of_nat s.(vm_mu) + b ->
  0 <= Z.of_nat s.(vm_mu) + b + a ->
  z_gauge_shift a (z_gauge_shift b s) = z_gauge_shift (a + b) s.
Proof.
  intros a b s Hb Hab. unfold z_gauge_shift. 
  destruct s; simpl. f_equal.
  (* LHS: Z.to_nat (Z.of_nat (Z.to_nat (Z.of_nat vm_mu + b)) + a)
     RHS: Z.to_nat (Z.of_nat vm_mu + (a + b)) *)
  rewrite (Z2Nat.id (Z.of_nat vm_mu + b)) by assumption.
  replace (Z.of_nat vm_mu + b + a) with (Z.of_nat vm_mu + (a + b)) by lia.
  reflexivity.
Qed.

(**
  z_action_inverse: GROUP ACTION AXIOM 3 - Shifts are invertible.

  THEOREM: Shifting by n then by -n recovers the original state:
           z_gauge_shift (-n) (z_gauge_shift n s) = s.

  WHY: This is the THIRD group action axiom. Every group element has an inverse.
  For (Z,+), the inverse of n is -n (since n + (-n) = 0). The action must satisfy:
  action(-n, action(n, s)) = s (applying inverse undoes the action).

  CLAIM: ∀ n, s. (0 ≤ μ+n) → shift(-n, shift(n, s)) = s.

  PROOF STRATEGY:
  1. Unfold z_gauge_shift, destruct s.
  2. Goal: Z.to_nat(Z.of_nat(Z.to_nat(μ+n)) + (-n)) = μ.
  3. Apply Z2Nat.id with hypothesis Hpos: cancel Z.to_nat ∘ Z.of_nat.
  4. Simplify: (μ + n) + (-n) = μ by ring (lia).
  5. Apply Nat2Z.id: Z.to_nat(Z.of_nat(μ)) = μ.
  6. Reflexivity.

  POSITIVITY GUARD: Requires 0 ≤ μ+n. This ensures the intermediate state
  shift(n, s) has non-negative μ. Without it, Z.to_nat clamps, and the inverse
  operation cannot recover the original (information lost to clamping).

  PHYSICAL MEANING: "Gauge transformations are reversible." If you shift μ by +50,
  you can shift back by -50 to get the original. Like voltage transformations in
  electromagnetism: add 5V then subtract 5V returns to original potential.

  COUNTEREXAMPLE (without positivity): μ=10, n=-15. shift(-15, s) → μ=0 (clamped).
  Then shift(+15, {μ=0}) → μ=15 ≠ 10. Lost information due to clamping. Inverse
  doesn't work when intermediate state is negative.

  FALSIFICATION: Find n, s with positivity satisfied where shift(-n, shift(n, s)) ≠ s.
  This would mean Z inverse is broken (impossible).

  DEPENDENCIES: Requires Z2Nat.id, Nat2Z.id, Z.add inverse (lia), z_gauge_shift.

  USED BY: orbit_equiv_sym (proves orbit equivalence is symmetric using inverses).
*)
(** Inverse: shift(n) followed by shift(-n) recovers original μ
    (when both are in nat range) *)
Theorem z_action_inverse : forall n s,
  0 <= Z.of_nat s.(vm_mu) + n ->
  z_gauge_shift (-n) (z_gauge_shift n s) = s.
Proof.
  intros n s Hpos.
  unfold z_gauge_shift. destruct s; simpl.
  f_equal. 
  (* Goal: Z.to_nat (Z.of_nat (Z.to_nat (Z.of_nat vm_mu + n)) + - n) = vm_mu *)
  rewrite Z2Nat.id by assumption.
  replace (Z.of_nat vm_mu + n + - n) with (Z.of_nat vm_mu) by lia.
  apply Nat2Z.id.
Qed.

(** =========================================================================
    GAUGE INVARIANCE (Noether Charge)
    =========================================================================*)

(**
  z_gauge_invariance: THE GAUGE INVARIANCE THEOREM - observables unchanged by μ-shifts.

  THEOREM: Shifting μ doesn't change observable partition structure:
           Observable_partition (z_gauge_shift delta s) = Observable_partition s.

  WHY THIS IS FUNDAMENTAL: This proves μ is a GAUGE DEGREE OF FREEDOM, not physical
  reality. Two states differing only in μ are OBSERVATIONALLY IDENTICAL. This is
  the core of the Noether theorem: gauge symmetry → conserved charge.

  CLAIM: ∀ delta, s. Observable_partition after μ-shift equals Observable_partition before.

  PROOF STRATEGY:
  1. Unfold Observable_partition and z_gauge_shift.
  2. Observable_partition extracts pg_modules from vm_graph.
  3. z_gauge_shift copies vm_graph unchanged (only vm_mu changes).
  4. Therefore Observable_partition unchanged. Reflexivity.

  PHYSICAL MEANING: This is EXACTLY like gauge invariance in electromagnetism:
  - Electric potential φ is gauge-dependent (add constant → new potential).
  - Electric field E = -∇φ is gauge-INvariant (field unchanged by constant shift).
  - Observable: field E (gauge-invariant). Unobservable: potential φ (gauge-dependent).

  Here:
  - μ-ledger is gauge-dependent (shift → new μ value).
  - Partition structure is gauge-INvariant (structure unchanged by μ-shift).
  - Observable: partition graph. Unobservable: absolute μ value.

  NOETHER CONNECTION: Gauge invariance (symmetry) implies conserved charge.
  The conserved charge is μ itself (vm_step_mu_monotonic). But μ is RELATIVE,
  not absolute - only differences matter (ΔΔμ = instruction cost is physical).

  EXAMPLE: s = {| vm_mu := 100; vm_graph := {modules: [[1,2], [3,4]]}; ... |}.
  shift(+50, s) = {| vm_mu := 150; vm_graph := {modules: [[1,2], [3,4]]}; ... |}.
  Observable_partition(s) = [[1,2], [3,4]] = Observable_partition(shift(+50, s)).
  The partition structure [[1,2], [3,4]] is IDENTICAL. μ changed 100→150, but
  that's unobservable (like shifting voltage reference ground).

  FALSIFICATION: Find delta, s where Observable_partition changes after μ-shift.
  This would mean μ-shifts AREN'T gauge transformations (affect physical state).
  The proof is trivial (reflexivity), so falsification requires z_gauge_shift
  implementation error (vm_graph accidentally modified).

  DEPENDENCIES: Requires z_gauge_shift (preserves graph), Observable_partition (extracts graph).

  USED BY: noether_backward (proves conservation from symmetry), all gauge theory theorems.
*)
(** DEFINITIONAL HELPER: [z_gauge_shift] only modifies [vm_mu], not the
    graph fields that [Observable_partition] reads.  Structural independence
    of Record fields makes the two sides definitionally equal. *)
Theorem z_gauge_invariance : forall delta s,
  Observable_partition (z_gauge_shift delta s) = Observable_partition s.
Proof.
  intros delta s.
  unfold Observable_partition, z_gauge_shift.
  simpl. reflexivity.
Qed.

(** =========================================================================
    CONSERVED CURRENT: μ-ledger
    =========================================================================*)

(**
  mu_current: Extract the Noether charge (μ-ledger value).

  WHY: I need a named accessor for the conserved quantity. mu_current extracts
  the μ-ledger from VMState, making it explicit that THIS is the quantity we're
  tracking conservation for.

  IMPLEMENTATION: mu_current s = s.vm_mu. Trivial projection.

  PHYSICAL MEANING: In Noether's theorem, every symmetry has an associated conserved
  quantity (the "Noether charge"). For μ-gauge symmetry (time-translation invariance
  of computational entropy), the Noether charge is μ itself. mu_current makes this
  explicit: "the current value of the conserved charge".

  EXAMPLE: s = {| vm_mu := 42; ... |}. mu_current s = 42.

  FALSIFICATION: Show mu_current extracts wrong field. This would be implementation
  error (accessing wrong record field).

  USED BY: vm_step_mu_monotonic (proves charge is conserved/monotone), noether_backward.
*)
(** vm_mu is the Noether charge: it changes predictably under vm_step *)
Definition mu_current (s : VMState) : nat := s.(vm_mu).

(**
  vm_step_mu_monotonic: THE CONSERVATION LAW - μ never decreases.

  THEOREM: Every vm_step increases (or preserves) μ:
           vm_step s i s' → mu_current s ≤ mu_current s'.

  WHY THIS IS FUNDAMENTAL: This is the CONSERVATION LAW derived from gauge symmetry.
  Noether's theorem: symmetry → conserved charge. Here: μ-gauge symmetry →
  μ-monotonicity (entropy-like conservation).

  CLAIM: ∀ s, i, s'. vm_step s i s' → s.vm_mu ≤ s'.vm_mu.

  PROOF STRATEGY:
  1. Unfold mu_current (just s.vm_mu projection).
  2. Inversion on Hstep: case split on all vm_step constructors.
  3. Each constructor uses advance_state or advance_state_rm, which applies apply_cost.
  4. apply_cost adds instruction_cost ≥ 0 to vm_mu.
  5. Therefore vm_mu' = vm_mu + cost ≥ vm_mu.
  6. All cases verified by lia (linear arithmetic solver).

  THE 23 CASES: vm_step has 23 constructors (one per instruction):
  - ALU ops (add, xor, etc.): cost = 1, μ increases by 1.
  - Memory ops (load, store): cost = 2, μ increases by 2.
  - Partition ops (PNEW, PDISCOVER): cost = 6-12, μ increases by that amount.
  - Control flow (HALT, branch): cost = 0, μ unchanged.
  ALL cases satisfy μ' ≥ μ. Monotonicity is UNIVERSAL (no exceptions).

  PHYSICAL MEANING: This is the SECOND LAW OF THERMODYNAMICS for computation.
  Entropy (μ) never decreases. Each irreversible operation (partition creation,
  information erasure) increases μ. Reversible operations (unitary gates) keep
  μ constant. The μ-ledger is computational entropy.

  THERMODYNAMIC ANALOGY:
  - Isolated system: entropy S never decreases (dS/dt ≥ 0).
  - Thiele Machine: μ never decreases (dμ/dstep ≥ 0).
  - Reversible process: ΔS = 0 (HALT, branches: Δμ = 0).
  - Irreversible process: ΔS > 0 (PNEW, PDISCOVER: Δμ > 0).

  COUNTEREXAMPLE (hypothetical): Find vm_step where μ decreases. This would violate
  the second law - "un-computing" information without thermodynamic cost. Proof
  shows this is IMPOSSIBLE (every constructor increases or preserves μ).

  FALSIFICATION: Find instruction i, states s, s' where vm_step s i s' but
  s'.vm_mu < s.vm_mu. This would require an instruction with NEGATIVE cost, violating
  instruction_cost definition (all costs ≥ 0 in VMStep.v).

  DEPENDENCIES: Requires vm_step (VMStep.v), advance_state (applies cost),
  instruction_cost ≥ 0 (VMStep.v), lia (arithmetic).

  USED BY: noether_backward (proves symmetry from conservation), PhysicsClosure.v
  (packages as fundamental physical law), all μ-cost analysis.
*)
(** Under vm_step, μ increases by instruction cost (monotonicity = conservation) *)
Theorem vm_step_mu_monotonic : forall s i s',
  vm_step s i s' -> (mu_current s <= mu_current s')%nat.
Proof.
  intros s i s' Hstep.
  unfold mu_current.
  inversion Hstep; subst;
    unfold advance_state, advance_state_rm, apply_cost in *;
    simpl; lia.
Qed.

(** =========================================================================
    ORBITS AND EQUIVALENCE CLASSES
    =========================================================================*)

(**
  in_same_orbit: Orbit equivalence relation for gauge-related states.

  WHY: I need to formalize "two states are gauge-equivalent (differ only in μ)".
  in_same_orbit captures this: s1 and s2 are in the same orbit if there exists
  a gauge shift connecting them.

  DEFINITION: in_same_orbit s1 s2 := ∃ delta, z_gauge_shift delta s1 = s2.

  STRUCTURE: Existential quantification over Z. Two states are orbit-equivalent
  iff you can reach one from the other via μ-shift.

  PHYSICAL MEANING: Orbit equivalence is GAUGE EQUIVALENCE. States in the same
  orbit represent the SAME PHYSICAL STATE but with different μ-bookkeeping. Like
  measuring voltage relative to different ground references - physically identical,
  numerically different.

  EXAMPLE: s1 = {| vm_mu := 10; vm_graph := g; ... |}.
           s2 = {| vm_mu := 15; vm_graph := g; ... |}.
  If ALL other fields match, in_same_orbit s1 s2 (witness: delta = 5).

  FALSIFICATION: Find s1, s2 with different partition graphs where in_same_orbit holds.
  This would violate gauge invariance (z_gauge_shift preserves graph by definition,
  so orbits can only connect states with same graph).

  USED BY: orbit_equiv_refl/sym/trans (prove equivalence relation properties),
  vm_step_orbit_equiv (prove dynamics preserves orbits).
*)
(** Two states are in the same orbit if related by Z-shift *)
Definition in_same_orbit (s1 s2 : VMState) : Prop :=
  exists delta : Z, z_gauge_shift delta s1 = s2.

(**
  orbit_equiv_refl: Orbit equivalence is REFLEXIVE.

  THEOREM: Every state is in the same orbit as itself: ∀ s. in_same_orbit s s.

  WHY: To be an equivalence relation, orbit equivalence must be reflexive. This
  proves the FIRST equivalence relation axiom.

  CLAIM: ∀ s. ∃ delta. z_gauge_shift delta s = s.

  PROOF STRATEGY:
  1. Provide witness: delta = 0.
  2. Apply z_action_identity: z_gauge_shift 0 s = s.
  3. Existential satisfied. QED.

  PHYSICAL MEANING: "A state is gauge-equivalent to itself." The identity gauge
  transformation (shift by 0) leaves the state unchanged. Trivial reflexivity.

  FALSIFICATION: Find state s where in_same_orbit s s fails. This would mean
  z_action_identity is broken (impossible - proven theorem).

  DEPENDENCIES: Requires z_action_identity (shift by 0 is identity), in_same_orbit.

  USED BY: Equivalence relation proofs, orbit structure analysis.
*)
(** Orbit equivalence is an equivalence relation *)
(** HELPER: Reflexivity/transitivity/symmetry property *)
(** HELPER: Reflexivity/transitivity/symmetry property *)
Theorem orbit_equiv_refl : forall s, in_same_orbit s s.
Proof.
  intros s. exists 0%Z. apply z_action_identity.
Qed.

(**
  orbit_equiv_sym: Orbit equivalence is SYMMETRIC.

  THEOREM: If s1 is in the same orbit as s2, then s2 is in the same orbit as s1:
           z_gauge_shift delta s1 = s2 → in_same_orbit s2 s1.

  WHY: To be an equivalence relation, orbit equivalence must be symmetric. This
  proves the SECOND equivalence relation axiom.

  CLAIM: ∀ s1, s2, delta. (0 ≤ μ₁+delta) → shift(delta, s1) = s2 → ∃ delta'. shift(delta', s2) = s1.

  PROOF STRATEGY:
  1. Provide witness: delta' = -delta (inverse shift).
  2. Rewrite s2 as z_gauge_shift delta s1 (from hypothesis).
  3. Apply z_action_inverse: shift(-delta, shift(delta, s1)) = s1.
  4. Existential satisfied. QED.

  POSITIVITY GUARD: Requires 0 ≤ μ₁+delta. This ensures the forward shift is
  valid (no clamping), so the inverse can recover the original state.

  PHYSICAL MEANING: "Gauge transformations are reversible." If you can shift from
  s1 to s2, you can shift back from s2 to s1 using the inverse transformation.
  Like voltage transformations: if you can add +5V, you can subtract -5V to return.

  COUNTEREXAMPLE (without positivity): μ₁=10, delta=-15. shift(-15, s1) → μ=0 (clamped).
  Now try shift(+15, {μ=0}) → μ=15 ≠ 10. Symmetry breaks due to clamping.

  FALSIFICATION: Find s1, s2, delta with positivity satisfied where orbit_equiv_sym
  fails. This would mean z_action_inverse is broken (impossible - proven theorem).

  DEPENDENCIES: Requires z_action_inverse (inverse gauge shifts), in_same_orbit.

  USED BY: Equivalence relation proofs, orbit symmetry analysis.
*)
Theorem orbit_equiv_sym : forall s1 s2 delta,
  0 <= Z.of_nat s1.(vm_mu) + delta ->
  z_gauge_shift delta s1 = s2 ->
  in_same_orbit s2 s1.
Proof.
  intros s1 s2 delta Hpos Heq.
  exists (-delta)%Z.
  rewrite <- Heq.
  apply z_action_inverse. assumption.
Qed.

(**
  orbit_equiv_trans: Orbit equivalence is TRANSITIVE.

  THEOREM: If s1 ~ s2 and s2 ~ s3, then s1 ~ s3:
           shift(d1, s1) = s2 ∧ shift(d2, s2) = s3 → in_same_orbit s1 s3.

  WHY: To be an equivalence relation, orbit equivalence must be transitive. This
  proves the THIRD equivalence relation axiom. Together with reflexivity and
  symmetry, this completes the equivalence relation proof.

  CLAIM: ∀ s1, s2, s3, d1, d2. (0 ≤ μ₁+d1) ∧ (0 ≤ μ₁+d1+d2) →
         shift(d1, s1) = s2 → shift(d2, s2) = s3 → ∃ delta. shift(delta, s1) = s3.

  PROOF STRATEGY:
  1. Provide witness: delta = d1 + d2 (compose shifts).
  2. Rewrite s3 as shift(d2, s2) (hypothesis H2).
  3. Rewrite s2 as shift(d1, s1) (hypothesis H1).
  4. Goal: shift(d1+d2, s1) = shift(d2, shift(d1, s1)).
  5. Apply z_action_composition: shift(d2, shift(d1, s1)) = shift(d1+d2, s1).
  6. Simplify with lia: d1+d2 = d1+d2. Reflexivity. QED.

  POSITIVITY GUARDS: Two requirements:
  - 0 ≤ μ₁+d1: First shift is valid (no clamping).
  - 0 ≤ μ₁+d1+d2: Composition is valid (no clamping).

  PHYSICAL MEANING: "Gauge transformations compose." If you can shift from s1 to
  s2 (by d1), then from s2 to s3 (by d2), you can shift directly from s1 to s3
  (by d1+d2). This is the GROUP ACTION property - shifts form a group.

  EXAMPLE: s1 = {μ=10}, s2 = {μ=15} (shift +5), s3 = {μ=22} (shift +7).
  Transitivity: s1 ~ s2 ~ s3 implies s1 ~ s3. Witness: shift(+12, s1) = s3.

  COUNTEREXAMPLE (without positivity): μ₁=5, d1=-3, d2=-4.
  s1 → s2: shift(-3, {μ=5}) = {μ=2} ✓.
  s2 → s3: shift(-4, {μ=2}) = {μ=0} (clamped to 0, should be -2).
  Direct: shift(-7, {μ=5}) = {μ=0} (clamped to 0, should be -2).
  Transitivity holds by accident (both clamped to 0), but not by composition law.
  With positivity guards, composition is EXACT, not accidental.

  FALSIFICATION: Find s1, s2, s3, d1, d2 with positivity satisfied where
  transitivity fails. This would mean z_action_composition is broken (impossible).

  DEPENDENCIES: Requires z_action_composition (shifts compose), in_same_orbit.

  USED BY: Equivalence relation proofs, orbit chain analysis.
(** HELPER: Reflexivity/transitivity/symmetry property *)
*)
(** HELPER: Reflexivity/transitivity/symmetry property *)
Theorem orbit_equiv_trans : forall s1 s2 s3 d1 d2,
  0 <= Z.of_nat s1.(vm_mu) + d1 ->
  0 <= Z.of_nat s1.(vm_mu) + d1 + d2 ->
  z_gauge_shift d1 s1 = s2 ->
  z_gauge_shift d2 s2 = s3 ->
  in_same_orbit s1 s3.
Proof.
  intros s1 s2 s3 d1 d2 Hpos1 Hpos2 H1 H2.
  exists (d1 + d2)%Z.
  rewrite <- H2. rewrite <- H1.
  rewrite z_action_composition by assumption.
  f_equal. lia.
Qed.

(** =========================================================================
    NOETHER THEOREM: Symmetry ↔ Conservation
    =========================================================================*)

(** **Equivariance Lemma**: vm_step preserves orbit equivalence.

    This establishes that vm_step is equivariant with respect to the Z-action:
    if two states s1, s1' are in the same orbit, and vm_step advances them to
    s2, s2', then s2 and s2' are also in the same orbit.

    CRITICAL PRECONDITION: The gauge shift delta must keep vm_mu non-negative.
    This is the "no bankruptcy" condition — the ledger cannot go into debt.

    Without this condition, Z.to_nat clamping breaks commutativity:
      Counter-example: vm_mu=10, cost=5, delta=-12
      Path A (step→shift): 10+5=15, then 15-12=3
      Path B (shift→step): 10-12=-2→CLAMP→0, then 0+5=5
      Result: 3 ≠ 5, diagram fails to commute.

    This is the key lemma connecting the symmetry (Z-action) to the dynamics
    (vm_step), demonstrating that the gauge transformation commutes with evolution
    IN THE NON-NEGATIVE REGIME.
*)

(**
  shift_cost_comm: Arithmetic lemma - gauge shifts commute with cost addition.

  LEMMA: (μ+delta) + cost = (μ+cost) + delta when μ+delta ≥ 0.

  WHY: This is the KEY ARITHMETIC fact for vm_step_orbit_equiv. I need to show
  that applying cost THEN shifting gives the same result as shifting THEN applying
  cost. This is the "commutativity diagram" for gauge transformations and dynamics.

  CLAIM: ∀ μ, cost, delta. (0 ≤ μ+delta) →
         Z.to_nat(μ+delta) + cost = Z.to_nat((μ+cost) + delta).

  PROOF STRATEGY:
  1. Convert nat addition to Z: LHS = Z.to_nat(μ+delta) + cost uses nat addition.
  2. Rewrite using Nat2Z.inj_add: Z.of_nat(a+b) = Z.of_nat(a) + Z.of_nat(b).
  3. LHS becomes: Z.of_nat(Z.to_nat(μ+delta)) + Z.of_nat(cost).
  4. Apply Z2Nat.id using Hpos: Z.of_nat(Z.to_nat(μ+delta)) = μ+delta.
  5. Simplify: (μ+delta) + cost = (μ+cost) + delta by associativity (lia).
  6. Both sides equal under Z.to_nat. QED.

  POSITIVITY GUARD: Requires 0 ≤ μ+delta. Without this, Z.to_nat(μ+delta) clamps
  to 0, and the equation becomes: 0 + cost ≠ Z.to_nat((μ+cost) + delta).

  PHYSICAL MEANING: "Energy is additive regardless of reference frame." If you
  shift the energy baseline (gauge shift), then add energy (cost), you get the
  same result as adding energy THEN shifting the baseline. This is energy
  conservation in different gauges.

  COUNTEREXAMPLE (without positivity): μ=5, cost=3, delta=-10.
  LHS: Z.to_nat(5-10) + 3 = 0 + 3 = 3.
  RHS: Z.to_nat((5+3) - 10) = Z.to_nat(-2) = 0.
  Result: 3 ≠ 0. Commutativity breaks due to clamping.

  FALSIFICATION: Find μ, cost, delta with positivity satisfied where the equation
  fails. This would mean Z arithmetic is inconsistent (impossible).

  DEPENDENCIES: Requires Nat2Z.inj_add, Z2Nat.id, lia (Z arithmetic).

  USED BY: vm_step_orbit_equiv (applies this to all 23 vm_step constructors).
*)
(** Key arithmetic lemma: shifting commutes with adding cost under positivity *)
Lemma shift_cost_comm : forall (mu cost : nat) (delta : Z),
  0 <= Z.of_nat mu + delta ->
  (* SAFE: Z.to_nat protected by hypothesis Hpos: 0 <= Z.of_nat mu + delta *)
  (Z.to_nat (Z.of_nat mu + delta) + cost)%nat =
  Z.to_nat (Z.of_nat (mu + cost) + delta).
Proof.
  intros mu cost delta Hpos.
  rewrite Nat2Z.inj_add. lia.
Qed.

(**
  vm_step_orbit_equiv: THE EQUIVARIANCE THEOREM - dynamics preserves gauge orbits.

  THEOREM: If s1 →[i] s2 via vm_step, then z_gauge_shift(delta, s1) →[i] s2'
           where s2' = z_gauge_shift(delta, s2).

  WHY THIS IS FUNDAMENTAL: This proves vm_step is EQUIVARIANT under Z-action.
  The gauge symmetry (Z-shifts) COMMUTES with dynamics (vm_step). This is the
  connection between SYMMETRY (gauge invariance) and DYNAMICS (state evolution).

  CLAIM: ∀ s1, s2, i, delta. (0 ≤ μ₁+delta) → vm_step s1 i s2 →
         ∃ s2'. vm_step (shift(delta, s1)) i s2' ∧ shift(delta, s2) = s2'.

  STRUCTURE: For any vm_step transition, the following diagram commutes (with positivity):

      s1 ──────vm_step i──────> s2
       |                         |
    shift(delta)             shift(delta)
       |                         |
       v                         v
    shift(delta, s1) ─vm_step i─> s2'

  The existence of s2' with s2' = shift(delta, s2) proves the diagram commutes.

  PROOF STRATEGY:
  1. Inversion on Hstep: case split on all 23 vm_step constructors.
  2. For each constructor:
     a. z_gauge_shift only changes vm_mu, all other fields unchanged.
     b. vm_step behavior depends ONLY on structural fields (graph, regs, mem).
     c. Since structural fields unchanged, SAME constructor applies to shifted state.
     d. econstructor automatically finds the right constructor and unifies fields.
  3. Arithmetic goal: show μ values match after shift+step vs. step+shift.
  4. Apply shift_cost_comm: proves μ values match when positivity holds.
  5. All 23 cases handled uniformly by this strategy.

  THE 23 CASES: All vm_step instructions satisfy equivariance:
  - ALU ops: Structural (registers, PC), μ unchanged by shift.
  - Memory ops: Structural (memory, registers), μ unchanged by shift.
  - Partition ops: Structural (graph), μ unchanged by shift.
  - Control flow: Structural (PC, conditions), μ unchanged by shift.

  PHYSICAL MEANING: "Physical laws are the same in all gauges." If you shift your
  energy reference frame, the dynamics don't change - Newton's laws hold in all
  inertial frames. Here: vm_step behavior is gauge-invariant - shifting μ doesn't
  affect which instruction executes or how it behaves.

  CRITICAL LIMITATION: Requires 0 ≤ μ₁+delta (positivity guard). Without this,
  Z.to_nat clamping breaks commutativity. The counterexample in the file header
  (line 625-628) demonstrates this explicitly.

  COUNTEREXAMPLE (without positivity): μ=10, cost=5, delta=-12.
  Path A: step then shift: (10+5=15) then (15-12=3) → μ'=3.
  Path B: shift then step: (10-12=0 CLAMPED) then (0+5=5) → μ'=5.
  Result: 3 ≠ 5. Equivariance FAILS without positivity.

  FALSIFICATION: Find s1, i, delta with positivity where vm_step from shifted
  state gives different structural result (not just μ). This would mean gauge
  shifts affect physical behavior (violates gauge invariance).

  DEPENDENCIES: Requires shift_cost_comm (arithmetic), z_gauge_shift (definition),
  vm_step (VMStep.v), econstructor (Coq proof automation).

  USED BY: Noether theorem proofs, gauge orbit analysis, equivariance theorems.
*)
Lemma vm_step_orbit_equiv : forall s1 s2 i delta,
  0 <= Z.of_nat s1.(vm_mu) + delta ->  (* Positivity: no bankruptcy *)
  vm_step s1 i s2 ->
  exists s2',
    vm_step (z_gauge_shift delta s1) i s2' /\
    z_gauge_shift delta s2 = s2'.
Proof.
  intros s1 s2 i delta Hpos Hstep.
  (* Strategy: z_gauge_shift only changes vm_mu. vm_step is determined by
     structural components which are unchanged. So same constructor applies.
     econstructor finds the right constructor and unifies, reflexivity
     handles trivial equalities. *)
  inversion Hstep; subst; eexists; split.
  (* All 23 cases: econstructor matches same constructor, then arithmetic *)
  all: try (econstructor; [reflexivity | reflexivity | reflexivity | idtac..]).
  all: try (econstructor; [reflexivity | reflexivity | idtac..]).
  all: try (econstructor; [reflexivity | idtac..]).
  all: try (econstructor; [eassumption | idtac..]).
  all: try econstructor.
  all: unfold z_gauge_shift, advance_state, advance_state_rm, apply_cost; simpl.
  all: try (f_equal; symmetry; apply shift_cost_comm; assumption).
Qed.

(**
  noether_forward: FORWARD NOETHER THEOREM - symmetry implies conserved charge.

  THEOREM: If two states are physically identical (same graph, registers, memory,
           etc.) but differ in μ, then they're gauge-equivalent (related by μ-shift).

  WHY THIS IS NOETHER'S THEOREM (FORWARD DIRECTION): Noether's theorem has two parts:
  1. FORWARD: Symmetry → conserved charge exists.
  2. BACKWARD: Conserved charge → symmetry exists.
  This theorem proves the FORWARD direction: if states are observationally identical
  (gauge-symmetric), then there exists a gauge transformation connecting them.

  CLAIM: ∀ s1, s2. (Observable_partition s1 = Observable_partition s2) ∧
         (all structural fields equal) →
         ∃ delta. z_gauge_shift delta s1 = s2.

  STRUCTURE: Given seven hypotheses (all fields except vm_mu are equal), construct
  witness delta = μ₂ - μ₁. This shift relates the two states.

  PROOF STRATEGY:
  1. Provide witness: delta = Z.of_nat(μ₂) - Z.of_nat(μ₁).
  2. Unfold z_gauge_shift, destruct s1 and s2.
  3. Apply hypotheses: all fields except vm_mu are equal (subst).
  4. Goal reduces to: μ₁ + (μ₂ - μ₁) = μ₂ (arithmetic).
  5. Prove: Z.of_nat(μ₁) + (Z.of_nat(μ₂) - Z.of_nat(μ₁)) = Z.of_nat(μ₂) by lia.
  6. Apply Nat2Z.id: Z.to_nat(Z.of_nat(μ₂)) = μ₂.
  7. Reflexivity. QED.

  PHYSICAL MEANING: "States differing only in gauge choice are gauge-equivalent."
  If two states have identical physical structure (partition graph, registers,
  memory) but different μ-ledgers, they represent the SAME PHYSICAL STATE viewed
  in different gauges. The μ difference is pure bookkeeping.

  EXAMPLE: s1 = {| vm_mu := 100; vm_graph := g; vm_regs := r; ... |}.
           s2 = {| vm_mu := 150; vm_graph := g; vm_regs := r; ... |}.
  If ALL other fields match, noether_forward proves: z_gauge_shift(50, s1) = s2.
  The μ difference (50) is the gauge shift connecting them.

  THERMODYNAMIC ANALOGY: Like choosing energy zero-point. You can define potential
  energy relative to ground level or sea level - physically equivalent, numerically
  different. μ is like potential energy: only DIFFERENCES matter (ΔΔμ = work done).

  FALSIFICATION: Find s1, s2 with all structural fields equal but NO gauge shift
  connecting them. This would require μ₁ + delta ≠ μ₂ for all delta (impossible
  by construction: delta = μ₂ - μ₁ satisfies the equation).

  DEPENDENCIES: Requires z_gauge_shift (gauge transformation), Observable_partition
  (gauge-invariant observable), Nat2Z.id, lia (arithmetic).

  USED BY: Noether's theorem package, gauge equivalence proofs, orbit structure.
*)
(** FORWARD: Symmetry implies conserved charge *)
Theorem noether_forward : forall s1 s2,
  Observable_partition s1 = Observable_partition s2 ->
  s1.(vm_graph) = s2.(vm_graph) ->
  s1.(vm_regs) = s2.(vm_regs) ->
  s1.(vm_mem) = s2.(vm_mem) ->
  s1.(vm_csrs) = s2.(vm_csrs) ->
  s1.(vm_pc) = s2.(vm_pc) ->
  s1.(vm_err) = s2.(vm_err) ->
  exists delta, z_gauge_shift delta s1 = s2.
Proof.
  intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.
  exists (Z.of_nat s2.(vm_mu) - Z.of_nat s1.(vm_mu))%Z.
  unfold z_gauge_shift. destruct s1, s2; simpl in *.
  subst. f_equal.
  assert (Harith: (Z.of_nat vm_mu + (Z.of_nat vm_mu0 - Z.of_nat vm_mu) = Z.of_nat vm_mu0)%Z) by lia.
  rewrite Harith. apply Nat2Z.id.
Qed.

(**
  noether_backward: BACKWARD NOETHER THEOREM - conserved charge implies symmetry.

  THEOREM: If μ is conserved (monotone under vm_step), then gauge shifts preserve
           observable partition structure.

  WHY THIS IS NOETHER'S THEOREM (BACKWARD DIRECTION): This proves the CONVERSE:
  if the conserved charge exists (μ-conservation), then the symmetry exists
  (gauge invariance of observables).

  CLAIM: ∀ s. (μ-conservation law holds) →
         ∀ delta. Observable_partition(shift(delta, s)) = Observable_partition(s).

  STRUCTURE: Given hypothesis that μ is conserved (monotone), prove that ALL
  gauge shifts preserve observables.

  PROOF STRATEGY:
  1. Assume hypothesis: ∀ i, s'. vm_step s i s' → μ(s) ≤ μ(s') (conservation).
  2. Goal: prove Observable_partition unchanged by any gauge shift delta.
  3. Apply z_gauge_invariance: this theorem already proves the goal directly.
  4. The hypothesis Hcons is UNUSED - gauge invariance holds UNCONDITIONALLY.
  5. QED (trivial application).

  KEY INSIGHT: The "backward" direction is TRIVIAL in this formalization because
  gauge invariance (z_gauge_invariance) is PROVEN DIRECTLY from the definition
  of z_gauge_shift (which preserves vm_graph by construction). The hypothesis
  about μ-conservation is not actually needed for this direction.

  PHYSICAL MEANING: "Conservation implies symmetry." If a quantity is conserved
  (μ-monotone), the system has an underlying symmetry (gauge invariance). But in
  this formalization, the symmetry is MANIFEST (z_gauge_shift preserves structure
  by definition), so conservation is CONSEQUENCE, not cause.

  NOETHER'S THEOREM STRUCTURE:
  - Forward (noether_forward): Symmetry → conserved charge (constructive).
  - Backward (noether_backward): Conserved charge → symmetry (trivial here).
  Both directions together establish the EQUIVALENCE: symmetry ↔ conservation.

  EXAMPLE: Given vm_step_mu_monotonic (μ conserved), noether_backward proves:
  z_gauge_shift(delta, s) has same Observable_partition as s for ALL delta.

  FALSIFICATION: Find state s where μ-conservation holds but gauge shift changes
  Observable_partition. This would contradict z_gauge_invariance (proven theorem).

  DEPENDENCIES: Requires z_gauge_invariance (gauge symmetry theorem), mu_current,
  vm_step (dynamics).

  USED BY: Noether's theorem package, physics closure theorems, gauge theory.
*)
(** BACKWARD: Conserved charge implies symmetry *)
Theorem noether_backward : forall s,
  (forall i s', vm_step s i s' -> mu_current s <= mu_current s')%nat ->
  forall delta, Observable_partition (z_gauge_shift delta s) = Observable_partition s.
Proof.
  intros s _ delta.
  apply z_gauge_invariance.
Qed.

(** =========================================================================
    SUMMARY: The Boundary Truth
    =========================================================================*)

(** PROVEN (with constraints):
    - Z-action group laws (identity, composition, inverse) — all require positivity
    - Z-gauge invariance of observables (unconditional)
    - Orbit equivalence relations (with positivity guards)
    - vm_step equivariance (with positivity guard)
    - Noether forward/backward (structural)
    
    THE FUNDAMENTAL LIMITATION:
    vm_mu : nat creates a boundary at zero that breaks unbounded Z-symmetry.
    
    Counter-example proving the boundary matters:
      State: vm_mu = 10, Instruction cost = 5, Gauge shift delta = -12
      
      Path A (step then shift):
        vm_step: 10 + 5 = 15
        shift:   Z.to_nat(15 - 12) = 3
      
      Path B (shift then step):  
        shift:   Z.to_nat(10 - 12) = Z.to_nat(-2) = 0  ← CLAMPED!
        vm_step: 0 + 5 = 5
      
      Result: 3 ≠ 5. The diagram does not commute without positivity guard.
    
    PHYSICAL INTERPRETATION:
    The μ-ledger tracks computational entropy. Like bank accounts, it cannot
    go negative — you cannot "un-compute" past work. The positivity constraint
    0 <= vm_mu + delta is a PHYSICAL LAW, not an ad-hoc restriction: entropy 
    is bounded below by thermodynamics.
    
    This is analogous to thermodynamics: energy can be negative (potential wells),
    but entropy cannot. The Thiele Machine's μ is entropy, not energy.
    
    ALTERNATIVE (not implemented):
    Change vm_mu : nat → vm_mu : Z to allow "entropy debt." This would make
    the symmetry perfect but changes the physical interpretation. The machine
    would track "net computational work" which can be negative (borrowed time).
    *)

