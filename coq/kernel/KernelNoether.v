(**
    KernelNoether: Z-indexed shifts of the μ-ledger.

    This file studies a bookkeeping symmetry: shift vm_mu by an integer while
    leaving the rest of VMState alone. Because vm_mu is a nat, negative shifts
    are clamped at zero by Z.to_nat. The useful group-action laws therefore
    hold only under explicit nonnegative-side conditions.

    The Noether language here is an analogy, not a derivation of a physical
    Noether theorem. What is proved is concrete and smaller: shift laws, graph
    invariance, orbit-style relations under positivity guards, and μ
    monotonicity under vm_step.

    z_action_identity: shifting by 0 is identity.
    z_action_composition: shifts compose, shift(a) ∘ shift(b) = shift(a+b).
    z_action_inverse: shift(n) ∘ shift(-n) = identity.
    z_gauge_invariance: Z-shifts preserve partition structure.

    To challenge this module: find an operation where shifting μ changes
    partition structure, find a vm_step that decreases μ, or find a positivity-
    guarded group-action law that fails.

    WHY: the zero boundary matters. The code records where Z-style symmetry
    works and where clamping breaks it.
  *)

From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import ZArith.ZArith.
From Coq Require Import micromega.Lia.
From Kernel Require Import VMState VMStep.
Import ListNotations.

Open Scope Z_scope.

(** Z-indexed shift definition. *)

(**
  z_gauge_shift: Shift μ-ledger by arbitrary integer (Z-action on VMState).

  This formalizes the bookkeeping operation "change μ by a global integer
  offset and keep every other VMState field fixed." Calling it a gauge shift is
  the analogy; the proved fact is that non-μ fields are copied unchanged.

  ALGORITHM: Copy all VMState fields except vm_mu:
  - vm_mu → Z.to_nat(Z.of_nat(vm_mu) + delta)
  - All other fields (graph, regs, mem, etc.) unchanged.

  Critical point: Z.to_nat clamps negative values to 0. If vm_mu + delta < 0,
  the result is 0. This breaks group-action laws unless the theorem carries a
  positivity guard.

  POSITIVITY GUARD: Most theorems require 0 ≤ vm_mu + delta. This ensures
  Z.to_nat doesn't clamp, preserving group action structure.

  Physical reading, if used: the absolute μ offset is treated like a reference
  choice for the ledger. The formal observable below is partition structure,
  not all possible physics.

  EXAMPLE: s = {| vm_mu := 100; vm_graph := g; ... |}.
           z_gauge_shift 50 s = {| vm_mu := 150; vm_graph := g; ... |} (same graph).
           z_gauge_shift (-50) s = {| vm_mu := 50; vm_graph := g; ... |} (same graph).
           z_gauge_shift (-150) s = {| vm_mu := 0; vm_graph := g; ... |} (CLAMPED!).

  To falsify the formal claim: show z_gauge_shift delta s changes vm_graph or
  another field it is supposed to copy.

  DEPENDENCIES: Requires Z.to_nat, Z.of_nat (Coq standard library).

  in_same_orbit, vm_step_orbit_equiv, noether_forward.
*)
(** Shift μ by Z amount (can be negative, though vm_mu is nat) *)
Definition z_gauge_shift (delta : Z) (s : VMState) : VMState :=
  {| vm_graph := s.(vm_graph);
     (* SAFE: Bounded arithmetic - caller ensures delta keeps result non-negative *)
     vm_mu := Z.to_nat (Z.of_nat s.(vm_mu) + delta);
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_csrs := s.(vm_csrs);
     vm_pc := s.(vm_pc);
  vm_err := s.(vm_err);
  vm_logic_acc := s.(vm_logic_acc);
  vm_mstatus := s.(vm_mstatus);
  vm_witness := s.(vm_witness);
  vm_certified := s.(vm_certified) |}.

(** Helper: z_gauge_shift preserves mem projection (used in LASSERT/LJOIN orbit proofs) *)
Lemma z_gauge_shift_mem : forall delta s,
  vm_mem (z_gauge_shift delta s) = vm_mem s.
Proof. intros. unfold z_gauge_shift. reflexivity. Qed.

(** Helper: z_gauge_shift preserves regs projection (used in LASSERT/LJOIN orbit proofs) *)
Lemma z_gauge_shift_regs : forall delta s,
  vm_regs (z_gauge_shift delta s) = vm_regs s.
Proof. intros. unfold z_gauge_shift. reflexivity. Qed.

(** Helper: z_gauge_shift preserves graph projection *)
Lemma z_gauge_shift_graph : forall delta s,
  vm_graph (z_gauge_shift delta s) = vm_graph s.
Proof. intros. unfold z_gauge_shift. reflexivity. Qed.

(** Helper: z_gauge_shift preserves read_reg (depends only on vm_regs) *)
Lemma z_gauge_shift_read_reg : forall delta s r,
  read_reg (z_gauge_shift delta s) r = read_reg s r.
Proof. intros. unfold read_reg, z_gauge_shift. reflexivity. Qed.

(**
  Observable_partition: Extract partition region structure (ignoring μ).

  This is the observable used in this file: module regions from the partition
  graph, ignoring μ and every other field.

  ALGORITHM: Map pg_modules to list of region lists. Each module m contributes
  m.module_region (list of partition IDs). Result: list (list nat) of all regions.

  The proved claim is z_gauge_invariance:
    Observable_partition (z_gauge_shift delta s) = Observable_partition s.

  This does not say every possible observation of the VM ignores μ. It says this
  specific partition projection ignores μ.

  EXAMPLE: s = {| vm_graph := {| pg_modules := [(0, {|module_region := [1,2]|}),
                                                  (1, {|module_region := [3,4]|})] |};
                  vm_mu := 100 |}.
           Observable_partition s = [[1,2], [3,4]] (no mention of μ = 100).

  To challenge this formal observable, show that it is too weak for the physics
  being claimed elsewhere.

*)
(** Observable: partition structure only (no μ) *)
Definition Observable_partition (s : VMState) : list (list nat) :=
  match s.(vm_graph) with
  | {| pg_modules := mods |} =>
      map (fun m => match m with (_, ms) => ms.(module_region) end) mods
  end.

(** Group-action-style laws, with positivity guards where clamping matters. *)

(**
  z_action_identity: identity shift preserves state.

  Shifting by 0 is the identity function: z_gauge_shift 0 s = s.

  This is the identity law for the shift operation.

  CLAIM: ∀ s. z_gauge_shift 0 s = s.

  1. Unfold z_gauge_shift definition.
  2. Simplify: Z.of_nat s.vm_mu + 0 = Z.of_nat s.vm_mu (Z.add_0_r).
  3. Apply Nat2Z.id: Z.to_nat (Z.of_nat n) = n.
  4. Destruct s, show all fields equal by reflexivity.

  Reading: shifting by nothing changes nothing.

  To falsify: Find state s where z_gauge_shift 0 s ≠ s. This would mean the
  implementation of z_gauge_shift is broken (adds spurious changes).

  DEPENDENCIES: Requires z_gauge_shift, Z.add_0_r (stdlib), Nat2Z.id (stdlib).

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
  z_action_composition: shifts compose when no clamping occurs.

  Shifting by b then by a equals shifting by (a+b):
           z_gauge_shift a (z_gauge_shift b s) = z_gauge_shift (a + b) s.

  This is the composition law for the shift operation under explicit
  nonnegative-side hypotheses.

  CLAIM: ∀ a, b, s. (0 ≤ μ+b) ∧ (0 ≤ μ+b+a) → shift(a, shift(b, s)) = shift(a+b, s).

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
  with μ=10, b=-5, a=+3: Path A: (10-5)+3 = 8. Path B: 10+(-5+3) = 8. Equal.
  But μ=10, b=-12, a=+5: Path A: (10-12)→0, then 0+5=5. Path B: 10+(-12+5)=-7→0.
  Result: 5 ≠ 0. Composition FAILS without positivity guard.

  To falsify: Find a, b, s satisfying positivity guards where composition fails.
  This would mean Z arithmetic in Coq is broken (impossible - machine-checked).

  DEPENDENCIES: Requires Z2Nat.id, Z.add associativity (lia), z_gauge_shift.

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
  z_action_inverse: shifts are invertible when no clamping occurs.

  Shifting by n then by -n recovers the original state:
           z_gauge_shift (-n) (z_gauge_shift n s) = s.

  This is the inverse law for the shift operation under the positivity guard.

  CLAIM: ∀ n, s. (0 ≤ μ+n) → shift(-n, shift(n, s)) = s.

  1. Unfold z_gauge_shift, destruct s.
  2. Goal: Z.to_nat(Z.of_nat(Z.to_nat(μ+n)) + (-n)) = μ.
  3. Apply Z2Nat.id with hypothesis Hpos: cancel Z.to_nat ∘ Z.of_nat.
  4. Simplify: (μ + n) + (-n) = μ by ring (lia).
  5. Apply Nat2Z.id: Z.to_nat(Z.of_nat(μ)) = μ.
  6. Reflexivity.

  POSITIVITY GUARD: Requires 0 ≤ μ+n. This ensures the intermediate state
  shift(n, s) has non-negative μ. Without it, Z.to_nat clamps, and the inverse
  operation cannot recover the original (information lost to clamping).

  Reading: if the intermediate μ never crosses below zero, shifting by n and
  then by -n recovers the original state.

  COUNTEREXAMPLE (without positivity): μ=10, n=-15. shift(-15, s) → μ=0 (clamped).
  Then shift(+15, {μ=0}) → μ=15 ≠ 10. Lost information due to clamping. Inverse
  doesn't work when intermediate state is negative.

  To falsify: Find n, s with positivity satisfied where shift(-n, shift(n, s)) ≠ s.
  This would mean Z inverse is broken (impossible).

  DEPENDENCIES: Requires Z2Nat.id, Nat2Z.id, Z.add inverse (lia), z_gauge_shift.

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

(** Gauge invariance for the chosen partition observable. *)

(**
  z_gauge_invariance: partition observable unchanged by μ-shifts.

  Shifting μ doesn't change observable partition structure:
           Observable_partition (z_gauge_shift delta s) = Observable_partition s.

  This proves only that Observable_partition ignores vm_mu because z_gauge_shift
  copies vm_graph unchanged. It does not prove that all possible observations
  ignore μ, and it does not derive a physical Noether theorem.

  CLAIM: ∀ delta, s. Observable_partition after μ-shift equals Observable_partition before.

  1. Unfold Observable_partition and z_gauge_shift.
  2. Observable_partition extracts pg_modules from vm_graph.
  3. z_gauge_shift copies vm_graph unchanged (only vm_mu changes).
  4. Therefore Observable_partition unchanged. Reflexivity.

  Physical analogy: partition structure plays the role of the invariant
  quantity for this file, while absolute μ is a ledger offset. The analogy does
  not replace the explicit hypotheses needed for physical claims.

  EXAMPLE: s = {| vm_mu := 100; vm_graph := {modules: [[1,2], [3,4]]}; ... |}.
  shift(+50, s) = {| vm_mu := 150; vm_graph := {modules: [[1,2], [3,4]]}; ... |}.
  Observable_partition(s) = [[1,2], [3,4]] = Observable_partition(shift(+50, s)).
  The partition structure [[1,2], [3,4]] is IDENTICAL. μ changed 100→150, but
  that's unobservable (like shifting voltage reference ground).

  To falsify the formal statement: find delta and s where Observable_partition
  changes after μ-shift. That would mean z_gauge_shift no longer copies vm_graph.

  DEPENDENCIES: Requires z_gauge_shift (preserves graph), Observable_partition (extracts graph).

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

(** μ-ledger projection and monotonicity. *)

(**
  mu_current: extract the μ-ledger value.

  This is a named accessor for the ledger value whose monotonicity is proved
  below.

  IMPLEMENTATION: mu_current s = s.vm_mu. Trivial projection.

  The Noether-charge language is an analogy. Formally this is just s.(vm_mu).

  EXAMPLE: s = {| vm_mu := 42; ... |}. mu_current s = 42.

  To falsify: Show mu_current extracts wrong field. This would be implementation
  error (accessing wrong record field).

*)
(** vm_mu changes predictably under vm_step. *)
Definition mu_current (s : VMState) : nat := s.(vm_mu).

(**
  vm_step_mu_monotonic: μ never decreases under vm_step.

  Every vm_step increases (or preserves) μ:
           vm_step s i s' → mu_current s ≤ mu_current s'.

  This is monotonicity, not conservation in the reversible-physics sense. The
  proof is by vm_step constructors and the fact that instruction costs are nat.

  CLAIM: ∀ s, i, s'. vm_step s i s' → s.vm_mu ≤ s'.vm_mu.

  1. Unfold mu_current (just s.vm_mu projection).
  2. Inversion on Hstep: case split on all vm_step constructors.
  3. Each constructor uses advance_state or advance_state_rm, which applies apply_cost.
  4. apply_cost adds instruction_cost ≥ 0 to vm_mu.
  5. Therefore vm_mu' = vm_mu + cost ≥ vm_mu.
  6. All cases verified by lia (linear arithmetic solver).

  The proof checks every vm_step constructor and reduces μ growth to adding a
  nonnegative instruction_cost.

  To falsify the theorem: find instruction i and states s, s' where vm_step s i s'
  but s'.vm_mu < s.vm_mu.

  DEPENDENCIES: Requires vm_step (VMStep.v), advance_state (applies cost),
  instruction_cost ≥ 0 (VMStep.v), lia (arithmetic).

  (packages as fundamental physical law), all μ-cost analysis.
*)
(** Under vm_step, μ increases by a nat instruction cost. *)
Theorem vm_step_mu_monotonic : forall s i s',
  vm_step s i s' -> (mu_current s <= mu_current s')%nat.
Proof.
  intros s i s' Hstep.
  unfold mu_current.
  inversion Hstep; subst;
    unfold advance_state, advance_state_reveal, advance_state_rm,
           jump_state, jump_state_rm, apply_cost in *;
    simpl; try lia.
Qed.

(** Orbit-style relation generated by μ-shifts. *)

(**
  in_same_orbit: Orbit equivalence relation for gauge-related states.

  WHY: I need to formalize "two states are gauge-equivalent (differ only in μ)".
  in_same_orbit captures this: s1 and s2 are in the same orbit if there exists
  a gauge shift connecting them.

  DEFINITION: in_same_orbit s1 s2 := ∃ delta, z_gauge_shift delta s1 = s2.

  STRUCTURE: Existential quantification over Z. Two states are orbit-equivalent
  iff you can reach one from the other via μ-shift.

  Physical reading, if used: states in the same orbit differ by μ-bookkeeping
  while the copied fields are held fixed by z_gauge_shift.

  EXAMPLE: s1 = {| vm_mu := 10; vm_graph := g; ... |}.
           s2 = {| vm_mu := 15; vm_graph := g; ... |}.
  If ALL other fields match, in_same_orbit s1 s2 (witness: delta = 5).

  To falsify: Find s1, s2 with different partition graphs where in_same_orbit holds.
  This would violate gauge invariance (z_gauge_shift preserves graph by definition,
  so orbits can only connect states with same graph).

  vm_step_orbit_equiv (prove dynamics preserves orbits).
*)
(** Two states are in the same orbit if related by Z-shift *)
Definition in_same_orbit (s1 s2 : VMState) : Prop :=
  exists delta : Z, z_gauge_shift delta s1 = s2.

(**
  orbit_equiv_refl: Orbit equivalence is REFLEXIVE.

  Every state is in the same orbit as itself: ∀ s. in_same_orbit s s.

  WHY: To be an equivalence relation, orbit equivalence must be reflexive. This
  proves the FIRST equivalence relation axiom.

  CLAIM: ∀ s. ∃ delta. z_gauge_shift delta s = s.

  1. Provide witness: delta = 0.
  2. Apply z_action_identity: z_gauge_shift 0 s = s.
  3. Existential satisfied. QED.

  PHYSICAL MEANING: "A state is gauge-equivalent to itself." The identity gauge
  transformation (shift by 0) leaves the state unchanged. Trivial reflexivity.

  To falsify: Find state s where in_same_orbit s s fails. This would mean
  z_action_identity is broken (impossible - proven theorem).

  DEPENDENCIES: Requires z_action_identity (shift by 0 is identity), in_same_orbit.

*)
(** Reflexivity of the shift-generated orbit relation. *)
Theorem orbit_equiv_refl : forall s, in_same_orbit s s.
Proof.
  intros s. exists 0%Z. apply z_action_identity.
Qed.

(**
  orbit_equiv_sym: Orbit equivalence is SYMMETRIC.

  If s1 is in the same orbit as s2, then s2 is in the same orbit as s1:
           z_gauge_shift delta s1 = s2 → in_same_orbit s2 s1.

  WHY: To be an equivalence relation, orbit equivalence must be symmetric. This
  proves the SECOND equivalence relation axiom.

  CLAIM: ∀ s1, s2, delta. (0 ≤ μ₁+delta) → shift(delta, s1) = s2 → ∃ delta'. shift(delta', s2) = s1.

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

  To falsify: Find s1, s2, delta with positivity satisfied where orbit_equiv_sym
  fails. This would mean z_action_inverse is broken (impossible - proven theorem).

  DEPENDENCIES: Requires z_action_inverse (inverse gauge shifts), in_same_orbit.

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

  If s1 ~ s2 and s2 ~ s3, then s1 ~ s3:
           shift(d1, s1) = s2 ∧ shift(d2, s2) = s3 → in_same_orbit s1 s3.

  WHY: To be an equivalence relation, orbit equivalence must be transitive. This
  proves the THIRD equivalence relation axiom. Together with reflexivity and
  symmetry, this completes the equivalence relation proof.

  CLAIM: ∀ s1, s2, s3, d1, d2. (0 ≤ μ₁+d1) ∧ (0 ≤ μ₁+d1+d2) →
         shift(d1, s1) = s2 → shift(d2, s2) = s3 → ∃ delta. shift(delta, s1) = s3.

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
  s1 -> s2: shift(-3, {μ=5}) = {μ=2}.
  s2 -> s3: shift(-4, {μ=2}) = {μ=0} (clamped to 0, should be -2).
  Direct: shift(-7, {μ=5}) = {μ=0} (clamped to 0, should be -2).
  Transitivity holds by accident (both clamped to 0), but not by composition law.
  With positivity guards, composition is EXACT, not accidental.

  To falsify: Find s1, s2, s3, d1, d2 with positivity satisfied where
  transitivity fails. This would mean z_action_composition is broken (impossible).

  DEPENDENCIES: Requires z_action_composition (shifts compose), in_same_orbit.

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

(**
    Noether-style symmetry/conservation analogy
  *)

(** Equivariance lemma: vm_step preserves the shift relation under a guard.

    This establishes that vm_step is equivariant for the Z-action:
    if two states s1, s1' are in the same orbit, and vm_step advances them to
    s2, s2', then s2 and s2' are also in the same orbit.

    CRITICAL PRECONDITION: The gauge shift delta must keep vm_mu non-negative.
    This is the "no bankruptcy" condition: the ledger cannot go below zero.

    Without this condition, Z.to_nat clamping breaks commutativity:
      Counter-example: vm_mu=10, cost=5, delta=-12
      Path A (step then shift): 10+5=15, then 15-12=3
      Path B (shift then step): 10-12=-2, clamp to 0, then 0+5=5
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

  To falsify: Find μ, cost, delta with positivity satisfied where the equation
  fails. This would mean Z arithmetic is inconsistent (impossible).

  DEPENDENCIES: Requires Nat2Z.inj_add, Z2Nat.id, lia (Z arithmetic).

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

  If s1 →[i] s2 via vm_step, then z_gauge_shift(delta, s1) →[i] s2'
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
  demonstrates this explicitly.

  COUNTEREXAMPLE (without positivity): μ=10, cost=5, delta=-12.
  Path A: step then shift: (10+5=15) then (15-12=3) → μ'=3.
  Path B: shift then step: (10-12=0 CLAMPED) then (0+5=5) → μ'=5.
  Result: 3 ≠ 5. Equivariance FAILS without positivity.

  To falsify: Find s1, i, delta with positivity where vm_step from shifted
  state gives different structural result (not just μ). This would mean gauge
  shifts affect physical behavior (violates gauge invariance).

  DEPENDENCIES: Requires shift_cost_comm (arithmetic), z_gauge_shift (definition),
  vm_step (VMStep.v), econstructor (Coq proof automation).

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
  (* Tensor OOB cases: explicit eapply BEFORE econstructor to prevent
     econstructor from committing to step_tensor_set/get (wrong constructors).
     step_tensor_set_oob / step_tensor_get_oob come AFTER step_tensor_set/get
     in the Inductive declaration, so econstructor would always pick the wrong one. *)
  all: try (eapply step_tensor_set_oob; eassumption).
  all: try (eapply step_tensor_get_oob; eassumption).
  (* Tensor in-bounds cases: 4 constructor args (i<4, j<4, graph'=..., regs'=...) *)
  all: try (eapply step_tensor_set; [eassumption | eassumption | reflexivity]).
  all: try (eapply step_tensor_get; [eassumption | eassumption | reflexivity | reflexivity]).
  (* Morph instruction cases: z_gauge_shift only changes vm_mu, not vm_graph/vm_csrs/etc.
     Each morph op now has _ok and _bad constructors. *)
  all: try (eapply step_morph_ok; eassumption).
  all: try (eapply step_morph_bad_src; eassumption).
  all: try (eapply step_morph_bad_dst; eassumption).
  all: try (eapply step_compose_ok; eassumption).
  all: try (eapply step_compose_bad; eassumption).
  all: try (eapply step_morph_id_ok; eassumption).
  all: try (eapply step_morph_id_bad; eassumption).
  all: try (eapply step_morph_delete_ok; eassumption).
  all: try (eapply step_morph_delete_bad; eassumption).
  all: try (eapply step_morph_assert_ok; eassumption).
  all: try (eapply step_morph_assert_bad; eassumption).
  all: try (eapply step_morph_tensor_ok; eassumption).
  all: try (eapply step_morph_tensor_bad; eassumption).
  all: try (eapply step_morph_get_ok; [eassumption | reflexivity]).
  all: try (eapply step_morph_get_bad; eassumption).
  (* LASSERT: single unified constructor, no premises. *)
  all: try (eapply step_lassert).
  (* LJOIN: single unified constructor, no premises. *)
  all: try (eapply step_ljoin).
  (* All other (non-tensor) instruction cases: econstructor matches same constructor *)
  all: try (econstructor; [reflexivity | reflexivity | reflexivity | idtac..]).
  all: try (econstructor; [reflexivity | reflexivity | idtac..]).
  all: try (econstructor; [reflexivity | idtac..]).
  all: try (econstructor; [eassumption | idtac..]).
  all: try econstructor.
  (* Goal B: z_gauge_shift commutes with cost addition (arithmetic) *)
  all: unfold z_gauge_shift, advance_state, advance_state_reveal, advance_state_rm,
              jump_state, jump_state_rm, apply_cost; simpl.
  all: try (f_equal; symmetry; apply shift_cost_comm; assumption).
Qed.

(**
  noether_forward: construct the shift between structurally identical states.

  If two states agree on every field except possibly μ, then choosing
  delta = μ₂ - μ₁ shifts one state to the other. This is a structural orbit
  statement, not a derivation of a conserved charge.

  CLAIM: ∀ s1, s2. (Observable_partition s1 = Observable_partition s2) ∧
         (all structural fields equal) →
         ∃ delta. z_gauge_shift delta s1 = s2.

  STRUCTURE: Given seven hypotheses (all fields except vm_mu are equal), construct
  witness delta = μ₂ - μ₁. This shift relates the two states.

  1. Provide witness: delta = Z.of_nat(μ₂) - Z.of_nat(μ₁).
  2. Unfold z_gauge_shift, destruct s1 and s2.
  3. Apply hypotheses: all fields except vm_mu are equal (subst).
  4. Goal reduces to: μ₁ + (μ₂ - μ₁) = μ₂ (arithmetic).
  5. Prove: Z.of_nat(μ₁) + (Z.of_nat(μ₂) - Z.of_nat(μ₁)) = Z.of_nat(μ₂) by lia.
  6. Apply Nat2Z.id: Z.to_nat(Z.of_nat(μ₂)) = μ₂.
  7. Reflexivity. QED.

  Physical reading, if used: states differing only in the ledger offset can be
  treated as the same structural state with different bookkeeping.

  EXAMPLE: s1 = {| vm_mu := 100; vm_graph := g; vm_regs := r; ... |}.
           s2 = {| vm_mu := 150; vm_graph := g; vm_regs := r; ... |}.
  If ALL other fields match, noether_forward proves: z_gauge_shift(50, s1) = s2.
  The μ difference (50) is the gauge shift connecting them.

  To falsify: Find s1, s2 with all structural fields equal but NO gauge shift
  connecting them. This would require μ₁ + delta ≠ μ₂ for all delta (impossible
  by construction: delta = μ₂ - μ₁ satisfies the equation).

  DEPENDENCIES: Requires z_gauge_shift (gauge transformation), Observable_partition
  (gauge-invariant observable), Nat2Z.id, lia (arithmetic).

*)
(** Structurally identical states differ by one μ-shift. *)
Theorem noether_forward : forall s1 s2,
  Observable_partition s1 = Observable_partition s2 ->
  s1.(vm_graph) = s2.(vm_graph) ->
  s1.(vm_regs) = s2.(vm_regs) ->
  s1.(vm_mem) = s2.(vm_mem) ->
  s1.(vm_csrs) = s2.(vm_csrs) ->
  s1.(vm_pc) = s2.(vm_pc) ->
  s1.(vm_mu_tensor) = s2.(vm_mu_tensor) ->
  s1.(vm_err) = s2.(vm_err) ->
  s1.(vm_logic_acc) = s2.(vm_logic_acc) ->
  s1.(vm_mstatus) = s2.(vm_mstatus) ->
  s1.(vm_witness) = s2.(vm_witness) ->
  s1.(vm_certified) = s2.(vm_certified) ->
  exists delta, z_gauge_shift delta s1 = s2.
Proof.
  intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Hmutensor Herr Hlogic Hmstatus Hwitness Hcertified.
  exists (Z.of_nat s2.(vm_mu) - Z.of_nat s1.(vm_mu))%Z.
  unfold z_gauge_shift. destruct s1, s2; simpl in *.
  subst. f_equal.
  assert (Harith: (Z.of_nat vm_mu + (Z.of_nat vm_mu0 - Z.of_nat vm_mu) = Z.of_nat vm_mu0)%Z) by lia.
  rewrite Harith. apply Nat2Z.id.
Qed.

(**
  noether_backward: the conservation premise is not needed here.

  The historical name suggests a Noether converse. The proof is smaller:
  Observable_partition ignores μ by definition, so z_gauge_invariance proves
  the result directly. The μ-monotonicity premise is accepted for API shape but
  unused.

  CLAIM: ∀ s. (μ-conservation law holds) →
         ∀ delta. Observable_partition(shift(delta, s)) = Observable_partition(s).

  STRUCTURE: Given hypothesis that μ is conserved (monotone), prove that ALL
  gauge shifts preserve observables.

  1. Assume hypothesis: ∀ i, s'. vm_step s i s' → μ(s) ≤ μ(s') (conservation).
  2. Goal: prove Observable_partition unchanged by any gauge shift delta.
  3. Apply z_gauge_invariance: this theorem already proves the goal directly.
  4. The hypothesis Hcons is UNUSED - gauge invariance holds UNCONDITIONALLY.
  5. QED (trivial application).

  This is why the Noether wording must stay scoped: the file does not prove a
  bidirectional physical equivalence between symmetry and conservation.

  EXAMPLE: Given vm_step_mu_monotonic (μ conserved), noether_backward proves:
  z_gauge_shift(delta, s) has same Observable_partition as s for ALL delta.

  To falsify: Find state s where μ-conservation holds but gauge shift changes
  Observable_partition. This would contradict z_gauge_invariance (proven theorem).

  DEPENDENCIES: Requires z_gauge_invariance (gauge symmetry theorem), mu_current,
  vm_step (dynamics).

*)
(** The partition observable ignores μ-shifts regardless of the premise. *)
Theorem noether_backward : forall s,
  (forall i s', vm_step s i s' -> mu_current s <= mu_current s')%nat ->
  forall delta, Observable_partition (z_gauge_shift delta s) = Observable_partition s.
Proof.
  intros s _ delta.
  apply z_gauge_invariance.
Qed.

(** Summary: the zero boundary is the point. *)

(** PROVEN (with constraints):
    - Z-indexed shift laws (identity, composition, inverse); composition and
      inverse require positivity
    - Z-gauge invariance of observables (unconditional)
    - Orbit equivalence relations (with positivity guards)
    - vm_step equivariance (with positivity guard)
    - Noether-named structural lemmas, scoped as bookkeeping analogies
    
    THE FUNDAMENTAL LIMITATION:
    vm_mu : nat creates a boundary at zero that breaks unbounded Z-symmetry.
    
    Counter-example proving the boundary matters:
      State: vm_mu = 10, Instruction cost = 5, Gauge shift delta = -12
      
      Path A (step then shift):
        vm_step: 10 + 5 = 15
        shift:   Z.to_nat(15 - 12) = 3
      
      Path B (shift then step):  
        shift:   Z.to_nat(10 - 12) = Z.to_nat(-2) = 0  (clamped)
        vm_step: 0 + 5 = 5
      
      Result: 3 ≠ 5. The diagram does not commute without positivity guard.
    
    The μ-ledger tracks computational entropy. Like bank accounts, it cannot
    go negative in this model. The positivity constraint 0 <= vm_mu + delta is
    the formal boundary imposed by using nat for vm_mu.
    
    This is analogous to thermodynamics: energy can be negative (potential wells),
    but entropy cannot. The Thiele Machine's μ is entropy, not energy.
    
    ALTERNATIVE (not implemented):
    Change vm_mu : nat -> vm_mu : Z to allow "entropy debt." This would make
    the symmetry perfect but changes the physical interpretation. The machine
    would track "net computational work" which can be negative (borrowed time).
    *)
