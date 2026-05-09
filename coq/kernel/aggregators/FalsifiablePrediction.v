(**
    FALSIFIABLE PREDICTIONS: μ-Cost Bounds and Experimental Protocols

    I claim μ-cost is not just an abstract bookkeeping device. It is supposed
    to behave like a physical resource with experimentally testable scaling
    laws. This file states the predictions and the check protocol.

    The Coq part defines cost functions, monotonicity, additivity, and
    falsification predicates. The scaling claims still have to be measured
    against the Python/Verilog implementations.

    Here is how to falsify this: run actual VM instructions on the
    Python/Verilog implementations, measure μ-cost (tracked by vm_mu),
    compare against the predicted bounds below. If ANY operation violates
    its bound, the theory is falsified.

    This is Popperian falsifiability: the claim is useful because it can die.

*)

Require Import VMState VMStep KernelPhysics.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Import Nat.

(**
    μ-COST EXTRACTION

    These functions extract the structural information cost from VM operations.

    mu_cost_of_instr: Gets cost from a single instruction
    - Maps to VMStep.instruction_cost (the ground truth implementation)
    - This is WHERE the theory meets measurement

    trace_mu_cost: Accumulates cost over a trace (execution history)
    - Recursive sum: cost([]) = 0, cost(i :: rest) = cost(i) + cost(rest)
    - This is the additivity law (weight_sequential from Definitions.v)

    To falsify: If trace_mu_cost(t) ≠ (final_state.vm_mu - initial_state.vm_mu)
    for some execution, the theory is inconsistent. The Coq definition must
    match the Python/Verilog implementation exactly.
*)

(** Extract μ-cost from instruction *)
Definition mu_cost_of_instr (i : VMStep.vm_instruction) : nat :=
  VMStep.instruction_cost i.

(** Total μ-cost of a trace *)
Fixpoint trace_mu_cost (trace : list VMStep.vm_instruction) : nat :=
  match trace with
  | [] => 0
  | i :: rest => mu_cost_of_instr i + trace_mu_cost rest
  end.

(**
    PREDICTED COST BOUNDS

    These are FALSIFIABLE PREDICTIONS about how measured μ-cost should scale
    with input size. They are bound definitions, not proof that every
    implementation satisfies them.

    region_size: Counts unique memory addresses in a region (after deduplication)
    - normalize_region removes duplicates
    - This is the "effective size" for costing purposes

    PREDICTION 1: pnew_cost_bound = O(|region|)
    Creating a new partition costs proportional to region size.
    To falsify: Find a region where PNEW costs more than |region| μ-bits.

    PREDICTION 2: psplit_cost_bound = O(|left| + |right|)
    Splitting a partition costs proportional to total split size.
    To falsify: Find a split where cost exceeds |left| + |right|.

    PREDICTION 3: pmerge_cost_bound = O(|r1| + |r2|)
    Merging partitions costs linear in combined size (with deduplication).
    To falsify: Find a merge where overlap doesn't reduce cost, or where
    cost exceeds the sum of region sizes.

    PREDICTION 4: discover_cost_bound = O(|evidence|)
    Discovery (adding axioms to partition knowledge) costs linear in evidence count.
    To falsify: Find evidence where PDISCOVER costs more than |evidence| μ-bits.

    WHY LINEAR MATTERS:
    If measurements show superlinear scaling (O(n²), O(2ⁿ), etc.) where this
    file predicts a stable linear bound, this μ-cost story fails at that point.
*)

(** Region "size" as observed by the kernel: duplicates do not count. *)
Definition region_size (region : list nat) : nat :=
  length (normalize_region region).

Definition evidence_size (evidence : list VMAxiom) : nat :=
  length evidence.

(** PREDICTION 1: PNEW cost is O(|region|) *)
Definition pnew_cost_bound (region : list nat) : nat :=
  region_size region.

(** PREDICTION 2: PSPLIT cost is O(|left| + |right|) *)
Definition psplit_cost_bound (left right : list nat) : nat :=
  region_size left + region_size right.

(** PREDICTION 3: PMERGE cost is O(|m1.region| + |m2.region|) with dedup *)
Definition pmerge_cost_bound (r1 r2 : list nat) : nat :=
  region_size r1 + region_size r2.

(** PREDICTION 4: Discovery cost is O(evidence size) *)
Definition discover_cost_bound (evidence : list VMAxiom) : nat :=
  evidence_size evidence.

(**
    COST MONOTONICITY

    μ never decreases during any VM step.

    Structural information is preserved or increased in the μ-ledger.
    You cannot "uncompose" structure without cost. This is like thermodynamic
    irreversibility: the μ-ledger is an arrow of time.

    PROOF: By exhaustive case analysis on vm_step constructors. Every
    instruction uses advance_state or apply_cost, both of which add to vm_mu.

    To falsify: Find ANY instruction where vm_mu decreases. This would
    violate μ-conservation and destroy the theory's connection to thermodynamics.
*)

(** μ never decreases during a single step *)
Theorem mu_monotonic_step : forall s i s',
  VMStep.vm_step s i s' -> (s'.(vm_mu) >= s.(vm_mu))%nat.
Proof.
  intros s i s' Hstep.
  inversion Hstep; subst;
    unfold VMStep.advance_state, VMStep.advance_state_reveal, VMStep.advance_state_rm,
           VMStep.jump_state, VMStep.jump_state_rm, VMStep.apply_cost;
    simpl; try lia.
Qed.

(**
    COST ADDITIVITY

    Sequential trace costs add by definition.

    Running two listed instructions sequentially costs exactly the sum of the
    two instruction_cost values. No extra interaction term appears in
    trace_mu_cost.

    PROOF: Direct computation from trace_mu_cost definition.

    To falsify: Find two instructions where cost([i1, i2]) ≠ cost([i1]) + cost([i2]).
    This would indicate nonlocal cost correlations, violating the theory's
    compositional structure.
*)

(** Sequential execution costs add *)
Theorem mu_cost_additive : forall i1 i2 cost1 cost2,
  mu_cost_of_instr i1 = cost1 ->
  mu_cost_of_instr i2 = cost2 ->
  trace_mu_cost [i1; i2] = cost1 + cost2.
Proof.
  intros i1 i2 cost1 cost2 H1 H2.
  unfold trace_mu_cost. simpl.
  rewrite H1, H2. lia.
Qed.

(**
    FALSIFICATION PROTOCOL

    cost_violation: A prediction fails if measured > predicted.
    - This is the Popperian criterion: ONE counterexample kills the theory.
    - No statistical wiggle room, no error bars, no "approximately true".
    - Either the bound holds or it doesn't.

    ExperimentalTrial: A recorded execution with measured cost.
    - trial_instr: The instruction that was executed
    - trial_measured_cost: The actual vm_mu increase

    check_prediction: Boolean test for violations.
    - Returns true if measured cost exceeds instruction's declared cost
    - This is the automated falsification check

    HOW TO USE:
    1. Execute instruction on real VM implementation (Python/Verilog)
    2. Record vm_mu before and after
    3. Construct ExperimentalTrial with measured_cost = after - before
    4. Run check_prediction
    5. If true, the theory is falsified for that instruction

    To falsify: If check_prediction returns true for ANY trial, I'm wrong.
*)

(** A prediction is violated if measured cost exceeds predicted bound *)
Definition cost_violation (measured predicted : nat) : Prop :=
  (measured > predicted)%nat.

(** Experimental trial: instruction + actual μ-cost *)
Record ExperimentalTrial := {
  trial_instr : VMStep.vm_instruction;
  trial_measured_cost : nat
}.

(** Check if trial violates prediction *)
Definition check_prediction (t : ExperimentalTrial) : bool :=
  Nat.ltb (mu_cost_of_instr (trial_instr t)) (trial_measured_cost t).

(**
    SPECIFIC TESTABLE PREDICTIONS

    These are predictions with explicit constants that experiments must verify.

    TESTABLE PREDICTION 1: pnew_linear_bound
    CLAIM: PNEW with n-element region costs ≤ C·n for some constant C.
    EXPERIMENTAL TEST: Plot measured cost vs region_size, fit linear regression,
    check all points below C·n line.
    To falsify: Find ANY region where measured > C·|region| for best-fit C.

    TESTABLE PREDICTION 2: discover_linear_bound
    CLAIM: PDISCOVER with k axioms costs ≤ C·k for some constant C.
    EXPERIMENTAL TEST: Vary evidence size from 1 to 1000, verify linearity.
    To falsify: Show cost grows superlinearly (e.g., O(k²) or O(2^k)).

    TESTABLE PREDICTION 3: merge_dedup_savings
    CLAIM: PMERGE achieves deduplication savings exactly equal to overlap size.
    If r1 and r2 overlap in m addresses, cost ≤ |r1| + |r2| - m.
    EXPERIMENTAL TEST: Create pairs with known overlap, measure savings.
    To falsify: Find merge where savings ≠ overlap, or where no savings occur.

    WHY CONSTANTS MATTER:
    By allowing arbitrary constant C, I make the scaling claim harder to falsify.
    But C must be FINITE and STABLE across experiments. If C grows with input
    size, that's superlinear scaling and the theory fails.

    The prediction: plot measured vs predicted and get a stable straight line
    through the origin with slope C. Persistent curvature or outliers falsify
    this scaling claim.
*)

(** TESTABLE PREDICTION 1: PNEW with n-element region costs ≤ C·n *)
Definition pnew_linear_bound (C : nat) (region : list nat) (measured : nat) : Prop :=
  (measured <= C * region_size region)%nat.

(** TESTABLE PREDICTION 2: Discovery cost scales with evidence count *)
Definition discover_linear_bound (C : nat) (evidence : list VMAxiom) (measured : nat) : Prop :=
  (measured <= C * evidence_size evidence)%nat.

(** TESTABLE PREDICTION 3: Merge deduplication savings *)
Definition merge_dedup_savings (r1 r2 : list nat) (overlap : nat) (measured : nat) : Prop :=
  (measured <= region_size r1 + region_size r2 - overlap)%nat.

(**
    BENCHMARK SPECIFICATIONS (For Python implementation)
*)

(** To falsify, run these experiments and check bounds:

    EXPERIMENT 1: PNEW_LINEAR
       - Generate random regions of size n ∈ {1, 10, 100, 1000, 10000}
       - For each size, run 100 trials with different random memory addresses
       - Measure actual μ-cost (vm_mu after - vm_mu before)
       - Plot measured vs n, fit linear regression y = C·n
       - PASS: All points satisfy measured ≤ C·n with R² > 0.99
       - FAIL: Any outlier above line, or R² < 0.99 (indicates nonlinearity)

    EXPERIMENT 2: DISCOVER_LINEAR
       - Generate random evidence lists of size k ∈ {1, 10, 100, 1000}
       - Each evidence list contains k VMAxiom entries
       - Measure μ-cost of PDISCOVER instruction
       - Check linearity with R² > 0.99
       - FAIL: Superlinear growth (e.g., O(k log k) or O(k²))

    EXPERIMENT 3: MERGE_DEDUP
       - Create partition pairs (r1, r2) with controlled overlap
       - Vary overlap from 0% to 100% of smaller region
       - Measure PMERGE cost
       - Verify savings = overlap size (within 1% tolerance)
       - FAIL: Savings don't match overlap, or dedup is not working

    IMPLEMENTATION NOTE:
    All three experiments MUST use the actual VM implementation (Python or Verilog),
    not simulations or approximations. The measurements must come from vm_mu field.

    STATISTICAL RIGOR:
    The theory predicts EXACT bounds (not approximate). Small deviations are acceptable
    (±5% tolerance for implementation noise), but systematic violations or wrong
    asymptotic scaling = falsification.
*)

(** Summary.

  The proved part of this file is the bookkeeping and the predicted scaling
  bounds. The unproved part is empirical by construction: the real Python or
  hardware measurements still have to line up with those bounds. If the
  measurements come back superlinear where the theorem predicts linear, this
  cost-scaling story is wrong.

  There is no wiggle room hidden in the asymptotics. The claim is stable linear
  scaling up to fixed constants, and systematic deviation is exactly what would
  falsify it. That is what makes the theory useful. *)
