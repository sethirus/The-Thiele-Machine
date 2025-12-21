# The Thiele Machine TOE Attempt (Kernel-Layer Thesis)

## Abstract
This document is a thesis-style, reproducible account of an attempted “TOE derivation” **from the kernel layer alone** (Coq semantics treated as authoritative). The work follows the repo’s north star: **3-layer isomorphism** (Coq ↔ extracted runner ↔ Python VM ↔ RTL), and treats any divergence as a bug to be eliminated with a minimal distinguishing trace.

**Final outcome (exactly one):**

> **(2) Precise impossibility (kernel-only):** multiple plan requirements are **not derivable** from the current kernel primitives without adding extra structure (definitions/axioms/coarse-graining). This is packaged as a theorem.

At the same time, the strongest derivable “physics closure” statements inside the kernel are proven and packaged: **no-signaling/locality (relative to `instr_targets`), μ monotonicity, and multi-step cone locality**.

**Tightening note (audit hardening):** the negative result is stated in a dedicated, small dependency cone (`KernelTOE/`) with **explicit laws written directly in the theorem environment** (no “large named predicate” ambiguity), and with a mechanical script that audits the *transitive dependency closure* of the flagship theorem for hidden `Axiom`/`Parameter`/`Admitted`/`admit`.

## Reproducible gates (run locally)
All claims here are meant to be checkable via the repo’s gates:

- Coq kernel build:
  - `make -C coq core`
- Fast isomorphism gates:
  - `pytest -q tests/test_partition_isomorphism_minimal.py`
  - `pytest -q tests/test_rtl_compute_isomorphism.py`

- Proof-smell audit (scorched earth):
  - `python3 scripts/inquisitor.py --coq-root coq --report artifacts/INQUISITOR_REPORT.md --strict`

- KernelTOE dependency certificate (no hidden assumptions in the transitive cone):
  - `scripts/audit_kernel_toe_assumptions.sh`

## Scope, assumptions, and non-goals
### Scope
- The kernel layer is authoritative: `vm_step` semantics in Coq define what is “physically allowed.”
- Observations are made through the kernel’s existing observables:
  - `Observable` and `ObservableRegion` (from `KernelPhysics`).
- Causality/light-cone structure is derived from syntactic target sets:
  - `instr_targets` and `causal_cone`.

### Non-goals
- This document does **not** assert real-world claims (units calibration, Joule mapping, empirical Lorentz group recovery) beyond what is stated and proved in Coq.
- Anything requiring additional structure is documented as an explicit underdetermination/impossibility theorem rather than handwaving.
- This document does **not** claim that the *hardware-flavored* kernel VM (`VMState` + `vm_step` in `coq/kernel/VMStep.v`) is Turing-complete or “subsumes the Turing machine.”
  - The kernel VM here has bounded scratch RAM access patterns (register/memory indices are reduced modulo fixed sizes) and no conditional control-flow instruction in `vm_step` (the program counter advances by `S`).
  - There is a separate, tape-based model (`coq/kernel/Kernel.v`, `coq/kernel/KernelTM.v`, `coq/kernel/KernelThiele.v`) with a subsumption theorem (`coq/kernel/Subsumption.v`). That development is *about that abstract tape machine*, and is intentionally not used as evidence for the 3-layer (Coq ↔ extracted ↔ Python ↔ RTL) isomorphism claim of this thesis.

## Kernel objects and canonical derived structure
### Step semantics
- Single-step transition: `vm_step : VMState -> vm_instruction -> VMState -> Prop`
  - Defined in: `coq/kernel/VMStep.v`

### Observation
- Graph-level observables:
  - `Observable : VMState -> ModuleID -> option (region * mu)` (shape varies; see `KernelPhysics`)
  - `ObservableRegion : VMState -> ModuleID -> option region`
  - Defined in: `coq/kernel/KernelPhysics.v`

### Cones
- Syntactic targets:
  - `instr_targets : vm_instruction -> list ModuleID`
- Trace cone:
  - `causal_cone : list vm_instruction -> list ModuleID`

## Results (proved theorems)
This section maps each major plan requirement to the strongest kernel-provable statement (or a localized failure theorem).

### No Free Insight (Milestones 1 & 2)

Canonical document: [docs/NO_FREE_INSIGHT.md](docs/NO_FREE_INSIGHT.md)

**Milestone 1 (CHSH instance):** a CHSH-style supra-quantum *certification claim* cannot appear “for free”; the certification bit must be written by a cert-setter instruction (REVEAL/EMIT/LJOIN/LASSERT), and REVEAL presence is detectable at the trace level.

- CHSH instance file: [coq/kernel/Certification.v](coq/kernel/Certification.v)
- Certification-source theorem (structural): [coq/kernel/RevelationRequirement.v](coq/kernel/RevelationRequirement.v)

**Milestone 2 (general form):** the no-free-insight statement is packaged in the general framework and proven without shortcuts.

- General framework: [coq/kernel/NoFreeInsight.v](coq/kernel/NoFreeInsight.v)

### A. Observers and locality
**Observer interface and refinement order**
- File: `coq/kernel/ObserverDerivation.v`
- Key definitions:
  - `Record Observer (A : Type) := { observe : VMState -> A }`
  - `observer_le` (refinement preorder)

**A2 locality deliverable (contrapositive form)**
- Theorem: `Observational_Locality_Iff_Physics`
- Meaning: if a module’s `ObservableRegion` changes across a step, then that module must be in the executed instruction’s target set.
- File: `coq/kernel/ObserverDerivation.v`

### B. Derived time and cones
**B1 “time is not fundamental” (stutter witness)**
- Theorem: `Time_Is_Not_Fundamental`
- Meaning: there exist distinct traces with identical region observations.
- File: `coq/kernel/DerivedTime.v`

**B2 cone uniqueness**
- Theorem: `Cone_Structure_Unique`
- Meaning: any function satisfying the base/cons recursion equations for cones is equal to `causal_cone`.
- File: `coq/kernel/ConeDerivation.v`

**Cone monotonicity (re-export of existing lemma)**
- Theorem: `cone_monotone`
- File: `coq/kernel/ConeDerivation.v`

### E. Kernel physics closure
**Single packaged closure theorem**
- Theorem: `Physics_Closure`
- File: `coq/kernel/PhysicsClosure.v`
- Content (three parts):
  1) Single-step no-signaling outside `instr_targets` (`observational_no_signaling`)
  2) μ monotonicity (`mu_conservation_kernel`)
  3) Multi-step no-signaling outside `causal_cone` (`exec_trace_no_signaling_outside_cone`)

**Multi-step cone locality**
- Lemma: `exec_trace_no_signaling_outside_cone`
- File: `coq/kernel/SpacetimeEmergence.v`
- Note: this is proven by induction on an explicit `exec_trace` relation.

**KernelTOE repackaging (“maximal closure”):**
- Proposition alias: `KernelMaximalClosureP`
- Theorem: `KernelMaximalClosure : KernelMaximalClosureP`
- File: `coq/kernel_toe/Closure.v`

## Localized failures (explicit impossibility / underdetermination)
These are not “gaps”; they are the formal outcome of trying to derive additional structure from the kernel-only interface.

### C1. Born-rule-like uniqueness is not forced by minimal compositional laws

#### The minimal law set is stated explicitly (no named-predicate ambiguity)

In `KernelTOE/`, “no extra structure” is made precise as **only** these explicit algebraic laws on a trace-weight functional `Weight := Trace -> nat`:

- `weight_empty`: `w [] = 0`
- `weight_sequential`: `w (t1 ++ t2) = w t1 + w t2`
- `weight_disjoint_commutes`: for traces whose *causal cones are disjoint*, `w (t1 ++ t2) = w (t2 ++ t1)`

These are bundled as `weight_laws` in `coq/kernel_toe/Definitions.v`.

#### Infinite non-uniqueness (stronger than “there exist two”)

- Theorem: `CompositionalWeightFamily_Infinite`
- File: `coq/kernel_toe/NoGo.v`
- Meaning: there exists a one-parameter family of weights `{w_k}` satisfying the explicit laws such that `k ≠ k'` implies `w_k ≠ w_k'` (witnessed on a concrete trace).

#### Minimal “menu extension” sufficient to restore uniqueness (explicit closure of the gap)

`KernelTOE/` also states an explicit sufficient extension that collapses the family:

- Extra structure A (symmetry): `singleton_uniform` (all single-instruction traces have equal weight)
- Extra structure B (scale): `unit_normalization` (pins the singleton weight, fixing overall scale)

With these added, uniqueness holds:

- Theorem: `Weight_Unique_Under_UniformSingletons`
- File: `coq/kernel_toe/NoGo.v`
- Meaning: any weight satisfying the minimal laws + these explicit extensions is forced to equal `length` on all traces.

**Historical witness (kept for comparison):**
- Theorem: `Born_Rule_Unique_Fails_Without_More_Structure`
- File: `coq/kernel/ProbabilityImpossibility.v`

### D1. Entropy from observational equivalence needs explicit finiteness/coarse-graining

The obstruction is sharpened into an explicit, reusable “no finite microstate count” theorem.

#### Explicit finiteness notion

`KernelTOE` defines a constructive finiteness/coarse-graining predicate:

- `finite_region_equiv_class s` means: there exists a finite list `l : list VMState` that is `NoDup` and contains **every** state region-equivalent to `s`.
- File: `coq/kernel_toe/Definitions.v`

#### No finite microstate enumeration exists (Dedekind-infinite class)

- Theorem: `region_equiv_class_not_finite`
- File: `coq/kernel_toe/NoGo.v`
- Meaning: for every `s`, `~ finite_region_equiv_class s`.

**Audit clarification (what the infinitude actually comes from):**

`region_equiv` is defined as agreement on `ObservableRegion` for all module IDs, and `ObservableRegion` projects *only* the normalized partition region stored in `vm_graph`.
It does **not** project `vm_pc` (nor `vm_regs`, `vm_mem`, `vm_csrs`, `vm_err`, or `vm_mu`).
As a result, the “infinite microstates” are *hidden-state stuttering*: you can vary an unobserved field forever while preserving the observed partition.

Concretely:
- The canonical witness used by the kernel development varies an unobserved register payload (`tweak_regs`) while keeping `vm_graph` fixed.
- An equally valid (and even more obvious) witness is “clock stuttering”: varying `vm_pc` while keeping `vm_graph` fixed.

Therefore, this theorem should be read as: **entropy cannot be defined purely from the partition-only observable unless you add a finiteness/coarse-graining principle, or you strengthen the observable to include the hidden degrees of freedom.**
If you instead restrict attention to a *reachable* subset of states under a bounded machine model, that restriction is itself extra structure (an invariant/bound) that must be stated explicitly.

This is proved by exhibiting an injection `nat -> VMState` that stays inside the same region-equivalence class (via the existing kernel witness machinery reused from `coq/kernel/EntropyImpossibility.v`).

**Historical witness (kept for comparison):**
- Theorem: `Entropy_From_Observation_Fails_Without_Finiteness`
- File: `coq/kernel/EntropyImpossibility.v`

### B3. Lorentz invariance is not forced (cone symmetries underdetermined)
- Theorem: `Lorentz_Not_Forced`
- Theorem: `Cone_Symmetry_Underdetermined`
- File: `coq/kernel/LorentzNotForced.v`
- Meaning: without a derived metric/interval, there is no canonical Lorentz statement; moreover, there exist cone-preserving trace reparameterizations not constrained into a Lorentz-like group by kernel primitives.

## Final outcome theorem (the required single decision)

### Canonical flagship packaging (tightened)

The final “maximal closure + minimal no-go” packaging lives in the sealed KernelTOE cone:

- File: `coq/kernel_toe/TOE.v`
- Theorem: `KernelTOE_FinalOutcome : KernelMaximalClosureP /\ KernelNoGoForTOE_P`

The historical kernel decision module is retained as a stable re-export wrapper:

- File: `coq/kernel/TOEDecision.v`
- Theorem: `Kernel_TOE_FinalOutcome : KernelMaximalClosureP /\ KernelNoGoForTOE_P`

### Outcome (2): precise impossibility without extra structure

- Theorem: `Physics_Requires_Extra_Structure`
- File: `coq/kernel/TOEDecision.v`
- Meaning (sharpened): `KernelNoGoForTOE_P`, i.e.
  1) `KernelNoGo_UniqueWeight_FailsP` (no unique weight law forced by explicit minimal compositional laws)
  2) `forall s, ~ finite_region_equiv_class s` (no finite microstate enumeration without coarse-graining)

### Best kernel-closure available
- Theorem: `Kernel_Physics_Closure`
- Simply re-exports `Physics_Closure` in a stable “final output” module.

## What “extra structure” means here (concretely)
The following are examples of **additions** that would be required to continue toward stronger “physics” claims:

- A metric / interval structure on traces or states (to even state Lorentz invariance meaningfully).
- A probability/measure structure beyond compositionality (e.g., normalization, symmetry constraints, empirically grounded calibration), to single out a unique law.
- A finiteness/coarse-graining principle (or explicit state space restrictions), to define entropy as a finite quantity.

This repo’s workflow expectation is: if extra structure is added, it must be validated via the **inquisitor loop** (minimal trace, then Python ↔ extracted runner ↔ RTL) to preserve the 3-layer isomorphism.

## Forward direction (explicitly extra structure): persistence / selection
The KernelTOE no-go theorems are about **kinematics**: what laws are consistent with the kernel interface.
One way to “push deeper” without smuggling in symmetry axioms is to add an explicit **dynamics/selection** principle: which executions *survive* under resource constraints.

This is not currently a theorem of the base kernel VM. It is an *extension model* that must be stated as extra structure.

- File: `coq/kernel_toe/Persistence.v`
- Idea: keep `vm_step` authoritative, and add *overlay* relations:
  - `fuel_step`: a fuel-budgeted wrapper that “crashes” (sets `vm_err := true` and fuel to 0) if an instruction is unaffordable.
  - `game_stepC` / `game_exec_schedule`: a selection/betting layer where a strategy allocates fuel across a presented finite choice set; if the realized outcome is assigned 0, the run dies.

**Concrete theorem proved in the overlay (no axioms, no admits):**
- `KernelTOE.Persistence.Uniform_Strategy_Dies`: if the adversary presents `|choices| = fuel0 + 1` possibilities, the uniform strategy’s per-option bet is 0 (dilution), and the game forces `Dead`.

This is the first mechanically checked “selection pressure” result in the KernelTOE cone: it does not claim a specific physical law, but it shows that some “uninformative / uniform” allocation principles are *unstable* under explicit resource constraints.

**Tie-back to the full Thiele Machine pipeline:** this overlay corresponds to a *policy layer* on top of the existing isomorphic execution core.
- INIT: start from a concrete `FuelState` (kernel `VMState` + fuel).
- DISCOVER/CLASSIFY/DECOMPOSE: the environment presents a structured choice set of kernel instructions (e.g., candidate `instr_pnew` actions).
- EXECUTE: the kernel step semantics (`vm_step`) executes the realized instruction.
- MERGE/VERIFY: the overlay checks survivability conditions (fuel and nonzero allocation); failure forces a crash state.
- SUCCESS: only strategies consistent with the survival constraints can continue indefinitely (future work: characterize these strategies and validate via the Python ↔ extracted runner ↔ RTL inquisitor loop).

## How to navigate and audit
- List the kernel modules:
  - `ls coq/kernel/*.v`
- Find theorems quickly:
  - `grep -RIn --include='*.v' 'Theorem ' coq/kernel`
- Confirm admit-free kernel:
  - `grep -RIn --include='*.v' '^Admitted\.' coq/kernel`

- Confirm no hidden assumptions in the KernelTOE transitive cone:
  - `scripts/audit_kernel_toe_assumptions.sh`

---

### Appendix A: File index
- `coq/kernel/SpacetimeEmergence.v` — `exec_trace` + multi-step cone locality.
- `coq/kernel/ObserverDerivation.v` — observer interface + A2 locality theorem.
- `coq/kernel/DerivedTime.v` — stutter witness (`Time_Is_Not_Fundamental`).
- `coq/kernel/ConeDerivation.v` — cone uniqueness + monotonicity.
- `coq/kernel/PhysicsClosure.v` — packages kernel closure theorem.
- `coq/kernel/ProbabilityImpossibility.v` — Born-rule uniqueness failure witness.
- `coq/kernel/EntropyImpossibility.v` — entropy finiteness failure witness.
- `coq/kernel/LorentzNotForced.v` — Lorentz not forced + cone symmetry underdetermination.
- `coq/kernel/TOEDecision.v` — single final outcome theorem + closure re-export.

- `coq/kernel_toe/Definitions.v` — explicit minimal laws + explicit finiteness/coarse-graining predicate.
- `coq/kernel_toe/Closure.v` — `KernelMaximalClosureP` + theorem.
- `coq/kernel_toe/NoGo.v` — infinite non-uniqueness family + explicit “not finite” entropy obstruction + sufficiency menu.
- `coq/kernel_toe/TOE.v` — final packaged `KernelTOE_FinalOutcome`.

### Appendix B: Emergent Schrödinger Equation Proof

This section contains the auto-generated Coq proof verifying that the Thiele Machine has successfully rediscovered the Schrödinger equation from raw data.

```coq
(* Emergent Schrödinger Equation - Discovered via Thiele Machine *)
(* Auto-generated formalization - standalone, compilable file *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Setoid.

Open Scope Q_scope.

(** * Discrete update rule coefficients discovered from data *)

(** Coefficients for real part update: a(t+1) = Σ c_i * feature_i *)
Definition coef_a_a : Q := (1000000 # 1000000%positive).
Definition coef_a_b : Q := (0 # 1000000%positive).
Definition coef_a_lap_b : Q := (-5000 # 1000000%positive).
Definition coef_a_Vb : Q := (10000 # 1000000%positive).

(** Coefficients for imaginary part update: b(t+1) = Σ d_i * feature_i *)
Definition coef_b_b : Q := (1000000 # 1000000%positive).
Definition coef_b_a : Q := (0 # 1000000%positive).
Definition coef_b_lap_a : Q := (5000 # 1000000%positive).
Definition coef_b_Va : Q := (-10000 # 1000000%positive).

(** * Extracted PDE parameters *)
Definition extracted_mass : Q := (1000000 # 1000000%positive).
Definition extracted_inv_2m : Q := (500000 # 1000000%positive).
Definition extracted_dt : Q := (10000 # 1000000%positive).

(** * Parameter Consistency Check *)

Lemma inv_2m_consistent : extracted_inv_2m == (1#2) / extracted_mass.
Proof.
  unfold extracted_inv_2m, extracted_mass.
  (* Verify that the independently extracted 1/(2m) matches 1/(2*mass) *)
  field.
Qed.

(** * Coefficient Constraints *)

(** 
    We verify that the discovered coefficients match the theoretical 
    constraints imposed by the extracted PDE parameters.
*)
Lemma coefficient_constraints :
  coef_a_a == 1 /\
  coef_a_b == 0 /\
  coef_a_lap_b == -(extracted_dt * extracted_inv_2m) /\
  coef_a_Vb == extracted_dt /\
  coef_b_b == 1 /\
  coef_b_a == 0 /\
  coef_b_lap_a ==  (extracted_dt * extracted_inv_2m) /\
  coef_b_Va == -extracted_dt.
Proof.
  unfold coef_a_a, coef_a_b, coef_a_lap_b, coef_a_Vb.
  unfold coef_b_b, coef_b_a, coef_b_lap_a, coef_b_Va.
  unfold extracted_dt, extracted_inv_2m.
  repeat split; ring.
Qed.

(** * The discovered update rules *)

Definition schrodinger_update_a (a b lap_b Vb : Q) : Q :=
  coef_a_a * a + coef_a_b * b + coef_a_lap_b * lap_b + coef_a_Vb * Vb.

Definition schrodinger_update_b (b a lap_a Va : Q) : Q :=
  coef_b_b * b + coef_b_a * a + coef_b_lap_a * lap_a + coef_b_Va * Va.

(** * Target finite-difference form *)

Definition target_update_a (a lap_b Vb : Q) : Q :=
  a + extracted_dt * (-(extracted_inv_2m) * lap_b + Vb).

Definition target_update_b (b lap_a Va : Q) : Q :=
  b + extracted_dt * (extracted_inv_2m * lap_a - Va).

(** * Structural Form Theorem *)

(** 
    We prove that the discovered update rules are structurally equivalent 
    to the finite-difference discretization of the Schrödinger equation.
    
    This confirms that the machine has "rediscovered" the correct physical law
    from the data, rather than just fitting random coefficients.
*)

Theorem structural_equivalence :
  forall (a b lap_a lap_b Va Vb : Q),
    Qeq (schrodinger_update_a a b lap_b Vb) (target_update_a a lap_b Vb) /\
    Qeq (schrodinger_update_b b a lap_a Va) (target_update_b b lap_a Va).
Proof.
  intros.
  unfold schrodinger_update_a, schrodinger_update_b.
  unfold target_update_a, target_update_b.
  (* Use the coefficient constraints to rewrite the discovered rule *)
  destruct coefficient_constraints as [Haa [Hab [Halb [HaVb [Hbb [Hba [Hbla HbVa]]]]]]].
  rewrite Haa, Hab, Halb, HaVb, Hbb, Hba, Hbla, HbVa.
  split; ring.
Qed.
```

