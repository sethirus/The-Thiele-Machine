# Proof Bedrock Strengthening Audit

Date: 2026-04-22
Scope: foundation-tier kernel proofs and direct strengthening path
Primary files: `coq/kernel/MuLedgerConservation.v`, `coq/kernel/MuCostModel.v`, `coq/kernel/VMStep.v`, `coq/kernel/SimulationProof.v`

## 1. Purpose

This file does one job.

It explains, in plain language and formal language, what is already proven, what is only partially strengthened, and what can still be tightened without pretending there are gaps where there are none.

For each concept and theorem block, this audit gives:

1. Concept definition
2. Formal object in the repo
3. Assumptions
4. What is proven now
5. What is not proven yet
6. Falsification condition
7. Concrete strengthening action

## 2. Core Terms (No Ambiguity)

### 2.1 Bedrock

Concept:
The lowest layer you can reduce a proof to without changing the model.

Formal meaning in this repo:
A theorem is at bedrock when its dependencies are only VM semantics, cost semantics, and standard library machinery needed to express those semantics.

Not the same thing:
Bedrock is not "perfect forever". Bedrock is a current closure statement under named assumptions.

### 2.2 Assumption Chain

Concept:
The dependency path from a theorem to primitives it relies on.

Formal meaning:
Imports, definitions, lemmas, and any explicit assumptions used by a theorem proof term.

Falsification condition:
If a theorem claims "no local assumptions" and `Print Assumptions` shows local axioms/parameters/hypotheses, the claim is false.

### 2.3 Strengthening

Concept:
Make a theorem strictly sharper without changing the VM meaning.

Examples:
- replace inequality with equality
- replace existence-only statement with quantitative bound
- replace implicit coupling with explicit construction

Not strengthening:
Rewording comments or renaming symbols is not strengthening.

### 2.4 Trust Boundary

Concept:
A place where correctness depends on something outside the proven kernel.

In this repo:
- extraction/compiler behavior
- external toolchain behavior
- proof assumptions outside the local kernel scope

## 3. Current Foundation Status

### 3.1 VM semantics relation status

Claim:
`vm_step` and `vm_apply` relation was previously listed as an open concern.

Current fact:
`SimulationProof.v` already contains `vm_step_vm_apply` and uses it in determinism arguments.

Meaning:
Do not treat "vm_step vs vm_apply equivalence" as a remaining primary gap.

### 3.2 NoFI step predicate status

Claim:
`nofi_step_always_ok` looked vacuous.

Current fact:
In `VMStep.v`, this is intentional and proven from cost construction:
- cert-setter instructions have cost >= 1 (`cert_setter_cost_pos`)
- non-cert-setters are unconstrained by that check
- therefore the boolean check is always true by construction

Meaning:
This is a design encoding theorem, not a runtime filter theorem.

## 4. Theorem Audit: `MuLedgerConservation.v`

### 4.1 `bounded_run_head`

Concept:
Every bounded run list has a first state.

Formal object:
`forall fuel trace s, exists rest, bounded_run fuel trace s = s :: rest`

Assumptions:
- recursive definition of `bounded_run`
- list lookup behavior (`nth_error`)

Proven now:
Head existence for all fuels.

Not proven yet:
Tight run length bounds in the same theorem statement.

Falsification condition:
A counterexample trace/fuel/state where `bounded_run fuel trace s` is `[]`.

Strengthening action:
Add explicit bounds:
- length >= 1
- length <= fuel + 1

### 4.2 `vm_apply_mu`

Concept:
One step increases mu by exactly that instruction's cost.

Formal object:
`(vm_apply s instr).(vm_mu) = s.(vm_mu) + instruction_cost instr`

Assumptions:
- totality of `vm_apply`
- totality of `instruction_cost`
- nat arithmetic

Proven now:
Exact single-step equality.

Not proven yet:
A fully parameterized version over arbitrary cost model function in this same layer.

Falsification condition:
Any instruction constructor where equality does not reduce.

Strengthening action:
Introduce generic cost model lemma and equivalence bridge to canonical `instruction_cost`.

### 4.3 `vm_step_respects_mu_ledger`

Concept:
Relational step and ledger conservation agree for one-step traces.

Formal object:
`vm_step s instr s' -> ledger_conserved [s; s'] [instruction_cost instr]`

Assumptions:
- `vm_step` semantics
- `instruction_cost` semantics

Proven now:
One-step ledger conservation witness.

Not proven yet:
A direct theorem that packages arbitrary trace conservation without intermediate unpacking in user proofs.

Falsification condition:
A valid `vm_step` where two-state ledger is not conserved.

Strengthening action:
Add convenience trace theorem that composes one-step conservation directly for full runs.

### 4.4 `run_vm_mu_monotonic`

Concept:
mu never decreases along run.

Formal object:
`run_vm fuel trace s = s' -> s.(vm_mu) <= s'.(vm_mu)`

Assumptions:
- single-step exact cost
- nat non-negativity

Proven now:
Monotonicity.

Not proven yet:
Direct equality with explicit summed executed costs in this theorem name.

Falsification condition:
A run where final mu < initial mu.

Strengthening action:
Add exact increment theorem for run-level cost decomposition using ledger entries.

### 4.5 `bounded_model_mu_ledger_conservation`

Concept:
Run states and ledger entries are jointly conserved.

Formal object:
`exists states entries, bounded_run = states /\ ledger_entries = entries /\ ledger_conserved states entries`

Assumptions:
- shared recursion shape for `bounded_run` and `ledger_entries`

Proven now:
Existential coupling with conservation proof.

Not proven yet:
By-construction coupling via one unified runner that returns both states and entries.

Falsification condition:
A fuel/trace/state where the produced pair fails `ledger_conserved`.

Strengthening action:
Define unified fixpoint returning `(states, entries)`, then prove projection equivalence.

## 5. Theorem Audit: `MuCostModel.v`

### 5.1 `partition_ops_mu_free`

Concept:
Some partition ops are zero-cost under zero delta.

Formal object:
`mu_cost_of_instr (instr_pnew mid 0) s = 0`

Proven now:
Definitional zero-cost case.

Not proven yet:
A normalized family theorem for all partition-op constructors and delta behavior.

Strengthening action:
Add family-level theorem classifying each partition opcode cost equation.

### 5.2 `reveal_cost_positive`

Concept:
Reveal cannot be free.

Formal object:
`mu_cost_of_instr (instr_reveal mid bits cert mu) s >= 1`

Proven now:
Strict positivity lower bound.

Not proven yet:
Same theorem with exact arithmetic expansion as primary form (instead of lower bound first).

Strengthening action:
Add exact formula theorem and derive positivity as corollary.

## 6. Theorem Audit: `VMStep.v`

### 6.1 `cert_setter_cost_pos`

Concept:
Every cert-setter is guaranteed positive cost.

Formal object:
`is_cert_setterb instr = true -> instruction_cost instr >= 1`

Proven now:
Global positivity for cert-setter class.

Not proven yet:
Per-opcode lower-bound table theorem exposed as one consolidated interface.

Strengthening action:
Add theorem bundle with one bound lemma per cert-setter constructor.

### 6.2 `nofi_step_always_ok`

Concept:
Boolean policy checker returns true for all instructions because policy is encoded in costs, not checked dynamically.

Formal object:
`forall instr, nofi_step_cost_okb instr = true`

Proven now:
Always true by construction.

What this does not mean:
It does not mean NoFI is weak.
It means the ISA encoding already enforces the policy.

Strengthening action:
Keep theorem as-is, but rename/expose companion explanatory lemma so readers do not mistake it for a vacuous bug.

## 7. Cross-Layer Boundaries (Explicit)

### 7.1 Closed concerns

1. `vm_step` and `vm_apply` relation concern is closed at kernel layer via `vm_step_vm_apply`.
2. Foundation theorems listed above are sound in current scope.

### 7.2 Open but bounded concerns

1. Exact run-level quantitation can still be surfaced in stronger user-facing theorems.
2. Unified state+ledger construction can reduce proof friction.
3. Cost parameterization remains an extensibility step, not a correctness emergency.

### 7.3 Out-of-scope concerns for this file

1. External extraction/compiler internal soundness.
2. Toolchain-level correctness outside Coq kernel.
3. Physics interpretation claims beyond formal theorem statements.

## 8. Roadmap (Corrected)

### Phase 1: Exact run-level quantitation (1 day)

Deliverables:
1. Add run-level exact increment theorem from ledger sum.
2. Keep monotonic theorem as corollary.

Pass condition:
All existing proofs compile and exact theorem used in at least one downstream bridge file.

### Phase 2: Unified run+ledger constructor (1-2 days)

Deliverables:
1. New unified fixpoint returning `(states, entries)`.
2. Projection lemmas to preserve compatibility.

Pass condition:
`bounded_model_mu_ledger_conservation` can be reproved using projections from unified function.

### Phase 3: Cost model parameterization (2-3 days)

Deliverables:
1. generic cost function theorem family
2. substitutability theorem against canonical cost

Pass condition:
At least one non-canonical cost model instance compiles against same theorem skeleton.

### Phase 4: Theorem interface cleanup (0.5-1 day)

Deliverables:
1. expose per-opcode bound bundle for cert-setters
2. explain/alias `nofi_step_always_ok` intent in proof comments

Pass condition:
No ambiguity in proof API about "always_ok" meaning.

## 9. Falsification Checklist

Use this checklist after each phase.

1. Kernel compile gate fails if any theorem statement is broken.
2. Assumption gate fails if prohibited trust-escape patterns are introduced in critical files.
3. Parity/extraction tests fail if semantics drift.
4. Audit scripts must regenerate without path errors.

If all four remain green, the strengthening changed structure without regressing trust profile.

## 10. Bottom Line

Current state:
Foundation is sound and the major previously suspected `vm_step`/`vm_apply` concern is already resolved in code.

Remaining work:
Mostly theorem sharpening and proof-interface cleanup, not emergency correctness repair.

Meaning:
There is still work left to prove stronger forms, but the current bedrock is real and bounded, not hand-wavy.
