# No Free Insight (Kernel Semantics)

**Last Reviewed**: January 4, 2026

This is the **single canonical document** for the No Free Insight result.

It contains:
1) Axioms / definitions / theorem statement (compact)
2) A human-readable proof sketch
3) A mapping to the exact Coq files and symbols witnessing each lemma

---

## 0. Abstract No Free Insight (limit theorem template)

This section is **system-agnostic**: no VM nouns, no CHSH, no μ, no code references.

### Objects

- A system executes from an initial state to a final state, producing an **execution trace** $\tau$.
- There is an **observable record** $\mathsf{obs}(s)$ derived from a state $s$.
- A **claim** is an acceptance predicate $P$ that depends only on the observable record: $P(\mathsf{obs}(s))$.
- There is a notion of **strict strengthening** $P_\text{strong} < P_\text{weak}$ meaning:
  - $\forall o,\; P_\text{strong}(o) \Rightarrow P_\text{weak}(o)$, and
  - $\exists o,\; P_\text{weak}(o) \wedge \neg P_\text{strong}(o)$.
- The system has a **certification marker** $\mathsf{cert}(s)$ (a bit/flag/token inside the state) indicating that a claim is certified.
- A **structure-adding event** is any trace event from a distinguished class $\mathcal{S}$ whose purpose is to introduce discriminative structure that is not obtainable from observation alone.

### Theorem (No Free Insight, abstract schema)

If, starting from an uncertified initial state, the system reaches a final state where a strictly stronger claim is certified, then the trace must contain a structure-adding event:

$$
\big(\mathsf{cert}(s_\text{init}) = \mathsf{false}\big)\;\wedge\;\big(\mathsf{cert}(s_\text{final}) = \mathsf{true}\big)\;\wedge\;\big(P_\text{strong} < P_\text{weak}\big)
\;\Rightarrow\;
\exists i,\; \tau[i] \in \mathcal{S}.
$$

### Corollary (Explanation is not observation)

Certification of stronger claims cannot be justified by observation alone: some explicit structure-adding act must occur in the execution history.

---

## 1. Thiele Machine kernel instantiation (what is proved here)

- **Layer:** Coq kernel semantics is authoritative.
- **Model:** a finite instruction list (called a “trace/program”) and bounded execution by fuel.
- **What this theorem guarantees (today):** certification cannot appear “for free”; it must be caused by an explicit **cert-setter opcode**.

This is intentionally a **structural kernel theorem**, not (yet) a quantitative μ lower bound theorem.

---

## 2. Axioms (project narrative) and kernel witnesses

These are the intended A1–A4 meta-assumptions used in the narrative. The core theorem itself relies on the step semantics and the definition of certification in CSRs; the items below are provided as explicit project context.

### A1 — Non-forgeability of receipts

Informal: user code cannot fabricate receipt constructors; receipts correspond to actual executed opcodes.

Kernel witness:
- The trace is a typed list of constructors (`vm_instruction`). `instr_pyexec` is just one constructor; it cannot fabricate other constructors.

### A2 — μ monotonicity / conservation

Informal: information accounting never decreases, and μ deltas match declared instruction costs.

Kernel witnesses:
- Single-step µ update inside `advance_state` / `apply_cost`.
- Ledger conservation theorem `run_vm_mu_conservation`.

### A3 — Locality / no-signaling

Informal: modules not targeted by an instruction cannot have their observable region changed.

Kernel witnesses:
- Single-step no-signaling outside `instr_targets`.
- Multi-step no-signaling outside the trace `causal_cone`.

### A4 — Underdetermination

Informal: observation alone does not force unique probability/entropy structure.

Kernel witnesses:
- A minimal no-go for “Born-rule-like uniqueness” without extra structure.
- An “entropy-from-observation” failure without finiteness/coarse-graining.

---

## 3. Definitions (the ones used by the theorem)

Let `Trace := list vm_instruction`.

### Bounded execution

`trace_run fuel trace s_init = Some s_final`

`trace_run` uses the program counter (`vm_pc`) to index into the instruction list.

### Certification bit

`has_supra_cert s := (csr_cert_addr s.(vm_csrs)) <> 0`

In Milestone 2’s packaged framework, “Certified” is strengthened to include this bit, i.e.
certification means **both** “no error” and “cert bit written” and “predicate holds on decoded observations”.

### Reveal detection

`uses_revelation trace` is a list scan for an instruction of the form `instr_reveal _ _ _ _`.

---

## 4. Theorem statement (kernel-level No Free Insight)

### Theorem (structural “no free certification”)

If:

1. `trace_run fuel trace s_init = Some s_final`
2. `csr_cert_addr s_init = 0`
3. `has_supra_cert s_final`

Then at least one cert-setter instruction must appear in the trace:

- `uses_revelation trace`
  **or** the trace contains one of the other cert-setting opcodes at some index:
  - `instr_emit ...`
  - `instr_ljoin ...`
  - `instr_lassert ...`

Interpretation:

> Certification cannot appear without an explicit cert-setting opcode.

This is the kernel form of “No Free Insight”: a certification claim requires an explicit, observable cause in the trace.

### Milestone 2 (strengthening form)

Milestone 2 adds an abstract receipt-predicate framework (strength ordering and decoder-based certification) packaged in the kernel as:

- `ReceiptPredicate`, `stronger`, `strictly_stronger`, `Certified`

and the following theorem:

> If `P_strong < P_weak` and the machine **certifies** `P_strong` starting from `csr_cert_addr = 0`, then the trace contains a **structure-addition** event.

At the kernel layer, “structure-addition” is defined as the trace containing a **cert-setter opcode** (`REVEAL`, `EMIT`, `LJOIN`, or `LASSERT`).

Important nuance:

- The *structural* “no free certification” property does **not** fundamentally depend on strict strengthening; it depends on the CSR cert-bit semantics.
- The strict-strengthening relation (`P_strong < P_weak`) is part of the *interface* for expressing “stronger claims”, but it does not (yet) drive a separate kernel theorem about epistemic refinement over time.

---

## 5. Proof sketch (human-readable)

### High-level idea

Certification (`csr_cert_addr`) is part of the machine state. Under the kernel semantics, only a small set of instructions is allowed to write it.

Therefore, if we start with `csr_cert_addr = 0` and end with `csr_cert_addr <> 0`, then **somewhere during execution** we must have executed a cert-setter instruction.

### The actual induction

The formal proof proceeds by induction on `fuel`, following the recursive definition of `trace_run`.

At each step:

1. We index into the trace/program using the current `vm_pc`.
2. If there is no instruction (`nth_error = None`), then `trace_run` stops and returns the current state. A non-zero cert address cannot suddenly appear in that case.
3. If there is an instruction, we case split by opcode:
   - For *non-cert-setter* opcodes, we show they do not create certification and then apply the induction hypothesis to the rest of the run.
   - For *cert-setter* opcodes, we conclude immediately:
     - `instr_reveal` gives `uses_revelation trace`
     - `instr_emit`, `instr_ljoin`, `instr_lassert` give the corresponding existential “appears at some index” witness.

This is a purely semantic argument: it does not rely on probability, entropy, or any runtime policy.

### Where the “strengthening” assumption enters

Milestone 2 adds an abstract interface for receipt predicates and a strict-strengthening relation (`P_strong < P_weak`).

The kernel theorem does not attempt to formalize “epistemic strengthening over time” (which would require modeling an agent that first accepts `P_weak` and later demands `P_strong` under the same observation). Instead, the strengthening-form theorem packages:

1) the abstract predicate framework, and
2) the kernel structural fact that any *certification* must be caused by a cert-setter opcode,

into a single admit-free statement.

### CHSH specialization (Milestone 1)

The CHSH development defines a decoder that extracts CHSH trials by scanning the trace for `instr_chsh_trial` constructors with a bit-check.

Then a CHSH “supra certified” predicate requires:

- there exists at least one CHSH trial in the trace, and
- the certification CSR is non-zero.

Applying the kernel theorem above yields: if a trace ends with certification set, it must have used a cert-setter opcode.

Runtime policy may further require that the cert-setter be `REVEAL` specifically; that is deliberately treated as policy, not as the kernel theorem.

---

## 6. Coq witness map (symbols → files)

### Core kernel objects

- Instruction datatype: `VMStep.vm_instruction` in [coq/kernel/VMStep.v](../coq/kernel/VMStep.v)
- Cost function: `VMStep.instruction_cost` in [coq/kernel/VMStep.v](../coq/kernel/VMStep.v)
- Small-step relation: `VMStep.vm_step` in [coq/kernel/VMStep.v](../coq/kernel/VMStep.v)
- Executable step function: `vm_apply` in [coq/kernel/SimulationProof.v](../coq/kernel/SimulationProof.v)

### Structural kernel theorem (the proved No Free Insight statement)

- Bounded runner: `RevelationProof.trace_run` in [coq/kernel/RevelationRequirement.v](../coq/kernel/RevelationRequirement.v)
- Reveal detection: `RevelationProof.uses_revelation` in [coq/kernel/RevelationRequirement.v](../coq/kernel/RevelationRequirement.v)
- Cert predicate: `RevelationProof.has_supra_cert` in [coq/kernel/RevelationRequirement.v](../coq/kernel/RevelationRequirement.v)
- Main theorem:
  - `RevelationProof.nonlocal_correlation_requires_revelation` in [coq/kernel/RevelationRequirement.v](../coq/kernel/RevelationRequirement.v)
  - Alias `RevelationProof.cert_setter_necessary_for_supra` in the same file

### Milestone 1 (CHSH instance)

- Trial extraction:
  - `CertificationTheory.is_chsh_trial_instr` in [coq/kernel/Certification.v](../coq/kernel/Certification.v)
  - `CertificationTheory.extract_chsh_trials` in [coq/kernel/Certification.v](../coq/kernel/Certification.v)
- Non-forgeability of extracted trials:
  - `CertificationTheory.chsh_trials_non_forgeable` in [coq/kernel/Certification.v](../coq/kernel/Certification.v)
- CHSH theorem (applies the structural theorem):
  - `CertificationTheory.no_free_insight_chsh` in [coq/kernel/Certification.v](../coq/kernel/Certification.v)

### Milestone 2 (general packaging)

- Framework definitions:
  - `NoFreeInsight.ReceiptPredicate`, `NoFreeInsight.stronger`, `NoFreeInsight.strictly_stronger`, `NoFreeInsight.Certified`
  - in [coq/kernel/NoFreeInsight.v](../coq/kernel/NoFreeInsight.v)
- Packaged theorem:
  - `NoFreeInsight.no_free_insight_general` in [coq/kernel/NoFreeInsight.v](../coq/kernel/NoFreeInsight.v)

- Strengthening-form theorem (Milestone 2):
  - `NoFreeInsight.strengthening_requires_structure_addition` in [coq/kernel/NoFreeInsight.v](../coq/kernel/NoFreeInsight.v)

- Supporting glue lemmas used by Milestone 2 packaging:
  - `NoFreeInsight.trace_run_run_vm`
  - `NoFreeInsight.uses_revelation_implies_nth_error_reveal`
  - `NoFreeInsight.cert_setter_disjunction_implies_structure_addition`
  - all in [coq/kernel/NoFreeInsight.v](../coq/kernel/NoFreeInsight.v)

### Supporting “axioms” (optional context)

- μ conservation: `run_vm_mu_conservation` in [coq/kernel/MuLedgerConservation.v](../coq/kernel/MuLedgerConservation.v)
- Closure/locality:
  - `Physics_Closure` in [coq/kernel/PhysicsClosure.v](../coq/kernel/PhysicsClosure.v)
  - `exec_trace_no_signaling_outside_cone` in [coq/kernel/SpacetimeEmergence.v](../coq/kernel/SpacetimeEmergence.v)
- Underdetermination witnesses:
  - `Born_Rule_Unique_Fails_Without_More_Structure` in [coq/kernel/ProbabilityImpossibility.v](../coq/kernel/ProbabilityImpossibility.v)
  - `Entropy_From_Observation_Fails_Without_Finiteness` in [coq/kernel/EntropyImpossibility.v](../coq/kernel/EntropyImpossibility.v)

---

## 7. Verification commands

- Inquisitor (no admits/axioms):
  - `python scripts/inquisitor.py`
- Coq build:
  - `make -C coq core`

---

## 8. What remains to be done

This repo enforces “no shortcuts” (no `Admitted.`, no `admit.`, no `Axiom`). Within that constraint, the remaining work is about **strengthening the theorem statement** (not weakening proof standards).

### A. Make the strengthening story fully semantic (A4 bridge)

Milestone 2 currently provides a strict-strengthening *interface* (`P_strong < P_weak`) and a packaged theorem that a certified stronger claim implies a cert-setter opcode exists.

What is still missing for the original narrative statement (“you can’t tighten acceptance without paying for discriminative structure”) is a precise kernel-level formalization of:

- what it means for an observer/agent to *start* accepting `P_weak` and later demand `P_strong`, and
- how A4 underdetermination constrains that refinement when the observer is restricted to partition-only observables.

That will likely require introducing an explicit notion of **observer knowledge state / acceptance policy** and proving a refinement impossibility theorem against that model.

### B. Quantitative μ lower bound for certification

Today’s kernel theorem is structural: “cert bit implies cert-setter opcode exists.”

To obtain a quantitative statement (“certification costs at least $k$ μ-bits”), we need a theorem that connects:

- execution *at a particular PC step* of a cert-setter opcode, to
- a lower bound on μ increase across the run.

This can be done by combining (i) an executed-step witness (e.g. derived from `trace_run` recursion / `nth_error trace (vm_pc s)` at that step) with (ii) μ-ledger conservation (`run_vm_mu_conservation`) and a lemma that the relevant `instruction_cost` is strictly positive.

### C. REVEAL-only requirement (policy vs theorem)

The kernel theorem allows `EMIT/LJOIN/LASSERT` as alternative cert setters.

If the project wants “supra-CHSH certification must use REVEAL specifically”, that is either:

- a **policy gate** (proved/validated elsewhere and enforced in runtime tests), or
- a new kernel theorem requiring additional assumptions that rule out the other channels.

### D. CHSH computation in Coq (optional strengthening)

The CHSH instance in Coq currently uses a simplified “supra certified” predicate rather than a full formalization of the $S$ statistic over a probability distribution of trials.

Formalizing the full CHSH computation (and linking it to a runtime CSV/probability table) would strengthen the end-to-end story, but it is not necessary for the structural “no free certification” theorem.
---

## Related Documentation

- [HONEST_TRUTH.md](HONEST_TRUTH.md) — Current state and test status
- [THEOREMS.md](THEOREMS.md) — All proven theorems including Initiality (Thm 6) and Necessity (Thm 7)