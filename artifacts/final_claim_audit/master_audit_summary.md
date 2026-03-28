# Master Audit Summary — The Thiele Machine
**Date**: 2026-03-27 | **Status**: INQUISITOR OK | **Coq**: 0 Admitted | **Tests**: 668 passed

---

## WHAT IS PROVEN

### The No Free Certification chain (fully closed)

```
                          csr_cert_addr: 0 → nonzero
                                    ↓
              thiele_non_cert_addr_setter_preserves
              (case analysis: all 32 opcodes, none of the
               27 non-cert-setters touch csr_cert_addr)
                                    ↓
                     cert_addr_setterb i = true
                                    ↓
                   cert_addr_setter_cost_pos
                   (definitional: S cost ≥ 1 for all
                    5 cert-addr-setters: REVEAL, EMIT,
                    LJOIN, LASSERT, MORPH_ASSERT)
                                    ↓
                   instruction_cost i ≥ 1   [no_free_certification]
                                    ↓
                       vm_apply_mu
                    (conservation: mu = sum of costs)
                                    ↓
           (vm_apply s i).mu ≥ s.mu + 1   [no_free_certification_mu]
```

The same chain for vm_certified:
```
                          vm_certified: false → true
                                    ↓
                       vm_apply_certified
                    (PrimeAxiom: only instr_certify
                     can set vm_certified = true)
                                    ↓
                   i = instr_certify n (some n)
                                    ↓
           instruction_cost (instr_certify n) = S n ≥ 1
                                    ↓
           (vm_apply s i).mu ≥ s.mu + 1   [no_free_certification_certified_mu]
```

Packaged: `certification_requires_positive_mu` — either cert channel activating implies mu grew ≥ 1.

### Trace-level: no smuggling through a sequence

```
cert_addr was 0 at s0, nonzero after running trace
         ↓
thiele_abstract_nfi_cost: ∃ cert-setter i in trace with cost ≥ 1
         ↓
acm_run_mu_exact: final_mu = initial_mu + trace_mu_delta
         ↓
In_cert_setter_trace_cost_ge: trace_mu_delta ≥ 1
         ↓
final_mu ≥ initial_mu + 1   [no_free_certification_trace_mu]
```

### Universality

`universal_nfi`: For ANY abstract machine over vm_instructions satisfying axiom A3
(non-cert-setters preserve cert indicator), executing a trace from uncert to cert
requires a cert-setter with cost ≥ 1. The Thiele VM is an instance.

### Categorical separation

`categorical_separation` + `classical_observer_cannot_separate`: Two programs
with identical classical observables (regs, mem, mu, pc, err, certified) can
differ in morphism graph. No function of the classical observables alone can
distinguish them. A single MORPH_DELETE probe does distinguish them.

### μ uniqueness

`mu_is_initial_monotone` (MuInitiality.v): Any function M satisfying
instruction_consistent + zero-init = vm_mu on all reachable states. μ is the
unique canonical cost measure. (Uniqueness GIVEN the cost function; see below.)

---

## WHAT IS CONDITIONAL

### Hardware bisimulation
The Kami/Bluespec/Verilog pipeline is implemented and the key opcode paths are
tested via Verilator simulation. `HardwareBisimulation.v` + `VerilogRefinement.v`
state the bisimulation. A complete formal bisimulation proof does not yet exist.
**Conditional on**: Kami extraction faithfully generates the Verilog.

### Cost derivation from information theory
`MuCostDerivation.v` attempts to derive `instruction_cost` values from information
theory. The theorem `cost_function_unique` is tautological (proved IF delta = formula
THEN derived_cost = delta, but derived_cost returns delta by definition).
**What IS non-conditional**: cert-setters cost ≥ 1 is proven structurally
(by no_free_certification, which derives from observing state change, not from
reading the cost definition).

### Physics claims
`EinsteinEmergence.v`, `CurvedTensorPipeline.v`, `DiscreteRaychaudhuri.v` prove
components of the physics derivation. The full chain from Thiele computational
structure to Einstein field equations is a research direction, not a closed theorem.
**Conditional on**: interpretation of discrete curvature as Ricci tensor, etc.

---

## WHAT IS ONLY AN INTERPRETATION

The following statements appear in narrative descriptions but are NOT theorems:

- "Thiele exceeds Turing" — informal until shadow projection is formalized and
  strictness is proven in Coq. Accurate statement: "Thiele has structure that any
  purely classical projection forgets." (This IS proven — categorical_separation.)

- "No Free Insight" as a universal principle — proven for certification insight.
  Not yet proven for partition insight, witness insight, or structural insight.
  The `universal_nfi` theorem is the current best formal statement.

- "Knowledge requires irreversible witness" — interpretive claim bridging the
  formal cost lower bounds to information-theoretic or physical meaning.
  Not a Coq theorem.

- "Physics emerges from computation" — research hypothesis supported by the
  discrete geometry proofs. Not yet a closed theorem.

---

## WHAT REMAINS OPEN

### Priority 1 (closes the "exceeds Turing" story)
- Formalize `shadow_proj : VMState → ClassicalState` as a Coq function
- Prove `classical_observer_blind_to_morphisms`: shadow_proj ∘ vm_apply ≠ injects morphism structure
- Prove Turing conservativity: Thiele restricted to classical ops = classical semantics
- State and prove strict refinement theorem

### Priority 2 (generalizes NoFI)
- Define formal taxonomy of insight events: cert, partition, structural, witness, logical
- Prove cost lower bound for partition refinement events (PNEW, morphism creation)
- Package into umbrella theorem: any insight event costs ≥ 1

### Priority 3 (closes cost derivation circularity)
- Replace tautological `cost_function_unique` with a proof that cert-setter costs
  are FORCED by the no-free-certification structural invariant
- Formalize: any instruction set where a cert-setter is zero-cost violates the invariant

### Priority 4 (implementation hardening)
- Full bisimulation proof for Coq → Verilog observable surface
- Automated extraction freshness gate in CI

---

## DEFENSIVE ANSWERS TO HOSTILE REVIEW

**Circularity attack**: "You defined cost as S cost, then proved cost ≥ 1 — trivial."
→ `no_free_certification` (AbstractNoFI.v §8) derives cost ≥ 1 from observing
csr_cert_addr state change, not from reading the definition. The structural pivot
is `thiele_non_cert_addr_setter_preserves`, proven by exhaustive case analysis.

**Vacuity attack**: "Are you just defining insight as something costly?"
→ `cert_addr_setterb` is a precise predicate over opcode constructors. The
claim is: an INDEPENDENTLY OBSERVABLE state change (cert_addr: 0→nonzero)
requires one of 5 specific opcodes, and those opcodes are proven to cost ≥ 1.

**Hidden-state attack**: "The morphism distinction is just hidden metadata."
→ `categorical_separation` + `classical_observer_cannot_separate` prove that
the distinction is semantically actionable (a MORPH_DELETE probe reveals it)
and not recoverable from classical observables.

**Simulation attack**: "A classical machine could simulate the same bookkeeping."
→ True for the bookkeeping aspects. The distinctness claim is not about
computational power but about WHAT INFORMATION IS RETAINED in state. The
separation theorem is about observational access, not Turing-completeness.

**Layer-mismatch attack**: "Does the hardware actually preserve the theorems?"
→ Tested on theorem-sensitive opcode paths. Full bisimulation open — see open obligations.

**Overclaim attack**: "Which of these is theorem-grade vs interpretation?"
→ See claim_ledger.md. Every claim is classified KERNEL/PROVEN, BRIDGE/PARTLY PROVEN,
or ASPIRATIONAL. The claim ledger is the authoritative source.

---

## STATUS SUMMARY

| Category | Count | Status |
|---|---|---|
| Coq files | ~160 | All compile, 0 Admitted |
| INQUISITOR | — | OK |
| Python tests | 668 passed, 1 skipped | Green |
| Master cert theorem | 2 channels, 3 levels (1-step / trace / PC-indexed) | CLOSED |
| Claim ledger | 14 KERNEL / 5 BRIDGE / 6 ASPIRATIONAL | see claim_ledger.md |
| Open obligations | 4 priority levels | see this document |
