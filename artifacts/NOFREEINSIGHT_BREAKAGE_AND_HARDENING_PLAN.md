# NoFreeInsight Dependency Breakage Matrix and Hardening Plan

Date: 2026-03-01
Scope: static dependency/use analysis from repository sources (`coq/**/*.v`, selected docs/tests).

## Implementation Status (Live)

- [x] Phase 1 started and implemented in code:
   - Added `CertifiedObs` and `CertifiedWithSupra` in `coq/kernel/NoFreeInsight.v`.
   - Kept backward-compatible alias `Certified := CertifiedWithSupra`.
   - Added helper lemmas `certified_with_supra_implies_obs` and `certified_implies_supra`.
- [x] Phase 2 started and implemented in code:
   - Added `strengthening_obs_requires_structure_addition` in `coq/kernel/NoFreeInsight.v`.
   - The new theorem consumes `strictly_stronger` to derive weak acceptance and route through a bridge premise.
   - Existing `strengthening_requires_structure_addition` now delegates through the strengthened theorem for compatibility.
- [x] Phase 4 partially implemented:
   - Added nontrivial guard test `coq/tests/verify_nofi_load_bearing.v` that applies
      `NoFreeInsight.strengthening_obs_requires_structure_addition` directly.
- [x] Phase 3 started and partially implemented:
    - `coq/kernel/Certification.v` adds `no_free_insight_from_strengthening_bridge`
       with direct application of `NoFreeInsight.strengthening_obs_requires_structure_addition`.
    - `coq/thielemachine/verification/RandomnessNoFI.v` adds
       `admissible_and_strengthening_obs_implies_structure_addition`, explicitly
       chaining `Admissible` hypotheses into strengthened NoFreeInsight.
    - `coq/thielemachine/verification/RandomnessNoFI.v` hardens
       `admissible_implies_cert_cost_leq_budget_for_supra_chsh` so its conclusion
       now includes `NoFreeInsight.has_structure_addition fuel trace s_init`,
       proven by direct application of
       `NoFreeInsight.strengthening_obs_requires_structure_addition`.
    - `coq/thielemachine/verification/RandomnessNoFI.v` now routes
       `quantum_admissible_cannot_certify_supra_chsh` through a NoFI contradiction:
       supra-certification implies structure-addition (via strengthened NoFI), while
       quantum-admissibility proves no structure-addition can occur.
    - `coq/kernel/Certification.v` now routes both
       `quantum_admissible_cannot_certify_supra_chsh` and
       `quantum_admissible_cannot_certify_chsh_claim` through NoFI structure-addition
       contradiction, instead of directly concluding from `has_supra_cert`.
    - `coq/kernel/Certification.v` strengthens
       `certified_supra_chsh_implies_mu_lower_bound` and
       `certified_chsh_claim_implies_mu_lower_bound` to return
       `NoFreeInsight.has_structure_addition ...` in their conclusions.
    - `coq/thielemachine/verification/RandomnessNoFI.v` rewires downstream proofs
       to use `Certification.no_free_insight_from_strengthening_bridge` as the
       dependency entrypoint (instead of direct application of the NoFI theorem).
- [ ] Phase 3 remaining:
    - Expand this bridge-routed pattern to additional verification modules beyond
       `RandomnessNoFI.v` so NoFI remains non-bypassable across more theorem families.
- [ ] Phase 5 pending (commentary/claim-to-theorem cleanup)

- [x] Extraction-facing proof entrypoints now carry explicit NoFI anchors:
   - `coq/kami_hw/CanonicalCPUProof.v` extends `CanonicalCPUProofBundle` with
      `canonical_nofi_supra_boundary` and `canonical_nofi_paid_certification`.
   - `coq/Extraction.v` includes `extraction_nofi_supra_boundary_anchor`, forcing
      extraction compilation to type-check the NoFI certification boundary theorem.
   - Verified by rebuilding `kami_hw/CanonicalCPUProof.vo`, `Extraction.vo`, and
      `kami_hw/KamiExtraction.vo`.

- [x] Runtime-significant NoFI policy path implemented (non-CI):
   - `coq/kernel/VMStep.v` adds executable checks:
      `is_cert_setterb`, `nofi_step_cost_okb`, `nofi_trace_cost_okb`.
   - `coq/Extraction.v` now extracts these computable policy functions into
      `build/thiele_core.ml`.
   - `tools/extracted_vm_runner.ml` enforces `nofi_trace_cost_okb` before
      execution and fails closed (`err=true`, `csr_err=1`, exit code 5) on
      cert-setting instructions with zero cost.
   - `thielecpu/hardware/testbench/thiele_cpu_kami_tb.v` enforces the same
      runtime policy during simulation (`$fatal` on zero-cost cert-setting
      opcode 0x03/0x04/0x0E/0x0F).

## 1) Breakage Matrix

This matrix distinguishes three removal scenarios because they break different things.

### Scenario A: Remove file `coq/kernel/NoFreeInsight.v` entirely

| Impact type | What breaks | Evidence |
|---|---|---|
| Compile break (hard) | Any file importing `NoFreeInsight` fails to resolve module import | `coq/Extraction.v:21`, `coq/kernel/Certification.v:13`, `coq/tests/verify_zero_admits.v:18`, `coq/thielemachine/verification/RandomnessNoFI.v:10`, `coq/kami_hw/CanonicalCPUProof.v:16`, `coq/kernel/MasterSummary.v:67`, `coq/kernel/TsirelsonComputation.v:11`, `coq/kernel/NoCloningFromMuMonotonicity.v:32`, `coq/physics/PreregSplit.v:7`, `coq/physics_exploration/ParticleMasses.v:5`, `coq/thielemachine/coqproofs/NUSD.v:6` |
| Theorem break (direct symbol use) | Files directly using `NoFreeInsight` symbols fail even if imports were rewritten | `coq/thielemachine/verification/RandomnessNoFI.v:148` (`NoFreeInsight.trace_run_run_vm`), `coq/tests/verify_zero_admits.v:45`, `coq/tests/verify_zero_admits.v:112` (`NoFreeInsight.strengthening_requires_structure_addition`) |
| Runtime semantic break | No direct runtime semantics break from extracted OCaml target, but Coq build pipeline breaks before extraction/proof checks | Extraction target in `coq/Extraction.v:53` only exports `vm_instruction`, `VMState`, `vm_apply`; import failure still blocks build |

### Scenario B: Keep file, remove theorem `strengthening_requires_structure_addition`

| Impact type | What breaks | Evidence |
|---|---|---|
| Compile break (direct) | `verify_zero_admits` checks this theorem explicitly | `coq/tests/verify_zero_admits.v:45`, `coq/tests/verify_zero_admits.v:112` |
| Theorem break (downstream proof payload) | No other substantive theorem proof currently depends on it by name | Global symbol search found no additional theorem applications outside `NoFreeInsight.v` and `verify_zero_admits.v` |
| Runtime semantic break | None directly | theorem is proof-level only |

### Scenario C: Keep file, remove theorem `no_free_insight_general`

| Impact type | What breaks | Evidence |
|---|---|---|
| Compile break (direct) | No direct theorem use found in proofs; mostly narrative references | Mentioned in prose/comments (`coq/kernel/Certification.v:538`) |
| Theorem break | No direct proof consumers found by name | symbol search results |
| Runtime semantic break | None directly | theorem is proof-level only |

## 2) Current Reality Summary

- `NoFreeInsight.v` is currently **module-critical** (many imports), but not yet **load-bearing-theorem-critical** for most downstream proof obligations.
- The strongest concrete re-use is utility lemma `trace_run_run_vm` in `RandomnessNoFI`.
- `strengthening_requires_structure_addition` is currently enforced mainly by zero-admit/meta checks, not by deep theorem chaining.

## 3) Hardening Plan: Make NoFreeInsight Truly Load-Bearing

Goal: force downstream verification to depend nontrivially on strengthening semantics, not only on cert-address transition facts.

### Phase 1: Fix definitions so strengthening matters

1. Split current `Certified` into two layers:
   - `CertifiedObs`: `vm_err = false /\ P (decoder receipts) = true`
   - `CertifiedWithSupra`: `CertifiedObs /\ has_supra_cert s_final`
2. Keep old `Certified` as compatibility alias temporarily, then migrate callers.
3. Add theorem that links `CertifiedObs` to `has_supra_cert` only under explicit assumptions (not by definition).

Deliverable theorem shape:
- `strengthening_to_cert_requires_supra : strictly_stronger P_strong P_weak -> ... -> CertifiedObs ... P_strong ... -> has_supra_cert s_final`.

### Phase 2: Strengthen NoFreeInsight theorem to consume predicate hypotheses

1. Refactor `strengthening_requires_structure_addition` so proof must use:
   - `Hstrict : strictly_stronger P_strong P_weak`
   - observation witness from strictness
   - decoder adequacy/non-triviality assumptions
2. Prove structure-addition via a chain:
   - strengthening consequence -> `has_supra_cert`
   - `has_supra_cert` + init-cert-zero -> `structure_addition_in_run`.

Deliverable:
- no dead hypotheses in final proof term (`Hstrict` and predicate side-conditions must be consumed).

### Phase 3: Rewire downstream proofs to depend on the strengthened theorem

1. In `coq/kernel/Certification.v`, replace narrative-only reference with theorem application.
2. In `coq/thielemachine/verification/RandomnessNoFI.v`, derive budget/cost claims by explicitly chaining through strengthened NoFreeInsight theorem.
3. Add a new theorem in a downstream file that fails if `strengthening_requires_structure_addition` is weakened.

### Phase 4: Add dependency guard tests

1. Add a Coq test file `coq/tests/verify_nofi_load_bearing.v` that:
   - imports a downstream theorem,
   - requires `NoFreeInsight.strengthening_requires_structure_addition` in proof body,
   - cannot close by mere `let _ := ...` connectivity tricks.
2. Keep `verify_zero_admits.v`, but treat it as meta-check only.

### Phase 5: Documentation honesty and traceability

1. Update `coq/kernel/NoFreeInsight.v` header comments:
   - explicitly state what is proved structurally,
   - move thermodynamic/proportional claims behind theorem references where they are actually proved.
2. Add a claim-to-theorem table in `artifacts/` with exact theorem names and file locations.

## 4) Success Criteria (objective)

- Removing or weakening `strengthening_requires_structure_addition` causes compile failures in at least one substantive downstream proof file (not just assumption print tests).
- At least one downstream quantitative theorem has a proof term that directly applies strengthened NoFreeInsight theorem.
- No major claim in top-level comments remains without theorem citation.

## 5) Risk Notes

- This refactor may require revisiting `Certification.v` theorem statements and interfaces.
- Some existing proofs rely on convenience of current `Certified` definition; migration should be staged with compatibility aliases.
- Static analysis was used for this matrix; full CI rebuild is recommended after implementing hardening steps.
