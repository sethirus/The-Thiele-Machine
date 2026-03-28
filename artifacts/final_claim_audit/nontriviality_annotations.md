# Nontriviality Annotations — Major Theorems

**Date**: 2026-03-27
**Purpose**: For each major theorem, classify whether the proof is definitional, case-analysis, algebraic, or bridge. This lets hostile reviewers assess which results are "obvious rewording" vs. genuine mathematical content.

**Classification key**:
- **DEFINITIONAL** — the conclusion follows directly from expanding definitions; `simpl; reflexivity` or `unfold ...; f_equal`. Minimal content, but still useful for formalizing the design.
- **CASE-ANALYSIS** — the conclusion requires matching over all constructors of an inductive type (typically: all 32 opcodes). The proof is mechanical but the result is non-obvious before doing it.
- **ALGEBRAIC** — the conclusion requires reasoning about equations/inequalities (lia, omega, arithmetic). Non-trivial algebraic structure.
- **STRUCTURAL** — the conclusion requires induction over a structure (trace, list) combined with preservation lemmas.
- **BRIDGE** — the conclusion connects two separate formalisms or layers; the interesting content is showing the connection holds.

---

## MuLedgerConservation.v

### `vm_apply_mu`
**Claim**: `(vm_apply s i).vm_mu = s.vm_mu + instruction_cost i`
**Classification**: **CASE-ANALYSIS**
**Content**: Must match over all 32 opcode constructors and verify that each branch adds exactly `instruction_cost i` to μ. The instruction_cost function uses `S cost` for cert-setters and `cost` for structural ops — this distinction is a design choice whose correctness is non-obvious without checking every case.
**Is it trivial?** No — a one-line proof would only work if the ISA definition were structured to make it trivial. The case analysis over 32 opcodes documents that the ledger is truly exact across the entire ISA.

---

## MuInitiality.v

### `mu_is_initial_monotone`
**Claim**: μ is the unique measure satisfying monotone conservation
**Classification**: **ALGEBRAIC + BRIDGE**
**Content**: Proves uniqueness by showing any other measure satisfying the same initiality condition must equal μ. Requires initiality arguments (universal property of the initial object in a category of cost-tracking functions).
**Is it trivial?** No — uniqueness proofs require showing that any two solutions are equal, which needs the universal property argument, not just "look at the definition."

---

## AbstractNoFI.v

### `no_free_certification` (§8)
**Claim**: If `csr_cert_addr` changes 0→nonzero in one step, `instruction_cost i ≥ 1`
**Classification**: **CASE-ANALYSIS + ALGEBRAIC**
**Content**: Non-circular derivation. Proof path:
1. `csr_cert_addr` changed → `cert_addr_setterb i = true` (by `thiele_non_cert_addr_setter_preserves`, a case analysis over all 32 opcodes)
2. `cert_addr_setterb i = true` → `instruction_cost i ≥ 1` (by `cert_addr_setter_cost_pos`, case analysis over cert-setter constructors)

**Is it trivial?** No — the non-circularity is the key point. The proof derives the cost bound from observing the state change, not from reading the cost definition. The case analysis over all opcodes is the substantive step.

### `no_free_certification_trace_mu` (§9)
**Claim**: Over any trace with cert_addr 0→nonzero, total μ grew ≥ 1
**Classification**: **STRUCTURAL + ALGEBRAIC**
**Content**: Induction over the trace list. At each step, uses either (a) the cert-addr was already nonzero (contradiction with premise that it was 0 at start) or (b) the cert-addr-setting step occurred, invoking the single-step theorem. Requires combining `acm_run_mu_exact` (exact μ formula for traces) with the single-step bound.
**Is it trivial?** No — the interesting content is ruling out "smuggling": showing that no combination of zero-cost structural ops can produce cert evidence. The induction makes this rigorous.

### `certification_requires_positive_mu` (§11)
**Claim**: Either cert channel activating requires μ to grow ≥ 1
**Classification**: **ALGEBRAIC** (combines §8 + §10)
**Content**: Direct combination of `no_free_certification_mu` (csr_cert_addr channel) and `no_free_certification_certified_mu` (vm_certified channel). Short proof, but the content is in the two component theorems.
**Is it trivial?** Conditional on §8 and §10, yes — it is a disjunction case split. The interesting work is in the components.

---

## InsightTaxonomy.v

### `pnew_can_be_free` / `morph_can_be_free`
**Claim**: PNEW/MORPH can have instruction_cost = 0
**Classification**: **DEFINITIONAL**
**Content**: `simpl; reflexivity`. These theorems are intentionally trivial — they formalize a design decision (structural creation is exploratory and can be free).
**Is it trivial?** Yes, intentionally. Their value is negative: they document that the ISA does NOT require cost > 0 for all instructions, which is essential for correctly framing NoFI as "CERTIFIED insight is non-free."

### `certified_insight_nonfree`
**Claim**: Any cert insight event (either channel) has cost ≥ 1 and μ grew ≥ 1
**Classification**: **ALGEBRAIC** (delegates to AbstractNoFI.v theorems)
**Content**: Dispatches on the two channels. Each channel invokes the corresponding AbstractNoFI theorem. The interesting content is in AbstractNoFI.v.
**Is it trivial?** As a standalone proof, yes — it is a wrapper. Its value is as the published API: the single theorem that users cite for NoFI.

### `no_free_certified_insight`
**Claim**: Any trace with cert evidence has a cert-setter instruction with cost ≥ 1 and μ grew ≥ 1
**Classification**: **STRUCTURAL** (delegates to `thiele_abstract_nfi_cost` + `no_free_certification_trace_mu`)
**Content**: Existential witness extraction (finding the cert-setter in the trace) plus the μ lower bound. The trace structure is the interesting part.
**Is it trivial?** As a standalone proof, it is a combination. The content is in the components. Value: packages the full design principle in one theorem name.

---

## ShadowProjection.v

### `shadow_proj_forgets_graph`
**Claim**: shadow_equal separation_A separation_B but their graphs differ
**Classification**: **DEFINITIONAL + DEFINITIONAL**
**Content**: Two parts: `shadow_proj` equality by `simpl; reflexivity` (both states have identical classical fields); graph inequality by `discriminate` (list with element ≠ empty list).
**Is it trivial?** The proof is trivial; the theorem is not. The interesting content is the witness construction (choosing separation_A and separation_B to have identical classical fields but different graphs) — that required design judgment.

### `shadow_separation_theorem`
**Claim**: ∃ states, same shadow, different graphs, probe separates them
**Classification**: **CASE-ANALYSIS (proof by witness construction)**
**Content**: Provides explicit witnesses (separation_A, separation_B, morph_delete_probe). Each conjunct is verified computationally. Non-trivial because the witnesses had to be designed.
**Is it trivial?** The proof is trivial given the witnesses; the theorem statement is the important output. An existential theorem about a new property is meaningful regardless of how the proof was found.

### `shadow_does_not_capture_morphisms`
**Claim**: ∀ f : ClassicalState → A, f(shadow_proj A) = f(shadow_proj B)
**Classification**: **ALGEBRAIC** (universal quantification over functions)
**Content**: Uses the fact that `shadow_proj separation_A = shadow_proj separation_B` (proven), so any function applied to both projections gives the same result. The universal quantification makes this genuinely general.
**Is it trivial?** No — the universal quantification is the point. The theorem says "any information-extracting function of classical state is blind to the difference," which is stronger than "one particular function fails to distinguish them."

---

## Summary Table

| Theorem | Classification | Nontrivial? | Key content |
|---|---|---|---|
| `vm_apply_mu` | CASE-ANALYSIS | YES | 32-opcode ledger exactness |
| `mu_is_initial_monotone` | ALGEBRAIC+BRIDGE | YES | Uniqueness via universal property |
| `no_free_certification` | CASE-ANALYSIS+ALGEBRAIC | YES | Non-circular cost bound from state observation |
| `no_free_certification_trace_mu` | STRUCTURAL+ALGEBRAIC | YES | No smuggling through zero-cost trace |
| `certification_requires_positive_mu` | ALGEBRAIC | CONDITIONAL | Combination of §8 + §10 |
| `pnew_can_be_free` | DEFINITIONAL | INTENTIONALLY TRIVIAL | Documents ISA design: structural creation is free |
| `morph_can_be_free` | DEFINITIONAL | INTENTIONALLY TRIVIAL | Same |
| `certified_insight_nonfree` | ALGEBRAIC | CONDITIONAL | API wrapper for AbstractNoFI.v |
| `no_free_certified_insight` | STRUCTURAL | CONDITIONAL | API wrapper for full NoFI principle |
| `shadow_proj_forgets_graph` | DEFINITIONAL | WITNESS-DESIGN | Proof trivial; witness construction non-trivial |
| `shadow_separation_theorem` | WITNESS | YES | Existential with explicit design |
| `shadow_does_not_capture_morphisms` | ALGEBRAIC | YES | Universal quantification over all classical functions |
| `shadow_strictly_lossy` | WITNESS | YES | Combines C2/C3/C4 in one statement |
