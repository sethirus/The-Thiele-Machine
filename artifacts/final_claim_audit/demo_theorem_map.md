# Demo-to-Theorem Map — demo_knowledge_receipt.py

**Date**: 2026-03-27
**Source**: `demo_knowledge_receipt.py` (four Acts)
**Purpose**: Map each executable demo step to its backing theorem, and state what the demo does NOT prove.

---

## ACT 1 — The Forged Claim

**Demo**: Run `MORPH_ASSERT 99 two-hop cert 0` on a state with no modules or morphisms. Machine errors; μ = 1.

**What the demo shows**: The machine errored (`vm_err = true`), but still charged μ = 1 (S(0) = 1).

### Theorem backing

| Claim | Theorem | File | Notes |
|---|---|---|---|
| MORPH_ASSERT costs S(cost) ≥ 1 regardless | `morph_assert_cost_pos` | InsightTaxonomy.v | Definitional: instruction_cost (instr_morph_assert ...) = S cost |
| cert-addr-setter instructions cost ≥ 1 | `cert_addr_setter_cost_pos` | AbstractNoFI.v §7 | Proven by case analysis over all 32 opcodes |
| μ grows by exactly instruction_cost at each step | `vm_apply_mu` | MuLedgerConservation.v | Exact conservation lemma |

**What Act 1 does NOT prove**:
- That the error was caused by the missing morphism (not a theorem about error conditions — it is ISA behavior)
- That the cost is "meaningful" in any physical sense
- That the machine is secure against adversaries who can manipulate the μ field directly

**Safe wording**: "MORPH_ASSERT charges S(cost) ≥ 1 even on a failed attempt. This is `morph_assert_cost_pos` in InsightTaxonomy.v — definitional from the ISA."

---

## ACT 2 — The Earned Path

**Demo**: Build modules A, B, C; create morphisms f: A→B and g: B→C; compose into g∘f: A→C; read back source and target. Asserts μ = 8, r0 = 1 (module A), r1 = 3 (module C).

**What the demo shows**: A navigable two-hop morphism chain was built; the composed morphism correctly identifies source and target modules; μ exactly equals the sum of all instruction costs.

### Theorem backing

| Claim | Theorem | File | Notes |
|---|---|---|---|
| μ = sum of instruction costs | `vm_apply_mu` + `acm_run_mu_exact` | MuLedgerConservation.v, AbstractNoFI.v §9 | Exact identity, not an approximation |
| PNEW/MORPH/COMPOSE preserve cert_addr | `pnew_preserves_cert_addr`, `morph_preserves_cert_addr` | InsightTaxonomy.v | Structural ops do not touch cert channel |
| Structural creation can be zero-cost | `pnew_can_be_free`, `morph_can_be_free` | InsightTaxonomy.v | Intentional ISA design |

**What Act 2 does NOT prove**:
- That the morphism graph represents a real two-hop path in any external system
- That the μ value is "fair" or "optimal" for this computation
- That composition is semantically correct (MORPH_GET retrieves real source/target — this is an executable demonstration, not a separate theorem)

**Safe wording**: "Act 2 demonstrates exact μ accounting: every instruction cost is recorded. This is `vm_apply_mu` in MuLedgerConservation.v."

---

## ACT 3 — The Certified Claim

**Demo**: Same path as Act 2, plus `MORPH_ASSERT 2 A-to-C-two-hop cert 4`. Asserts μ = 13 (= 8 + S(4) = 8 + 5), `cert_addr ≠ 0`. NoFI probe: `MORPH_ASSERT ... 0` still charges S(0) = 1.

**What the demo shows**: After MORPH_ASSERT, csr_cert_addr is nonzero; μ increased by exactly S(cost); even cost=0 costs 1.

### Theorem backing

| Claim | Theorem | File | Notes |
|---|---|---|---|
| cert_addr 0→nonzero requires cost ≥ 1 | `no_free_certification` | AbstractNoFI.v §8 | Non-circular: derives from state change observation |
| cert_addr 0→nonzero requires μ growth ≥ 1 | `no_free_certification_mu` | AbstractNoFI.v §8 | Corollary combining no_free_certification + vm_apply_mu |
| MORPH_ASSERT is a cert-addr-setter | `morph_assert_is_cert_setter` | InsightTaxonomy.v | cert_addr_setterb = true by computation |
| MORPH_ASSERT costs ≥ 1 | `morph_assert_cost_pos` | InsightTaxonomy.v | S(cost) ≥ 1 definitionally |
| Certified insight cannot be free | `certified_insight_nonfree` | InsightTaxonomy.v | Master theorem for cert insight events |
| Any trace with cert evidence has μ grew ≥ 1 | `no_free_certification_trace_mu` | AbstractNoFI.v §9 | Smuggling through a sequence is impossible |

**What Act 3 does NOT prove**:
- That `cert_addr ≠ 0` means the assertion is semantically correct (it means it was formally asserted, not that the assertion is true)
- That the cost cannot be gamed by manipulating intermediate state
- That two parties sharing a μ value have the same knowledge

**Safe wording**: "Act 3 demonstrates the No Free Insight law: `no_free_certification` (AbstractNoFI.v §8) proves that changing cert_addr from 0 to nonzero requires μ to grow by at least 1. Cost=0 is not an exception — S(0) = 1."

---

## ACT 4 — The Separation Theorem

**Demo**: Program A (builds morphism chain, r0=1, r1=3, μ=8) and Program B (no morphisms, same r0/r1/μ). Classical fingerprints identical. After MORPH_DELETE probe: Program A succeeds, Program B errors.

**What the demo shows**: Two programs with identical classical state can be distinguished by a single Thiele instruction.

### Theorem backing

| Claim | Theorem | File | Notes |
|---|---|---|---|
| States with identical shadows exist that Thiele separates | `shadow_separation_theorem` | ShadowProjection.v | Existential with explicit witnesses |
| Shadow projection is strictly lossy | `shadow_strictly_lossy` | ShadowProjection.v | Combines C2/C3/C4 |
| No classical function separates the pair | `shadow_does_not_capture_morphisms` | ShadowProjection.v | Forall f : ClassicalState → A, same result |
| Classical observer cannot separate | `no_classical_separation` | ShadowProjection.v | Corollary for functions that factor through shadow |
| Categorical separation exists | `categorical_separation` | PartitionSeparation.v | Earlier, independent proof |

**Relationship between demo and theorem**:
- The demo uses Programs A and B (built by different instruction sequences)
- The theorem uses `separation_A` and `separation_B` (handcrafted witness states)
- These are **different pairs** proving the same existential: the demo is a computational exemplar; the theorem is a formal certificate
- `shadow_separation_theorem` is stronger for publication; the demo is stronger for intuition

**What Act 4 does NOT prove**:
- That the specific Programs A and B are the unique witnesses (many pairs exist)
- That the separation is computationally hard to find (the probe is trivial: MORPH_DELETE)
- That the demo programs are reachable from a common initial state (the shadow_separation theorem uses handcrafted witnesses, not reachability from a blank tape)
- Formal Turing/Thiele strictness (D4-D5 in HARDENING_TRACKER.md are open)

**Safe wording**: "Act 4 is the executable version of `shadow_separation_theorem` (ShadowProjection.v): classically indistinguishable states are separated by a single MORPH_DELETE probe. The theorem proves existence; the demo makes it concrete."

---

## Demo Summary vs. Theorem Summary

| Demo assertion | Backed by theorem? | Theorem name |
|---|---|---|
| "Machine refused to certify without structure" | YES | `no_free_certification` (AbstractNoFI.v §8) |
| "Cost charged even on failed attempt" | YES | `morph_assert_cost_pos` (InsightTaxonomy.v) |
| "μ = 8 after Act 2 program" | YES (by computation) | `vm_apply_mu` (MuLedgerConservation.v) |
| "cert_addr nonzero after MORPH_ASSERT" | YES (by ISA definition) | `morph_assert_is_cert_setter` (InsightTaxonomy.v) |
| "S(0) = 1, cost=0 is not free" | YES | `morph_assert_cost_pos` (InsightTaxonomy.v) |
| "Program A and B classically identical" | YES | `shadow_proj_forgets_graph` (ShadowProjection.v) |
| "Probe distinguishes them" | YES | `shadow_separation_theorem` (ShadowProjection.v) |
| "No classical observer can separate them" | YES | `shadow_does_not_capture_morphisms` (ShadowProjection.v) |
| "Receipt is hardware-backed" | BRIDGE | `rtl_step_correct` (HardwareBisimulation.v) — main path only |
| "Three-layer isomorphism is exact" | ASPIRATIONAL | No formal bisimulation theorem yet |
