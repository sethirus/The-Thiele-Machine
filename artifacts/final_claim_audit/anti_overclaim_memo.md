# Anti-Overclaim Memo — What the Thiele Machine Proofs Do and Do Not Establish

**Date**: 2026-03-27
**Purpose**: This memo exists to prevent overclaiming. Every statement below has a "does NOT prove" companion. Read both columns.

---

## The Safe Claim Ladder

Claims are ordered from most-proven to least-proven. Do not cite a lower rung to support a claim that only the higher rungs establish.

### Rung 1 — Machine-Checked Kernel (cite freely, with theorem names)

| Proven claim | Theorem | File |
|---|---|---|
| μ is the unique monotone cost measure | `mu_is_initial_monotone` | MuInitiality.v |
| Every step charges exactly instruction_cost | `vm_apply_mu` | MuLedgerConservation.v |
| cert_addr 0→nonzero requires cost ≥ 1 | `no_free_certification` | AbstractNoFI.v §8 |
| cert_addr 0→nonzero requires μ growth ≥ 1 | `no_free_certification_mu` | AbstractNoFI.v §8 |
| Same holds over any trace | `no_free_certification_trace_mu` | AbstractNoFI.v §9 |
| vm_certified false→true requires cost ≥ 1 | `no_free_certification_certified` | AbstractNoFI.v §10 |
| Either channel requires μ growth ≥ 1 | `certification_requires_positive_mu` | AbstractNoFI.v §11 |
| Structural creation can be free | `pnew_can_be_free`, `morph_can_be_free` | InsightTaxonomy.v |
| Certified insight cannot be free | `no_free_certified_insight` | InsightTaxonomy.v |
| Classical shadow forgets graph structure | `shadow_proj_forgets_graph` | ShadowProjection.v |
| Separation pair exists with identical shadows | `shadow_separation_theorem` | ShadowProjection.v |
| No classical function separates the pair | `shadow_does_not_capture_morphisms` | ShadowProjection.v |

### Rung 2 — Bridge Claims (state with caveats, cite what is proven and what is assumed)

| Bridge claim | What IS proven | What is NOT proven |
|---|---|---|
| RTL implements Coq semantics | `rtl_step_correct` covers main instruction path | Full ISA coverage; all corner cases under Verilator |
| OCaml runner matches Coq semantics | Coq extraction produces OCaml | Formal bisimulation theorem not proven |
| Python VM matches Coq semantics | Python delegates to OCaml runner | Bridge from OCaml to Python is informal |
| CHSH separation exceeds classical bound | Structural bound derived in kernel | No quantum mechanics derivation in this codebase |

### Rung 3 — Aspirational (do NOT cite as proven; only use to motivate future work)

| Aspirational claim | What would be needed to prove it |
|---|---|
| NoFI implies thermodynamic cost floor | A formal model of thermodynamics in the kernel |
| Morphism receipts are unforgeable in adversarial settings | A security model with an adversary + hardness assumptions |
| Three-layer isomorphism is exact | Formal bisimulation proofs for all three layer pairs |
| Thiele measurement = quantum measurement | A formal embedding of quantum mechanics into the kernel |
| NoFI → Landauer bound | A derivation connecting μ to physical entropy |

---

## Specific Overclaims to Avoid

**"The Thiele Machine proves that knowledge has a cost in nature."**
- What is proven: in this formal model, certified structural knowledge requires μ ≥ 1.
- What is not proven: that physical knowledge acquisition follows this model.
- Safe wording: "In the Thiele Machine's formal model, certified structural insight is provably non-free (no_free_certified_insight, InsightTaxonomy.v)."

**"The μ ledger is unforgeable."**
- What is proven: μ is monotone and exact (vm_apply_mu). A program cannot certify without μ growing.
- What is not proven: that an adversary cannot manipulate the extraction chain to fake μ values.
- Safe wording: "Within the formal Coq semantics, μ satisfies an exact conservation law. Implementation fidelity depends on the bridge claims (see Rung 2)."

**"The separation theorem proves Thiele is strictly more powerful than classical machines."**
- What is proven: there exist states with identical classical shadows that Thiele can separate.
- What is not proven: conservativity (Thiele restricted to classical opcodes = classical) or a formal strictness theorem.
- Safe wording: "The shadow_separation_theorem proves that shadow_proj is strictly lossy. The formal Turing/Thiele strictness theorem (D4-D5 in HARDENING_TRACKER.md) is open."

**"No Free Insight proves thermodynamic laws."**
- What is proven: no_free_certified_insight is a property of this specific ISA.
- What is not proven: any connection to thermodynamics, entropy, or Landauer's principle.
- Safe wording: "The NoFI theorems establish a cost floor for certified structural claims within the Thiele Machine's formal model. Connections to physical laws are aspirational and not yet formalized."

**"All theorems are non-trivial."**
- What is true: the insight taxonomy required discovering that PNEW/MORPH can be zero-cost (ISA design choice), which changed the framing of NoFI from "all structural ops cost ≥ 1" to "certified structural insight costs ≥ 1."
- What to watch: several theorems reduce to `simpl; reflexivity` or `lia` — they are definitional. The nontrivial theorems are the ones that observe state change and derive cost bounds (see F8: nontriviality annotations).

---

## The One-Sentence Safe Summary

> The Thiele Machine is a formally verified computational model in which certifying structural knowledge provably requires paying at least one unit of cost (μ), and two states with identical classical behavior can be distinguished by a single structural probe — both results machine-checked in Coq with zero Admitted.

This summary is safe to publish. Any addition to it requires a corresponding theorem.
