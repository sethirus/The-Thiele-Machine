# The Thiele Machine — What Remains Open

**Date**: 2026-03-27
**Status**: This document is the honest accounting. It exists so that published claims can be checked against it.

---

## Summary: What Is Fully Proven

The following are machine-checked with zero Admitted in Coq (kernel tier):

1. **μ conservation** — `vm_apply_mu` in MuLedgerConservation.v: exact ledger identity
2. **μ uniqueness** — `mu_is_initial_monotone` in MuInitiality.v: canonical measure
3. **No free certification (single step)** — `no_free_certification` + `no_free_certification_mu` in AbstractNoFI.v §8
4. **No free certification (trace)** — `no_free_certification_trace_mu` in AbstractNoFI.v §9
5. **vm_certified channel** — `no_free_certification_certified` + `_certified_mu` in AbstractNoFI.v §10
6. **Master NoFI** — `certification_requires_positive_mu` in AbstractNoFI.v §11: both channels
7. **Insight taxonomy** — `no_free_certified_insight` in InsightTaxonomy.v: structural ops free, certified insight costs ≥ 1
8. **Classical shadow** — `shadow_proj`, `shadow_separation_theorem`, `shadow_strictly_lossy` in ShadowProjection.v
9. **Categorical separation** — `categorical_separation` in PartitionSeparation.v
10. **Hardware bisimulation** — `rtl_step_correct` in HardwareBisimulation.v (with ISA caveats, see E below)

---

## OPEN OBLIGATION D — Turing/Thiele Strictness

These items establish the formal comparison between Thiele and classical computation.

**D3 — Conservativity**: Prove that Thiele restricted to classical opcodes (no PNEW, MORPH, MORPH_ASSERT, REVEAL, EMIT, LJOIN, LASSERT) produces exactly the same trace semantics as a classical machine.
- Status: KernelTM.v has partial embedding; the conservativity direction is unproven.
- Risk if missing: the claim "Thiele extends classical machines" rests on a semantic argument, not a theorem.

**D4 — Strictness witness**: Exhibit a formal Thiele probe P such that P separates states reachable by the full Thiele ISA but not representable in any classical shadow.
- Status: shadow_separation_theorem proves existence informally, but it uses witness states, not reachability from a classical start.
- Risk if missing: separation is proven for handcrafted states, not states reachable from a common start.

**D5 — Safe wording theorem**: Formally state "Thiele strictly refines classical trace semantics under shadow_proj" as a theorem, not prose.
- Status: not started.
- Risk if missing: the strictness claim lives only in documentation, not in verified form.

---

## OPEN OBLIGATION E — Implementation Fidelity

These items close the gap between the Coq semantics and the running implementation.

**E3 — Extraction freshness gate**: CI must fail if `coq/Extraction.vo` is out-of-date with respect to `VMStep.v` or `Extraction.v`.
- Status: `scripts/check_isa_proof_freshness.sh` covers proof files; extraction freshness for `build/thiele_core.ml` is not gated.
- Risk if missing: an ISA change could silently invalidate the OCaml extracted runner without CI catching it.

**E4 — Python VM harness label**: `thielecpu/vm.py` must carry `# HARNESS — not normative semantics` header, and documentation must explain that the Python layer delegates to the OCaml extracted runner.
- Status: not done.
- Risk if missing: external readers may treat the Python VM as the normative semantics.

**E5 — ISA proof-impact checklist**: A formal table at `artifacts/final_claim_audit/isa_proof_impact.md` mapping every opcode to which theorems it affects (cert channel, mu channel, graph, err).
- Status: not created.
- Risk if missing: ISA changes may not be checked against affected proofs.

**E6 — Red-flag diff gate**: Makefile must warn when changes touch `VMStep.v`, `instruction_cost`, or cert state fields.
- Status: not implemented.
- Risk if missing: semantic drift in the normative spec goes unnoticed until CI runs manually.

---

## OPEN OBLIGATION F (documentation)

**F8 — Nontriviality annotations**: For each major theorem, a classification: definitional / case-analysis / algebraic / bridge. Without this, hostile reviewers may argue all theorems are trivial restatements of definitions.
- Status: see `what_remains_nontriviality.md` (F8 document).

---

## OPEN OBLIGATION (BRIDGE tier — 5 items)

From `claim_ledger.md`, these claims are PARTLY PROVEN — derivation chains exist but are not fully closed:

| Claim | What is missing |
|---|---|
| Extraction faithfulness | Formal bisimulation theorem between Coq semantics and OCaml extracted runner |
| RTL correctness | `rtl_step_correct` covers main path; full ISA coverage under Verilator not gated |
| CHSH/Tsirelson | Quantum bound derivations are structural; not derived from quantum mechanics |
| NoFI → physics | Bridge from formal NoFI to thermodynamic interpretations is not a theorem |
| Three-layer isomorphism | Coq↔OCaml is by extraction; OCaml↔Python and Python↔Verilog bridges are informal |

---

## What "Fully Proven" Means

"Zero Admitted" means: no step in the Coq proof was asserted without derivation. All results within a `[x]`-marked theorem chain are machine-checked. This does NOT mean:

- That the theorem proves physical reality
- That the Coq axioms are themselves provable (Coq's type theory is the base)
- That the hardware implements exactly the Coq semantics (RTL correctness is BRIDGE, not KERNEL)
- That the OCaml extracted runner is bitwise identical to Coq semantics (extraction faithfulness is BRIDGE)

The KERNEL tier is clean. The BRIDGE tier has open work. The ASPIRATIONAL tier requires new mathematics outside this codebase.
