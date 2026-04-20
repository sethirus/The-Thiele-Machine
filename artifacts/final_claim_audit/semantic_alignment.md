# Semantic Alignment: Which Layer Is Normative?

**Status**: Formal. Artifact for HARDENING_TRACKER.md E1.

---

## The Normative Layer

**The Coq proof layer is normative.**

All claims about the Thiele Machine's behavior — certification costs, structural separation, No Free Insight, Turing/classical strictness — are derived from Coq-proved theorems in `coq/kernel/`. The Python VM, OCaml extraction, and RTL hardware are implementation artifacts derived from the Coq spec.

---

## Layer Hierarchy

```
coq/kernel/         ← NORMATIVE: Definitions + theorems (VMState.v, VMStep.v, ...)
      │
      ▼
coq/Extraction.v    ← Extraction spec: maps Coq types to OCaml
      │
      ▼
build/thiele_core.ml ← OCaml extracted runtime (GENERATED — do not edit)
      │
      ▼
thielecpu/vm.py     ← Python VM harness (GENERATED — not normative semantics)
      │
      ▼
coq/kami_hw/        ← Kami/Bluespec RTL spec (normative for hardware)
      │
      ▼
build/kami_hw/thiele_hw.bsv ← Bluespec (GENERATED)
      │
      ▼
thielecpu/hardware/rtl/thiele_cpu_kami.v ← Verilog RTL (GENERATED)
```

---

## What "Normative" Means

| Layer | Normative for | Notes |
|---|---|---|
| `coq/kernel/` | All semantic claims | VMState, VMStep, vm_apply — source of truth |
| `coq/kami_hw/` | Hardware correctness | Abstraction.v bridges Kami ↔ VMState |
| `coq/Extraction.v` | OCaml extraction fidelity | check_isa_proof_freshness.sh guards staleness |
| `build/thiele_core.ml` | OCaml runtime behavior | Generated; must not diverge from Coq |
| `thielecpu/vm.py` | **Not normative** | Harness only — delegates to OCaml runner |
| `thielecpu/hardware/rtl/` | **Not normative** | Generated; verified via VerilogRefinement.v |

---

## Key Alignment Proofs

| Claim | Coq Theorem | File |
|---|---|---|
| Python VM delegates to OCaml runner | `python_bisimulation` | `kernel/PythonBisimulation.v` |
| RTL bisimulates Coq spec | `hardware_bisimulation` | `kernel/HardwareBisimulation.v` |
| Three layers are isomorphic | `three_layer_isomorphism` | `kernel/ThreeLayerIsomorphism.v` |
| Extraction preserves vm_apply | `vm_step_vm_apply` | `kernel/SimulationProof.v` |
| RTL refinement covers supported opcode paths with explicit unsupported classes | `verilog_simulates_vm_step_*` + gap registry lemmas | `kami_hw/VerilogRefinement.v`, `kami_hw/RTLGapRegistry.v` |

---

## Drift Prevention (CI Gates)

| Gate | What it checks |
|---|---|
| `make isa-proof-freshness-check` | `build/thiele_core.ml` not older than `VMStep.v`/`Extraction.v` |
| `make check-sensitive-files` | No uncommitted changes to `VMStep.v`/`VMState.v`/`Extraction.v` |
| `make proof-undeniable` | Full Coq build + freshness gate |
| Verilator test suite | RTL behavior matches Python VM for all tested opcodes |

---

## Summary

The Thiele Machine has **one normative semantics**: the Coq-proved operational semantics in `coq/kernel/VMStep.v` (the `vm_apply` function and `vm_step` inductive relation). All other layers are implementations derived from this spec, with formal correctness proofs connecting them. When any layer diverges from Coq, the Coq layer wins.
