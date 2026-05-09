# kernel/hardware_bridge

The three-layer isomorphism: Coq kernel ≡ Python VM ≡ Verilog RTL. These
files state and prove the abstract bisimulation contracts that
[`coq/kami_hw/`](../../kami_hw/) then instantiates with concrete Kami
hardware.

## Files

| File | Purpose |
|---|---|
| `ThreeLayerIsomorphism.v` | `WireSpec` and `FullWireSpec` contracts; abstract μ/PC/full-state agreement |
| `VerilogRTLCorrespondence.v` | Final formal RTL ↔ Coq correspondence (closes via Section Variable) |
| `HardwareBisimulation.v` | `hw_bisimulation_step`, `complete_verification_chain`, `hardware_synthesis_correctness` |
| `PythonBisimulation.v` | Python `step` ↔ Coq `vm_apply` correspondence |
| `OCamlExtractionBridge.v` | Names the OCaml extraction trust boundary as a tracked axiom |

## Load-bearing exports cited from the README

- `complete_verification_chain`, `hardware_synthesis_correctness`,
  `hw_bisimulation_step`, `hw_bisimulation_multi_step`,
  `hw_step_reflects_vm_cost`, `hw_mu_cost_consistency`, `mu_accumulation_monotonic`
- The opcode-bisim family `embed_step_*` / `full_embed_step_*` lives in
  [`coq/kami_hw/`](../../kami_hw/), but its abstract contracts live here.

## Imports

`foundation/`, `mu_calculus/`. No imports from `quantum/` or `curvature/`.

## Trust boundary

The README's named axiom `bsc_kami_compilation_trusted` (BSC compiler
→ physical Verilog) is the only place these files cross from formal proof
to external tools. See `OCamlExtractionBridge.v` and
`VerilogRTLCorrespondence.v` for the explicit trust-boundary statements.
