# kernel/hardware_bridge

Abstract comparison contracts between the Coq kernel, the Python VM, and the
Verilog RTL: any two implementations satisfying `WireSpec` agree on mu and pc,
and the cost-level hardware/Python model agrees on mu and pc over a list of
costs. No concrete Python or Verilog artifact is shown to satisfy them in this
directory; [`coq/kami_hw/`](../../kami_hw/) carries the concrete Kami
hardware step.

## Files

| File | Purpose |
|---|---|
| `ThreeLayerIsomorphism.v` | `WireSpec` and `FullWireSpec` contracts; abstract μ/PC/full-state agreement of any two implementations that satisfy them |
| `VerilogRTLCorrespondence.v` | Conditional correspondence between a projected RTL execution model and the Coq VM; the theorems require `rtl_step_correct`, and the trust propositions (`bsc_kami_compilation_trusted`) only label external obligations |
| `HardwareBisimulation.v` | Cost-level model agreement over a 4-field abstraction (pc, mu, alu_ready, overflow): `hw_bisimulation_step`, `complete_verification_chain`, `hardware_synthesis_correctness` |
| `PythonBisimulation.v` | Abstract Coq/Python correspondence for shared pc and mu, tracking error and module count; not full equality of the Python implementation with the Coq semantics |
| `OCamlExtractionBridge.v` | Names the OCaml extraction trust boundary as a premise inside `Section ExtractionBisimulationHypothesis`; the file declares no `Axiom` |

## Load-bearing exports cited from the README

- `complete_verification_chain`, `hardware_synthesis_correctness` (cost-level
  model agreement; the Kami step is `driven_step_wf` in
  [`coq/kami_hw/GraphReconstructionBridge.v`](../../kami_hw/GraphReconstructionBridge.v)),
  `hw_bisimulation_step`, `hw_bisimulation_multi_step`,
  `hw_step_reflects_vm_cost`, `hw_mu_cost_consistency`, `mu_accumulation_monotonic`
- The opcode-bisim family `embed_step_*` / `full_embed_step_*` lives in
  [`coq/kami_hw/`](../../kami_hw/), but its abstract contracts live here.

## Imports

`foundation/` and `nfi/`. No imports from `quantum/` or `curvature/`.

## Trust boundary

The named premise `bsc_kami_compilation_trusted` (a `Definition ... : Prop`
in `VerilogRTLCorrespondence.v`, not an axiom; BSC compiler to physical
Verilog) is the only place these files cross from formal proof
to external tools. See `OCamlExtractionBridge.v` and
`VerilogRTLCorrespondence.v` for the explicit trust-boundary statements.
