# The Thiele Machine

**A formally specified machine model where certified structural knowledge carries an explicit cost.**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

I started this trying to build a renderer. It turned into a machine model, a Coq proof tree, an extracted OCaml runtime, generated RTL, and a long paper trail around one claim: raw computation and certified structural knowledge are not the same thing.

The Thiele Machine makes that difference explicit with a monotone ledger called `mu`. Arithmetic, memory traffic, and control flow can be cheap. The moment a trace becomes entitled to reuse a certified structural claim, it pays. That is the No Free Insight boundary this repository is built to formalize, execute, and test.

## Status

This repository is still in active development. The proof tree, extracted artifacts, workflows, tests, and thesis are being tightened together, so generated files and CI structure may still change while the project is being finalized.

If you want the cleanest current statement of scope, rely on the active proof tree, the current CI workflows, and the thesis documents in `thesis/` rather than older generated reports that may lag behind the latest pass.

## First Principles

A Turing machine is the classical baseline in this project: local state, local symbol access, and a transition rule that advances the computation one step at a time. It can compute over structured objects, but certified structure is not first-class state in the model. If a graph decomposes, or two subproblems are independent, that fact is not something the machine carries around as an explicit certified resource.

The Thiele Machine keeps the classical compute surface and adds explicit structural state: a partition graph, certification channels, witness and tensor state, and a monotone `mu` ledger. Programs can build and manipulate structure directly. They can also certify structural claims, and that certification is where the charged boundary lives.

The key design split is deliberate:

- structure creation and manipulation can be cheap or even zero-cost
- certified structural entitlement is not free
- once a trace gains cert evidence, the `mu` ledger must have increased

That is the precise sense in which this repository treats "insight" as something stronger than ordinary computation.

## How Thiele Subsumes Classical Computation

The safe formal statement is not "Thiele computes more than Turing." The safer and stronger statement is:

- every classical program embeds directly into the Thiele VM
- classical traces leave the structural layer frozen
- the full Thiele VM has structural operations that classical traces cannot exercise

In the active proof tree, the embedding is identity-on-programs for the classical fragment, and the conservativity theorems show that classical traces preserve `vm_graph`, `csr_cert_addr`, and `vm_certified`. Separate strictness theorems show that structural Thiele instructions can reach states that no classical trace can reach from the same start state. A separate non-circular subsumption development shows the same computable functions can be simulated while Thiele additionally carries verifiable cost certificates.

So the README should say this plainly: the Thiele Machine subsumes classical computation by containing it as a fragment, then strictly extends that fragment with first-class structure, certification, and cost accounting. This is a claim about richer state and richer observable certificates, not a claim that bare computability suddenly outruns Turing completeness.

If you want the exact theorem surfaces behind that wording, start with:

- `coq/kernel/TuringClassicalEmbedding.v`
- `coq/kernel/ClassicalConservativity.v`
- `coq/kernel/TuringStrictness.v`
- `coq/kernel/ProperSubsumption.v`
- `coq/kernel/ShadowProjection.v`
- `coq/kernel/InsightTaxonomy.v`

## What Lives Here

- `coq/`: the active proof tree, extraction roots, and the standalone completeness file `ThieleMachineComplete.v`
- `build/`: extracted OCaml artifacts, generated Kami outputs, and the compiled runner when you build it
- `thielecpu/`: the generated Python protocol layer around the extracted runner, plus receipt helpers
- `thielecpu/hardware/rtl/`: the tracked RTL surface used by the hardware gates
- `tests/`: parity, gate, fuzz, RTL, receipt, and regression tests
- `thesis/`: the long thesis, short thesis, and mathematical specification
- `tools/`: TRS-1.0 verification tooling
- `artifacts/`: committed manifests and audit outputs used by the closeout tests

## Scope

The strongest claims in this repository are about the machine model itself: the `mu` ledger, certification-cost floors, extraction/RTL provenance, and cross-layer agreement on covered execution paths.

The physics-facing material is still here, but it is not all the same kind of statement. The thesis and math spec separate structural theorems, conditional derivations, and open or analogy-level material on purpose. If you want the cleanest statement of scope, start with:

- `thesis/short_thesis.tex`
- `thesis/thiele_machine_math_spec.tex`

## Quick Start

For the Python environment:

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
pip install -e . --no-deps
```

To build the extracted runner and run the default test surface:

```bash
make ocaml-runner
pytest -q
```

Full proof and hardware gates also need external toolchains:

- Coq `8.18+`
- OCaml with `ocamlfind`
- `iverilog` and/or `verilator`
- `yosys`

## Run a Program

Assemble and run straight through the extracted OCaml backend:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --run
```

Or emit the textual trace format the runner consumes:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm -o build/fibonacci.trace
./build/extracted_vm_runner build/fibonacci.trace
```

If you have the RTL toolchain installed, you can also go through the hardware path:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --sim
```

## Useful Targets

- `make ocaml-runner`: rebuild the extracted OCaml VM runner from the current proof tree
- `make canonical-extract`: rebuild the canonical OCaml and Kami extraction artifacts
- `make canonical-e2e`: run the canonical extraction, RTL, cosim, and smoke pipeline
- `make closeout-gate`: run the repository closeout gate
- `make proof-undeniable`: run the stronger proof gate, including `coqchk` and bitlock checks
- `make rtl-check`: compile-check the tracked RTL with `iverilog`
- `make rtl-cosim`: run the RTL co-simulation tests

Run `make help` for the broader target list.

## Ground Truth Chain

The repo is organized around one semantics source and two generated execution paths:

```text
coq/kernel/VMStep.v
  -> coq/Extraction.v
     -> build/thiele_core.ml
        -> build/extracted_vm_runner
           -> thielecpu/vm.py

coq/kernel/VMStep.v
  -> coq/kami_hw/KamiExtraction.v
     -> build/kami_hw/mkModule1_synth.v
        -> thielecpu/hardware/rtl/thiele_cpu_kami.v
```

`thielecpu/vm.py` is a generated protocol layer. It is not the normative semantics. The extracted OCaml runner is.

## ISA Surface

The active ISA has 46 opcodes. The instruction families cover:

- partition and module structure
- logic and certification
- memory, ALU, and control flow
- tensor and witness operations
- categorical morphism operations

The single-step semantics live in `coq/kernel/VMStep.v`, and the repository gates check that the extraction and RTL surfaces stay aligned with that source.

## Thesis and Specs

- Long thesis: `thesis/main.tex`
- Short thesis: `thesis/short_thesis.tex`
- Mathematical specification: `thesis/thiele_machine_math_spec.tex`
- Bibliography: `thesis/references.bib`

The long thesis is the full narrative. The short thesis is the fastest way to see the core argument without the full chapter load.

## Verification and Receipts

Proof hygiene is generated on demand:

```bash
python scripts/inquisitor.py
```

That command writes a Markdown report at `INQUISITOR_REPORT.md` unless you pass `--report` with another path.

The repository also contains TRS-1.0 receipt tooling:

```bash
python tools/verify_trs10.py path/to/receipt.json --trusted-pubkey <32-byte-hex>
```

Committed closeout manifests and audit artifacts live under:

- `artifacts/`
- `artifacts/final_claim_audit/`

## Project Layout

```text
The-Thiele-Machine/
├── coq/
├── thielecpu/
├── tests/
├── scripts/
├── tools/
├── thesis/
├── examples/
├── artifacts/
└── build/
```

## Citation

```bibtex
@misc{thielemachine2026,
  title={The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author={Thiele, Devon},
  year={2026},
  howpublished={\url{https://github.com/sethirus/The-Thiele-Machine}}
}
```

## License

Apache 2.0. See [LICENSE](LICENSE).

*If this is wrong, the proofs or gates should fail.*
