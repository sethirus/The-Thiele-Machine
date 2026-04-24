# The Thiele Machine

**A formally verified machine model where certified structural knowledge carries an explicit, monotone cost.**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

I started this in January 2025 trying to build a 3D renderer. It turned into a machine model, a Coq proof tree, an extracted OCaml runtime, generated RTL hardware, and a thesis — all built around one claim: raw computation and certified structural knowledge are not the same thing, and that difference has a price you cannot avoid.

The price is tracked by a monotone ledger called `mu`. Arithmetic, memory traffic, and control flow can be zero-cost. The moment a trace becomes entitled to reuse a certified structural claim — a decomposition, a morphism, a formula with a witness — it pays. That is the No Free Insight boundary this repository formalizes, executes, and tests.

**Current state:** 952 tests pass. Zero Admitted in the active proof tree. Zero Inquisitor findings. All 46 opcodes have formal hardware bisimulation proofs.

## The core idea

A Turing machine sees one tape cell at a time. It can compute over structured objects, but structure is not first-class state. If a graph decomposes into independent components, or two subproblems share no variables, the machine has no primitive way to know that. It has to compute its way to that knowledge, and it pays the same cost whether the structure was obvious or hard-won.

The Thiele Machine keeps the full classical compute surface and adds explicit structural state: a partition graph, certification channels, witness counters, a tensor layer, and the `mu` ledger. Programs can build and manipulate structure at zero cost. Certifying a structural claim is what costs. The design split is deliberate:

- structure creation can be cheap — even free
- certified structural entitlement is never free
- once a trace gains certified evidence, `mu` must have increased — proven, not assumed

That is what "No Free Insight" means. It is a machine-checked theorem, not a slogan.

## What the proofs establish

The Thiele Machine contains classical computation as a fragment and strictly extends it:

- every classical program embeds directly into the Thiele VM, leaving the structural layer untouched (`TuringClassicalEmbedding.v`, `ClassicalConservativity.v`)
- there exist Thiele states reachable by structural instructions that no classical trace can reach from the same start (`TuringStrictness.v`, `ShadowProjection.v`)
- `mu` is the unique canonical cost measure — any other instruction-consistent, zero-starting, monotone functional equals `mu` on every reachable state (`MuInitiality.v`)
- the `mu` balance, certification flag, and partition graph are each provably independent of strict classical state `(mem, regs, pc)` and of each other — five independence results, complete classification, from every reachable state, for any prefix computation of any length (`NecessityOfMuLedger.v`, `NecessityAbstract.v`)
- the `mu`-cost of any program is intrinsic to the instruction sequence: any instruction-consistent accounting system starting at zero assigns exactly `trace_total_cost` to the result — the Turing machine was always paying this cost, silently, on every execution (`NecessityOfMuLedger.v` §7)
- certification requires positive `mu`, unconditionally, for both cert channels, over any trace of any length (`AbstractNoFI.v`, `NoFreeInsight.v`)
- classical projection loses morphism structure — two states with identical registers, memory, mu, and PC can differ in ways no classical function can see (`PartitionSeparation.v`)
- the Tsirelson bound |S| ≤ 2√2 is proven by two independent routes: (1) from PSD of the zero-marginal NPA moment matrix (`MuLedgerQuantumBridge.v`), and (2) from algebraic coherence alone via Positivstellensatz SOS certificate — pure polynomial arithmetic, no physics premises (`AlgebraicCoherence.v`)

The full claim ledger is in `thesis/short_thesis.tex`, Section 12. Every claim there has a Coq file and a falsification condition.

## Repository layout

```text
coq/                  proof tree, extraction roots, ThieleMachineComplete.v
build/                extracted OCaml artifacts, compiled runner, Kami outputs
thielecpu/            generated Python protocol layer, receipt helpers
thielecpu/hardware/rtl/  tracked RTL surface
tests/                parity, gate, fuzz, RTL, receipt, and regression tests
thesis/               long thesis, short thesis, math spec
tools/                TRS-1.0 verification tooling
scripts/              build and audit scripts
artifacts/            committed manifests and closeout audit outputs
```

## Ground truth chain

One semantics source, two execution paths:

```text
coq/kernel/VMStep.v
  -> coq/Extraction.v
     -> build/thiele_core.ml
        -> build/extracted_vm_runner      (OCaml)
           -> thielecpu/vm.py             (generated protocol layer)

coq/kernel/VMStep.v
  -> coq/kami_hw/KamiExtraction.v
     -> build/kami_hw/mkModule1_synth.v
        -> thielecpu/hardware/rtl/thiele_cpu_kami.v
```

`thielecpu/vm.py` is generated. It is not the normative semantics. The extracted OCaml runner is. `build/thiele_core.ml` and `build/thiele_core_complete.ml` are bit-for-bit identical — the CI checks this on every commit.

## Quick start

```bash
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt && pip install -e . --no-deps
make ocaml-runner
pytest -q
```

Full proof and hardware gates also need: Coq 8.18+, OCaml with `ocamlfind`, `iverilog` and/or `verilator`, `yosys`.

## Run a program

Assemble and run through the extracted OCaml backend:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --run
```

Or emit the trace format the runner consumes directly:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm -o build/fibonacci.trace
./build/extracted_vm_runner build/fibonacci.trace
```

Through the RTL path (needs iverilog):

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --sim
```

## Key make targets

| Target | What it does |
|--------|-------------|
| `make ocaml-runner` | Rebuild the extracted OCaml runner from the current proof tree |
| `make canonical-extract` | Rebuild canonical OCaml and Kami extraction artifacts |
| `make canonical-e2e` | Full extraction → RTL → cosim → smoke pipeline |
| `make closeout-gate` | Full repository closeout gate (proof + extraction + tests + bitlock) |
| `make proof-undeniable` | Stronger gate: adds `coqchk` and bitlock checks |
| `make rtl-synth` | Yosys synthesis + circuit diagram (DOT/SVG in `artifacts/synthesis_gate/`) |
| `make rtl-cosim` | RTL co-simulation tests |
| `make rtl-verify` | Compile + synthesize + cosim in one shot |

`make help` for the full list.

## ISA

46 opcodes. Five families:

| Family | Opcodes | Cost floor |
|--------|---------|-----------|
| Partition and module structure | PNEW, PSPLIT, PMERGE, PDISCOVER | 0 (programmer-declared) |
| Logic and certification | LASSERT, LJOIN, MDLACC | LASSERT: `flen×8 + S(delta) ≥ 1` |
| Memory, ALU, control flow | LOAD, STORE, ADD, JUMP, HALT, ... | 0 |
| Witness, tensor, cert flags | CHSH_TRIAL, CERTIFY, REVEAL, TENSOR_SET/GET | CERTIFY/REVEAL: `S(delta) ≥ 1` |
| Categorical morphisms | MORPH, COMPOSE, MORPH_ID, MORPH_ASSERT, ... | MORPH_ASSERT: `S(delta) ≥ 1` always |

Single-step semantics: `coq/kernel/VMStep.v`. The CI checks that extraction and RTL stay aligned with that source.

## Thesis and specs

| Document | Path | What it is |
|----------|------|-----------|
| Short thesis | `thesis/short_thesis.tex` / `.pdf` | The fastest path to the core argument |
| Long thesis | `thesis/main.tex` / `.pdf` | Full 13-chapter narrative |
| Math spec | `thesis/thiele_machine_math_spec.tex` / `.pdf` | Complete mathematical specification |

Start with the short thesis. It covers everything from the Turing machine blind spot through CHSH and the physics bridges, with every claim tagged to a Coq file and a falsification condition.

## Proof hygiene

Run the Inquisitor on demand:

```bash
python scripts/inquisitor.py
```

It writes `INQUISITOR_REPORT.md`. Zero HIGH/MEDIUM/LOW findings means the proof tree is clean. If that number is nonzero, something degraded.

TRS-1.0 receipts:

```bash
python tools/verify_trs10.py path/to/receipt.json --trusted-pubkey <32-byte-hex>
```

## How to break this

Every claim has a concrete falsification condition. The main ones:

- **Falsify No Free Insight**: find a trace starting with `vm_certified = false`, `mu = 0`, ending with `vm_certified = true`, `mu = 0`. Add it as a Coq theorem — the proof of `certification_requires_positive_mu` won't compile.
- **Falsify ledger necessity**: define a total function from strict classical state `(mem, regs, pc)` that recovers `vm_mu` or `vm_certified` for every VM state. This contradicts `mu_ledger_necessity`, `vm_mu_not_classically_determined`, or `vm_certified_not_classically_determined`.
- **Falsify mu-monotonicity**: find a state `s` and instruction `i` where `(vm_apply s i).mu < s.mu`. `vm_apply_mu` fails.
- **Falsify categorical separation**: prove all states with identical classical shadow produce identical behavior. Contradicts `categorical_separation`.
- **Falsify the hardware bisimulation**: find an opcode where the Kami hardware step diverges from `vm_apply`. The bisimulation proof for that opcode won't close.
- **Run the gates**: `make closeout-gate`. If anything is wrong, it fails loudly.

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
