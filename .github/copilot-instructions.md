# Thiele Machine — Copilot Instructions

This is a proof-first computational physics project. ALL changes flow from Coq proofs outward.

## Architecture: Three Isomorphic Layers

Coq proofs (source of truth) generate:
1. OCaml extraction (`build/thiele_core.ml`) via `coq/Extraction.v`
2. Python VM (`build/thiele_vm.py`)
3. Verilog RTL (`thielecpu/hardware/rtl/thiele_cpu_kami.v`) via Kami/Bluespec from `coq/kami_hw/ThieleCPUCore.v`

All three layers implement the same 26 VM opcodes with identical semantics.

## NEVER Edit Generated Files

- `build/thiele_core.ml` — edit `coq/Extraction.v` instead, then `make -C coq`
- `build/thiele_core.mli` — generated alongside thiele_core.ml
- `thielecpu/hardware/rtl/thiele_cpu_kami.v` — edit `coq/kami_hw/ThieleCPUCore.v` instead, then run `scripts/kami_extract.sh`

## Iteration Workflow

### Quick Verification (Local Development)

Run fast checks locally before pushing:

```bash
# Fast verification only (proof + extraction + tests) — ~15-20 min
./scripts/quick_verify.sh

# Full verification (includes hardware synthesis) — ~45-60 min
./scripts/quick_verify.sh full

# Hardware synthesis only (assumes proof checks already passed)
./scripts/quick_verify.sh hw-only
```

### Manual Step-by-Step

If you need to run steps individually:

1. **Edit Coq source** in `coq/kernel/`, `coq/kami_hw/`, etc.
2. **Build Coq**: `make -C coq -j4` (all `.v` → `.vo`, zero errors)
3. **Audit proofs**: `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md` (must be HIGH=0, MEDIUM=0)
4. **Extract to OCaml** (if VM semantics changed): `make -C coq Extraction.vo` then rebuild:
   ```bash
   ocamlfind ocamlc -I build -package str -linkpkg \
     -o build/extracted_vm_runner \
     build/thiele_core.mli build/thiele_core.ml \
     tools/extracted_vm_runner.ml
   ```
5. **3-layer bisimulation**: `bash scripts/parity_extracted_only.sh`
6. **Kami/Bluespec** (if hardware changed): `./scripts/kami_extract.sh`
7. **Verilator** (if RTL changed): cosim.py auto-rebuilds, or `rm -rf build/verilator && python3 -c "from thielecpu.hardware.cosim import _ensure_verilator_current; _ensure_verilator_current()"`
8. **Python tests**: `python3 -m pytest tests/ -q -m "not coq"`

## CI Workflows

### What Runs Where

The project uses two GitHub Actions workflows:

- **`ci-fast.yml`** (Fast path for PRs)
  - Trigger: `push` to main/master, `pull_request`, `workflow_dispatch`
  - Time: ~20-25 minutes
  - Checks: Proof verification, extraction, 3-layer bisimulation, Python tests, dependency scan
  - Fails fast: Hardware synthesis doesn't run until proof checks pass

- **`ci-full.yml`** (Full verification)
  - Trigger: Nightly (`cron: 0 3 * * *`), manual `workflow_dispatch`
  - Time: ~60-90 minutes
  - Checks: All of `ci-fast.yml` + hardware synthesis + simulation + waveform analysis
  - FPGA bitstream: Only on manual trigger (requires additional tools)

### Why Two Workflows?

**Proof-first architecture:** The three layers (Coq → OCaml → Hardware) have strict ordering:
1. Coq must compile & pass Inquisitor
2. OCaml extraction must succeed
3. Hardware synthesis must succeed

`ci-fast.yml` validates layers 1-2 quickly for PR feedback. `ci-full.yml` adds layer 3 for nightly confidence.

## Local Verification Equivalents

Run these locally to match GitHub Actions:

```bash
# Matches ci-fast.yml (what PRs run)
./scripts/quick_verify.sh

# Matches ci-full.yml (what nightly runs)
./scripts/quick_verify.sh full
```



- **REVEAL, PDISCOVER, CHSH_TRIAL** need: `INIT_LOGIC_ACC 0xCAFEEACE`
- **LOAD, STORE, XOR_LOAD** need: `INIT_PT 0 256` and `INIT_ACTIVE_MODULE 0`
- **LASSERT, LJOIN, REVEAL, CHSH_TRIAL** need: cost > 0 (not 0)

The RTL enforces a logic gate key (`0xCAFEEACE`), locality wall (partition bounds), NoFreeInsight (cost > 0), and Bianchi alarm (mu >= tensor_total).

## RTL Error Codes

- `0xC43471A1` = ERR_LOGIC (logic gate locked)
- `0x0BADC0DE` = ERR_LOCALITY (LOAD/STORE outside bounds)
- `0x0BADC45C` = ERR_CHSH (CHSH cert missing)
- `0xBADF001D` = ERR_PARTITION (partition overflow)
- `0x4E4F4649` = ERR_NOFI (NoFreeInsight cost=0)
- `0x0B1A4C81` = ERR_BIANCHI (mu < tensor_total)
- Trap vector: PC jumps to `0xF00` on errors

## OCaml Extraction Flow

Source of truth: `coq/Extraction.v` extracts to `build/thiele_core.ml`.

The extraction maps Coq types to OCaml:
- `nat` → `int`, `bool` → `bool`, `list` → `list`, `option` → `option`
- `VMState.word32` → bitwise AND with `0xFFFFFFFF`
- `SimulationProof.vm_apply` → `vm_apply_runtime` (with NoFI enforcement)

Build the runner:
```bash
cd build && ocamlfind ocamlc -package str -linkpkg thiele_core.ml ../tools/extracted_vm_runner.ml -o extracted_vm_runner
```

## Kami/Bluespec Flow

Pipeline: Coq/Kami source → OCaml extraction → Bluespec pretty-printer → BSC compiler → Verilog

Key files in the pipeline:
1. `coq/kami_hw/ThieleCPUCore.v` — Kami module definition
2. `coq/kami_hw/KamiExtraction.v` — extracts Kami to OCaml (`build/kami_hw/Target.ml`)
3. `vendor/kami/Kami/Ext/Ocaml/PP.ml` — OCaml → Bluespec printer
4. `build/kami_hw/thiele_hw_clean.bsv` — generated Bluespec
5. BSC compiles to `thielecpu/hardware/rtl/thiele_cpu_kami.v`

Run: `./scripts/kami_extract.sh`

## Inquisitor Finding Fixes

- `PROOF_CONNECTIVITY_GAP`: add `From Kernel Require Import VMStep.` and `From Kernel Require Import MuCostModel.`
- `PHANTOM_KERNEL_IMPORT`: use `vm_instruction` or `VMState` in a definition/theorem
- `CIRCULAR_DEFINITION`: mark with `(* DEFINITIONAL HELPER *)` if legitimate
- `DEFINITIONAL_INVARIANCE`: mark with `(* Definitional lemma *)` comment
- `ZERO_CONST`: mark with `(* SAFE: <reason> *)` if legitimate
- `TAUTOLOGICAL_IMPLICATION`: mark with `(* INQUISITOR NOTE: <reason> *)` if legitimate

## Foundation Connectivity

Every proof file must transitively import from BOTH:
- **Semantics**: VMState, VMStep, VMEncoding, KernelTM, BridgeDefinitions, PythonBisimulation, HardwareBisimulation
- **Cost**: MuCostModel, MuLedgerConservation, MuInitiality, NoFreeInsight

## Enforcement (Non-Negotiable)

- NO `Admitted.` or `admit.` anywhere
- NO tier exemptions — all proofs same standard
- ALL proofs connect to both semantics AND cost foundations
- All 31 opcodes consistent across Coq, OCaml, Python, Verilog
