# OCaml <-> Kami Equivalence Report

Date: 2026-03-01
Workspace: `The-Thiele-Machine`

## Goal
Establish auditable evidence that the Coq-extracted OCaml VM semantics and the Kami/RTL execution path implement the same machine behavior on the exercised instruction/state projections.

## Evidence Chain
1. **Coq -> OCaml extraction execution**
- Harness: `tests/test_bisimulation_complete.py::TestBisimulationCoqPython`
- Compares Coq-extracted runner outputs against Python VM semantics used as shared bridge.
- Command:
```bash
python -m pytest -q tests/test_bisimulation_complete.py::TestBisimulationCoqPython
```
- Result: `6 passed in 4.41s`

2. **Python bridge -> Kami RTL (Verilator backend)**
- Harness: `tests/test_bisimulation_complete.py::TestBisimulationVerilog`
- Backend: `THIELE_RTL_SIM=verilator` (authoritative RTL path in this repo)
- Command:
```bash
THIELE_RTL_SIM=verilator python -m pytest -q tests/test_bisimulation_complete.py::TestBisimulationVerilog
```
- Result: `6 passed in 5.42s`

3. **Opcode / mu-cost / trace-level consistency checks**
- Harnesses:
  - `tests/test_bisimulation_complete.py::TestOpcodeAlignment`
  - `tests/test_bisimulation_complete.py::TestMuCostIsomorphism`
  - `tests/test_bisimulation_complete.py::TestTraceEquivalence`
- Command:
```bash
THIELE_RTL_SIM=verilator python -m pytest -q \
  tests/test_bisimulation_complete.py::TestOpcodeAlignment \
  tests/test_bisimulation_complete.py::TestMuCostIsomorphism \
  tests/test_bisimulation_complete.py::TestTraceEquivalence
```
- Result: `5 passed in 2.89s`

4. **Combined bisimulation run (broad selection)**
- Command:
```bash
python -m pytest -q tests/test_bisimulation_complete.py -k "bisimulation or opcode or mu"
```
- Result: `39 passed in 24.09s`

## What Is Matched
Across these tests, the following projected behaviors are validated through the bridge:
- opcode alignment
- mu-cost accumulation
- key register outcomes
- error/halt projections
- trace/equivalence scenarios in the test suite scope

## Conclusion
Within the tested scope, the repository currently provides **passing constructive evidence** that:
- Coq-extracted OCaml semantics and
- Kami RTL execution (via Verilator)

are behaviorally aligned through the established bisimulation harnesses.

## Scope Notes
- This is strong executable evidence, not a claim of universal equivalence over every untested state/program.
- CHSH semantic contracts are now reconciled with extracted RTL gate ordering:
  - `tests/test_unified_cpu_semantic_contracts.py` passes (`6 passed`).
  - CHSH bit-validation (`0x0BADC45C`) is exercised under the constructive
    precondition `INIT_LOGIC_ACC 0xCAFEEACE`.
  - A dedicated policy-gate test verifies that without this precondition,
    the higher-priority gate emits `0xC43471A1`.
