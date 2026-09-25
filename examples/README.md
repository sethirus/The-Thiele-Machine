# Example Programs

This directory contains the compatibility examples at its top level and the larger program corpus under `examples/programs/`.

`examples/run_all.py` finds both locations and runs them through the current extracted VM API.

Run the whole example set with:

```bash
python examples/run_all.py
```

## Programs

These are the top-level compatibility examples.

| File | Description |
|------|-------------|
| [benchmark.asm](benchmark.asm) | Runs a 100-iteration countdown loop for a small throughput check. |
| [bianchi_violation.asm](bianchi_violation.asm) | Exercises the error path by revealing more than the selected μ budget permits. |
| [chsh_full.asm](chsh_full.asm) | Runs all four CHSH setting combinations with binary settings. |
| [conditional.asm](conditional.asm) | Counts down from 10 and accumulates the sum from 10 through 1. |
| [edge_cases.asm](edge_cases.asm) | Exercises boundary registers and the maximum encoded cost field. |
| [emit_discover.asm](emit_discover.asm) | Runs EMIT and PDISCOVER together as an observable-event example. |
| [fibonacci.asm](fibonacci.asm) | Stores the first eight Fibonacci numbers in memory. |
| [hello_world.asm](hello_world.asm) | Emits a short greeting and then halts. |
| [lassert_ljoin.asm](lassert_ljoin.asm) | Exercises a logic assertion followed by certificate delegation. |
| [mdl_acc.asm](mdl_acc.asm) | Demonstrates minimum-description-length accumulation. |
| [memory_test.asm](memory_test.asm) | Checks STORE and LOAD round trips at several addresses. |
| [mu_demo.asm](mu_demo.asm) | Shows that the selected VM ledger does not decrease during this trace. |
| [checkpoint_demo.asm](checkpoint_demo.asm) | Exercises CHECKPOINT labels and their scheduled costs. |
| [partition_demo.asm](partition_demo.asm) | Exercises PNEW, PSPLIT, PMERGE, and PDISCOVER. |
| [popcount.asm](popcount.asm) | Computes Hamming weights with the XOR_RANK family. |
| [reveal_sweep.asm](reveal_sweep.asm) | Reads the 16 μ-tensor entries and charges the scheduled cost. |
| [stack_demo.asm](stack_demo.asm) | Emulates a small LIFO stack with STORE and LOAD. |
| [stress_test.asm](stress_test.asm) | Runs 2,000 inner-loop iterations as a longer correctness check. |
| [subroutine.asm](subroutine.asm) | Demonstrates a CALL/RET subroutine that multiplies by two. |
| [xor_alu.asm](xor_alu.asm) | Exercises the XOR_LOAD, XOR_ADD, XOR_SWAP, and XOR_RANK instructions. |

The `examples/programs/` directory contains broader ISA coverage and larger workloads, including `all_opcodes_test.asm`, `goldbach_witness.asm`, `stress_memory.asm`, and the tensor examples.

## Running a single program

The assembler driver for single-program runs is `scripts/thiele_asm.py`.

Assemble and run through the extracted OCaml runner with:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --run
```

Assemble and run through Verilator RTL cosimulation with:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --sim
```

Write a trace, hexadecimal file, or binary file instead of running it by choosing an output path.

```bash
python scripts/thiele_asm.py examples/fibonacci.asm -o build/fibonacci.trace
```

The output format is inferred from the extension unless `--format` is supplied.

Run every example through the same path with:

```bash
python examples/run_all.py
```

## Expected results

These are representative outcomes, not fixed promises about every implementation detail.

Exact `pc` and `mu` values depend on the current assembler and VM implementation.

| Program | Runtime shape | μ-cost | Expected behavior |
|---------|---------------|--------|-------------------|
| benchmark | finite loop | positive | Completes the countdown sanity check. |
| bianchi_violation | early stop | error path | Sets `err=True` by design. |
| chsh_full | short trace | small positive | Exercises the CHSH instruction path. |
| conditional | short loop | positive | Checks branching and arithmetic. |
| fibonacci | finite loop | positive | Leaves the Fibonacci sequence in memory. |
| stress_test | long loop | larger positive | Runs the extended execution check. |

The Bianchi-violation example is expected to set `err=True`; that is the behavior the example is checking.
