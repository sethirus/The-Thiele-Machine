# Example Programs

All 20 example programs are verified to assemble and run correctly in the Thiele VM.

Run all at once:
```bash
python examples/run_all.py
```

---

## Programs

| File | Description |
|------|-------------|
| [benchmark.asm](benchmark.asm) | Instruction throughput benchmark — 100-iteration tight countdown loop |
| [bianchi_violation.asm](bianchi_violation.asm) | Triggers Bianchi conservation violation by REVEALing more than μ — CPU halts with error |
| [chsh_full.asm](chsh_full.asm) | All 4 CHSH (x,a) measurement combinations with op_a, op_b ∈ {0,1} |
| [conditional.asm](conditional.asm) | JNEZ branching demo — counts down from 10, accumulates sum 10+…+1 |
| [edge_cases.asm](edge_cases.asm) | Tests boundary registers (r0, r31) and maximum cost field (255) |
| [emit_discover.asm](emit_discover.asm) | EMIT + PDISCOVER — observable events and information-gain accumulation |
| [fibonacci.asm](fibonacci.asm) | First 8 Fibonacci numbers, stored in mem[0..7] |
| [hello_world.asm](hello_world.asm) | Hello World via EMIT opcodes, then HALT |
| [lassert_ljoin.asm](lassert_ljoin.asm) | LASSERT + LJOIN — logic assertion and certificate delegation |
| [mdl_acc.asm](mdl_acc.asm) | MDLACC — Minimum Description Length accumulation demo |
| [memory_test.asm](memory_test.asm) | STORE + LOAD round-trip verification across multiple addresses |
| [mu_demo.asm](mu_demo.asm) | μ monotonically increases — every instruction charges non-negative cost |
| [oracle_demo.asm](oracle_demo.asm) | ORACLE_HALTS — non-deterministic oracle probe (no-op in reference VM) |
| [partition_demo.asm](partition_demo.asm) | PNEW + PSPLIT + PMERGE + PDISCOVER — partition graph operations |
| [popcount.asm](popcount.asm) | Hamming weight (popcount) via XOR_RANK for several bit patterns |
| [reveal_sweep.asm](reveal_sweep.asm) | REVEAL all 16 μ_tensor entries (indices 0–15), charging cost=1 each |
| [stack_demo.asm](stack_demo.asm) | Manual LIFO stack emulation via STORE/LOAD at fixed literal addresses |
| [stress_test.asm](stress_test.asm) | 200 × 10 = 2,000 inner iterations — long-running correctness test |
| [subroutine.asm](subroutine.asm) | CALL/RET subroutine demo — multiply-by-2 via a called function |
| [xor_alu.asm](xor_alu.asm) | XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK — all XOR-family instructions |

---

## Running a Single Program

```bash
# Assemble to hex
thiele-asm examples/fibonacci.asm -o fibonacci.hex

# Run interactively in the debugger
thiele-debug fibonacci.hex
# > run
# HALTED  pc=22  mu=22  mem[0..7]=[0,1,1,2,3,5,8,13]

# Or run non-interactively
python -c "
from thielecpu.assembler import Assembler
from thielecpu.debugger import ThieleVM
asm = Assembler()
prog = asm.assemble_file('examples/fibonacci.asm')
vm = ThieleVM(prog)
result = vm.run()
print(result)
"
```

---

## Expected Results Summary

| Program | Cycles | μ-cost | Notes |
|---------|--------|--------|-------|
| benchmark | 202 | 201 | 100-iter loop |
| bianchi_violation | 7 | — | err=True (expected) |
| chsh_full | 5 | 4 | 4 CHSH_TRIAL + HALT |
| conditional | ~25 | ~24 | Sum 10+…+1 = 55 in r2 |
| edge_cases | ~8 | — | Boundary register/cost tests |
| fibonacci | ~22 | 22 | mem[0..7] = Fibonacci sequence |
| stress_test | 4032 | 4031 | 2000-iteration nested loop |

Bianchi violation programs are expected to set `err=True` — this is **correct** behaviour.
