# WASM Execution Receipts

Deterministic execution receipts for WebAssembly programs.

## Overview

WASM execution receipts prove not just artifact bytes, but **execution output** on fixed input. This enables:

- Reproducible computation verification
- Deterministic function evaluation proofs
- Off-chain computation with on-chain verification

## Receipt Format

```json
{
  "version": "TRS-WASM-1",
  "program": {
    "wasm_sha256": "abc123...",
    "wasm_url": "https://example.com/program.wasm"
  },
  "input": {
    "data_sha256": "def456...",
    "size": 1024
  },
  "output": {
    "stdout_sha256": "ghi789...",
    "stderr_sha256": "jkl012...",
    "exit_code": 0
  },
  "execution": {
    "fuel_consumed": 10000,
    "memory_pages": 2,
    "timestamp": "2025-01-01T00:00:00Z"
  }
}
```

## Usage

### Run and Emit Receipt

```bash
thiele-run --wasm program.wasm \
  --input input.bin \
  --emit-receipt output.receipt.json
```

### Verify Receipt

```bash
thiele-verify-wasm output.receipt.json
```

## Determinism

The WASM VM must be fully deterministic:

1. **Memory**: Fixed initial state, no ASLR
2. **Time**: Mocked `clock_gettime()`
3. **Random**: Seeded PRNG, no `/dev/random`
4. **I/O**: Captured stdout/stderr, no network
5. **Fuel**: Gas metering for bounded execution

## Implementation

Uses Wasmtime with deterministic flags:

```rust
let engine = Engine::new(Config::new()
    .consume_fuel(true)
    .epoch_interruption(true)
    .cranelift_opt_level(OptLevel::None))?;
```

## Security

- ✅ Prevents infinite loops (fuel limit)
- ✅ Prevents OOM (memory limit)
- ✅ Prevents non-determinism (mocked syscalls)
- ✅ Proves computation correctness (output hash)

## Use Cases

- **Smart contracts**: Off-chain execution, on-chain verification
- **Scientific computing**: Reproducible research
- **Distributed computation**: Verify worker outputs
- **Zero-knowledge proofs**: Prove computation without revealing inputs
