# Kami RTL tuple wiring audit (S, Π, A, R, L)

This note documents what is currently wired in `thiele_cpu_kami.v` and what is still abstracted.

## Current status

The extracted Kami core is a **single monolithic module** (`mkModule1`) with these observable state interfaces:

- **S (state/control):** `getPC`, `getMu`, `getErr`, `getHalted`, `getErrorCode`
- **Π (partition table):** `getPtNextId`, `getPtSize`
- **A/R diagnostics for revelation/conservation:** `getMuTensor0..3`, `getBianchiAlarm`

This confirms the tuple is wired for runtime observation and enforcement of the Bianchi guard.

## Logic engine (L) integration reality

The current extraction now includes an **explicit L coprocessor interface** as in-core ports/state:

- Request outputs: `getLogicReqValid`, `getLogicReqOpcode`, `getLogicReqPayload`
- Response input: `setLogicResp(valid,error,value)`

`LASSERT`/`LJOIN` issue a request and stall architectural progression while waiting for response validity.
When response arrives, `logic_acc` consumes `value`; `error=1` maps to protocol `err` with `ERR_LOGIC_VAL`.
`ORACLE_HALTS` remains an in-core opcode update path.

## Remaining L work for a physically separate island

To split L into a distinct hardware module (not just explicit in-core interface registers), still needed:

1. Replace stateful request/response registers with true ready/valid wires to a separate instantiated module.
2. Add timeout/backpressure policy and prove no deadlock under interface assumptions.
3. Prove refinement/observational equivalence against the current in-core interface model.
4. Re-extract and keep `thiele_cpu_kami.v` generated-only (no manual edits).


## Verilator logic bridge (request/response loop)

The canonical testbench now supports an optional external bridge for the in-core
logic interface. Enable with plusarg `+LOGIC_Z3_BRIDGE=1`.

When enabled:
- Testbench reads `getLogicReqValid/getLogicReqOpcode/getLogicReqPayload`.
- It evaluates a deterministic checker in testbench space for LASSERT/LJOIN.
- It drives `setLogicResp(valid,error,value)` for the core.

A standalone helper (`thielecpu/hardware/logic_z3_bridge.py`) is included for
future external-solver wiring, while the in-core request/response protocol is
already fully wired and exercised today.
