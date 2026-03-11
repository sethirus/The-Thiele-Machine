# Isomorphism Finish-Order Roadmap

This roadmap translates current audit gaps into execution priority.

```mermaid
flowchart TD
    R0[Current Baseline
proof-undeniable + isomorphism-bitlock PASS]
    R1[P0: Coq FullWireSpec discharge
(concrete non-Coq instantiation)]
    R2[P1: Lockstep corpus expansion
(edge/corner/fuzz traces)]
    R3[P1: Receipt end-to-end closure
(proof + runtime anti-forgery)]
    R4[P2: Dual-simulator parity
(iverilog + verilator)]
    R5[Release Readiness
mathematical + visual + runtime closure]

    R0 --> R1 --> R2 --> R5
    R1 --> R3 --> R5
    R2 --> R4 --> R5

```

## Priority Policy

- P0: theorem-surface obligations that block full mathematical closure
- P1: runtime confidence expansion and attack-surface closure
- P2: robustness and environment parity hardening

## Programmatic Backlog

See `artifacts/isomorphism_development_backlog.json` for machine-readable tasks.
