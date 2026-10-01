---
name: c1c2-scope-decision
description: Devon chose (2026-09-14) full-generality C2 and adding hardware storage for tensors/CSR status/heap_base
metadata:
  type: project
---
Asked on 2026-09-14. Devon chose: (1) ADD HARDWARE STORAGE in ThieleCPUCore for per-module tensors (TENSOR_SET/GET) and CSR status and heap_base, then regenerate BSV/Verilog and re-audit C3; (2) C2 at FULL GENERALITY: every opcode including all multi-cycle FSMs (LASSERT SAT scan, CHSH_LASSERT, MORPH/COMPOSE/MORPH_TENSOR coupling, normalization, commit) over all admitted states, with invariants and retirement progress.

**Why:** They want the closest reading of the contract and accepted the longest path when the options were laid out.

**How to apply:** Do not scope down. Proof architecture found feasible: vm_compute on observe_dispatch_write with opaque register/memory/mu contents, instruction operand fields shattered into symbolic bits (Word.combine of w8 bit literals), and instruction memory as a constant function so a symbolic pc can fetch (probe took 0.18 s). Fault guards stay symbolic and need case analysis against admission premises. Related: [[b3-self-interpreter-closed]], [[guarded-coq-builds]].
