# Thiele Machine Extension Plan
## External Memory, I/O, and Persistent Storage

**Date:** 2026-03-03
**Status:** Kami Hardware Layer Complete — 31 opcodes, all formally proven, hardware Coq source updated
**Scope:** Extend the Thiele Machine with external memory access, I/O channels, and
checkpoint/resume persistence without breaking the existing 1134-passing test suite
or any Coq proofs.

---

## What Currently Exists (Baseline)

- 26 opcodes, all formally proven in Coq, extracted to OCaml, mirrored in Verilog RTL
- 256-word flat memory, 32 registers, 16-entry μ-tensor
- Zero `Admitted.`, Inquisitor clean (0 HIGH, 0 MEDIUM)
- 1134 tests passing, 4 skips (environmental), 0 xfails
- No I/O mechanism of any kind — machine is closed-form
- No checkpoint or resume — one-shot JSON output after termination
- FUEL capped at 256 by default (trivially overridden with `FUEL <n>` directive)

---

## Design Constraint: The Determinism Requirement

The Coq step relation `vm_step` is a pure function. It cannot read from an external
source at runtime without breaking the proof structure. This forces a choice for any
I/O mechanism:

**Philosophy A (Trace-declared I/O):** Input values are embedded in the instruction
trace at program-generation time. Execution stays deterministic; proofs hold.
Example: `READ_PORT r0 stdin 42 8 1` — value 42 is pre-declared in the instruction.

**Philosophy B (Harness-mediated I/O):** The OCaml runner intercepts special directives
and does real syscalls, injecting results outside the Coq universe. Fast to implement,
zero Coq regression risk, but the formal proofs don't cover the execution path.

Both philosophies can coexist. Phase 1 uses Philosophy B (harness only). Phase 2
promotes to Philosophy A (proven).

---

## Impact Map: What Each Change Touches

### Adding a new `vm_instruction` constructor (any new Coq opcode)

**Coq files that will fail to compile** (exhaustive match expressions):

| File | What breaks |
|---|---|
| `coq/kernel/VMStep.v` | `instruction_cost`, `is_cert_setterb` |
| `coq/kernel/SimulationProof.v` | `vm_apply_unsafe` (the main step function, lines 243-510) |
| `coq/kernel/VMEncoding.v` | `compile_vm_operation` |
| `coq/kernel/MuLedgerConservation.v` | `vm_apply_mu` proof tactic (`destruct instr; simpl`) |
| `coq/kernel/MuCostDerivation.v` | `derived_instruction_cost` (2 matches + 1 destruct) |
| `coq/kernel/QuantumBound.v` | `quantum_admissible` (2 matches + 2 destructs) |
| `coq/kernel/RevelationRequirement.v` | 2 matches + 1 destruct |
| `coq/kernel/MuNoFreeInsightQuantitative.v` | 2 destruct tactics |
| `coq/kernel/StressEnergyDynamics.v` | 1 match + 1 destruct |
| `coq/kernel/PythonBisimulation.v` | 1 match + 1 destruct |
| `coq/kernel/CPURefinement.v` | `match next_instr with` |
| `coq/kernel/Kernel.v` | 1 match |
| `coq/kernel/CHSHExtraction.v` | 1 match |
| `coq/kernel/ThreeLayerIsomorphism.v` | 2 matches (both use `\| _ => true` — auto-handled) |
| `coq/kernel/MuCostModel.v` | Uses `\| _ => 0` wildcard — auto-handled |
| All `coq/thielemachine/coqproofs/*.v` | CoreSemantics.v (5 sites), BellInequality.v, BellReceiptSoundness.v (5 sites), ThieleMachineConcrete.v (3 sites), ThieleKernelCausality.v (2 sites) |
| `coq/thielemachine/verification/*.v` | Symmetry.v, Admissibility.v, Prediction.v |
| `coq/thieleuniversal/verification/BridgeDefinitions.v` | 1 destruct |

**Also required:**
- `tools/extracted_vm_runner.ml` — add parse case for new opcode text
- `build/thiele_core.ml` — auto-updated by `make -C coq` (Extraction.v includes `vm_instruction` as a whole type)
- Recompile OCaml binary
- `build/thiele_vm.py` `_run_python` fallback — add or document skip behavior
- Inquisitor: any new `.v` file needs `From Kernel Require Import VMStep MuCostModel.`

**Does NOT need updating:**
- `coq/bridge/PythonMuLedgerBisimulation.v` — abstracts over delta, not instructions
- `coq/kernel/HardwareBisimulation.v` — instruction-agnostic
- `coq/kami_hw/CanonicalCPUProof.v` — only needs update if adding a hardware-level proof for the new opcode
- `coq/Extraction.v` — `vm_instruction` type is extracted as a whole automatically

### Adding a new `CSRState` field

The CSR record has 3 fields today. Adding `csr_heap_base` cascades to
**~15 files** with direct `{| csr_cert_addr := ...; |}` construction syntax:

`VMState.v` (csr_set_* helpers), `MuCostModel.v` (3 sites), `TsirelsonUpperBound.v`
(4 sites), `KernelPhysics.v` (4 sites), `MuInitiality.v`, `MuGravity.v`,
`ClassicalBound.v`, `NonCircularityAudit.v`, `PartitionSeparation.v`,
`TsirelsonLowerBound.v`, `PhysicsEmbedding.v`, `WaveEmbedding.v`,
`DissipativeEmbedding.v`, `Extraction.v`.

All changes are mechanical (add `csr_heap_base := 0` to each constructor) but a
`make -C coq` full rebuild is required.

### Changing `MEM_SIZE` from 256

`VMState.v:653` is the Coq constant. The following will diverge if only this is changed:
- Python VM (`thielecpu/state.py`) — hardcoded to 256 entries
- Verilog RTL — 256 individual `Register "mem0"..."mem255"` declarations, hardcoded
  memory bus at `MemAddrSz = 8` (type-level in Kami)
- `tools/extracted_vm_runner.ml` — 4 literal `256`s in `make_list`/`list_set_mod`
- Tests in `test_bisimulation_complete.py`, `test_extracted_vm_runner.py` that compare
  `extracted["mem"]` arrays will fail if OCaml produces 1024-element arrays while Python
  has 256

Safe path: change `MEM_SIZE` for the **software VM only** (Coq + OCaml runner), leave
RTL at 256. The three layers then have different memory sizes, which is acceptable if
the software VM is the primary execution target and you don't need RTL validation for
programs using memory beyond address 255.

---

## The Plan: Five Phases

---

### Phase 0 — Extraction Gap Closure (PREREQUISITE) ✅ COMPLETE
**Completed 2026-03-03.** All gaps closed, gates passed:
- `make -C coq -j4` — zero errors
- Inquisitor — 0 HIGH, 0 MEDIUM
- `pytest` — 1131 passed, 7 skipped, 0 failed

**Summary of changes:**
- Deleted stale `vm_instructions.py` and redundant `generate_python_from_coq.py`
- Fixed `make generate-python` to invoke `forge.py` (the active pipeline)
- Added all 9 missing opcode handlers to `thielecpu/vm.py`
- Extended `PythonBisimulation.v` with jump/branch bisimulation theorems
- Added per-instruction `vm_step` witnesses to `VerilogRefinement.v` (all 26 opcodes)
- Connected `HardwareBisimulation.v` to `vm_step` via `hw_step_reflects_vm_cost`
- Fixed `VMStep.v` header comment (18 → 26, removed PYEXEC)
- Updated `CanonicalCPUProof.v` (removed reference to deleted duplicate theorem)

#### Current Gaps

| Layer | Gap |
|---|---|
| `thielecpu/generated/vm_instructions.py` | Has stale `InstrPyexec` (no Coq constructor). Missing 9 classes: Load_imm, Load, Store, Add, Sub, Jump, Jnez, Call, Ret. Says `INSTRUCTION_COUNT = 18`, should be 26. |
| `scripts/generate_python_from_coq.py` | **Does not exist** — Makefile `generate-python` target is broken |
| `thielecpu/vm.py` | No dispatch handlers for 9 opcodes (LOAD_IMM, LOAD, STORE, ADD, SUB, JUMP, JNEZ, CALL, RET) — they raise `ValueError`. Still handles dead `PYEXEC` and `PYTHON` opcodes with no Coq counterpart. |
| `coq/kernel/PythonBisimulation.v` | Excludes JUMP/JNEZ/CALL/RET from PC bisimulation — `python_step_abstract` only models `pc := pc + 1` |
| `coq/kami_hw/VerilogRefinement.v` | Only LOAD_IMM has a constructive `vm_step` simulation witness. 25 instructions unrefined. `verilog_oracle_halts_charge_sound` is a duplicate of `verilog_mu_non_decreasing_on_charge`. |
| `coq/kernel/HardwareBisimulation.v` | Proves bisimulation between abstract `hardware_step`/`python_step` functions that are disconnected from actual `vm_step` or Kami abstraction. No theorem connects to any concrete instruction. |
| `coq/kernel/VMStep.v` | Header comment says "18 instructions" and mentions PYEXEC in the special group, but actual inductive has 26 constructors and no PYEXEC. |

#### 0A. Remove stale `vm_instructions.py` and fix `generate-python` Makefile target

**Finding:** `thielecpu/generated/vm_instructions.py` is **unused** — nothing imports it.
The ACTIVE generation pipeline is `scripts/forge.py`, which reads the OCaml extraction
(`build/thiele_core.ml`) and produces `thielecpu/generated/generated_core.py` with all
26 instruction tags. This is the correct proof-first flow: Coq → OCaml extraction → forge.py → Python.

**What:**
- Delete `thielecpu/generated/vm_instructions.py` (stale, unused, redundant)
- Delete `scripts/generate_python_from_coq.py` (if present — duplicates forge.py's job)
- Update Makefile `generate-python` target to invoke `scripts/forge_artifact.sh` instead
  of the nonexistent/redundant script
- Verify `generated_core.py` has all 26 instruction tags (it already does)

**Files:**
- `thielecpu/generated/vm_instructions.py` (delete)
- `scripts/generate_python_from_coq.py` (delete if present)
- `Makefile` (update `generate-python` target)

#### 0C. Add missing opcode handlers to `thielecpu/vm.py`

**What:** Add dispatch branches for all 9 missing opcodes, matching `vm_step`
semantics from VMStep.v exactly:

| Opcode | Semantics (from vm_step) |
|---|---|
| LOAD_IMM | `regs[dst] = imm & 0xFFFFFFFF` (word32), PC += 1 |
| LOAD | `regs[dst] = mem[addr]`, PC += 1 |
| STORE | `mem[addr] = regs[src]`, PC += 1 |
| ADD | `regs[dst] = (regs[rs1] + regs[rs2]) & 0xFFFFFFFF`, PC += 1 |
| SUB | `regs[dst] = (regs[rs1] - regs[rs2]) & 0xFFFFFFFF`, PC += 1 |
| JUMP | PC = target (not PC+1) |
| JNEZ | if regs[rs] != 0: PC = target, else PC += 1 |
| CALL | mem[SP] = PC+1; SP += 1; PC = target (r31 = SP) |
| RET | SP -= 1; PC = mem[SP] (r31 = SP) |

Also deprecate PYEXEC and PYTHON handlers — they have no Coq counterparts.

**Files:** `thielecpu/vm.py`

#### 0D. Extend `PythonBisimulation.v` for jump instructions

**What:** The current bisimulation only covers instructions where `increments_pc = true`.
Add coverage for the 4 control-flow instructions:

- Add `python_step_jump (target cost)` abstract function: `pc := target, mu := mu + cost`
- Add `bisimulation_step_jump` theorem for JUMP
- Add `bisimulation_step_jnez_taken` / `_not_taken` theorems for JNEZ
- Add `bisimulation_step_call` / `_ret` theorems for CALL/RET
- Keep existing `bisimulation_step` for non-jump instructions unchanged

The key insight: JUMP/JNEZ-taken use `jump_state` (PC = target), JNEZ-not-taken uses
`advance_state` (PC + 1), CALL/RET use `jump_state_rm` (PC = target, modified regs/mem).
All charge mu identically via `apply_cost`.

**Files:** `coq/kernel/PythonBisimulation.v`

#### 0E. Add per-instruction witnesses to `VerilogRefinement.v`

**What:** Add `verilog_simulates_vm_step_<opcode>` theorems for all 25 remaining
instructions, following the same pattern as the existing `verilog_simulates_vm_step_load_imm`:

```coq
Theorem verilog_simulates_vm_step_<opcode> :
  forall (hs : KamiSnapshot) <params>,
    exists vs',
      vm_step (abs_phase1 hs) (instr_<opcode> <params>) vs' /\ vs' = <state>.
```

Group by category:
- Structural: PNEW, PSPLIT (success/failure), PMERGE (success/failure), PDISCOVER
- Logical: LASSERT (SAT/UNSAT), LJOIN (equal/mismatch), EMIT, REVEAL
- Compute: LOAD, STORE, ADD, SUB, XFER
- Control: JUMP, JNEZ (taken/not-taken), CALL, RET
- XOR: XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
- Special: MDLACC, CHSH_TRIAL (ok/badbits), ORACLE_HALTS, HALT

Remove duplicate `verilog_oracle_halts_charge_sound`.

**Files:** `coq/kami_hw/VerilogRefinement.v`

#### 0F. Connect `HardwareBisimulation.v` to `vm_step`

**What:** The current file proves bisimulation between abstract functions disconnected
from `vm_step`. Add a bridging theorem:

```coq
Theorem hw_step_reflects_vm_cost :
  forall coq_s coq_s' hw py instr,
    bisimulation_invariant coq_s py ->
    hw_bisimulation_invariant hw py ->
    vm_step coq_s instr coq_s' ->
    hw_bisimulation_invariant
      (hardware_step hw (instruction_cost instr))
      (python_step py (instruction_cost instr)).
```

This closes the formal chain: `vm_step` → `python_step` (via PythonBisimulation)
→ `hardware_step` (via this theorem) → actual Kami hardware (via VerilogRefinement).

**Files:** `coq/kernel/HardwareBisimulation.v`

#### 0G. Fix VMStep.v header comment

**What:** Update the header comment block (lines 8-44) to:
- Say "26 instructions" instead of "18"
- Replace PYEXEC in the Special group with: LOAD_IMM, LOAD, STORE, ADD, SUB,
  JUMP, JNEZ, CALL, RET as a new "General-purpose compute" group
- Update instruction counts in each group

**Files:** `coq/kernel/VMStep.v`

#### 0H. Build and verify

**Gate:**
1. `make -C coq -j4` — zero errors
2. `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md` — 0 HIGH, 0 MEDIUM
3. `make generate-python` — forge.py produces correct `generated_core.py` with 26 tags
4. `python3 -m pytest tests/ -q` — all tests pass

---

### Phase 0.5 — VMStep Completeness Fix ✅ COMPLETE
**Completed 2026-03-03.** Gates: `make -C coq -j4` zero errors, Inquisitor 0 HIGH / 0 MEDIUM, 1140 passed / 4 skipped / 0 failed.
**Identified 2026-03-03.** Post-Phase-0 audit revealed a step-relation incompleteness.

**Finding:** `vm_step` had no rules for invalid LASSERT certificates:
- `step_lassert_sat` requires `check_model = true` — no rule for `= false`
- `step_lassert_unsat` requires `check_lrat = true` — no rule for `= false`

With an invalid certificate the relation was **stuck** (no applicable constructor), violating
the header comment "every step either succeeds or sets the error flag." This is not undefined
behavior in the C sense — a stuck state is well-defined in operational semantics — but it is an
incompleteness that breaks the totality claim.

**Fix:** Add two failure constructors to `vm_step` in `VMStep.v`:
- `step_lassert_sat_failure` — guard `check_model = false`, sets error flag, graph unchanged
- `step_lassert_unsat_failure` — guard `check_lrat = false`, sets error flag, graph unchanged

Both mirror the existing `step_psplit_failure` / `step_pmerge_failure` pattern exactly.

**Downstream proof repairs required:**
- `coq/kernel/Locality.v:412` — add two `+ reflexivity` bullets (graph unchanged in failure)
- `coq/kernel/LocalInfoLoss.v:211` — add two `+ reflexivity` bullets (same reason)
- All other sites (`SpacetimeEmergence.v`, `KernelPhysics.v`, `PythonBisimulation.v`, etc.)
  use `try lia / try exact Hwf / try reflexivity` tactics that auto-close the new goals
  because both failure constructors leave the graph unchanged and use `advance_state`.

**Gate:** `make -C coq -j4` zero errors, Inquisitor 0 HIGH / 0 MEDIUM, full pytest green.

---

### Phase 1 — Harness-Only Extensions ✅ COMPLETE
**Completed 2026-03-03.** All four directives implemented, all tests pass.

**Summary of changes:**
- Added `CHECKPOINT <label>` directive: mid-execution state serialized to `<label>.json`, execution continues
- Added `--resume <file>` flag: deserializes JSON state into `s0` before running program
- Added `MEM_SIZE <n>` directive: overrides default 256-word memory at trace parse time
- Added `WRITE_PORT <path> <reg>` directive: appends register value (decimal + newline) to file
- Added `READ_PORT <dst_reg> <path>` directive: reads next line from file, parses as int, loads into register
- All channels auto-closed at exit via `at_exit` handler
- New tests in `tests/test_extracted_vm_runner.py` covering all four directives

**No Coq changes. No proof impact. No test regressions.**

#### 1A. Checkpoint / Resume

**What:** Add `CHECKPOINT <label>` as a trace directive. The runner serializes the
full `vMState` to `<label>.json` mid-execution and continues. Add `--resume <file>`
to restore state before execution begins.

**Files changed:**
- `tools/extracted_vm_runner.ml` — intercept `CHECKPOINT` in the trace parser,
  serialize current state to JSON file at that point in execution, immediately continue
- `tools/extracted_vm_runner.ml` — add `--resume` flag: parse JSON, populate
  `vm_regs`, `vm_mem`, `vm_mu`, `vm_pc`, `vm_mu_tensor`, `vm_csrs`, `vm_graph`
  before running the program

**Gap to close:** Current JSON output serializes `axioms: <count>` per module (line 299
of runner) but not the actual axiom strings. Full resume requires serializing the
actual `module_axioms` list (a `char list list` in OCaml). Add a `"axiom_strings"` field
to the modules JSON output.

**Coq impact:** None.
**Test impact:** None (new behavior, no existing tests break).
**Inquisitor impact:** None.

**Steps:**
1. In `tools/extracted_vm_runner.ml`, add axiom string serialization to `modules_json`
2. Add `CHECKPOINT` case to `parse_line` that does not return an instruction but
   instead triggers a mid-execution serialize
3. Add `--resume <file>` argument handling: parse JSON → populate `s0` fields
4. Write a test in `tests/test_checkpoint_resume.py` that runs a program to a
   checkpoint, resumes, verifies final state matches a single-run version

#### 1B. Dynamic Memory Size (Software VM Only)

**What:** Add `MEM_SIZE <n>` as a trace directive that overrides the default 256 before
execution. The Coq constant stays at 256; the runner uses the directive value.

**Files changed:**
- `tools/extracted_vm_runner.ml` — parse `MEM_SIZE <n>` directive in `parse_program`,
  use it in `make_list n []` for `init_mem` rather than the hardcoded 256. Keep `mem_index`
  modulus consistent with the declared size.
- `build/thiele_vm.py` — pass `MEM_SIZE` through to the subprocess runner as a
  trace directive, document the divergence from Coq spec when >256

**RTL:** Stays at 256. Tests that run both RTL and OCaml paths must not use programs
that require >256 memory cells if RTL co-simulation is also being tested.

**Coq impact:** None (Coq constant unchanged; runner behavior diverges from spec for
addresses > 255, which is acceptable as a harness extension).
**Test impact:** No regressions. Existing 256-cell tests still work.

**Steps:**
1. Add `MEM_SIZE` directive parsing in `parse_program`
2. Use the directive value in `initial_state` construction
3. Document the divergence from Coq spec in a comment

#### 1C. Write Port (Host Output)

**What:** Add `WRITE_PORT <channel_name> <src_reg>` as a runner directive. The runner
reads `vm_regs[src]` and writes the value to a named file or stdout channel.

**Channel naming:** `stdout`, `stderr`, or any file path. The channel is opened (append
mode) at first use and closed on program termination.

**Files changed:**
- `tools/extracted_vm_runner.ml` — add directive, maintain `Hashtbl` of open channels,
  write `vm_regs[src]` as decimal or hex integer

**Coq impact:** None.
**NoFI impact:** None (harness-level, invisible to proofs).

**Steps:**
1. Add `Hashtbl.t` of output channels to the runner state
2. Parse `WRITE_PORT <channel> <reg>` as a non-instruction directive
3. On encountering it during execution loop, write current `vm_regs[src]` to channel
4. Close all channels on exit

#### 1D. Read Port (Host Input, Philosophy B)

**What:** Add `READ_PORT <dst_reg> <channel_name>` as a runner directive. The runner
reads the next whitespace-delimited integer from a named file or stdin and sets
`vm_regs[dst]`.

**Determinism note:** This breaks the proof chain (Coq cannot see what was read). The
runner is the only layer that observes the actual value. Programs using READ_PORT cannot
be formally verified against the Coq spec for their full behavior — only the parts
before/after can be verified.

**Files changed:**
- `tools/extracted_vm_runner.ml` — add `Hashtbl.t` of input channels, parse directive,
  read integer, call `list_set_mod 32 s.vm_regs dst value` and update state

**Coq impact:** None.
**Caveat:** Document clearly that programs using READ_PORT are not covered by the
three-layer isomorphism. The Inquisitor and existing proofs remain valid.

---

### Phase 2 — Proven Coq Instructions (Philosophy A) ✅ COMPLETE

**Completed 2026-03-03.** All three instructions promoted to full Coq constructors.
Gates: `make -C coq -j4` zero errors, Inquisitor 0 HIGH / 0 MEDIUM, **1143 passed / 4 skipped / 0 failed**.

**Summary of Phase 2 changes:**
- **VMStep.v**: Added `instr_checkpoint`, `instr_read_port`, `instr_write_port` constructors
  (total: 29 opcodes). Added `step_checkpoint`, `step_read_port`, `step_write_port` rules.
  `instr_read_port` added to `is_cert_setterb` (NoFI-enforced cert-setter).
- **Exhaustive-match cascade**: Updated VMEncoding.v, SimulationProof.v, CPURefinement.v,
  RevelationRequirement.v, ModularObservation.v, Locality.v, LocalInfoLoss.v,
  ThreeLayerIsomorphism.v, ThieleKernelCausality.v — all with correct arms/bullets.
- **thielecpu/isa.py**: Added CHECKPOINT=0x19, READ_PORT=0x1A, WRITE_PORT=0x1B to Opcode enum.
- **thielecpu/vm.py**: Added CHECKPOINT, READ_PORT, WRITE_PORT handlers to main dispatch and
  `_simulate_witness_step`.
- **tools/extracted_vm_runner.ml**: Added Phase 2 parse cases (3-token CHECKPOINT, 4-token
  WRITE_PORT, 6-token READ_PORT) before Phase 1 harness catch-alls. Added checkpoint
  side-effect (serializes state to `<label>.json`) in execution loop for Coq instr_checkpoint.
- **build/extracted_vm_runner**: Rebuilt from updated runner + fresh .cmi from updated .mli.

**Strategy for each new instruction:** Follow the REVEAL pattern exactly.
REVEAL is the template for "instruction that carries external information with μ-cost."

#### 2A. CHECKPOINT as a Coq instruction

**Instruction form:** `CHECKPOINT <label_string> <cost>`

**Coq changes:**
1. `coq/kernel/VMStep.v` — add `instr_checkpoint (label : string) (cost : nat)` to
   `vm_instruction`, add `step_checkpoint` rule (pure no-op: same state, PC+1, costs μ)
2. All exhaustive-match files — add `| instr_checkpoint _ cost => cost` (trivial arm)
3. `coq/kernel/SimulationProof.v` `vm_apply_unsafe` — add trivial arm that returns
   `advance_state s instr s.vm_graph s.vm_csrs s.vm_err`
4. `coq/kernel/MuLedgerConservation.v` — the `destruct instr; simpl; try reflexivity`
   tactic will close the new case automatically (cost is just `cost`)
5. `coq/kernel/MuCostModel.v` — wildcard already handles it (`| _ => 0`), but add an
   explicit arm for clarity
6. `coq/Extraction.v` — no change needed (type is auto-included)

**OCaml runner changes:**
- `tools/extracted_vm_runner.ml` — parse `CHECKPOINT <label> <cost>`, return the
  actual `VMStep.Coq_instr_checkpoint` value. In `run_vm_iterative`, after calling
  `vm_apply_nofi`, check if the instruction was a checkpoint and if so, serialize state
  to `<label>.json` as a side effect.

**Inquisitor impact:** None if CHECKPOINT is added to an existing file (VMStep.v). If
a new file is created for checkpoint semantics, it needs foundation imports.

#### 2B. READ_PORT (Proven, Philosophy A)

**Instruction form:** `READ_PORT <dst_reg> <channel_idx> <value> <bits> <cost>`

The `value` is declared in the instruction — the program author is responsible for
pre-filling it. This is identical to how LASSERT works (`lassert_certificate` carries
the proof witness inline).

**Coq changes:**
1. `coq/kernel/VMStep.v`:
   - Add `instr_read_port (dst : nat) (channel_idx : nat) (value : nat) (bits : nat) (cost : nat)`
   - Add `step_read_port` rule: `regs' = write_reg s dst value → vm_step s instr (advance_state_rm s instr s.vm_graph s.vm_csrs regs' s.vm_mem s.vm_err)`
   - Add to `is_cert_setterb`: `| instr_read_port _ _ _ _ _ => true` (forces NoFI cost ≥ 1)
   - `instruction_cost` arm: `| instr_read_port _ _ _ _ cost => cost`
2. `coq/kernel/SimulationProof.v` `vm_apply_unsafe`:
   - Add arm that calls `write_reg s dst value` and returns `advance_state_rm`
3. All exhaustive-match files — add trivial arm (same as EMIT pattern)
4. `coq/kernel/MuLedgerConservation.v` — new case is trivially handled by `try reflexivity`
5. `coq/kernel/NoFreeInsight.v` — add `instr_read_port` to the disjunction in
   `no_free_insight_general` (it is a cert-setter, so it must appear in the "revelation
   required" conclusion — same pattern as `instr_emit`)

**μ-tensor tracking (optional, for full accounting):**
   If READ_PORT should charge both scalar μ AND the μ-tensor entry for `channel_idx`
   (following REVEAL's bidirectional accounting), use `advance_state_reveal` semantics
   instead of `advance_state_rm`. This records the information source in the tensor,
   enabling later CHSH_TRIAL validation against the channel's evidence.

**OCaml runner changes:**
- `tools/extracted_vm_runner.ml` — parse `READ_PORT <dst> <channel_idx> <value> <bits> <cost>`
- In Philosophy B mode: optionally override the `value` field at runtime by reading
  from an actual input source before constructing the instruction. The Coq semantic sees
  the pre-declared value; the harness substitutes the live-read value.

**Inquisitor:** READ_PORT is a cert-setter → NoFI enforcement applies automatically.
No special Inquisitor handling needed.

#### 2C. WRITE_PORT (Proven)

**Instruction form:** `WRITE_PORT <channel_idx> <src_reg> <cost>`

**Coq changes:**
1. `coq/kernel/VMStep.v` — add `instr_write_port`, step rule: reads `vm_regs[src]`,
   no state change (pure side-effect instruction at Coq level), advance PC, charge μ
2. NOT a cert-setter (does not set csr_cert_addr) — no NoFI enforcement beyond `cost ≥ 0`
3. All exhaustive-match files — trivial arm

**OCaml runner changes:**
- Intercept during execution and write `vm_regs[src]` to the named output channel

---

### Phase 3 — Memory Expansion

#### 3A. Increase MEM_SIZE (Software VM Only)

**Target:** 4096 words (addressable with 12-bit addresses, enough for real programs).

**Files changed:**
1. `coq/kernel/VMState.v:653` — `Definition MEM_SIZE : nat := 4096.`
2. `tools/extracted_vm_runner.ml` — change 4 `256` literals to `4096`
   (or use a constant rather than literals)
3. Rebuild Coq: `make -C coq -j4`
4. Recompile OCaml binary
5. Add a `MEM_SIZE <n>` override directive as per Phase 1B (for flexibility)

**Proof impact:** The proofs do not directly depend on the value `256` — they use
`MEM_SIZE` as a symbol. Changing the constant does not require any proof edits.
The `make -C coq` rebuild verifies this.

**Test impact:** Tests comparing OCaml and Python `mem` arrays will fail for programs
that access addresses ≥ 256, because Python's `thielecpu/state.py` still uses 256.
Resolution options:
- Update `thielecpu/state.py` to match (Python and OCaml diverge from RTL)
- Or gate extended-memory tests with a new pytest mark `extended_memory` and skip them
  in RTL co-simulation

**RTL impact:** Stays at 256. Divergence from Coq spec for addresses > 255 is
acceptable and documented.

#### 3B. csr_heap_base (Relocatable Window)

**What:** Add `csr_heap_base : nat` to `CSRState`. New instructions `HEAP_LOAD` and
`HEAP_STORE` use `(csr_heap_base + addr) mod MEM_SIZE` as the effective address.
This provides a relocatable view into the same flat memory —
useful for stack/heap separation without adding a second memory region.

**Files changed (Coq):** All ~15 CSRState construction sites — mechanical, add
`csr_heap_base := 0` to each. The three CSR helper functions in `VMState.v` must be
updated to pass through the new field. Rebuild Coq.

**New instructions:** `HEAP_LOAD` and `HEAP_STORE` are new opcodes — same cascade as
Phase 2 (all exhaustive-match files). Follow LOAD/STORE pattern but compute
`effective_addr = (s.vm_csrs.csr_heap_base + addr) mod MEM_SIZE`.

**A simpler alternative** if the CSRState cascade is too disruptive: implement
heap-relative addressing as a harness-level transformation. The runner rewrites
`HEAP_LOAD dst addr cost` → `LOAD dst (heap_base + addr) cost` before passing to
the OCaml step function. No Coq changes at all.

---

### Phase 4 — Full Second Memory Region

**What:** Add `vm_heap : list nat` to the `VMState` record — a completely separate
address space from `vm_mem`.

**This is the most expensive change.** Every `advance_state` variant in VMStep.v
(there are 4: `advance_state`, `advance_state_rm`, `advance_state_reveal`,
`jump_state_rm`) must pass `vm_heap` through. Every test state construction in
MuCostModel.v, TsirelsonUpperBound.v, KernelPhysics.v etc. must include `vm_heap := []`.
All bisimulation proofs that refer to the full VMState record must be re-checked.

**Recommended scope:** Do Phase 4 only if Phase 3A (4096-word flat memory) is
insufficient, which is unlikely for the machine's actual use cases.

If Phase 4 is needed, the harness-only alternative (Phase B fallback):
implement a host-side `Hashtbl` for heap memory in the OCaml runner, intercepted
by `HEAP_LOAD`/`HEAP_STORE` text directives. No Coq changes. Programs using heap
operate outside the proof envelope but work practically.

---

## Build / Gate Changes Required (All Phases)

### New Makefile target: `ocaml-runner`
```makefile
ocaml-runner: build/thiele_core.ml tools/extracted_vm_runner.ml
    ocamlfind ocamlc -package str -linkpkg \
        -I build build/thiele_core.ml tools/extracted_vm_runner.ml \
        -o build/extracted_vm_runner
```
Currently the runner is compiled on-demand by test code. A first-class Make target
ensures it is always up to date after Coq extraction.

### Update `extraction-gate`
When new symbols are added to `Extraction.v`, add them to the symbol-presence check
in the `extraction-gate` target.

### Update `test_all_26_opcodes_comprehensive.py`
When new opcodes are added, update the opcode count (currently 26) and add test
coverage for each new instruction.

### Inquisitor: No special handling needed
The Inquisitor scans for structural properties (Admitted, tautologies, connectivity).
New instructions in existing files do not trigger new findings if:
- They have proper `instruction_cost` arms
- They are covered by `is_cert_setterb` correctly
- The file they're in already imports both foundation groups

---

## Sequence: Steps to Execute

The order matters — later phases depend on earlier ones being clean.

| Step | Phase | Gate to pass |
|---|---|---|
| ~~0a. Remove stale files, fix Makefile~~ | 0A | ✅ Done |
| ~~0c. Add 9 missing opcode handlers to `vm.py`~~ | 0C | ✅ Done |
| ~~0d. Extend `PythonBisimulation.v` for jumps~~ | 0D | ✅ Done |
| ~~0e. Per-instruction witnesses in `VerilogRefinement.v`~~ | 0E | ✅ Done |
| ~~0f. Connect `HardwareBisimulation.v` to `vm_step`~~ | 0F | ✅ Done |
| ~~0g. Fix VMStep.v header comment~~ | 0G | ✅ Done |
| ~~0h. Full build + test gate~~ | 0H | ✅ 1131 passed, 0 HIGH, 0 MEDIUM |
| ~~0.5. Add LASSERT failure constructors~~ | 0.5 | ✅ VMStep total, Locality/LocalInfoLoss fixed, 1140 passed |
| ~~1. Add checkpoint/resume to runner~~ | 1A | ✅ Done |
| ~~2. Add dynamic MEM_SIZE directive~~ | 1B | ✅ Done |
| ~~3. Add WRITE_PORT harness directive~~ | 1C | ✅ Done |
| ~~4. Add READ_PORT harness directive~~ | 1D | ✅ Done |
| ~~5. Add CHECKPOINT as Coq instruction~~ | 2A | ✅ Done — 1143 passed |
| ~~6. Add READ_PORT as Coq instruction~~ | 2B | ✅ Done — 1143 passed |
| ~~7. Add WRITE_PORT as Coq instruction~~ | 2C | ✅ Done — 1143 passed |
| ~~8. Add `ocaml-runner` Makefile target~~ | All | ✅ Done — `make ocaml-runner` succeeds |
| ~~9. Raise MEM_SIZE to 4096 (SW VM)~~ | 3A | ✅ Done — MEM_SIZE=4096 in Coq/OCaml/Python |
| ~~10. Add csr_heap_base~~ | 3B | ✅ Done — CSRState has 4th field |
| ~~11. Add HEAP_LOAD / HEAP_STORE opcodes~~ | 3B | ✅ Done — 31 opcodes, 1145 passed, HIGH: 0, MEDIUM: 0 |
| ~~11.5. Kami hardware layer: add 5 new opcodes~~ | Kami | ✅ Done — ThieleTypes.v+ThieleCPUCore.v+VerilogRefinement.v+Abstraction.v updated, 1145 passed, HIGH: 0, MEDIUM: 0 |
| 12. vm_heap second region (if needed) | 4 | `make -C coq`, Inquisitor, full pytest |

After each step: zero `Admitted.`, Inquisitor 0 HIGH / 0 MEDIUM, all existing tests pass.

---

## What This Does NOT Change

- The 26 existing opcodes and their semantics — unchanged
- The Verilog RTL stays at 256 memory cells and 32 registers unless explicitly retargeted
- The NoFreeInsight theorem — any new cert-setting instruction pays μ
- The μ-ledger monotonicity — all new instructions either charge μ ≥ 1 or are no-ops
- The three-layer isomorphism — Phase 0 closes the existing gaps; after that,
  new opcodes may not have RTL counterparts initially, which is acceptable

---

## Risk Register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Adding new Coq opcode breaks 25+ exhaustive matches | Certain | Work through files systematically; `make -C coq` error output identifies every site |
| Inquisitor finds PROOF_CONNECTIVITY_GAP in new files | High | Every new `.v` file must start with `From Kernel Require Import VMStep MuCostModel.` |
| MEM_SIZE change breaks Python↔OCaml comparison tests | High | Gate extended-memory tests under `extended_memory` pytest mark; skip in RTL co-sim |
| OCaml runner binary silently stale after Coq changes | Medium | Add `ocaml-runner` Make target; gate tests check binary freshness |
| Philosophy B READ_PORT silently passes incorrect tests | Medium | Add `pytest.mark.no_formal_coverage` to all Philosophy B tests; document the gap |
| Phase 4 (vm_heap) breaks all proof states that construct VMState | High | Do only if Phase 3A is actually insufficient; the harness alternative avoids it |
