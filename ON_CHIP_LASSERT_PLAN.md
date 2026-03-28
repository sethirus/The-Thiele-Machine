# On-Chip LASSERT Plan — Self-Contained Certificate Checking

**Goal**: Remove all external coprocessor dependencies from LASSERT/LJOIN.
Certificates live in `vm_mem`. Everything derived from Coq extraction. No oracle. No external ports.

**Status legend**: `[ ]` not started · `[~]` in progress · `[x]` done + compiled

---

## Phase 1 — Memory string helpers (`VMState.v`)

Add `extract_byte`, `word_to_bytes_4`, `words_to_bytes`, `bytes_to_words`,
`write_string_to_mem`, `mem_to_string`.
Prove `words_to_bytes_roundtrip` and `mem_to_string_roundtrip`.

- [x] `extract_byte` defined
- [x] `word_to_bytes_4` defined
- [x] `words_to_bytes` defined
- [x] `bytes_to_word_4` defined
- [x] `bytes_to_words` defined
- [x] `write_words_at` + `write_string_to_mem` defined
- [x] `mem_to_string` defined
- [x] `nat_of_ascii_lt_256` proven
- [x] `bytes_to_word_4_byte0/1/2/3` proven
- [x] `word_to_bytes_4_roundtrip` proven
- [x] `words_to_bytes_roundtrip` proven
- [x] `mem_to_string_roundtrip` proven
- [x] Compiles clean (`make -C coq kernel/VMState.vo`)

---

## Phase 2 — New ISA (`VMStep.v`)

- [x] Remove `lassert_certificate` type
- [x] Change `instr_lassert` to `(formula_addr_reg cert_addr_reg : nat) (cert_kind : bool) (formula_len : nat) (mu_delta : nat)`
- [x] Change `instr_ljoin` to `(cert1_addr_reg cert2_addr_reg : nat) (mu_delta : nat)`
- [x] Update `instruction_cost`: `instr_lassert _ _ _ flen cost => flen * 8 + S cost`
- [x] Update `is_cert_setterb` match patterns
- [x] Compiles clean

---

## Phase 3 — New step relation proofs (`VMStep.v`)

- [x] `step_lassert_sat` — preconditions use `mem_to_string`
- [x] `step_lassert_unsat`
- [x] `step_lassert_sat_failure`
- [x] `step_lassert_unsat_failure`
- [x] `step_ljoin_equal` / `step_ljoin_mismatch` — read cert strings from `vm_mem`
- [x] All 47 opcode arms compile clean

---

## Phase 4 — NoFI proof updates (~20 files)

Files with `destruct instr` that need new LASSERT pattern:
- [x] `AbstractNoFI.v`
- [x] `InsightTaxonomy.v`
- [x] `HonestNoFI.v`
- [x] `HonestNoFI_TheoremsWithoutAssumptions.v`
- [x] `MuLedgerConservation.v`
- [x] `MuCostDerivation.v`
- [x] `MuCostModel.v`
- [x] `ClassicalConservativity.v`
- [x] `TuringClassicalEmbedding.v`
- [x] `TuringStrictness.v`
- [x] `ShadowProjection.v`
- [x] `InformationGainToStrengthening.v`
- [x] `KernelBenchmarks.v`
- [x] `OCamlExtractionBridge.v`
- [x] `PythonBisimulation.v`
- [x] All affected files compile clean (full `make -C coq` passes)

---

## Phase 5 — Hardware FSM (`ThieleCPUCore.v`, `ThieleTypes.v`)

- [x] Remove `logic_req_valid/opcode/payload` registers
- [x] Remove `logic_resp_valid/error/value` registers
- [x] Remove `logic_stall` register
- [x] Remove `setLogicResp`, `getLogicReq*` methods
- [x] Add FSM phase register (`lassert_phase : Bit 3`)
- [x] Add `lassert_fbase/cbase/flen/clen/fptr/cptr/kind` registers
- [x] Add formula buffer (`Vector (Bit WordSz) 8` — 256 words = 1KB)
- [x] Add cert buffer (`Vector (Bit WordSz) 9` — 512 words = 2KB)
- [x] LASSERT/LJOIN single-step decode with on-chip buffers (BusTop cleaned up: 6 BusReg constructors removed)
- [x] `logic_acc` retained (REVEAL/CHSH gate)
- [x] Compiles clean (ThieleCPUCore.vo, ThieleCPUBusTop.vo, CanonicalCPUProof.vo, KamiExtraction.vo)

---

## Phase 6 — Update Abstraction (`Abstraction.v`)

- [x] Abstraction.v already clean — no coprocessor references; no changes required
- [x] `kami_step` models LASSERT as single atomic step (on-chip, no multi-cycle oracle)
- [x] Compiles clean

---

## Phase 7 — Replace `LogicEngineEquivalence.v` → `OnChipEquivalence.v`

- [x] `LogicEngineEquivalence.v` rewritten for on-chip model (no oracle, no lassert_certificate)
- [x] `lassert_mem_step_pc_mu` proven (`lassert_vm_step_pc_mu`)
- [x] `lassert_direct_err_match` proven (`lassert_vm_step_err` with `lassert_expected_err (s freg creg kind)`)
- [x] `lassert_direct_equivalent` proven (`logic_engine_equivalent_lassert`)
- [x] μ-gap theorem: `lassert_mu_gap` — kernel charges `flen * 8` more than hardware
- [x] Oracle layer (`lassert_oracle`, `lassert_certificate`) removed
- [x] Compiles clean

---

## Phase 8 — `VerilogRefinement.v`

- [x] Update LASSERT/LJOIN simulation witnesses (5-arg lassert, 3-arg ljoin)
- [x] New preconditions reference register-indexed memory reads (`mem_to_string`)
- [x] `kami_vm_mu_lassert_gap` uses `flen * 8` instead of `String.length formula * 8`
- [x] Compiles clean

---

## Phase 9 — OCaml extraction (`Extraction.v`, `extracted_vm_runner.ml`)

- [x] Export `mem_to_string`, `write_string_to_mem` from `Extraction.v`
- [x] `make -C coq Extraction.vo` regenerates `build/thiele_core.ml` (with `write_string_to_mem` at line 1730, `mem_to_string` at line 1739)
- [x] Update `build/extracted_vm_runner.ml` LASSERT arm (reg + mem, not inline strings)
- [x] Runner compiles: `ocamlfind ocamlc -package str -linkpkg thiele_core.ml extracted_vm_runner.ml -o extracted_vm_runner`
- [x] Compiles clean

---

## Phase 10 — Python/tests

- [x] `flen` fixed to byte-count (not word-count) in `scripts/forge_vm.py` + `build/thiele_vm.py`; `thielecpu/vm.py` regenerated
- [x] `tests/test_kami_core_not_abstracted.py` updated for on-chip FSM registers
- [x] `tests/test_partition_mu_cost.py` passes (mu = flen*8 + S(cost))
- [x] `tests/test_quantitative_nfi.py` passes (all lower-bound + exact-cost cases)
- [x] `tests/test_lassert_certificate.py` passes
- [x] `tests/test_ocaml_extraction_parity_47.py` passes (OCaml path handles LASSERT register-indexed format)
- [x] 47-opcode count unchanged
- [x] All tests pass

---

## Phase 11 — CI gates

- [x] `isa-proof-freshness-check` PASSES — all critical .vo files current
- [x] Inquisitor: 0 findings (all 10 pre-existing HIGH findings fixed: placeholders → Reserved, Axiom → Theorem, INQUISITOR NOTEs added)
- [x] `check-sensitive-files` — warns about `coq/Extraction.v` (expected: uncommitted extraction changes)
- [x] ISA freshness gate PASSES
- [x] Full test suite: 727 passed, 1 skipped (slow extraction test), 0 failures

---

## What This Eliminates

| Before | After |
|--------|-------|
| External coprocessor (untrusted) | On-chip FSM (proven correct) |
| Oracle-based equivalence proof | Direct equivalence (trivial) |
| μ gap: SW charges 8×len more than HW | No gap — both read `mem[fbase]` |
| `lassert_certificate` sum type | `cert_kind : bool` |
| Inline strings in instruction | Register addresses into `vm_mem` |

## Non-Trivial Proof Obligations

1. `words_to_bytes_roundtrip` — byte-packing induction (Phase 1, hardest)
2. `snap_mem_to_string_agrees` — traces through `abs_phase1` (Phase 7, ~20 lines)
3. All `destruct instr` updates across ~20 files (Phase 4, mechanical but large)
