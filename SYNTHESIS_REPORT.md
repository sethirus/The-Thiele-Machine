# Thiele CPU — Synthesis Proof Report

**Date:** 2026-02-11  
**File:** `thielecpu/hardware/rtl/thiele_cpu_unified.v`  
**Tool:** Yosys 0.33 (git sha1 2584903a060)  
**Platform:** Ubuntu 24.04.2 LTS (dev container)

---

## 1. Executive Summary

The unified Thiele CPU (`thiele_cpu_unified.v`) **synthesises to gate-level logic
with zero errors and zero unsynthesisable constructs.** All `$display` statements
are guarded by `` `ifndef SYNTHESIS `` and are stripped during synthesis. The
generated netlist is 261,349 lines of structural Verilog.

---

## 2. Synthesis Pipeline

```
read_verilog -sv -DSYNTHESIS -DYOSYS_LITE thiele_cpu_unified.v
hierarchy -top thiele_cpu -check
proc            # Convert always-blocks to muxes/FFs
flatten         # Inline all submodules
opt -full       # Constant folding, dead code elimination
fsm             # Map FSMs to logic
opt -full
memory          # Map memories to register arrays
opt -full
techmap         # Generic gate-level technology mapping
opt -full
clean -purge
stat
write_verilog -noattr synth_lite_out.v
```

Defines:
- `-DSYNTHESIS` — strips all `$display` statements
- `-DYOSYS_LITE` — uses `NUM_MODULES=4`, `REGION_SIZE=16`
  (same logic paths, smaller arrays; see §5 for rationale)

---

## 3. Results

### 3.1 Errors & Warnings

| Metric | Count |
|--------|-------|
| **Errors** | **0** |
| **Warnings** | 3 (expected memory-to-register conversion) |
| **$print cells** | **0** (all `$display` stripped) |

Warnings (all benign):
```
Warning: Replacing memory \reg_file with list of registers.
Warning: Replacing memory \region_table with list of registers.
Warning: Replacing memory \module_table with list of registers.
```

### 3.2 Gate-Level Statistics

```
=== thiele_cpu ===

   Number of wires:              20,280
   Number of wire bits:         358,162
   Number of public wires:         150
   Number of public wire bits:    4,047
   Number of memories:               0
   Number of memory bits:            0
   Number of processes:              0
   Number of cells:             234,940
     $_AND_                      25,100
     $_DFFE_PN0P_                   382    (D flip-flop, async reset low, enable)
     $_DFFE_PN1P_                     1
     $_DFFE_PP_                   3,352    (D flip-flop, async reset high, enable)
     $_DFF_PN0_                       8
     $_MUX_                     182,610    (2:1 multiplexers)
     $_NOT_                       1,954
     $_OR_                       18,384
     $_SDFFCE_PN0P_                   2    (sync DFF with clock enable)
     $_SDFFCE_PN1P_                   6
     $_SDFFCE_PP0P_                   6
     $_XOR_                       3,131
     $mux                             4    (wide muxes)
```

### 3.3 Module Hierarchy (Flattened)

```
Top module:  thiele_cpu
├── mu_alu                        Q16.16 fixed-point ALU
├── mu_core                       Partition isomorphism enforcement
│   └── receipt_integrity_checker Receipt verification
└── clz8                          ceil(log2) helper
```

All submodules were flattened into the top-level `thiele_cpu` module.

### 3.4 Performance

```
CPU time:    user 290.77s system 1.26s
Peak memory: 1,575.68 MB
Netlist:     261,349 lines (synth_lite_out.v)
```

---

## 4. Verification Chain

| Step | Tool | Result |
|------|------|--------|
| **Parse** | iverilog -g2012 -Wall | Zero warnings, zero errors |
| **Synthesis** | Yosys 0.33 (synth_lite.ys) | Zero errors, 3 benign warnings |
| **Bisimulation cosim** | pytest (39 tests) | All pass |
| **Accelerator cosim** | pytest (22 tests + 2 skipped) | All pass |
| **Coq proof** | coqc ThreeLayerIsomorphism.v | 3 theorems, zero axioms |

Combined: `make rtl-verify`

---

## 5. YOSYS_LITE Rationale

The full-size configuration (`NUM_MODULES=64`, `REGION_SIZE=1024`) creates a
`region_table` of 64×1024×32 = 2,097,152 bits. Yosys converts this to flat
registers during Verilog parsing, consuming >2 GB RAM — exceeding the 2.7 GB
available in this container.

`YOSYS_LITE` reduces arrays to `NUM_MODULES=4`, `REGION_SIZE=16` (2,048 bits).
This is **not a logic shortcut**:

- The `ifdef` controls **only array dimensions** (localparam values)
- All FSM states, opcode decode, ALU operations, enforcement logic, and
  receipt checking paths are **identical** in both configurations
- Every gate type in the statistics block would be present at full size;
  only the MUX and FF counts scale with array size

In a real FPGA flow, the `region_table` would be inferred as block RAM (BRAM),
not register arrays. The synthesis proof confirms all **logic** is gate-level
clean.

---

## 6. File Inventory

| File | Purpose |
|------|---------|
| `thiele_cpu_unified.v` | Single-file RTL (all 5 modules) |
| `synth_lite.ys` | Yosys synthesis script |
| `synth_lite_clean.log` | Complete synthesis log (6,616 lines) |
| `synth_lite_out.v` | Gate-level netlist (261,349 lines) |

---

## 7. Reproduction

```bash
# One-command full verification:
make rtl-verify

# Or step by step:
make rtl-check    # iverilog compilation
make rtl-synth    # Yosys synthesis (~5 min)
make rtl-cosim    # 61 co-simulation tests
```
