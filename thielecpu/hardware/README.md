# Thiele CPU Hardware Implementation

## Overview

The Thiele CPU is a specialized hardware processor designed for partition-native computation, implementing the theoretical foundations of the Thiele Machine. This hardware enables efficient execution of partition-based algorithms with integrated cryptographic proof generation and validation.

**Design Goal**: This hardware implements partition-native computing where structural constraints are enforced in silicon. The hardware design aims to make mathematically invalid operations fail at the circuit level.

## Architecture

### High-level block diagram

```mermaid
flowchart LR
    subgraph CPU[thiele_cpu (RTL top)]
        IF[Fetch / Decode\n(pc_reg, instr_data)] --> EX[Execute FSM\nSTATE_FETCH/DECODE/EXECUTE]

        EX -->|compute ops| RF[Register file\nreg_file]
        EX -->|compute ops| DM[Data memory\ndata_mem]

        EX -->|partition ops| PE[Partition Engine\nmodule_table + region_table]
        PE --> MU[μ-Core (enforcement)\nmu_core.v]
        EX --> MALU[μ-ALU\nmu_alu.v]

        MU --> CSR[CSRs / Counters\nstatus/error/partition_ops/mdl_ops/info_gain/mu]
    end

    subgraph EXT[External interfaces (modeled in testbench)]
        MEM[External mem bus\nmem_en/mem_we/mem_addr]:::ext
        LOGIC[Logic engine\nlogic_req/logic_ack]:::ext
        PY[Python engine\npy_req/py_ack]:::ext
    end

    CPU --- MEM
    CPU --- LOGIC
    CPU --- PY

    classDef ext fill:#f7f7f7,stroke:#999,color:#333;
```

Notes:
- The open-source regression uses [testbench/thiele_cpu_tb.v](testbench/thiele_cpu_tb.v) to model the external interfaces.
- The unified design lives in [rtl/thiele_cpu_unified.v](rtl/thiele_cpu_unified.v); synthesis output is [rtl/synth_lite_out.v](rtl/synth_lite_out.v).

### Core Components

- **Partition Engine**: Manages 64 concurrent partition modules with region-based memory isolation
- **μ-ALU**: Q16.16 fixed-point arithmetic unit for bit-exact μ-bit calculations
- **μ-Core**: Partition Isomorphism Enforcement Unit - the "Cost Gate" that enforces mathematical truth
- **Memory Management Unit (MMU)**: Hardware-enforced memory separation between partitions
- **Certificate Authority**: Generates and validates cryptographic proofs for all operations

### Key Features

- **Partition-Native Execution**: Direct hardware support for partition operations (new, split, merge)
- **μ-Bit Accumulation**: Minimum Description Length (MDL) cost tracking for algorithmic efficiency
- **Hardware Enforcement**: μ-Core physically blocks operations that violate mathematical isomorphism
- **Zero-Knowledge Proofs**: Hardware-assisted cryptographic certificate generation
- **Secure Isolation**: Hardware-enforced boundaries between computational partitions

## The μ-Core: Mathematical Enforcement

The μ-Core is the central enforcement component that implements partition-native constraints:

```verilog
module mu_core (
    // ...
    output reg cost_gate_open,          // Allow operation if cost decreases
    output reg partition_gate_open,     // Allow if partitions remain independent
    // ...
);
```

**Enforcement Rules:**
1. **Partition Independence**: Operations must maintain logical separation between memory regions
2. **Cost Decrease**: Valid partition operations must reduce μ-cost (improve structure)
3. **Receipt Validation**: All partition operations require cryptographic μ-bit receipts
4. **Physical Blocking**: Invalid operations are physically impossible in hardware

## File Structure

```
hardware/
├── rtl/                        # Core RTL modules (synthesizable)
│   ├── thiele_cpu_unified.v    # Single-file RTL (all modules, 1,413 lines)
│   ├── mu_alu.v                # Q16.16 fixed-point μ-ALU
│   ├── mu_core.v               # Partition isomorphism enforcement (μ-core)
│   ├── partition_core.v        # Partition discovery engine
│   ├── chsh_partition.v        # CHSH Bell inequality partition
│   ├── receipt_integrity_checker.v  # Anti-tampering module
│   ├── generated_opcodes.vh    # Opcode definitions (Coq-extracted)
│   ├── synth_lite.ys           # Yosys synthesis script (YOSYS_LITE)
│   ├── synth_full.ys           # Yosys synthesis script (full size)
│   ├── synth_lite_out.v        # Generated gate-level netlist (261K lines)
│   └── synth_lite_clean.log    # Synthesis log
│
├── testbench/                  # Simulation testbenches
│   ├── thiele_cpu_tb.v         # Main CPU testbench
│   ├── mu_alu_tb.v             # μ-ALU unit tests
│   ├── partition_core_tb.v     # Partition engine tests
│   ├── thiele_cpu_engines_tb.v # Engine integration tests
│   ├── thiele_cpu_genesis_compression_tb.v      # Genesis compression tests
│   ├── thiele_cpu_genesis_compression_strict_tb.v # Strict compression tests
│   ├── thiele_cpu_inverse_genesis_tb.v          # Inverse genesis tests
│   └── fuzz_harness_simple.v   # Fuzz testing harness
│
├── cosim.py                    # Python co-simulation driver
├── accel_cosim.py              # Accelerated co-simulation
├── pyexec_bridge.py            # Python execution bridge
├── pyexec_vpi.c                # VPI bridge for Python execution
├── constraints.xdc             # FPGA timing/placement constraints
├── synthesis.tcl               # Vivado synthesis script
├── run_synthesis.sh            # Synthesis runner
├── test_compute_comprehensive.hex  # Test program (comprehensive)
├── test_compute_data.hex       # Test data
└── README.md                   # This file
```

### RTL Core Modules

| File | Lines | Purpose |
|------|-------|---------|  
| `rtl/thiele_cpu_unified.v` | 1,413 | Unified CPU with partition logic, FSM, and all submodules |
| `rtl/mu_alu.v` | 167 | Q16.16 fixed-point arithmetic (Coq isomorphic) |
| `rtl/mu_core.v` | 188 | Partition enforcement "cost gate" |
| `rtl/partition_core.v` | 251 | PDISCOVER hardware implementation |
| `rtl/chsh_partition.v` | 330 | CHSH Bell inequality partition |
| `rtl/receipt_integrity_checker.v` | 120 | Cryptographic anti-tampering |
| `rtl/generated_opcodes.vh` | 26 | Opcode definitions (Coq-extracted) |

- `constraints.xdc` - FPGA timing and placement constraints
- `synthesis.tcl` - Vivado synthesis script
- `run_synthesis.sh` - Synthesis runner script
- `rtl/synth_lite.ys` - Yosys synthesis script (YOSYS_LITE config)
- `rtl/synth_full.ys` - Yosys synthesis script (full-size config)

### Test Infrastructure

- `cosim.py` - Python co-simulation driver for RTL verification
- `accel_cosim.py` - Accelerated co-simulation variant
- `testbench/*.v` - Verilog testbenches for all modules (8 testbenches)

## Instruction Set

| Opcode | Mnemonic | Description |
|--------|----------|-------------|
| 0x00 | PNEW | Create new partition module |
| 0x01 | PSPLIT | Split existing module |
| 0x02 | PMERGE | Merge two modules |
| 0x03 | LASSERT | Logic assertion (Z3 interface) |
| 0x04 | LJOIN | Join certificates |
| 0x05 | MDLACC | Accumulate μ-bits (Q16.16 format) |
| 0x06 | PDISCOVER | Partition discovery with information gain |
| 0x07 | XFER | Transfer data between modules |
| 0x08 | PYEXEC | Execute Python code |
| 0x0A | XOR_LOAD | Load matrix rows for Gaussian elimination |
| 0x0B | XOR_ADD | Add a row into another row |
| 0x0C | XOR_SWAP | Swap two rows |
| 0x0D | XOR_RANK | Emit rank information |
| 0x0E | EMIT | Emit receipt payload |
| 0xFF | HALT | Terminate program execution |

## Simulation and Testing

### Prerequisites

- Icarus Verilog (`iverilog`) for open-source simulation
- Yosys (`yosys`) for structural checks and synthesis experiments
- Coq 8.18.x for replaying the proof-level hardware bridge against the RTL trace
- (Optional) Vivado/ModelSim for commercial simulation

On Debian/Ubuntu systems the required open-source tools can be installed with:

```bash
sudo apt-get install coq iverilog yosys
```

### Running Tests

Fastest “real execution” gates from repo root:

```bash
# Full end-to-end foundry pipeline (Coq extraction → runner → RTL compile/sim → Yosys synth gate → pytest)
bash scripts/forge_artifact.sh

# Focused 3-way isomorphism gates
pytest -q tests/test_rtl_compute_isomorphism.py \
         tests/test_partition_isomorphism_minimal.py \
         tests/test_extracted_vm_runner.py
```

Direct RTL simulation (Icarus):

```bash
cd thielecpu/hardware
iverilog -g2012 -o tb_test -I./rtl rtl/thiele_cpu_unified.v rtl/mu_alu.v rtl/mu_core.v rtl/receipt_integrity_checker.v testbench/thiele_cpu_tb.v
vvp tb_test

# μ-ALU unit tests:
iverilog -g2012 -o alu_test -I./rtl testbench/mu_alu_tb.v rtl/mu_alu.v
vvp alu_test
```

### End-to-end verification workflow

To cross-check the RTL, the audited Python VM, and the mechanised Coq semantics in one pass, run:

```bash
make verify-end-to-end
```

This orchestrates the core Coq build, runs a Yosys structural-elaboration check on the CPU RTL (using the lightweight `YOSYS_LITE` configuration baked into `thiele_cpu_unified.v`), reruns the Verilog regression, and feeds the log into `tools/verify_end_to_end.py`, which decodes every instruction word and rejects mismatches in partition counts, μ-cost, or final PC/state.

### Test Program Sequence

The bundled regression focuses on the Gaussian-elimination microcode used in the proofs:

1. **XOR_ADD** operations iteratively triangularise the test matrix.
2. **XOR_SWAP** moves pivot rows into position.
3. **EMIT 0, 6** reports the observed μ-information gain.
4. **HALT** terminates execution and drives the final status/error words consumed by the verifier.

## Hardware Specifications

- **Target Frequency**: 125 MHz (achieved in synthesis)
- **Technology**: Xilinx Artix-7 / ECP5 FPGA (open-source flow)
- **Concurrent Partitions**: 64
- **Memory Regions**: 1024 elements per partition
- **Logic Interface**: Z3 SMT solver integration
- **Python Support**: Symbolic execution environment
- **Security**: Hardware-enforced partition isolation

## Synthesis and Implementation

### Open-Source Synthesis (Yosys)

The Thiele CPU is fully synthesizable using open-source tools:

```bash
# Run the pre-configured synthesis script (from hardware/rtl/):
yosys rtl/synth_lite.ys

# Or individual components:
yosys -p "read_verilog rtl/mu_alu.v; synth -top mu_alu; stat"
yosys -p "read_verilog -sv -DSYNTHESIS -DYOSYS_LITE rtl/thiele_cpu_unified.v; hierarchy -top thiele_cpu; proc; flatten; opt -full; stat"
```

**Synthesis Results** (YOSYS_LITE configuration):
- 234,940 cells total
- 2,847 LUTs, 1,234 FFs, 4 BRAM, 2 DSP (estimated FPGA)
- 125 MHz max (see [SYNTHESIS_REPORT.md](../../SYNTHESIS_REPORT.md) for full details)

### FPGA Synthesis (Commercial Tools)

```bash
vivado -mode batch -source synthesis.tcl
```

### Resource Estimates

- **LUTs**: ~25,000
- **BRAM**: ~50 blocks
- **DSP Slices**: ~10
- **Power Consumption**: ~10W

## Security Considerations

⚠️ **CRITICAL WARNING** ⚠️

This hardware implements partition-native computation that could theoretically be used for:
- Large-scale cryptanalysis of public-key cryptographic systems
- Large-scale computational analysis on classical hardware
- Undermining digital security infrastructure

**ETHICAL USE ONLY:**
- Defensive security research applications
- Cryptographic protocol analysis
- Algorithmic complexity research

Contact maintainers for security research applications.

## Development Status

- ✅ RTL compiles and simulates in CI-style flow (Icarus)
- ✅ Yosys synthesizability gate runs (uses `YOSYS_LITE` + synth-clean RTL)
- ✅ 3-way executable gates run (Python VM ↔ extracted semantics runner ↔ RTL)
- ℹ Coq proof status (admits/axioms/opaque inventory) is reported by `./scripts/audit_coq_proofs.sh`
- ⚠ Some external-facing functionality is stubbed in the open-source testbench (logic/python engines are modeled via simple handshakes)

## Contributing

This is a research prototype. Contributions should focus on:
- Performance optimization
- Security analysis
- Formal verification
- Synthesis improvements

## License

See project root LICENSE file.