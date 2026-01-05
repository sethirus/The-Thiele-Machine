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
- The open-source regression uses [thielecpu/hardware/thiele_cpu_tb.v](thielecpu/hardware/thiele_cpu_tb.v) to model the external interfaces.
- For synthesis-facing checks we generate [thielecpu/hardware/thiele_cpu_synth.v](thielecpu/hardware/thiele_cpu_synth.v) (derived from [thielecpu/hardware/thiele_cpu.v](thielecpu/hardware/thiele_cpu.v)).

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
├── rtl/                    # Core RTL modules (synthesizable)
│   ├── thiele_cpu.v        # Main CPU with partition logic and state machine
│   ├── thiele_cpu_synth.v  # Synthesis-friendly variant
│   ├── mu_alu.v            # Q16.16 fixed-point μ-ALU
│   ├── mu_core.v           # Partition isomorphism enforcement (μ-core)
│   ├── receipt_integrity_checker.v  # Anti-tampering module
│   ├── partition_core.v    # Partition discovery engine
│   ├── chsh_partition.v    # CHSH Bell inequality partition
│   ├── shor_partition.v    # Shor's algorithm partition
│   ├── mmu.v               # Memory Management Unit
│   ├── mau.v               # Memory Access Unit
│   ├── lei.v               # Logic Engine Interface
│   ├── pee.v               # Python Execution Engine
│   ├── generated_opcodes.vh # Opcode definitions (Coq-extracted)
│   └── ...                 # Additional RTL modules
│
├── testbench/              # Simulation testbenches
│   ├── thiele_cpu_tb.v     # Main CPU testbench
│   ├── mu_alu_tb.v         # μ-ALU unit tests
│   ├── partition_core_tb.v # Partition engine tests
│   └── ...                 # Additional testbenches
│
├── constraints.xdc         # FPGA timing/placement constraints
├── synthesis.tcl           # Vivado synthesis script
├── simulate.do             # ModelSim simulation script
├── simulate.tcl            # Vivado simulation script
├── test_hardware.py        # Automated test suite
└── README.md               # This file
```

### RTL Core Modules

| File | Purpose |
|------|---------|
| `rtl/thiele_cpu.v` | Main CPU with partition logic and FSM |
| `rtl/mu_alu.v` | Q16.16 fixed-point arithmetic (Coq isomorphic) |
| `rtl/mu_core.v` | Partition enforcement "cost gate" |
| `rtl/partition_core.v` | PDISCOVER hardware implementation |
| `rtl/receipt_integrity_checker.v` | Cryptographic anti-tampering |

### Configuration Files

- `constraints.xdc` - FPGA timing and placement constraints
- `synthesis.tcl` - Vivado synthesis script
- `simulate.do` - ModelSim simulation script
- `simulate.tcl` - Vivado simulation script

### Test Infrastructure

- `test_hardware.py` - Automated test suite supporting multiple simulators
- `testbench/*.v` - Verilog testbenches for all modules

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
iverilog -g2012 -o tb_test -I./rtl rtl/thiele_cpu.v rtl/mu_alu.v rtl/mu_core.v rtl/receipt_integrity_checker.v testbench/thiele_cpu_tb.v
./tb_test

# μ-ALU unit tests:
iverilog -g2012 -o alu_test -I./rtl testbench/mu_alu_tb.v rtl/mu_alu.v
./alu_test
```

```bash
cd thielecpu/hardware
python3 test_hardware.py
```

The test suite will:
1. Verify Verilog file presence
2. Compile and simulate the design
3. Execute a comprehensive instruction sequence
4. Generate detailed test reports (`simulation_output.log` and `test_report.md`)

### End-to-end verification workflow

To cross-check the RTL, the audited Python VM, and the mechanised Coq semantics in one pass, run:

```bash
make verify-end-to-end
```

This orchestrates the core Coq build, runs a Yosys structural-elaboration check on the CPU RTL (using the lightweight `YOSYS_LITE` configuration baked into `thiele_cpu.v`), reruns the Verilog regression, and feeds the log into `tools/verify_end_to_end.py`, which decodes every instruction word and rejects mismatches in partition counts, μ-cost, or final PC/state.

### Test Program Sequence

The bundled regression focuses on the Gaussian-elimination microcode used in the proofs:

1. **XOR_ADD** operations iteratively triangularise the test matrix.
2. **XOR_SWAP** moves pivot rows into position.
3. **EMIT 0, 6** reports the observed μ-information gain.
4. **HALT** terminates execution and drives the final status/error words consumed by the verifier.

## Hardware Specifications

- **Target Frequency**: 200 MHz
- **Technology**: Xilinx Zynq UltraScale+ FPGA
- **Concurrent Partitions**: 64
- **Memory Regions**: 1024 elements per partition
- **Logic Interface**: Z3 SMT solver integration
- **Python Support**: Symbolic execution environment
- **Security**: Hardware-enforced partition isolation

## Synthesis and Implementation

### FPGA Synthesis

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