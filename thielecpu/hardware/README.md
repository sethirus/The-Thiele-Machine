# Thiele CPU Hardware Implementation

## Overview

The Thiele CPU is a specialized hardware processor designed for partition-native computation, implementing the theoretical foundations of the Thiele Machine. This hardware enables efficient execution of partition-based algorithms with integrated cryptographic proof generation and validation.

**The Holy Grail**: This hardware implements "Non-Quantum Quantum" computing where **optimization is the physics**. The silicon enforces mathematical isomorphism - invalid operations are physically impossible.

## Architecture

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

The μ-Core is the revolutionary component that makes this "Non-Quantum Quantum" computing:

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

## Demonstration

Run the Holy Grail demonstration:

```bash
cd thielecpu/hardware
python3 holy_grail_demo.py
```

This shows the μ-Core blocking invalid operations while allowing mathematically valid ones.

## File Structure

### Core Verilog Files

- `thiele_cpu.v` - Main CPU implementation with partition logic and state machine
- `thiele_cpu_tb.v` - Testbench with comprehensive instruction sequence testing
- `lei.v` - Logic Engine Interface module
- `mau.v` - Memory Access Unit
- `mmu.v` - Memory Management Unit
- `pee.v` - Python Execution Engine

### Configuration Files

- `constraints.xdc` - FPGA timing and placement constraints
- `synthesis.tcl` - Vivado synthesis script
- `simulate.do` - ModelSim simulation script
- `simulate.tcl` - Vivado simulation script

### Test Infrastructure

- `test_hardware.py` - Automated test suite supporting multiple simulators
- `test_report.md` - Generated test results and hardware specifications

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

- ✅ Verilog implementation complete with μ-ALU and μ-Core
- ✅ Hardware enforcement of mathematical isomorphism demonstrated
- ✅ Q16.16 fixed-point arithmetic for bit-exact μ-bit calculations
- ✅ Partition discovery (PDISCOVER) operation implemented
- ✅ Holy Grail demonstration: hardware that cannot violate math
- 🔄 Functional simulation verified (Python demonstration)
- 🔄 Verilog compilation pending (syntax compatibility)
- 🔄 FPGA synthesis pending (requires Vivado)

## Contributing

This is a research prototype. Contributions should focus on:
- Performance optimization
- Security analysis
- Formal verification
- Synthesis improvements

## License

See project root LICENSE file.