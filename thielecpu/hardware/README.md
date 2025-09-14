# Thiele CPU Hardware Implementation

## Overview

The Thiele CPU is a specialized hardware processor designed for partition-native computation, implementing the theoretical foundations of the Thiele Machine. This hardware enables efficient execution of partition-based algorithms with integrated cryptographic proof generation and validation.

## Architecture

### Core Components

- **Partition Engine**: Manages 64 concurrent partition modules with region-based memory isolation
- **Logic Engine Interface**: Connects to Z3 SMT solver for automated theorem proving
- **Python Execution Unit**: Interfaces with Python interpreter for symbolic computation
- **Memory Management Unit (MMU)**: Hardware-enforced memory separation between partitions
- **Certificate Authority**: Generates and validates cryptographic proofs for all operations

### Key Features

- **Partition-Native Execution**: Direct hardware support for partition operations (new, split, merge)
- **μ-Bit Accumulation**: Minimum Description Length (MDL) cost tracking for algorithmic efficiency
- **Zero-Knowledge Proofs**: Hardware-assisted cryptographic certificate generation
- **Secure Isolation**: Hardware-enforced boundaries between computational partitions

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
| 0x05 | MDLACC | Accumulate μ-bits |
| 0x06 | EMIT | Emit result value |
| 0x07 | XFER | Transfer data between modules |
| 0x08 | PYEXEC | Execute Python code |

## Simulation and Testing

### Prerequisites

- Icarus Verilog (`iverilog`) for open-source simulation
- Or Vivado/ModelSim for commercial simulation

### Running Tests

```bash
cd thielecpu/hardware
python3 test_hardware.py
```

The test suite will:
1. Verify Verilog file presence
2. Compile and simulate the design
3. Execute a comprehensive instruction sequence
4. Generate detailed test reports

### Test Program Sequence

The testbench executes the following sequence:

1. **PNEW {10}** - Create partition module with 10-element region
2. **PSPLIT 1, 0** - Split module 1 into even/odd partitions
3. **PMERGE 2, 3** - Merge partitions 2 and 3
4. **MDLACC 4** - Calculate MDL cost for merged partition
5. **EMIT 1, 2** - Output result value
6. **HALT** - End execution

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
- Breaking RSA and other public-key cryptographic systems
- Large-scale cryptanalysis on classical hardware
- Undermining digital security infrastructure

**ETHICAL USE ONLY:**
- Defensive security research applications
- Cryptographic protocol analysis
- Algorithmic complexity research

Contact maintainers for security research applications.

## Development Status

- ✅ Verilog implementation complete
- ✅ Functional simulation verified
- ✅ Test suite operational
- 🔄 FPGA synthesis pending
- 🔄 Hardware validation pending

## Contributing

This is a research prototype. Contributions should focus on:
- Performance optimization
- Security analysis
- Formal verification
- Synthesis improvements

## License

See project root LICENSE file.