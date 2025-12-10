# Thiele Machine Verilog Simulator Extension

This VS Code extension provides integrated Verilog simulation tools for the Thiele Machine hardware implementation.

## Commands Added

| Command | Title | Description | Context |
|---------|-------|-------------|---------|
| `verilog-simulator.clearCache` | Clear Environment Cache | Clears simulation cache | Command Palette |
| `verilog-simulator.generateWaveform` | Generate Waveform | Compiles and simulates testbenches, generates VCD | Command Palette, Editor Context (.v files) |
| `verilog-simulator.regenerateVcd` | Regenerate VCD (Robust Mode) | Clean rebuild with all dependencies | Command Palette, Editor Context (.v files) |

## Quick Start

1. **Open a testbench file** (e.g., `mu_alu_tb.v` or `thiele_cpu_tb.v`)
2. **Press F1** or **Ctrl+Shift+P** to open Command Palette
3. **Select "Verilog Simulator: Generate Waveform"**
4. **Watch the simulation run** and **view waveforms in GTKWave**

## Features

- **Automatic VCD Generation**: Testbenches now include waveform dumping
- **GTKWave Integration**: Automatically opens waveforms for analysis
- **Robust Mode**: Handles complex designs with multiple dependencies
- **Progress Feedback**: Real-time compilation and simulation status
- **Error Handling**: Clear error messages for troubleshooting

## Testbenches Updated

- `mu_alu_tb.v` - μ-ALU arithmetic verification
- `thiele_cpu_tb.v` - Complete CPU instruction testing

## Dependencies

- **Icarus Verilog** (`iverilog`) - ✅ Installed
- **GTKWave** - ✅ Installed
- **VS Code 1.74+** - ✅ Available

## Usage Examples

### Basic Simulation
```
1. Open thielecpu/hardware/mu_alu_tb.v
2. Run "Verilog Simulator: Generate Waveform"
3. GTKWave opens with μ-ALU waveforms
```

### Robust Mode for Complex Designs
```
1. Open thielecpu/hardware/thiele_cpu_tb.v
2. Run "Verilog Simulator: Regenerate VCD (Robust Mode)"
3. All dependencies rebuilt from scratch
```

### Cache Management
```
Run "Verilog Simulator: Clear Environment Cache" to reset
```

## Integration with Thiele Machine

This extension completes the hardware verification toolchain:

- **Python VM** ✅ (Isomorphic)
- **Verilog Hardware** ✅ (Now with simulation tools)
- **Coq Proofs** ✅ (Compiled and verified)

The Thiele Machine is now **fully verifiable** across all implementation layers with integrated simulation capabilities.