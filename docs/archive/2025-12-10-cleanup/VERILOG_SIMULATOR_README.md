# Thiele Machine Verilog Simulator

A VS Code extension that provides Verilog simulation tools specifically designed for the Thiele Machine hardware implementation.

## Features

### Commands

- **Clear Environment Cache** (`verilog-simulator.clearCache`)
  - Clears the Verilog simulation cache directory
  - Available in Command Palette

- **Generate Waveform** (`verilog-simulator.generateWaveform`)
  - Compiles and simulates Verilog testbenches
  - Generates VCD waveform files
  - Automatically opens waveforms in GTKWave (if installed)
  - Available in Command Palette and editor context menu for .v files

- **Regenerate VCD File (Robust Mode)** (`verilog-simulator.regenerateVcd`)
  - Performs a clean rebuild of all Verilog dependencies
  - Ensures robust simulation with all module dependencies
  - Available in Command Palette and editor context menu for .v files

## Requirements

- **Icarus Verilog** (`iverilog`) - for compilation and simulation
- **GTKWave** (optional) - for waveform viewing
- VS Code 1.74.0 or later

## Installation

### From Source

1. Clone the Thiele Machine repository
2. Navigate to the root directory
3. Run `npm install`
4. Run `npm run compile`
5. Press `F5` to launch extension development host

### From VSIX

1. Download the `.vsix` file
2. In VS Code: `Extensions` → `Install from VSIX...`

## Usage

### Basic Simulation

1. Open a Verilog testbench file (files containing "tb" or "test" in the name)
2. Use `Ctrl+Shift+P` to open Command Palette
3. Select "Verilog Simulator: Generate Waveform"
4. The extension will:
   - Compile the Verilog files
   - Run the simulation
   - Generate a VCD file
   - Open GTKWave for waveform viewing

### Robust Mode

For complex designs with multiple dependencies:

1. Open any Verilog file in the design
2. Run "Verilog Simulator: Regenerate VCD File (Robust Mode)"
3. The extension will clean all build artifacts and rebuild everything

### Cache Management

- Run "Verilog Simulator: Clear Environment Cache" to clear cached files
- Useful when switching between different design versions

## Supported File Types

- `.v` - Verilog source files
- Testbenches with "tb" or "test" in filename are automatically detected

## Architecture

The extension integrates with the Thiele Machine's hardware directory structure:

```
thielecpu/hardware/
├── *.v              # Verilog source files
├── *_tb.v          # Testbench files
├── .verilog_cache/ # Cache directory (auto-managed)
└── *.vcd           # Generated waveform files
```

## Troubleshooting

### "iverilog command not found"
Install Icarus Verilog:
```bash
sudo apt install iverilog  # Ubuntu/Debian
brew install icarus-verilog  # macOS
```

### "gtkwave command not found"
Install GTKWave for waveform viewing:
```bash
sudo apt install gtkwave  # Ubuntu/Debian
brew install gtkwave      # macOS
```

### Compilation Errors
- Ensure all Verilog dependencies are in the same directory
- Use "Regenerate VCD (Robust Mode)" for complex designs
- Check the VS Code output panel for detailed error messages

## Contributing

This extension is part of the Thiele Machine project. Contributions should follow the main project's guidelines.

## License

Licensed under the Apache License, Version 2.0. See the main Thiele Machine repository for details.