#!/bin/bash
set -e

# Compile the simulation
echo "Compiling Thiele CPU Simulation (YOSYS_LITE)..."
iverilog -g2012 -D YOSYS_LITE -I thielecpu/hardware -o artifacts/thiele_cpu_sim \
    thielecpu/hardware/thiele_cpu_tb.v \
    thielecpu/hardware/thiele_cpu.v \
    thielecpu/hardware/mu_core.v \
    thielecpu/hardware/mu_alu.v

# Run the simulation
echo "Running Simulation..."
./artifacts/thiele_cpu_sim
