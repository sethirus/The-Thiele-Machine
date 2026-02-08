#!/bin/bash
set -e

# Compile the simulation
echo "Compiling Thiele CPU Simulation (YOSYS_LITE)..."
iverilog -g2012 -D YOSYS_LITE -I thielecpu/hardware/rtl -o artifacts/thiele_cpu_sim \
    thielecpu/hardware/testbench/thiele_cpu_tb.v \
    thielecpu/hardware/rtl/thiele_cpu_unified.v

# Run the simulation
echo "Running Simulation..."
./artifacts/thiele_cpu_sim
