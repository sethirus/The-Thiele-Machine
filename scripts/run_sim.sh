#!/bin/bash
set -e

# Compile the simulation
echo "Compiling Thiele CPU Simulation (YOSYS_LITE)..."
iverilog -g2012 -D YOSYS_LITE -I thielecpu/hardware/rtl -o artifacts/thiele_cpu_sim \
    thielecpu/hardware/testbench/thiele_cpu_tb.v \
    thielecpu/hardware/rtl/thiele_cpu.v \
    thielecpu/hardware/rtl/mu_core.v \
    thielecpu/hardware/rtl/mu_alu.v \
    thielecpu/hardware/rtl/receipt_integrity_checker.v

# Run the simulation
echo "Running Simulation..."
./artifacts/thiele_cpu_sim
