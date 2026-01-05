
vlib work
vlog /workspaces/The-Thiele-Machine/thielecpu/hardware/rtl/thiele_cpu.v
vlog /workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_tb.v
vsim -c thiele_cpu_tb -do "run -all; quit"
