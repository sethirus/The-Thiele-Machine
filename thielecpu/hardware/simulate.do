
vlib work
vlog /workspace/The-Thiele-Machine/thielecpu/hardware/thiele_cpu.v
vlog /workspace/The-Thiele-Machine/thielecpu/hardware/thiele_cpu_tb.v
vsim -c thiele_cpu_tb -do "run -all; quit"
