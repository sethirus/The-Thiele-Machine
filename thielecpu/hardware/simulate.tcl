
create_project -in_memory test_sim
add_files /workspaces/The-Thiele-Machine/thielecpu/hardware/rtl/thiele_cpu.v
add_files /workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_tb.v
set_property top thiele_cpu_tb [get_filesets sim_1]
launch_simulation
run all
close_sim
exit
