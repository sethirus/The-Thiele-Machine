
create_project -in_memory test_sim
add_files C:\Users\tbagt\TheThieleMachine\thielecpu\hardware\thiele_cpu.v
add_files C:\Users\tbagt\TheThieleMachine\thielecpu\hardware\thiele_cpu_tb.v
set_property top thiele_cpu_tb [get_filesets sim_1]
launch_simulation
run all
close_sim
exit
