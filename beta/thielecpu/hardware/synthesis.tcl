# ============================================================================
# Thiele CPU FPGA Synthesis Script
# ============================================================================

# Create project
create_project thiele_cpu ./thiele_cpu_vivado -part xczu7ev-ffvc1156-2-e -force

# Add source files
add_files thiele_cpu.v
add_files thiele_cpu_tb.v

# Set top module
set_property top thiele_cpu [current_fileset]

# Add constraints
add_files -fileset constrs_1 constraints.xdc

# Set synthesis and implementation strategies
set_property strategy Flow_PerfOptimized_high [get_runs synth_1]
set_property strategy Performance_ExplorePostRoutePhysOpt [get_runs impl_1]

# Enable verbose reporting
set_param synth.elaboration.rodinMoreOptions "rt::set_parameter verbose 1"
set_param synth.elaboration.rodinMoreOptions "rt::set_parameter printBanner 0"

# Run synthesis
launch_runs synth_1 -jobs 8
wait_on_run synth_1

# Run implementation
launch_runs impl_1 -jobs 8
wait_on_run impl_1

# Generate reports
open_run impl_1
report_utilization -file utilization.rpt
report_timing -file timing.rpt
report_power -file power.rpt

# Generate bitstream
launch_runs impl_1 -to_step write_bitstream -jobs 8
wait_on_run impl_1

puts "FPGA synthesis completed successfully!"
puts "Check the following reports:"
puts "- utilization.rpt: Resource utilization"
puts "- timing.rpt: Timing analysis"
puts "- power.rpt: Power consumption"
puts "- thiele_cpu.bit: Generated bitstream"