# ============================================================================
# Thiele CPU Timing and Pin Constraints
# ============================================================================

# Clock constraints
create_clock -period 5.000 -name clk [get_ports clk]
set_clock_uncertainty 0.100 [get_clocks clk]

# Input delay constraints
set_input_delay -clock clk 1.000 [get_ports rst_n]

# Output delay constraints
set_output_delay -clock clk 1.000 [get_ports cert_addr]
set_output_delay -clock clk 1.000 [get_ports status]
set_output_delay -clock clk 1.000 [get_ports error_code]

# Memory interface constraints
set_output_delay -clock clk 1.000 [get_ports mem_addr]
set_output_delay -clock clk 1.000 [get_ports mem_wdata]
set_output_delay -clock clk 1.000 [get_ports mem_we]
set_output_delay -clock clk 1.000 [get_ports mem_en]
set_input_delay -clock clk 1.000 [get_ports mem_rdata]

# Logic engine interface constraints
set_output_delay -clock clk 1.000 [get_ports logic_req]
set_output_delay -clock clk 1.000 [get_ports logic_addr]
set_input_delay -clock clk 1.000 [get_ports logic_ack]
set_input_delay -clock clk 1.000 [get_ports logic_data]

# Python execution interface constraints
set_output_delay -clock clk 1.000 [get_ports py_req]
set_output_delay -clock clk 1.000 [get_ports py_code_addr]
set_input_delay -clock clk 1.000 [get_ports py_ack]
set_input_delay -clock clk 1.000 [get_ports py_result]

# Instruction interface constraints
set_input_delay -clock clk 1.000 [get_ports instr_data]
set_output_delay -clock clk 1.000 [get_ports pc]

# Multi-cycle path constraints for complex operations
set_multicycle_path 3 -setup -from [get_pins dut/state_reg*/C] -to [get_pins dut/state_reg*/D]
set_multicycle_path 2 -hold -from [get_pins dut/state_reg*/C] -to [get_pins dut/state_reg*/D]

# False path constraints for reset
set_false_path -from [get_ports rst_n] -to [get_pins dut/state_reg*/D]

# Physical constraints (example for ZCU102 board)
# Clock input
set_property PACKAGE_PIN G21 [get_ports clk]
set_property IOSTANDARD LVCMOS18 [get_ports clk]

# Reset input
set_property PACKAGE_PIN G22 [get_ports rst_n]
set_property IOSTANDARD LVCMOS18 [get_ports rst_n]

# Example output pin assignments (adjust for your board)
# set_property PACKAGE_PIN A20 [get_ports {cert_addr[0]}]
# set_property PACKAGE_PIN B20 [get_ports {cert_addr[1]}]
# ... (add more pin assignments as needed)

# Timing exceptions for external interfaces
set_max_delay 10.000 -from [get_ports logic_req] -to [get_ports logic_ack]
set_max_delay 15.000 -from [get_ports py_req] -to [get_ports py_ack]

# Area constraints
create_pblock pblock_cpu
add_cells_to_pblock [get_pblocks pblock_cpu] [get_cells dut]
resize_pblock [get_pblocks pblock_cpu] -add {SLICE_X0Y0:SLICE_X50Y50}

# Power optimization
set_power_opt -include_all

puts "Constraints loaded successfully"