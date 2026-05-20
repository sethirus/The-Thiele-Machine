# =============================================================================
# Genesys 2 (Digilent, xc7k325t-ffg900-2) constraints for Thiele CPU.
# =============================================================================
# Pin assignments per the Digilent Genesys 2 reference manual.
# Clock: 200MHz LVDS sysclk on AD12 (P) / AD11 (N) — converted to single-ended
#        via IBUFDS in thiele_cpu_top_genesys2.v.
# Reset: CPU_RESETN button (R19), active-low with on-board pull-up.
# LEDs:  LD0..LD2 on T28 / V19 / U30 (active-high).
# =============================================================================

# 200MHz LVDS system clock
set_property PACKAGE_PIN AD12 [get_ports clk_p]
set_property IOSTANDARD  LVDS [get_ports clk_p]
set_property PACKAGE_PIN AD11 [get_ports clk_n]
set_property IOSTANDARD  LVDS [get_ports clk_n]
create_clock -period 5.000 -name sys_clk_pin [get_ports clk_p]

# CPU_RESETN button (active-low)
set_property PACKAGE_PIN R19      [get_ports cpu_reset_n]
set_property IOSTANDARD  LVCMOS33 [get_ports cpu_reset_n]

# Status LEDs (active-high)
set_property PACKAGE_PIN T28      [get_ports LED_HALTED]
set_property IOSTANDARD  LVCMOS33 [get_ports LED_HALTED]
set_property PACKAGE_PIN V19      [get_ports LED_ERR]
set_property IOSTANDARD  LVCMOS33 [get_ports LED_ERR]
set_property PACKAGE_PIN U30      [get_ports LED_BIANCHI]
set_property IOSTANDARD  LVCMOS33 [get_ports LED_BIANCHI]
