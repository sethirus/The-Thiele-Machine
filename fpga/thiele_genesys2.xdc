# =============================================================================
# Kintex-7 K420T (ffg900) constraints for Thiele CPU.
# =============================================================================
# File name kept as thiele_genesys2.xdc to minimise churn vs. the prior K325T
# iteration; the ffg900 package bonding is identical on K420T, so the same
# pin assignments compile cleanly. The bigger DSP budget (1680 vs 840) is
# what motivates the part change — see synth_xc7.ys for the DSP-fit rationale.
#
# Pin assignments below are the Digilent Genesys 2 K325T-ffg900 layout. They
# remain valid at the package level on K420T-ffg900 for CI synthesis. A
# physical K420T-ffg900 board may differ in routing — adjust here when there
# is an actual board to target.
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
