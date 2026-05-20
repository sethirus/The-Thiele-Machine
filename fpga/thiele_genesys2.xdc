# =============================================================================
# Kintex-7 K480T (ffg901) CI-synthesis constraints for Thiele CPU.
# =============================================================================
# File name kept as thiele_genesys2.xdc to minimise downstream churn —
# run_synthesis_xc7.sh and the workflow reference this file by name. The
# actual target part is xc7k480tffg901-2 (1920 DSP48E1, smallest openXC7-
# supported Kintex-7 with a complete prjxray-db entry that fits the ~1131
# DSPs the design needs). Original Genesys 2 K325T-ffg900 pin layout is no
# longer valid — different package, different pinout — so this XDC uses
# arbitrary single-ended GPIO pins drawn from the K480T-ffg901
# package_pins.csv. These are placeholder assignments suitable for CI
# synthesis verification; a real board build would replace them with the
# board's actual pinout.
#
# Pins drawn from bank 11 (HR, LVCMOS33-capable). All single-ended; the
# wrapper (thiele_cpu_top_genesys2.v) was updated to drop the IBUFDS so
# the design no longer requires an LVDS pair.
# =============================================================================

# 200 MHz single-ended system clock (CI placeholder pin; bank 11 IO_0_11)
set_property PACKAGE_PIN AC19     [get_ports sysclk]
set_property IOSTANDARD  LVCMOS33 [get_ports sysclk]
create_clock -period 5.000 -name sys_clk_pin [get_ports sysclk]

# CPU reset (active-low)
set_property PACKAGE_PIN AG19     [get_ports cpu_reset_n]
set_property IOSTANDARD  LVCMOS33 [get_ports cpu_reset_n]

# Status LEDs (active-high)
set_property PACKAGE_PIN AH20     [get_ports LED_HALTED]
set_property IOSTANDARD  LVCMOS33 [get_ports LED_HALTED]
set_property PACKAGE_PIN AH19     [get_ports LED_ERR]
set_property IOSTANDARD  LVCMOS33 [get_ports LED_ERR]
set_property PACKAGE_PIN AJ19     [get_ports LED_BIANCHI]
set_property IOSTANDARD  LVCMOS33 [get_ports LED_BIANCHI]
