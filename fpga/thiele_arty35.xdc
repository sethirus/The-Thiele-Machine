## Arty A7-35T pin constraints for thiele_cpu_top wrapper.
## Board: Digilent Arty A7-35T (xc7a35tcsg324-1).
## Synthesized top exposes only 5 device pins; the rest of mkModule1's
## Bluespec-method I/Os are tied off internally by the wrapper.

# 100 MHz clock from the on-board oscillator
set_property -dict { PACKAGE_PIN E3   IOSTANDARD LVCMOS33 } [get_ports CLK]
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports CLK]

# Active-low reset (BTN0 on Arty A7)
set_property -dict { PACKAGE_PIN D9   IOSTANDARD LVCMOS33 } [get_ports RST_N]

# Status LEDs (LD0/LD1/LD2 on Arty A7)
set_property -dict { PACKAGE_PIN H5   IOSTANDARD LVCMOS33 } [get_ports LED_HALTED]
set_property -dict { PACKAGE_PIN J5   IOSTANDARD LVCMOS33 } [get_ports LED_ERR]
set_property -dict { PACKAGE_PIN T9   IOSTANDARD LVCMOS33 } [get_ports LED_BIANCHI]
