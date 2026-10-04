Pinned Xilinx UNISIM simulation sources

Upstream: https://github.com/Xilinx/XilinxUnisimLibrary
Revision: 1c8e05fd1e9a79ceb8b996a0996674122eed086f
RAMB36E1.v: verilog/src/unisims/RAMB36E1.v
  SHA256 b6153b595696f7eebe6840b2b8d518e32df698cb8e8b2730c8838648ceec72fb
glbl.v: verilog/src/glbl.v
  SHA256 de59a57e3e0091f1b9162d9914dce24c469820a0c5b5a41d1d202d93fae0abdd

Both files retain their upstream Apache-2.0 copyright/license headers and are
unmodified. RAMB36E1.v is the regression reference, run under Icarus; its older
procedural assign/deassign/event scheduling is not supported faithfully by
Verilator 5.020. glbl.v supplies the vendor startup/reset global.

The gate harness uses ../ramb36_sdp72.v for the exact mode synthesized here:
72-bit simple-dual-port RAM, port B write / port A synchronous read, no output
pipeline, ECC, cascade or inverted pins, common clock. Other configurations
fail explicitly. Port/parameter declarations retain the Yosys 0.33 ISC notice;
the functional body implements INIT data/parity layout, byte write enables,
read enable/hold and collision-undefined read data. This model is tested under
Icarus and Verilator against the same reset, initialized read, full-write/read
and byte-masked-read traces passed by the unmodified vendor model in Icarus.
The CI simulator is pinned to upstream Verilator 5.050 by setup-verilator:
5.020 fails the same initialized-read regression that passes under 5.050.
The pin includes the upstream revision and archive SHA256; no assertion is
disabled to accommodate the simulator difference.

This changes simulation support only, never the synthesized netlist. It is not
an analogue, timing, or physical-board sign-off. The three clock/input stand-ins
in ../xilinx_board_cells.v retain their separately documented limits.
