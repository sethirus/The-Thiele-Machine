// xilinx_board_cells.v: simulation stand-ins for the three Xilinx cells the
// Genesys 2 board wrapper (thielecpu/hardware/rtl/thiele_cpu_top_genesys2.v)
// instantiates and that yosys's techlibs/xilinx/cells_sim.v does not model:
// IBUFDS, MMCME2_BASE and BUFGCE. Every other cell in the synthesized
// netlist is simulated with yosys's own cells_sim.v.
//
// These are behavioural models, not Xilinx's UNISIM library. They model
// only what the board-top simulation depends on:
//
//   IBUFDS       O follows I; the model stops the simulation if I and IB are
//                ever equal at an edge of I (the pair is not differential).
//   MMCME2_BASE  CLKOUT0 is CLKIN1 divided by the integer GLS_MMCM_RATIO,
//                which scripts/board_gls.py derives from the wrapper's
//                CLKIN1_PERIOD, CLKFBOUT_MULT_F, DIVCLK_DIVIDE and
//                CLKOUT0_DIVIDE_F (200 MHz * 5 / 1 / 50 = 20 MHz, ratio 10).
//                Edges of CLKOUT0 fall on rising edges of CLKIN1. LOCKED
//                rises after LOCK_CYCLES output periods and falls on RST or
//                PWRDWN. No jitter, phase offset, duty-cycle or lock-time
//                accuracy is modelled. Other outputs are held low.
//   BUFGCE       O is I gated by CE, with CE sampled while I is low, so the
//                gated clock has no short pulses (the cell's documented
//                glitch-free behaviour for the default CE polarity).
//
// The parameters are declared without types so that whatever form the
// netlist writer gives them (real, string) elaborates; the MMCM model reads
// none of them and uses GLS_MMCM_RATIO instead.

`timescale 1ns/1ps

`ifndef GLS_MMCM_RATIO
  `define GLS_MMCM_RATIO 0
`endif

module IBUFDS #(
  parameter CAPACITANCE = "DONT_CARE",
  parameter DIFF_TERM = "FALSE",
  parameter DQS_BIAS = "FALSE",
  parameter IBUF_DELAY_VALUE = "0",
  parameter IBUF_LOW_PWR = "TRUE",
  parameter IFD_DELAY_VALUE = "AUTO",
  parameter IOSTANDARD = "DEFAULT"
) (
  output O,
  input  I,
  input  IB
);
  assign O = I;
  always @(posedge I or negedge I)
    if (I == IB) begin
      $display("{\"error\": \"IBUFDS: I and IB equal at an edge of I\"}");
      $finish;
    end
endmodule

module BUFGCE #(
  parameter CE_TYPE = "SYNC",
  parameter IS_CE_INVERTED = 1'b0,
  parameter IS_I_INVERTED = 1'b0,
  parameter SIM_DEVICE = "7SERIES",
  parameter STARTUP_SYNC = "FALSE"
) (
  output O,
  input  CE,
  input  I
);
  reg ce_q = 1'b0;
  always @(negedge I) ce_q <= CE;
  assign O = I & ce_q;
endmodule

module MMCME2_BASE #(
  parameter BANDWIDTH = "OPTIMIZED",
  parameter CLKFBOUT_MULT_F = 5.0,
  parameter CLKFBOUT_PHASE = 0.0,
  parameter CLKIN1_PERIOD = 0.0,
  parameter CLKOUT0_DIVIDE_F = 1.0,
  parameter CLKOUT0_DUTY_CYCLE = 0.5,
  parameter CLKOUT0_PHASE = 0.0,
  parameter CLKOUT1_DIVIDE = 1,
  parameter CLKOUT1_DUTY_CYCLE = 0.5,
  parameter CLKOUT1_PHASE = 0.0,
  parameter CLKOUT2_DIVIDE = 1,
  parameter CLKOUT2_DUTY_CYCLE = 0.5,
  parameter CLKOUT2_PHASE = 0.0,
  parameter CLKOUT3_DIVIDE = 1,
  parameter CLKOUT3_DUTY_CYCLE = 0.5,
  parameter CLKOUT3_PHASE = 0.0,
  parameter CLKOUT4_CASCADE = "FALSE",
  parameter CLKOUT4_DIVIDE = 1,
  parameter CLKOUT4_DUTY_CYCLE = 0.5,
  parameter CLKOUT4_PHASE = 0.0,
  parameter CLKOUT5_DIVIDE = 1,
  parameter CLKOUT5_DUTY_CYCLE = 0.5,
  parameter CLKOUT5_PHASE = 0.0,
  parameter CLKOUT6_DIVIDE = 1,
  parameter CLKOUT6_DUTY_CYCLE = 0.5,
  parameter CLKOUT6_PHASE = 0.0,
  parameter DIVCLK_DIVIDE = 1,
  parameter REF_JITTER1 = 0.0,
  parameter STARTUP_WAIT = "FALSE"
) (
  output CLKFBOUT,
  output CLKFBOUTB,
  output CLKOUT0,
  output CLKOUT0B,
  output CLKOUT1,
  output CLKOUT1B,
  output CLKOUT2,
  output CLKOUT2B,
  output CLKOUT3,
  output CLKOUT3B,
  output CLKOUT4,
  output CLKOUT5,
  output CLKOUT6,
  output LOCKED,
  input  CLKFBIN,
  input  CLKIN1,
  input  PWRDWN,
  input  RST
);
  localparam integer RATIO = `GLS_MMCM_RATIO;
  localparam integer HALF = RATIO / 2;
  localparam integer LOCK_CYCLES = 64;

  initial begin
    if (RATIO < 2 || (RATIO % 2) != 0) begin
      $display("{\"error\": \"MMCME2_BASE model: GLS_MMCM_RATIO must be an even integer >= 2, got %0d\"}", RATIO);
      $finish;
    end
  end

  reg out_q = 1'b0;
  reg locked_q = 1'b0;
  integer in_count = 0;
  integer out_periods = 0;

  always @(posedge CLKIN1) begin
    if (RST || PWRDWN) begin
      out_q <= 1'b0;
      locked_q <= 1'b0;
      in_count <= 0;
      out_periods <= 0;
    end else if (in_count == HALF - 1) begin
      in_count <= 0;
      out_q <= ~out_q;
      if (out_q) begin
        if (out_periods < LOCK_CYCLES) out_periods <= out_periods + 1;
        else locked_q <= 1'b1;
      end
    end else begin
      in_count <= in_count + 1;
    end
  end

  assign CLKOUT0 = out_q;
  assign CLKOUT0B = ~out_q;
  assign CLKFBOUT = CLKIN1;
  assign CLKFBOUTB = ~CLKIN1;
  assign LOCKED = locked_q;
  assign CLKOUT1 = 1'b0;
  assign CLKOUT1B = 1'b0;
  assign CLKOUT2 = 1'b0;
  assign CLKOUT2B = 1'b0;
  assign CLKOUT3 = 1'b0;
  assign CLKOUT3B = 1'b0;
  assign CLKOUT4 = 1'b0;
  assign CLKOUT5 = 1'b0;
  assign CLKOUT6 = 1'b0;
endmodule
