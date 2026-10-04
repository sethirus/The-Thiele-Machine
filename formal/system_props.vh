// system_props.vh: safety properties of the extracted serial loader and
// status reporter (mkThieleSystem in thielecpu/hardware/rtl/thiele_system.v,
// from coq/kami_hw/ThieleLoader.v and ThieleSystem.v).
//
// scripts/formal_prepare.py includes this file just before mkThieleSystem's
// final `endmodule` in a copy under build/formal/. The CPU inside (m1) is the
// unmodified extracted mkModule1; the CPU properties are not included here,
// so their environment assumption (S1 below) is not assumed in this task.
//
//   S1  the loader calls the CPU's start method only while the CPU is
//       halted (the assumption cpu_props.vh makes about its environment).
//   S2  once started, the loader never writes instruction memory again.
//   S3  start is called at most once after reset.
//   S4  the status report begins only after the start and only when the CPU
//       is halted or in error.
//   S5  once the report has been sent, no second report begins.
// Covers: a load, the start, the report beginning, the report finishing.

`ifdef FORMAL
  `ifdef FORMAL_COVER
    `define S_ASSERT(name, c) assume(c)
    `define S_COVER(idx, name, c) cover(c)
  `else
    `define S_ASSERT(name, c) assert(c)
    `define S_COVER(idx, name, c)
  `endif
  `define S_ALWAYS always @*
`else
  `define S_ASSERT(name, c) if (!(c)) $display("{\"assert_fail\": \"%s\", \"time\": %0t}", name, $time)
  `define S_COVER(idx, name, c) if ((c) && !s_hits[idx]) begin s_hits[idx] = 1'b1; $display("{\"cover\": \"%s\"}", name); end
  `define S_ALWAYS always @(posedge CLK)
`endif

`ifndef FORMAL
  reg [7:0] s_hits = 8'd0;
`endif

  reg s_past_valid = 1'b0;
`ifdef FORMAL_COVER
  reg s_reset_seen = 1'b1;
`else
  reg s_reset_seen = 1'b0;
`endif
  always @(posedge CLK) begin
    s_past_valid <= 1'b1;
    if (RST_N == `BSV_RESET_VALUE) s_reset_seen <= 1'b1;
  end
`ifdef FORMAL
  `ifdef FORMAL_COVER
  always @* assume(RST_N != `BSV_RESET_VALUE);
  `else
  always @* if (!s_reset_seen) assume(RST_N == `BSV_RESET_VALUE);
  `endif
`endif

  reg s_rst_q, s_txa_q, s_txdone_q, s_started_q, s_halted_q, s_err_q, s_start_q;
  always @(posedge CLK) begin
    s_rst_q     <= (RST_N != `BSV_RESET_VALUE);
    s_txa_q     <= m2_tx_active;
    s_txdone_q  <= m2_tx_done;
    s_started_q <= m2_started;
    s_halted_q  <= m1$getHalted;
    s_err_q     <= m1$getErr;
    s_start_q   <= m1$EN_start;
  end
  wire s_chk  = s_reset_seen;
  wire s_chk1 = s_reset_seen && s_past_valid && s_rst_q;
  wire s_tx_begins = !s_txa_q && m2_tx_active;

`ifdef FORMAL
`ifndef FORMAL_COVER
  // Strengthen the induction hypothesis with the loader's intermediate
  // invariants. These are proved alongside S1-S5, never assumed. The CPU
  // remains the full extracted design, with no abstracted ports or new
  // environment restrictions. Phase 3 is terminal; start_req toggles once
  // on entry, and start_ack catches it only after the final load is drained.
  always @* if (s_chk) begin
    assert(!m2_started || m2_ld_phase == 2'd3);
    assert(!m2_started || m2_load_req == m2_load_ack);
    assert(m2_start_ack == m2_started);
    assert(m2_start_req == (m2_ld_phase == 2'd3));
    assert(!m2_started || m2_start_req == m2_start_ack);
    assert(m2_started || m1$getHalted);
  end
`endif
`endif

  `S_ALWAYS begin
    if (s_chk) begin
      `S_ASSERT("S1_start_only_when_halted", !m1$EN_start || m1$getHalted);
      `S_ASSERT("S2_no_load_after_start", !(m2_started && m1$EN_loadInstr));
    end
    if (s_chk1) begin
      `S_ASSERT("S3_start_once", !(s_started_q && m1$EN_start));
      `S_ASSERT("S4_report_after_stop", !s_tx_begins || (s_started_q && (s_halted_q || s_err_q)));
      `S_ASSERT("S5_report_once", !s_txdone_q || (m2_tx_done && !s_tx_begins));
      `S_COVER(0, "D1_load", m1$EN_loadInstr);
      `S_COVER(1, "D2_start", m1$EN_start);
      `S_COVER(2, "D3_report_begins", s_tx_begins);
      `S_COVER(3, "D4_report_done", !s_txdone_q && m2_tx_done);
    end
  end
