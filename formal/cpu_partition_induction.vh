// Induction obligations for A3-A8 of cpu_props.vh.
// scripts/cpu_partition_prove.py checks every obligation before reporting PASS.
// These assertions observe the extracted RTL; they do not drive its state.
//
// J strengthens A3-A5 with base <= 255, including empty entries. PNEW's
// base is a byte; splitting and merging preserve this bound. Empty bases
// need not be <= 128. J is proved from reset and preserved independently
// before it is used in the non-overlap obligations.
`define PT_SIZE(i) ptTable[(i)*32 +: 32]
`define PT_BASE(i) ptBases[(i)*32 +: 32]
`define PT_END(i) ({1'b0,`PT_BASE(i)} + {1'b0,`PT_SIZE(i)})

(* anyconst *) reg [5:0] ptf_a, ptf_b;
wire [5:0] ptf_source_a = imem$D_OUT_1[21:16];
wire [5:0] ptf_source_b = imem$D_OUT_1[13:8];

function ptf_disjoint;
  input [5:0] a, b;
  begin
    ptf_disjoint = a == b || `PT_SIZE(a) == 0 || `PT_SIZE(b) == 0 ||
      `PT_END(a) <= {1'b0,`PT_BASE(b)} ||
      `PT_END(b) <= {1'b0,`PT_BASE(a)};
  end
endfunction

wire [63:0] ptf_slot_valid;
genvar ptf_i;
generate for (ptf_i = 0; ptf_i < 64; ptf_i = ptf_i + 1) begin
  assign ptf_slot_valid[ptf_i] =
    `PT_BASE(ptf_i) <= 255 &&
    (ptf_i < pt_next_id || `PT_SIZE(ptf_i) == 0) &&
    (`PT_SIZE(ptf_i) == 0 || `PT_END(ptf_i) <= 128);
end endgenerate
wire ptf_j = pt_next_id >= 1 && pt_next_id <= 64 && (&ptf_slot_valid);

// Every conjunct below follows from J and global pairwise disjointness.
// Using only the pairs relevant to this transition reduces the solver input;
// the conclusion still quantifies over every pair of table indices.
wire ptf_relevant = ptf_j &&
  ptf_disjoint(ptf_a, ptf_b) &&
  ptf_disjoint(ptf_a, ptf_source_a) &&
  ptf_disjoint(ptf_b, ptf_source_a) &&
  ptf_disjoint(ptf_a, ptf_source_b) &&
  ptf_disjoint(ptf_b, ptf_source_b) &&
  ptf_disjoint(ptf_source_a, ptf_source_b);

`ifdef PT_DISJOINT
// PSPLIT's old/left/right cases cover all unordered pairs. This flag is
// constrained in the OLD SAT frame only; it never constrains the update.
(* keep *) wire ptf_old_pair =
  ptf_a != pt_next_id && ptf_a != pt_next_id + 1 &&
  ptf_b != pt_next_id && ptf_b != pt_next_id + 1;
`endif

reg ptf_past = 0;
reg ptf_j_q, ptf_relevant_q, ptf_rst_q, ptf_step_q, ptf_err_q;
reg [7:0] ptf_opcode_q;
reg [31:0] ptf_trap_q;
reg [6:0] ptf_next_q;
reg [2047:0] ptf_sizes_q, ptf_bases_q;
always @(posedge CLK) begin
  ptf_past <= 1;
  ptf_j_q <= ptf_j;
  ptf_relevant_q <= ptf_relevant;
  ptf_rst_q <= RST_N != `BSV_RESET_VALUE;
  ptf_step_q <= WILL_FIRE_RL_step;
  ptf_err_q <= err;
  ptf_opcode_q <= imem$D_OUT_1[31:24];
  ptf_trap_q <= trap_vector;
  ptf_next_q <= pt_next_id;
  ptf_sizes_q <= ptTable;
  ptf_bases_q <= ptBases;
end
wire ptf_same = pt_next_id == ptf_next_q &&
  `PT_SIZE(ptf_a) == ptf_sizes_q[ptf_a*32 +: 32] &&
  `PT_BASE(ptf_a) == ptf_bases_q[ptf_a*32 +: 32];
wire ptf_partition = ptf_opcode_q <= 2;

`ifdef PT_BOUNDS
// The original CPU environment contract, proved by the loader's S1.
always @* if (EN_start) assume(halted);
`endif

always @* if (ptf_past) begin
`ifdef PT_DISJOINT
  assume(ptf_relevant_q);
  assert(ptf_disjoint(ptf_a, ptf_b));
`else
  `ifdef PT_FRAME
    if (ptf_rst_q)
      assert((ptf_step_q && ptf_partition) || ptf_same);
  `else
    `ifdef PT_BOUNDS
      assume(ptf_j_q);
    `endif
    assert(`PT_BASE(ptf_a) <= 255);
    assert(pt_next_id >= 1 && pt_next_id <= 64);
    assert(ptf_a < pt_next_id || `PT_SIZE(ptf_a) == 0);
    assert(`PT_SIZE(ptf_a) == 0 || `PT_END(ptf_a) <= 128);
    `ifdef PT_BASE_CASE
      assert(ptf_disjoint(ptf_a, ptf_b));
    `else
      if (ptf_rst_q) begin
        assert(!(ptf_step_q && ptf_partition && !ptf_err_q && err) ||
          (pc == ptf_trap_q && ptf_same));
        assert((ptf_step_q && ptf_partition) || ptf_same);
      end
    `endif
  `endif
`endif
end

`undef PT_SIZE
`undef PT_BASE
`undef PT_END
