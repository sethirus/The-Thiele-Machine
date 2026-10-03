// cpu_props.vh: safety properties of the extracted CPU (mkModule1 in
// thielecpu/hardware/rtl/thiele_cpu_kami.v).
//
// scripts/formal_prepare.py copies thiele_cpu_kami.v into build/formal/ and
// includes this file just before mkModule1's final `endmodule`, so the
// properties read the CPU's own registers and rule-enable wires by name. The
// copy adds no logic that drives the CPU; the extracted file in the tree is
// never edited.
//
// Three ways to use it:
//   FORMAL, no FORMAL_COVER  the A* lines are assertions, checked for every
//                            state reachable from reset (sby task cpu_prove).
//   FORMAL + FORMAL_COVER    the A* lines become assumptions and the C*
//                            lines are cover goals (sby task cpu_cover): each
//                            cover must be reached by a real transition of
//                            the RTL from a state satisfying every proved
//                            property.
//   neither (simulation)     A* failures and first C* hits are printed as JSON
//                            lines (scripts/board_gls.py --props), so the
//                            programs show which covers are reachable from
//                            reset through the board pins.
//
// What the properties state (each is a fact the Coq refinement relies on or
// implies for the extracted CPU; names in [] are the Coq sources):
//   A1  err never clears except by reset. The step rule is guarded by !err and
//       every other rule writes err := err || ... [ThieleCPUCore.v rule step,
//       lassert_fsm_scan, mc_*, chsh_lassert_fsm].
//   A2  no instruction executes while err is set.
//   A3  1 <= pt_next_id <= 64: the 64-slot partition table bound
//       [ptable_full/ptable_room_* capacity guards].
//   A4  every slot at or above pt_next_id is empty (size 0).
//   A5  every nonempty slot's range [base, base+size) lies inside the
//       128-word data memory [pnew_out_of_memory; regions_in_memory].
//   A6  nonempty slots are pairwise disjoint [pt_range_conflict;
//       vm_reachable_regions_disjoint].
//   A7  a PNEW/PSPLIT/PMERGE that sets err sends pc to the trap vector and
//       leaves the partition table and pt_next_id as they were.
//   A8  the partition table and pt_next_id change only when the step rule
//       retires a PNEW, PSPLIT or PMERGE.
//   A9  1 <= morph_next_id <= 16 [rich_table_overflow].
//   A10 a valid morphism slot lies below morph_next_id
//       [hwb_morph_valid_below_next, StepRefineMorph.v].
//   A11 mu changes only when the step rule or the LASSERT scan rule fires.
//   A12 halted clears only through the start method.
// Not stated: "mu never decreases". mu is a 32-bit register; a charge such
// as LASSERT's flen*8 + cost + 1 can wrap it, and the Coq refinement assumes
// no counter exceeds 32 bits. A11 and the GLS comparison against the VM are
// what the hardware side checks about mu.
//
// Environment assumption (cpu_prove only): the start method is called only
// while the CPU is halted. mkThieleSystem's loader is the only caller;
// system_props.vh proves it keeps this contract (S1).

`ifdef FORMAL
  `ifdef FORMAL_COVER
    `define F_ASSERT(name, c) assume(c)
    `define F_COVER(idx, name, c) cover(c)
  `else
    `define F_ASSERT(name, c) assert(c)
    `define F_COVER(idx, name, c)
  `endif
  `define F_ALWAYS always @*
`else
  `define F_ASSERT(name, c) if (!(c)) $display("{\"assert_fail\": \"%s\", \"time\": %0t}", name, $time)
  `define F_COVER(idx, name, c) if ((c) && !f_hits[idx]) begin f_hits[idx] = 1'b1; $display("{\"cover\": \"%s\"}", name); end
  `define F_ALWAYS always @(posedge CLK)
`endif

`ifndef FORMAL
  reg [15:0] f_hits = 16'd0;   // simulation: covers already printed
`endif

  reg f_past_valid = 1'b0;
`ifdef FORMAL_COVER
  reg f_reset_seen = 1'b1;
`else
  reg f_reset_seen = 1'b0;
`endif
  always @(posedge CLK) begin
    f_past_valid <= 1'b1;
    if (RST_N == `BSV_RESET_VALUE) f_reset_seen <= 1'b1;
  end

  // Formal: the first cycle is a reset cycle (prove), or the design is never
  // reset and starts anywhere the assumed invariants allow (cover).
`ifdef FORMAL
  `ifdef FORMAL_COVER
  always @* assume(RST_N != `BSV_RESET_VALUE);
  `else
  always @* if (!f_reset_seen) assume(RST_N == `BSV_RESET_VALUE);
  always @* if (EN_start) assume(halted);
  `endif
`endif

  // One-cycle history.
  reg        f_rst_q, f_err_q, f_step_q, f_scan_q, f_halted_q, f_start_q, f_erren_q;
  reg [7:0]  f_opc_q;
  reg [31:0] f_tv_q, f_mu_q;
  reg [6:0]  f_next_q;
  reg [4:0]  f_mnext_q;
  reg [2047:0] f_pt_q, f_pb_q;
  always @(posedge CLK) begin
    f_rst_q    <= (RST_N != `BSV_RESET_VALUE);
    f_err_q    <= err;
    f_erren_q  <= err$EN;
    f_step_q   <= WILL_FIRE_RL_step;
    f_scan_q   <= WILL_FIRE_RL_lassert_fsm_scan;
    f_halted_q <= halted;
    f_start_q  <= EN_start;
    f_opc_q    <= imem$D_OUT_1[31:24];
    f_tv_q     <= trap_vector;
    f_mu_q     <= mu;
    f_next_q   <= pt_next_id;
    f_mnext_q  <= morph_next_id;
    f_pt_q     <= ptTable;
    f_pb_q     <= ptBases;
  end

  wire f_chk  = f_reset_seen;                              // reached through a reset
  wire f_chk1 = f_reset_seen && f_past_valid && f_rst_q;   // and the last edge was not a reset
  wire f_part_q = (f_opc_q == 8'h00) || (f_opc_q == 8'h01) || (f_opc_q == 8'h02);
  wire f_pt_same = (ptTable == f_pt_q) && (ptBases == f_pb_q) && (pt_next_id == f_next_q);
  wire f_part_trap = f_chk1 && f_step_q && f_part_q && !f_err_q && err;
`ifdef FORMAL
  wire f_pt_check = f_chk;
`else
  // Simulation checks the table invariants when the table has just changed
  // (or right after reset); between writes the table is constant.
  wire f_pt_check = f_chk && (!f_past_valid || !f_pt_same || !f_rst_q);
`endif

  // Slot i owns [ptBases[i], ptBases[i] + ptTable[i]); size 0 is an empty slot.
  `define F_SZ(i) ptTable[(i)*32 +: 32]
  `define F_BS(i) ptBases[(i)*32 +: 32]
  `define F_EN(i) ({1'b0, `F_BS(i)} + {1'b0, `F_SZ(i)})

  // Two groups, so a formal task can carry only one group's cone of logic:
  // F_SKIP_PT drops the partition-table group (A3-A8), F_SKIP_CTRL the
  // control group (A1, A2, A9-A12). Simulation and the cover task use both.
`ifndef F_SKIP_CTRL
  `F_ALWAYS begin
    if (f_chk) begin
      `F_ASSERT("A2_no_step_after_err", !(err && WILL_FIRE_RL_step));
      `F_ASSERT("A9_morph_next_id_bounds", morph_next_id >= 5'd1 && morph_next_id <= 5'd16);
    end
    if (f_chk1) begin
      `F_ASSERT("A1_err_sticky", !f_err_q || err);
      `F_ASSERT("A11_mu_written_by_charging_rules", mu == f_mu_q || f_step_q || f_scan_q);
      `F_ASSERT("A12_halted_cleared_by_start", !f_halted_q || halted || f_start_q);
    end
  end
  genvar f_m;
  generate
    for (f_m = 0; f_m < 16; f_m = f_m + 1) begin : f_morph
      `F_ALWAYS if (f_chk) begin
        `F_ASSERT("A10_morph_valid_below_next", !morph_valid_table[f_m] || f_m < morph_next_id);
      end
    end
  endgenerate
`endif

`ifndef F_SKIP_PT
  `F_ALWAYS begin
    if (f_chk) begin
      `F_ASSERT("A3_pt_next_id_bounds", pt_next_id >= 7'd1 && pt_next_id <= 7'd64);
    end
    if (f_chk1) begin
      `F_ASSERT("A7_partition_trap", !f_part_trap || (pc == f_tv_q && f_pt_same));
      `F_ASSERT("A8_pt_written_by_partition_ops", (f_step_q && f_part_q) || f_pt_same);
    end
  end

  genvar f_i, f_j;
  generate
    for (f_i = 0; f_i < 64; f_i = f_i + 1) begin : f_slot
      `F_ALWAYS if (f_pt_check) begin
        `F_ASSERT("A4_dead_above_next", f_i < pt_next_id || `F_SZ(f_i) == 32'd0);
        `F_ASSERT("A5_in_memory", `F_SZ(f_i) == 32'd0 || `F_EN(f_i) <= 33'd128);
      end
      for (f_j = f_i + 1; f_j < 64; f_j = f_j + 1) begin : f_pair
        `F_ALWAYS if (f_pt_check) begin
          `F_ASSERT("A6_disjoint",
            `F_SZ(f_i) == 32'd0 || `F_SZ(f_j) == 32'd0 ||
            `F_EN(f_i) <= {1'b0, `F_BS(f_j)} || `F_EN(f_j) <= {1'b0, `F_BS(f_i)});
        end
      end
    end
  endgenerate
`endif

  // Cover goals. Each names an event an assertion above is about, so no
  // assertion holds only because its trigger never happens.
  `F_ALWAYS begin
    if (f_chk1) begin
      `F_COVER(0, "C1_pnew_allocates", f_step_q && f_opc_q == 8'h00 && !err && pt_next_id == f_next_q + 7'd1);
      `F_COVER(1, "C2_psplit_allocates_two", f_step_q && f_opc_q == 8'h01 && !err && pt_next_id == f_next_q + 7'd2);
      `F_COVER(2, "C3_pmerge_allocates", f_step_q && f_opc_q == 8'h02 && !err && pt_next_id == f_next_q + 7'd1);
      `F_COVER(3, "C4_partition_overlap_trap", f_part_trap && error_code == 32'hBADF001E);
      `F_COVER(4, "C5_partition_capacity_trap", f_part_trap && error_code == 32'hBADF001D);
      `F_COVER(5, "C6_err_rewritten_while_set", f_err_q && f_erren_q);
      `F_COVER(6, "C7_halted_cleared_by_start", f_halted_q && !halted);
      `F_COVER(7, "C8_morph_allocates", morph_next_id == f_mnext_q + 5'd1);
      `F_COVER(8, "C9_mu_charged", mu != f_mu_q);
      `F_COVER(9, "C10_err_rises", !f_err_q && err);
    end
    if (f_chk) begin
      `F_COVER(10, "C11_partition_table_full", pt_next_id == 7'd64);
      `F_COVER(11, "C12_two_live_slots", `F_SZ(2) != 32'd0 && `F_SZ(3) != 32'd0);
    end
  end
