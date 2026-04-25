// gls_tb.v — Gate-Level Simulation testbench for Thiele CPU
//
// Functional difference from thiele_cpu_kami_tb.v:
//   Uses ONLY the external module interface (no internal signal access).
//   Works with the flat synthesized netlist (build/gls_flat.v) because
//   all internal signals are flattened away after synthesis.
//
// Supported plusargs (same subset as behavioral testbench):
//   +PROGRAM=<hex_file>   : hex-encoded instruction memory
//   +N_INSTRS=<n>         : number of instructions to load
//   +MAX_CYCLES=<n>       : cycle limit (default 100000)
//
// Output: a single JSON object on stdout (matching thiele_cpu_kami_tb format):
//   { "pc": N, "mu": N, "err": 0/1, "certified": 0/1, "regs": [...] }

`timescale 1ns/1ps

module gls_tb;

  reg clk = 0;
  reg rst_n = 0;
  always #5 clk = ~clk;

  reg [143:0] load_data;
  reg         load_en;

  wire [31:0] pc_out, mu_out;
  wire [31:0] partition_ops_out, mdl_ops_out, info_gain_out, error_code_out;
  wire [31:0] mstatus_out, mcycle_lo_out, mcycle_hi_out, minstret_lo_out, minstret_hi_out;
  wire [31:0] logic_acc_out, cert_addr_out;
  wire [31:0] mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3;
  wire [31:0] pt_next_id_out, pt_size_out;
  wire        err_out, halted_out, bianchi_alarm_out, certified_out;
  wire        rdy_load;
  wire [31:0] wc_same_00_out, wc_diff_00_out, wc_same_01_out, wc_diff_01_out;
  wire [31:0] wc_same_10_out, wc_diff_10_out, wc_same_11_out, wc_diff_11_out;

  mkModule1 dut (
    .CLK(clk), .RST_N(rst_n),
    .loadInstr_x_0(load_data), .EN_loadInstr(load_en), .RDY_loadInstr(rdy_load),
    .EN_getPC(1'b1), .getPC(pc_out), .RDY_getPC(),
    .EN_getMu(1'b1), .getMu(mu_out), .RDY_getMu(),
    .EN_getErr(1'b1), .getErr(err_out), .RDY_getErr(),
    .EN_getHalted(1'b1), .getHalted(halted_out), .RDY_getHalted(),
    .EN_getCertified(1'b1), .getCertified(certified_out), .RDY_getCertified(),
    .EN_getPartitionOps(1'b1), .getPartitionOps(partition_ops_out), .RDY_getPartitionOps(),
    .EN_getMdlOps(1'b1), .getMdlOps(mdl_ops_out), .RDY_getMdlOps(),
    .EN_getInfoGain(1'b1), .getInfoGain(info_gain_out), .RDY_getInfoGain(),
    .EN_getErrorCode(1'b1), .getErrorCode(error_code_out), .RDY_getErrorCode(),
    .EN_getMstatus(1'b1), .getMstatus(mstatus_out), .RDY_getMstatus(),
    .EN_getMcycleLo(1'b1), .getMcycleLo(mcycle_lo_out), .RDY_getMcycleLo(),
    .EN_getMcycleHi(1'b1), .getMcycleHi(mcycle_hi_out), .RDY_getMcycleHi(),
    .EN_getMinstretLo(1'b1), .getMinstretLo(minstret_lo_out), .RDY_getMinstretLo(),
    .EN_getMinstretHi(1'b1), .getMinstretHi(minstret_hi_out), .RDY_getMinstretHi(),
    .EN_getLogicAcc(1'b1), .getLogicAcc(logic_acc_out), .RDY_getLogicAcc(),
    .EN_getCertAddr(1'b1), .getCertAddr(cert_addr_out), .RDY_getCertAddr(),
    .EN_getMuTensor0(1'b1), .getMuTensor0(mu_tensor_0), .RDY_getMuTensor0(),
    .EN_getMuTensor1(1'b1), .getMuTensor1(mu_tensor_1), .RDY_getMuTensor1(),
    .EN_getMuTensor2(1'b1), .getMuTensor2(mu_tensor_2), .RDY_getMuTensor2(),
    .EN_getMuTensor3(1'b1), .getMuTensor3(mu_tensor_3), .RDY_getMuTensor3(),
    .setActiveModule_x_0(6'd0), .EN_setActiveModule(1'b0), .RDY_setActiveModule(),
    .setTrapVector_x_0(32'd0), .EN_setTrapVector(1'b0), .RDY_setTrapVector(),
    .apbReadData_x_0(32'd0), .EN_apbReadData(1'b0), .apbReadData(), .RDY_apbReadData(),
    .apbReadErr_x_0(32'd0), .EN_apbReadErr(1'b0), .apbReadErr(), .RDY_apbReadErr(),
    .apbWrite_x_0(160'h0), .EN_apbWrite(1'b0), .apbWrite(), .RDY_apbWrite(),
    .EN_getBianchiAlarm(1'b1), .getBianchiAlarm(bianchi_alarm_out), .RDY_getBianchiAlarm(),
    .EN_getPtNextId(1'b1), .getPtNextId(pt_next_id_out), .RDY_getPtNextId(),
    .getPtSize_x_0(6'd0), .EN_getPtSize(1'b1), .getPtSize(pt_size_out), .RDY_getPtSize(),
    .EN_getWcSame00(1'b1), .getWcSame00(wc_same_00_out), .RDY_getWcSame00(),
    .EN_getWcDiff00(1'b1), .getWcDiff00(wc_diff_00_out), .RDY_getWcDiff00(),
    .EN_getWcSame01(1'b1), .getWcSame01(wc_same_01_out), .RDY_getWcSame01(),
    .EN_getWcDiff01(1'b1), .getWcDiff01(wc_diff_01_out), .RDY_getWcDiff01(),
    .EN_getWcSame10(1'b1), .getWcSame10(wc_same_10_out), .RDY_getWcSame10(),
    .EN_getWcDiff10(1'b1), .getWcDiff10(wc_diff_10_out), .RDY_getWcDiff10(),
    .EN_getWcSame11(1'b1), .getWcSame11(wc_same_11_out), .RDY_getWcSame11(),
    .EN_getWcDiff11(1'b1), .getWcDiff11(wc_diff_11_out), .RDY_getWcDiff11()
  );

  // Instruction storage (128-bit words, up to 64k entries)
  reg [127:0] instr_memory [0:65535];

  reg [1023:0] program_hex_path;
  integer      num_instrs;
  integer      max_cycles;
  integer      cycle_count;
  integer      i;

  initial begin
    // ----- reset -----
    rst_n = 0;
    load_en = 0;
    load_data = 144'd0;
    #20;
    rst_n = 1;
    #10;

    // ----- read program -----
    if ($value$plusargs("PROGRAM=%s", program_hex_path)) begin
      $readmemh(program_hex_path, instr_memory);
    end
    if (!$value$plusargs("N_INSTRS=%d", num_instrs))
      num_instrs = 64;
    if (!$value$plusargs("MAX_CYCLES=%d", max_cycles))
      max_cycles = 100000;

    // ----- load instructions via loadInstr port -----
    // Protocol: assert load_en while RDY_loadInstr is high.
    // loadInstr_x_0 is 144-bit: {addr[15:0], data[127:0]}
    for (i = 0; i < num_instrs; i = i + 1) begin
      @(posedge clk);
      while (!rdy_load) @(posedge clk);
      load_data = {16'(i), instr_memory[i]};
      load_en = 1;
      @(posedge clk);
      load_en = 0;
    end

    // ----- wait for halt -----
    @(posedge clk);
    cycle_count = 0;
    while (!halted_out && !err_out && cycle_count < max_cycles) begin
      @(posedge clk);
      cycle_count = cycle_count + 1;
    end

    // ----- emit JSON result -----
    // No internal register readout in GLS mode: report the observable state.
    $display("{");
    $display("  \"pc\": %0d,", pc_out);
    $display("  \"mu\": %0d,", mu_out);
    $display("  \"err\": %0d,", err_out);
    $display("  \"certified\": %0d,", certified_out);
    $display("  \"cycles\": %0d,", cycle_count);
    $display("  \"cert_addr\": %0d,", cert_addr_out);
    $display("  \"info_gain\": %0d,", info_gain_out);
    $display("  \"partition_ops\": %0d,", partition_ops_out);
    $display("  \"mu_tensor\": [%0d, %0d, %0d, %0d],",
             mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3);
    $display("  \"witness\": [%0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d],",
             wc_same_00_out, wc_diff_00_out, wc_same_01_out, wc_diff_01_out,
             wc_same_10_out, wc_diff_10_out, wc_same_11_out, wc_diff_11_out);
    $display("  \"halted\": %0d", halted_out);
    $display("}");

    $finish;
  end

endmodule
