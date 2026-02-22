// thiele_cpu_kami_tb.v — Testbench for Kami-generated mkModule1
//
// Loads a program into the CPU via loadInstr, then lets it execute.
// After halt, dumps all state as JSON (same format as thiele_cpu_tb.v).
//
// Usage with iverilog:
//   iverilog -g2012 -o tb.vvp thiele_cpu_kami.v thiele_cpu_kami_tb.v
//   vvp tb.vvp +PROGRAM=prog.hex +DATA=data.hex

`timescale 1ns/1ps

module thiele_cpu_kami_tb;

  // Clock and reset
  reg clk = 0;
  reg rst_n = 0;
  always #5 clk = ~clk;

  // loadInstr interface
  reg [39:0] load_data;
  reg load_en;

  // Output ports from mkModule1
  wire [31:0] pc_out, mu_out;
  wire [31:0] partition_ops_out, mdl_ops_out, info_gain_out, error_code_out;
  wire [31:0] mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3;
  wire err_out, halted_out, bianchi_alarm_out;
  wire rdy_load;

  // Instantiate the Kami-generated CPU
  mkModule1 dut (
    .CLK(clk),
    .RST_N(rst_n),

    // Instruction loading
    .loadInstr_x_0(load_data),
    .EN_loadInstr(load_en),
    .RDY_loadInstr(rdy_load),

    // Output methods — always enabled
    .EN_getPC(1'b1),
    .getPC(pc_out),
    .RDY_getPC(),

    .EN_getMu(1'b1),
    .getMu(mu_out),
    .RDY_getMu(),

    .EN_getErr(1'b1),
    .getErr(err_out),
    .RDY_getErr(),

    .EN_getHalted(1'b1),
    .getHalted(halted_out),
    .RDY_getHalted(),

    .EN_getPartitionOps(1'b1),
    .getPartitionOps(partition_ops_out),
    .RDY_getPartitionOps(),

    .EN_getMdlOps(1'b1),
    .getMdlOps(mdl_ops_out),
    .RDY_getMdlOps(),

    .EN_getInfoGain(1'b1),
    .getInfoGain(info_gain_out),
    .RDY_getInfoGain(),

    .EN_getErrorCode(1'b1),
    .getErrorCode(error_code_out),
    .RDY_getErrorCode(),

    .EN_getMuTensor0(1'b1),
    .getMuTensor0(mu_tensor_0),
    .RDY_getMuTensor0(),

    .EN_getMuTensor1(1'b1),
    .getMuTensor1(mu_tensor_1),
    .RDY_getMuTensor1(),

    .EN_getMuTensor2(1'b1),
    .getMuTensor2(mu_tensor_2),
    .RDY_getMuTensor2(),

    .EN_getMuTensor3(1'b1),
    .getMuTensor3(mu_tensor_3),
    .RDY_getMuTensor3(),

    .EN_getBianchiAlarm(1'b1),
    .getBianchiAlarm(bianchi_alarm_out),
    .RDY_getBianchiAlarm()
  );

  // Instruction and data memory arrays for loading
  reg [31:0] instr_memory [0:255];
  reg [31:0] data_memory  [0:255];

  // State
  integer i;
  integer cycle_count;
  integer num_instrs;
  reg [8191:0] mem_init_val;

  // File paths from plusargs
  reg [1023:0] program_hex_path;
  reg [1023:0] data_hex_path;

  // CHSH trial tracing
  wire [31:0] current_instr;
  wire [7:0]  current_opcode;
  assign current_instr = dut.imem[pc_out[7:0] * 32 +: 32];
  assign current_opcode = current_instr[31:24];

  initial begin
    // Initialize memories to zero
    for (i = 0; i < 256; i = i + 1) begin
      instr_memory[i] = 32'h00000000;
      data_memory[i]  = 32'h00000000;
    end

    // Load program and data from hex files
    if ($value$plusargs("PROGRAM=%s", program_hex_path)) begin
      $readmemh(program_hex_path, instr_memory);
    end else begin
      // Default: HALT at address 0
      instr_memory[0] = 32'hFF000000;
    end

    if ($value$plusargs("DATA=%s", data_hex_path)) begin
      $readmemh(data_hex_path, data_memory);
    end

    // Count actual instructions (find last non-zero)
    num_instrs = 256;

    // Phase 1: Reset (2 cycles)
    rst_n = 0;
    load_en = 0;
    load_data = 40'd0;
    @(posedge clk);
    @(posedge clk);

    // Phase 2: Release reset and load instructions via loadInstr
    rst_n = 1;
    for (i = 0; i < 256; i = i + 1) begin
      load_data = {i[7:0], instr_memory[i]};
      load_en = 1;
      @(posedge clk);
    end
    load_en = 0;

    // Phase 3: Force-reset execution state after loading
    // During loading, the CPU was executing garbage from uninitialized imem.
    // imem itself is safe (only written by loadInstr), but pc/mu/regs/mem
    // were corrupted. Reset them to initial values.

    // Build packed data memory init value
    mem_init_val = {8192{1'b0}};
    for (i = 0; i < 256; i = i + 1) begin
      mem_init_val[i*32 +: 32] = data_memory[i];
    end

    @(negedge clk);
    force dut.pc = 32'd0;
    force dut.mu = 32'd0;
    force dut.err = 1'b0;
    force dut.halted = 1'b0;
    force dut.regs = {1024{1'b0}};
    force dut.mem = mem_init_val;
    force dut.partition_ops = 32'd0;
    force dut.mdl_ops = 32'd0;
    force dut.info_gain = 32'd0;
    force dut.error_code = 32'd0;
    force dut.mu_tensor = {512{1'b0}};
    @(posedge clk);
    @(negedge clk);
    release dut.pc;
    release dut.mu;
    release dut.err;
    release dut.halted;
    release dut.regs;
    release dut.mem;
    release dut.partition_ops;
    release dut.mdl_ops;
    release dut.info_gain;
    release dut.error_code;
    release dut.mu_tensor;

    // Phase 4: Let CPU execute and wait for halt
    cycle_count = 0;
    while (!halted_out && !err_out && cycle_count < 10000) begin
      @(posedge clk);
      cycle_count = cycle_count + 1;

      // CHSH trial tracing
      if (current_opcode == 8'h09) begin
        $display("CHSH_TRIAL %0d %0d %0d %0d",
          current_instr[17],   // x setting (op_a bit 1)
          current_instr[16],   // y setting (op_a bit 0)
          current_instr[9],    // a outcome (op_b bit 1)
          current_instr[8]     // b outcome (op_b bit 0)
        );
      end
    end

    // Small delay for outputs to settle
    #1;

    // Phase 5: Dump state as JSON (matching thiele_cpu_tb.v format)
    $display("{");
    $display("  \"status\": %0d,", halted_out ? 32'd2 : (err_out ? 32'd3 : 32'd0));
    $display("  \"error_code\": %0d,", error_code_out);
    $display("  \"partition_ops\": %0d,", partition_ops_out);
    $display("  \"mdl_ops\": %0d,", mdl_ops_out);
    $display("  \"info_gain\": %0d,", info_gain_out);
    $display("  \"mu\": %0d,", mu_out);
    $display("  \"mu_tensor_0\": %0d,", mu_tensor_0);
    $display("  \"mu_tensor_1\": %0d,", mu_tensor_1);
    $display("  \"mu_tensor_2\": %0d,", mu_tensor_2);
    $display("  \"mu_tensor_3\": %0d,", mu_tensor_3);
    $display("  \"bianchi_alarm\": %0d,", bianchi_alarm_out);
    $display("  \"cycles\": %0d,", cycle_count);
    $display("  \"pc\": %0d,", pc_out);
    $display("  \"err\": %0d,", err_out);

    // Dump registers
    $display("  \"regs\": [");
    for (i = 0; i < 32; i = i + 1) begin
      if (i < 31)
        $display("    %0d,", dut.regs[i*32 +: 32]);
      else
        $display("    %0d", dut.regs[i*32 +: 32]);
    end
    $display("  ],");

    // Dump memory
    $display("  \"mem\": [");
    for (i = 0; i < 256; i = i + 1) begin
      if (i < 255)
        $display("    %0d,", dut.mem[i*32 +: 32]);
      else
        $display("    %0d", dut.mem[i*32 +: 32]);
    end
    $display("  ],");

    // Modules (empty — partition table managed externally)
    $display("  \"modules\": [");
    $display("    {\"id\": -1, \"region\": []}");
    $display("  ]");
    $display("}");

    $finish;
  end

endmodule
