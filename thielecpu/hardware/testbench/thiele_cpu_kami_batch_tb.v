// thiele_cpu_kami_batch_tb.v — Run multiple programs per vvp invocation.
//
// Usage:
//   vvp compiled_batch.vvp +MANIFEST=/path/to/manifest.txt
//
// Manifest format (one line per program, space-separated):
//   <n_instrs> <prog.hex> <data.hex>
//
// n_instrs: number of instruction slots to load (all others stay 0 = PNEW-nop).
//           Programs MUST end with HALT as their last instruction so the CPU
//           halts before reaching any zero-filled slots.
//
// Output: one JSON block per program (same schema as thiele_cpu_kami_tb.v),
//         plus a "batch_index" field added to each block.

`timescale 1ns/1ps

module thiele_cpu_kami_batch_tb;

  // ── Clock / reset ────────────────────────────────────────────

  reg clk = 0;
  reg rst_n = 0;
  always #5 clk = ~clk;

  // ── loadInstr interface ──────────────────────────────────────

  reg [39:0] load_data;
  reg        load_en;

  // ── DUT outputs ─────────────────────────────────────────────

  wire [31:0] pc_out, mu_out;
  wire [31:0] partition_ops_out, mdl_ops_out, info_gain_out, error_code_out;
  wire [31:0] mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3;
  wire        err_out, halted_out, bianchi_alarm_out;
  wire        rdy_load;

  mkModule1 dut (
    .CLK   (clk),
    .RST_N (rst_n),

    .loadInstr_x_0(load_data),
    .EN_loadInstr (load_en),
    .RDY_loadInstr(rdy_load),

    .EN_getPC(1'b1), .getPC(pc_out), .RDY_getPC(),
    .EN_getMu(1'b1), .getMu(mu_out), .RDY_getMu(),
    .EN_getErr(1'b1), .getErr(err_out), .RDY_getErr(),
    .EN_getHalted(1'b1), .getHalted(halted_out), .RDY_getHalted(),
    .EN_getPartitionOps(1'b1), .getPartitionOps(partition_ops_out), .RDY_getPartitionOps(),
    .EN_getMdlOps(1'b1), .getMdlOps(mdl_ops_out), .RDY_getMdlOps(),
    .EN_getInfoGain(1'b1), .getInfoGain(info_gain_out), .RDY_getInfoGain(),
    .EN_getErrorCode(1'b1), .getErrorCode(error_code_out), .RDY_getErrorCode(),
    .EN_getMuTensor0(1'b1), .getMuTensor0(mu_tensor_0), .RDY_getMuTensor0(),
    .EN_getMuTensor1(1'b1), .getMuTensor1(mu_tensor_1), .RDY_getMuTensor1(),
    .EN_getMuTensor2(1'b1), .getMuTensor2(mu_tensor_2), .RDY_getMuTensor2(),
    .EN_getMuTensor3(1'b1), .getMuTensor3(mu_tensor_3), .RDY_getMuTensor3(),
    .EN_getBianchiAlarm(1'b1), .getBianchiAlarm(bianchi_alarm_out), .RDY_getBianchiAlarm()
  );

  // ── Working memories ─────────────────────────────────────────

  reg [31:0] instr_memory [0:255];
  reg [31:0] data_memory  [0:255];
  reg [8191:0] mem_init_val;

  integer i;
  integer cycle_count;

  // ── String buffers (2048 bits = 256 bytes each — enough for any temp path) ──

  reg [2047:0] manifest_path;
  reg [2047:0] prog_path;
  reg [2047:0] data_path;

  integer manifest_fd;
  integer n_instrs;
  integer scan_result;
  integer batch_index;

  // ── CHSH tracing wires ───────────────────────────────────────

  wire [31:0] current_instr;
  wire [7:0]  current_opcode;
  assign current_instr  = dut.imem[pc_out[7:0] * 32 +: 32];
  assign current_opcode = current_instr[31:24];

  // ── Task: reset CPU and load one program ─────────────────────

  task load_and_reset;
    input integer n;          // number of slots to load
    input [2047:0] p_path;    // prog hex path
    input [2047:0] d_path;    // data hex path (may be ignored if empty)
    integer j;
    begin
      // Initialize working memory arrays to zero
      for (j = 0; j < 256; j = j + 1) begin
        instr_memory[j] = 32'h00000000;
        data_memory[j]  = 32'h00000000;
      end

      $readmemh(p_path, instr_memory);
      $readmemh(d_path, data_memory);

      // Reset the CPU
      rst_n   = 0;
      load_en = 0;
      load_data = 40'd0;
      @(posedge clk);
      @(posedge clk);

      // Load only n instruction slots
      rst_n = 1;
      for (j = 0; j < n; j = j + 1) begin
        load_data = {j[7:0], instr_memory[j]};
        load_en   = 1;
        @(posedge clk);
      end
      load_en = 0;

      // Force-reset execution state (pc/mu/regs/mem/counters/tensor)
      mem_init_val = {8192{1'b0}};
      for (j = 0; j < 256; j = j + 1)
        mem_init_val[j*32 +: 32] = data_memory[j];

      @(negedge clk);
      force dut.pc            = 32'd0;
      force dut.mu            = 32'd0;
      force dut.err           = 1'b0;
      force dut.halted        = 1'b0;
      force dut.regs          = {1024{1'b0}};
      force dut.mem           = mem_init_val;
      force dut.partition_ops = 32'd0;
      force dut.mdl_ops       = 32'd0;
      force dut.info_gain     = 32'd0;
      force dut.error_code    = 32'd0;
      force dut.mu_tensor     = {512{1'b0}};
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
    end
  endtask

  // ── Task: execute until halt and dump JSON ───────────────────

  task run_and_dump;
    input integer bidx;
    integer j;
    begin
      cycle_count = 0;
      while (!halted_out && !err_out && cycle_count < 10000) begin
        @(posedge clk);
        cycle_count = cycle_count + 1;
        if (current_opcode == 8'h09) begin
          $display("CHSH_TRIAL %0d %0d %0d %0d",
            current_instr[17], current_instr[16],
            current_instr[9],  current_instr[8]);
        end
      end

      #1;

      $display("{");
      $display("  \"batch_index\": %0d,", bidx);
      $display("  \"status\": %0d,",
        halted_out ? 32'd2 : (err_out ? 32'd3 : 32'd0));
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

      $display("  \"regs\": [");
      for (j = 0; j < 32; j = j + 1) begin
        if (j < 31)
          $display("    %0d,", dut.regs[j*32 +: 32]);
        else
          $display("    %0d", dut.regs[j*32 +: 32]);
      end
      $display("  ],");

      $display("  \"mem\": [");
      for (j = 0; j < 256; j = j + 1) begin
        if (j < 255)
          $display("    %0d,", dut.mem[j*32 +: 32]);
        else
          $display("    %0d", dut.mem[j*32 +: 32]);
      end
      $display("  ],");

      $display("  \"modules\": []");
      $display("}");
    end
  endtask

  // ── Main ─────────────────────────────────────────────────────

  initial begin
    if (!$value$plusargs("MANIFEST=%s", manifest_path)) begin
      $display("ERROR: +MANIFEST=<path> required");
      $finish;
    end

    manifest_fd = $fopen(manifest_path, "r");
    if (manifest_fd == 0) begin
      $display("ERROR: cannot open manifest: %0s", manifest_path);
      $finish;
    end

    load_en   = 0;
    load_data = 40'd0;
    batch_index = 0;

    // Read entries: n_instrs prog.hex data.hex
    while ($fscanf(manifest_fd, " %d %s %s", n_instrs, prog_path, data_path) == 3) begin
      load_and_reset(n_instrs, prog_path, data_path);
      run_and_dump(batch_index);
      batch_index = batch_index + 1;
    end

    $fclose(manifest_fd);
    $finish;
  end

endmodule
