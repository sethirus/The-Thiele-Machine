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

  // Shadow partition tracker: max distinct module IDs tracked in testbench
  parameter NUM_SHADOW_MODS = 64;

  // Clock and reset
  reg clk = 0;
  reg rst_n = 0;
  always #5 clk = ~clk;

  // loadInstr interface
  reg [39:0] load_data;
  reg load_en;

  // Logic coprocessor response drive (optional external Z3 bridge)
  reg [33:0] logic_resp_in;
  reg logic_resp_en;
  wire logic_req_valid_out;
  wire [7:0] logic_req_opcode_out;
  wire [31:0] logic_req_payload_out;

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

    .EN_getLogicReqValid(1'b1),
    .getLogicReqValid(logic_req_valid_out),
    .RDY_getLogicReqValid(),

    .EN_getLogicReqOpcode(1'b1),
    .getLogicReqOpcode(logic_req_opcode_out),
    .RDY_getLogicReqOpcode(),

    .EN_getLogicReqPayload(1'b1),
    .getLogicReqPayload(logic_req_payload_out),
    .RDY_getLogicReqPayload(),

    .setLogicResp_x_0(logic_resp_in),
    .EN_setLogicResp(logic_resp_en),
    .RDY_setLogicResp(),

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

  // Shadow partition tracker: maps module_id -> 64-bit element bitmask.
  // Maintained by the testbench monitor; mirrors Python VM and Coq extracted runner.
  reg [63:0]   shadow_masks [0:NUM_SHADOW_MODS-1];
  reg [7:0]    shadow_next_mid;   // next free module ID (1-based; 0 reserved)
  reg          shadow_executing;  // gate: set after force/release, cleared post-halt
  reg [31:0]   exec_word;         // instruction captured before each posedge
  integer      exec_op_i, exec_a_i, exec_b_i;   // decoded fields
  integer      sh_e, sh_m;                        // loop counters
  integer      sh_pred_mode_i, sh_pred_param_i;  // PSPLIT predicate decode
  reg [63:0]   sh_left, sh_right;                // PSPLIT left/right masks
  integer      shadow_found_dup;                  // PNEW dedup flag
  reg [63:0]   shadow_new_mask;                  // PNEW singleton mask
  integer      mod_j, bit_b, first_mod, first_bit; // JSON dump loop vars

  // Optional external logic bridge controls
  integer      logic_bridge_enable;
  integer      logic_bridge_error;
  integer      logic_bridge_value;
  integer      logic_bridge_rc;
  integer      logic_bridge_req_fd;
  integer      logic_bridge_rsp_fd;
  reg [1023:0] logic_bridge_req_path;
  reg [1023:0] logic_bridge_rsp_path;
  reg [2047:0] logic_bridge_cmd;
  reg          logic_prev_req_valid;

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

    // Initialize shadow partition tracker
    for (i = 0; i < NUM_SHADOW_MODS; i = i + 1)
      shadow_masks[i] = 64'd0;
    shadow_next_mid  = 8'd1;
    shadow_executing = 1'b0;
    exec_word        = 32'd0;
    shadow_found_dup = 0;

    logic_resp_in = 34'd0;
    logic_resp_en = 1'b0;
    logic_prev_req_valid = 1'b0;
    logic_bridge_enable = 0;
    logic_bridge_req_path = "build/logic_bridge_req.txt";
    logic_bridge_rsp_path = "build/logic_bridge_rsp.txt";
    if ($value$plusargs("LOGIC_Z3_BRIDGE=%d", logic_bridge_enable)) begin end
    if ($value$plusargs("LOGIC_REQ_FILE=%s", logic_bridge_req_path)) begin end
    if ($value$plusargs("LOGIC_RSP_FILE=%s", logic_bridge_rsp_path)) begin end

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

    // +N_INSTRS=N: only load N slots instead of all 256 (huge speedup for short programs).
    // The Nth slot itself should be HALT (programs always end with HALT), so slots N..255
    // retain their reset-default of 0 (PNEW 0 0 0 with 0 cost) but are never reached.
    // Default: 256 (full load, backward-compatible).
    if (!$value$plusargs("N_INSTRS=%d", num_instrs))
      num_instrs = 256;

    // Phase 1: Reset (2 cycles)
    rst_n = 0;
    load_en = 0;
    load_data = 40'd0;
    @(posedge clk);
    @(posedge clk);

    // Phase 2: Release reset and load instructions via loadInstr (only num_instrs slots)
    rst_n = 1;
    for (i = 0; i < num_instrs; i = i + 1) begin
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
    force dut.logic_acc = 32'd0;
    force dut.logic_req_valid = 1'b0;
    force dut.logic_req_opcode = 8'd0;
    force dut.logic_req_payload = 32'd0;
    force dut.logic_resp_valid = 1'b0;
    force dut.logic_resp_error = 1'b0;
    force dut.logic_resp_value = 32'd0;
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
    release dut.logic_acc;
    release dut.logic_req_valid;
    release dut.logic_req_opcode;
    release dut.logic_req_payload;
    release dut.logic_resp_valid;
    release dut.logic_resp_error;
    release dut.logic_resp_value;

    // Phase 4: Let CPU execute and wait for halt
    shadow_executing = 1'b1;
    cycle_count = 0;
    while (!halted_out && !err_out && cycle_count < 10000) begin
      // Capture instruction executing THIS cycle (before posedge advances pc)
      exec_word = dut.imem[pc_out[7:0] * 32 +: 32];

      // Logic bridge handshake: consume in-core request/response wires.
      // The bridge check is deterministic and synth-independent for cosim.
      logic_resp_en = 1'b0;
      logic_resp_in = 34'd0;
      if (logic_bridge_enable != 0 && logic_req_valid_out && !logic_prev_req_valid) begin
        logic_bridge_error = 0;
        logic_bridge_value = logic_req_payload_out;
        case (logic_req_opcode_out)
          8'h03: begin  // LASSERT: sat iff op_a >= op_b
            if (logic_req_payload_out[15:8] < logic_req_payload_out[7:0]) begin
              logic_bridge_error = 1;
              logic_bridge_value = 0;
            end
          end
          8'h04: begin  // LJOIN: sat iff both terms are non-zero
            if (logic_req_payload_out[15:8] == 0 || logic_req_payload_out[7:0] == 0) begin
              logic_bridge_error = 1;
              logic_bridge_value = 0;
            end
          end
          default: begin
            logic_bridge_error = 1;
            logic_bridge_value = 0;
          end
        endcase
        logic_resp_in = {1'b1, logic_bridge_error[0], logic_bridge_value[31:0]};
        logic_resp_en = 1'b1;
      end
      logic_prev_req_valid = logic_req_valid_out;

      @(posedge clk);

      cycle_count = cycle_count + 1;

      // Shadow partition tracker: decode and apply instruction that just executed
      exec_op_i = exec_word[31:24];
      exec_a_i  = exec_word[23:16];
      exec_b_i  = exec_word[15:8];
      case (exec_op_i)
        8'h00: begin  // PNEW: allocate singleton module for element exec_a_i
          shadow_new_mask  = (64'h1 << (exec_a_i & 8'h3F));
          shadow_found_dup = 0;
          for (sh_m = 1; sh_m < shadow_next_mid; sh_m = sh_m + 1)
            if (shadow_masks[sh_m] == shadow_new_mask) shadow_found_dup = 1;
          if (!shadow_found_dup && shadow_next_mid < NUM_SHADOW_MODS) begin
            shadow_masks[shadow_next_mid] = shadow_new_mask;
            shadow_next_mid = shadow_next_mid + 1;
          end
        end
        8'h02: begin  // PMERGE: merge modules exec_a_i and exec_b_i into new module
          if (exec_a_i < shadow_next_mid && exec_b_i < shadow_next_mid &&
              shadow_next_mid < NUM_SHADOW_MODS) begin
            shadow_masks[shadow_next_mid] = shadow_masks[exec_a_i] | shadow_masks[exec_b_i];
            shadow_masks[exec_a_i]        = 64'd0;
            shadow_masks[exec_b_i]        = 64'd0;
            shadow_next_mid               = shadow_next_mid + 1;
          end
        end
        8'h01: begin  // PSPLIT: split module exec_a_i with predicate byte exec_b_i
          if (exec_a_i < shadow_next_mid && (shadow_next_mid + 1) < NUM_SHADOW_MODS) begin
            sh_pred_mode_i  = (exec_b_i >> 6) & 3;
            sh_pred_param_i = exec_b_i & 8'h3F;
            sh_left  = 64'd0;
            sh_right = 64'd0;
            for (sh_e = 0; sh_e < 64; sh_e = sh_e + 1) begin
              if ((shadow_masks[exec_a_i] >> sh_e) & 64'h1) begin
                case (sh_pred_mode_i)
                  0: begin  // even/odd: (sh_e & 1) == (sh_pred_param_i & 1)
                    if ((sh_e & 1) == (sh_pred_param_i & 1))
                      sh_left  = sh_left  | (64'h1 << sh_e);
                    else
                      sh_right = sh_right | (64'h1 << sh_e);
                  end
                  1: begin  // threshold: sh_e >= sh_pred_param_i
                    if (sh_e >= sh_pred_param_i)
                      sh_left  = sh_left  | (64'h1 << sh_e);
                    else
                      sh_right = sh_right | (64'h1 << sh_e);
                  end
                  2: begin  // bitwise: bit sh_pred_param_i of element index sh_e
                    if (((sh_e >> sh_pred_param_i) & 1) != 0)
                      sh_left  = sh_left  | (64'h1 << sh_e);
                    else
                      sh_right = sh_right | (64'h1 << sh_e);
                  end
                  default: begin  // mode 11: route all to right (divisor, rarely tested)
                    sh_right = sh_right | (64'h1 << sh_e);
                  end
                endcase
              end
            end
            shadow_masks[shadow_next_mid]     = sh_left;
            shadow_masks[shadow_next_mid + 1] = sh_right;
            shadow_masks[exec_a_i]            = 64'd0;
            shadow_next_mid                   = shadow_next_mid + 2;
          end
        end
        // 8'hFF HALT and all other opcodes: no module-table change
      endcase

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

    // Modules — emit live (non-empty) modules from shadow partition tracker.
    // Each entry: {"id": N, "region": [list of element indices]}.
    $write("  \"modules\": [");
    first_mod = 1;
    for (mod_j = 1; mod_j < shadow_next_mid; mod_j = mod_j + 1) begin
      if (shadow_masks[mod_j] != 64'd0) begin
        if (!first_mod) $write(", ");
        $write("{\"id\": %0d, \"region\": [", mod_j);
        first_bit = 1;
        for (bit_b = 0; bit_b < 64; bit_b = bit_b + 1) begin
          if ((shadow_masks[mod_j] >> bit_b) & 64'h1) begin
            if (!first_bit) $write(", ");
            $write("%0d", bit_b);
            first_bit = 0;
          end
        end
        $write("]}");
        first_mod = 0;
      end
    end
    $display("]");
    $display("}");

    $finish;
  end

endmodule
