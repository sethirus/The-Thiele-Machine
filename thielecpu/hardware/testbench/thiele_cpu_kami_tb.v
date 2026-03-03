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
  reg [33:0] logic_resp_in /* verilator public */;
  reg logic_resp_en /* verilator public */;
  wire logic_req_valid_out /* verilator public */;
  wire [7:0] logic_req_opcode_out /* verilator public */;
  wire [31:0] logic_req_payload_out /* verilator public */;

  // Output ports from mkModule1
  wire [31:0] pc_out, mu_out;
  wire [31:0] partition_ops_out, mdl_ops_out, info_gain_out, error_code_out;
  wire [31:0] mstatus_out, mcycle_lo_out, mcycle_hi_out, minstret_lo_out, minstret_hi_out, logic_acc_out;
  wire [31:0] mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3;
  wire [7:0] pt_next_id_out;
  wire [31:0] pt_size_out;
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

    .EN_getMstatus(1'b1),
    .getMstatus(mstatus_out),
    .RDY_getMstatus(),

    .EN_getMcycleLo(1'b1),
    .getMcycleLo(mcycle_lo_out),
    .RDY_getMcycleLo(),

    .EN_getMcycleHi(1'b1),
    .getMcycleHi(mcycle_hi_out),
    .RDY_getMcycleHi(),

    .EN_getMinstretLo(1'b1),
    .getMinstretLo(minstret_lo_out),
    .RDY_getMinstretLo(),

    .EN_getMinstretHi(1'b1),
    .getMinstretHi(minstret_hi_out),
    .RDY_getMinstretHi(),

    .EN_getLogicAcc(1'b1),
    .getLogicAcc(logic_acc_out),
    .RDY_getLogicAcc(),

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

    .setActiveModule_x_0(8'd0),
    .EN_setActiveModule(1'b0),
    .RDY_setActiveModule(),

    .setTrapVector_x_0(32'd0),
    .EN_setTrapVector(1'b0),
    .RDY_setTrapVector(),

    .EN_getBianchiAlarm(1'b1),
    .getBianchiAlarm(bianchi_alarm_out),
    .RDY_getBianchiAlarm(),

    .EN_getPtNextId(1'b1),
    .getPtNextId(pt_next_id_out),
    .RDY_getPtNextId(),

    .getPtSize_x_0(8'd0),
    .EN_getPtSize(1'b1),
    .getPtSize(pt_size_out),
    .RDY_getPtSize(),

    // APB write port — unused in simulation; must be tied low so that
    // WILL_FIRE_RL_step = !halted && !err && !EN_apbWrite asserts correctly.
    // Without this, iverilog leaves EN_apbWrite floating (Z→X) and the
    // entire step rule becomes permanently disabled.
    .apbWrite_x_0(64'h0),
    .EN_apbWrite(1'b0),
    .RDY_apbWrite()
  );

  // Instruction and data memory arrays for loading
  reg [31:0] instr_memory [0:255];
  reg [31:0] data_memory  [0:255];

  // State
  integer i;
  integer cycle_count;
  integer num_instrs;
  integer init_mu_en, init_mu_value;
  integer init_active_module_en, init_active_module_value;
  integer init_pt_en, init_pt_idx, init_pt_value;
  integer init_tensor_en, init_tensor_idx, init_tensor_value;
  integer init_logic_stall_en, init_logic_stall_value;
  integer init_logic_req_valid_en, init_logic_req_valid_value;
  integer init_logic_acc_en, init_logic_acc_value;

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
  integer      logic_bridge_external;

  // File paths from plusargs
  reg [1023:0] program_hex_path;
  reg [1023:0] data_hex_path;

  // Physical assertion monitor state
  reg [31:0] prev_mu;
  reg        prev_mu_valid;

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
    prev_mu = 32'd0;
    prev_mu_valid = 1'b0;
    logic_bridge_enable = 0;
    logic_bridge_external = 0;
    logic_bridge_req_path = "build/logic_bridge_req.txt";
    logic_bridge_rsp_path = "build/logic_bridge_rsp.txt";
    if ($value$plusargs("LOGIC_Z3_BRIDGE=%d", logic_bridge_enable)) begin end
    if ($value$plusargs("LOGIC_BRIDGE_EXTERNAL=%d", logic_bridge_external)) begin end
    if ($value$plusargs("LOGIC_REQ_FILE=%s", logic_bridge_req_path)) begin end
    if ($value$plusargs("LOGIC_RSP_FILE=%s", logic_bridge_rsp_path)) begin end

    init_mu_en = 0;
    init_active_module_en = 0;
    init_pt_en = 0;
    init_tensor_en = 0;
    init_logic_stall_en = 0;
    init_logic_req_valid_en = 0;
    init_logic_acc_en = 0;
    if ($value$plusargs("INIT_MU=%d", init_mu_value)) init_mu_en = 1;
    if ($value$plusargs("INIT_ACTIVE_MODULE=%d", init_active_module_value)) init_active_module_en = 1;
    if ($value$plusargs("INIT_PT_IDX=%d", init_pt_idx)) init_pt_en = 1;
    if ($value$plusargs("INIT_PT_VAL=%d", init_pt_value)) init_pt_en = init_pt_en & 1;
    if ($value$plusargs("INIT_TENSOR_IDX=%d", init_tensor_idx)) init_tensor_en = 1;
    if ($value$plusargs("INIT_TENSOR_VAL=%d", init_tensor_value)) init_tensor_en = init_tensor_en & 1;
    if ($value$plusargs("INIT_LOGIC_STALL=%d", init_logic_stall_value)) init_logic_stall_en = 1;
    if ($value$plusargs("INIT_LOGIC_REQ_VALID=%d", init_logic_req_valid_value)) init_logic_req_valid_en = 1;
    if ($value$plusargs("INIT_LOGIC_ACC=%d", init_logic_acc_value)) init_logic_acc_en = 1;

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

    @(negedge clk);
    force dut.pc = 32'd0;
    force dut.mu = 32'd0;
    force dut.err = 1'b0;
    force dut.halted = 1'b0;
    force dut.reg0 = 32'd0;
    force dut.reg1 = 32'd0;
    force dut.reg2 = 32'd0;
    force dut.reg3 = 32'd0;
    force dut.reg4 = 32'd0;
    force dut.reg5 = 32'd0;
    force dut.reg6 = 32'd0;
    force dut.reg7 = 32'd0;
    force dut.reg8 = 32'd0;
    force dut.reg9 = 32'd0;
    force dut.reg10 = 32'd0;
    force dut.reg11 = 32'd0;
    force dut.reg12 = 32'd0;
    force dut.reg13 = 32'd0;
    force dut.reg14 = 32'd0;
    force dut.reg15 = 32'd0;
    force dut.reg16 = 32'd0;
    force dut.reg17 = 32'd0;
    force dut.reg18 = 32'd0;
    force dut.reg19 = 32'd0;
    force dut.reg20 = 32'd0;
    force dut.reg21 = 32'd0;
    force dut.reg22 = 32'd0;
    force dut.reg23 = 32'd0;
    force dut.reg24 = 32'd0;
    force dut.reg25 = 32'd0;
    force dut.reg26 = 32'd0;
    force dut.reg27 = 32'd0;
    force dut.reg28 = 32'd0;
    force dut.reg29 = 32'd0;
    force dut.reg30 = 32'd0;
    force dut.reg31 = 32'd0;
    for (i = 0; i < 256; i = i + 1) begin
      force_mem_word(i, data_memory[i]);
    end
    force dut.partition_ops = 32'd0;
    force dut.mdl_ops = 32'd0;
    force dut.info_gain = 32'd0;
    force dut.error_code = 32'd0;
    force dut.pt_next_id = 32'd1;
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
    release dut.reg0;
    release dut.reg1;
    release dut.reg2;
    release dut.reg3;
    release dut.reg4;
    release dut.reg5;
    release dut.reg6;
    release dut.reg7;
    release dut.reg8;
    release dut.reg9;
    release dut.reg10;
    release dut.reg11;
    release dut.reg12;
    release dut.reg13;
    release dut.reg14;
    release dut.reg15;
    release dut.reg16;
    release dut.reg17;
    release dut.reg18;
    release dut.reg19;
    release dut.reg20;
    release dut.reg21;
    release dut.reg22;
    release dut.reg23;
    release dut.reg24;
    release dut.reg25;
    release dut.reg26;
    release dut.reg27;
    release dut.reg28;
    release dut.reg29;
    release dut.reg30;
    release dut.reg31;
    for (i = 0; i < 256; i = i + 1) begin
      release_mem_word(i);
    end
    release dut.partition_ops;
    release dut.mdl_ops;
    release dut.info_gain;
    release dut.error_code;
    release dut.pt_next_id;
    release dut.mu_tensor;
    release dut.logic_acc;
    release dut.logic_req_valid;
    release dut.logic_req_opcode;
    release dut.logic_req_payload;
    release dut.logic_resp_valid;
    release dut.logic_resp_error;
    release dut.logic_resp_value;

    // Optional post-reset state overrides (force for one cycle to ensure latch).
    if (init_mu_en != 0) force dut.mu = init_mu_value[31:0];
    if (init_active_module_en != 0) force dut.active_module = init_active_module_value[5:0];
    if (init_pt_en != 0) force_pt_word(init_pt_idx, init_pt_value[31:0]);
    if (init_tensor_en != 0) force_tensor_word(init_tensor_idx, init_tensor_value[31:0]);
    if (init_logic_stall_en != 0) force dut.logic_stall = init_logic_stall_value[0];
    if (init_logic_req_valid_en != 0) force dut.logic_req_valid = init_logic_req_valid_value[0];
    if (init_logic_acc_en != 0) force dut.logic_acc = init_logic_acc_value[31:0];
    if (init_mu_en != 0 || init_active_module_en != 0 || init_pt_en != 0 || init_tensor_en != 0 || init_logic_stall_en != 0 || init_logic_req_valid_en != 0 || init_logic_acc_en != 0) begin
      @(posedge clk);
      @(negedge clk);
    end
    if (init_mu_en != 0) release dut.mu;
    if (init_active_module_en != 0) release dut.active_module;
    if (init_pt_en != 0) release_pt_word(init_pt_idx);
    if (init_tensor_en != 0) release_tensor_word(init_tensor_idx);
    if (init_logic_stall_en != 0) release dut.logic_stall;
    if (init_logic_req_valid_en != 0) release dut.logic_req_valid;
    if (init_logic_acc_en != 0) release dut.logic_acc;

    // Phase 4: Let CPU execute and wait for halt
    shadow_executing = 1'b1;
    cycle_count = 0;
    while (!halted_out && !err_out && cycle_count < 10000) begin
      // Capture instruction executing THIS cycle (before posedge advances pc)
      exec_word = dut.imem[pc_out[7:0] * 32 +: 32];

      // Logic bridge handshake: consume in-core request/response wires.
      // The bridge check is deterministic and synth-independent for cosim.
      if (logic_bridge_external == 0) begin
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
      end

      @(posedge clk);

      cycle_count = cycle_count + 1;

      // Shadow partition tracker: decode and apply instruction that just executed
      exec_op_i = exec_word[31:24];
      exec_a_i  = exec_word[23:16];
      exec_b_i  = exec_word[15:8];

      // Runtime NoFreeInsight policy: cert-setting instructions must pay cost > 0.
      if ((exec_op_i == 8'h03 || exec_op_i == 8'h04 || exec_op_i == 8'h0E || exec_op_i == 8'h0F)
          && (exec_word[7:0] == 8'h00)) begin
        $display("[NOFI] policy violation at cycle %0d pc=%0d opcode=0x%0h cost=0", cycle_count, pc_out, exec_op_i);
        $fatal(1, "NoFreeInsight runtime policy violated: cert-setting opcode with zero cost");
      end

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
    $display("  \"logic_stall\": %0d,", dut.logic_stall);
    $display("  \"logic_req_valid\": %0d,", logic_req_valid_out);
    $display("  \"pt0_size\": %0d,", pt_size_out);
    $display("  \"pt_next_id\": %0d,", pt_next_id_out);

    // Dump registers
    $display("  \"regs\": [");
    $display("    %0d,", dut.reg0);
    $display("    %0d,", dut.reg1);
    $display("    %0d,", dut.reg2);
    $display("    %0d,", dut.reg3);
    $display("    %0d,", dut.reg4);
    $display("    %0d,", dut.reg5);
    $display("    %0d,", dut.reg6);
    $display("    %0d,", dut.reg7);
    $display("    %0d,", dut.reg8);
    $display("    %0d,", dut.reg9);
    $display("    %0d,", dut.reg10);
    $display("    %0d,", dut.reg11);
    $display("    %0d,", dut.reg12);
    $display("    %0d,", dut.reg13);
    $display("    %0d,", dut.reg14);
    $display("    %0d,", dut.reg15);
    $display("    %0d,", dut.reg16);
    $display("    %0d,", dut.reg17);
    $display("    %0d,", dut.reg18);
    $display("    %0d,", dut.reg19);
    $display("    %0d,", dut.reg20);
    $display("    %0d,", dut.reg21);
    $display("    %0d,", dut.reg22);
    $display("    %0d,", dut.reg23);
    $display("    %0d,", dut.reg24);
    $display("    %0d,", dut.reg25);
    $display("    %0d,", dut.reg26);
    $display("    %0d,", dut.reg27);
    $display("    %0d,", dut.reg28);
    $display("    %0d,", dut.reg29);
    $display("    %0d,", dut.reg30);
    $display("    %0d", dut.reg31);
    $display("  ],");

    // Dump memory
    $display("  \"mem\": [");
    for (i = 0; i < 256; i = i + 1) begin
      if (i < 255)
        $display("    %0d,", read_mem_word(i));
      else
        $display("    %0d", read_mem_word(i));
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

  task force_pt_word(input integer idx, input [31:0] val);
    reg [511:0] pt_tmp;
    begin
      pt_tmp = dut.ptTable;
      case (idx)
        0: pt_tmp[31:0] = val;
        1: pt_tmp[63:32] = val;
        2: pt_tmp[95:64] = val;
        3: pt_tmp[127:96] = val;
        4: pt_tmp[159:128] = val;
        5: pt_tmp[191:160] = val;
        6: pt_tmp[223:192] = val;
        7: pt_tmp[255:224] = val;
        8: pt_tmp[287:256] = val;
        9: pt_tmp[319:288] = val;
        10: pt_tmp[351:320] = val;
        11: pt_tmp[383:352] = val;
        12: pt_tmp[415:384] = val;
        13: pt_tmp[447:416] = val;
        14: pt_tmp[479:448] = val;
        15: pt_tmp[511:480] = val;
        default: ;
      endcase
      force dut.ptTable = pt_tmp;
    end
  endtask

  task release_pt_word(input integer idx);
    begin
      release dut.ptTable;
    end
  endtask

  task force_tensor_word(input integer idx, input [31:0] val);
    reg [511:0] tensor_tmp;
    begin
      tensor_tmp = dut.mu_tensor;
      case (idx)
        0: tensor_tmp[31:0] = val;
        1: tensor_tmp[63:32] = val;
        2: tensor_tmp[95:64] = val;
        3: tensor_tmp[127:96] = val;
        4: tensor_tmp[159:128] = val;
        5: tensor_tmp[191:160] = val;
        6: tensor_tmp[223:192] = val;
        7: tensor_tmp[255:224] = val;
        8: tensor_tmp[287:256] = val;
        9: tensor_tmp[319:288] = val;
        10: tensor_tmp[351:320] = val;
        11: tensor_tmp[383:352] = val;
        12: tensor_tmp[415:384] = val;
        13: tensor_tmp[447:416] = val;
        14: tensor_tmp[479:448] = val;
        15: tensor_tmp[511:480] = val;
        default: ;
      endcase
      force dut.mu_tensor = tensor_tmp;
    end
  endtask

  task release_tensor_word(input integer idx);
    begin
      release dut.mu_tensor;
    end
  endtask

  task force_mem_word(input integer idx, input [31:0] val);
    begin
      case (idx)
        0: force dut.mem0 = val;
        1: force dut.mem1 = val;
        2: force dut.mem2 = val;
        3: force dut.mem3 = val;
        4: force dut.mem4 = val;
        5: force dut.mem5 = val;
        6: force dut.mem6 = val;
        7: force dut.mem7 = val;
        8: force dut.mem8 = val;
        9: force dut.mem9 = val;
        10: force dut.mem10 = val;
        11: force dut.mem11 = val;
        12: force dut.mem12 = val;
        13: force dut.mem13 = val;
        14: force dut.mem14 = val;
        15: force dut.mem15 = val;
        16: force dut.mem16 = val;
        17: force dut.mem17 = val;
        18: force dut.mem18 = val;
        19: force dut.mem19 = val;
        20: force dut.mem20 = val;
        21: force dut.mem21 = val;
        22: force dut.mem22 = val;
        23: force dut.mem23 = val;
        24: force dut.mem24 = val;
        25: force dut.mem25 = val;
        26: force dut.mem26 = val;
        27: force dut.mem27 = val;
        28: force dut.mem28 = val;
        29: force dut.mem29 = val;
        30: force dut.mem30 = val;
        31: force dut.mem31 = val;
        32: force dut.mem32 = val;
        33: force dut.mem33 = val;
        34: force dut.mem34 = val;
        35: force dut.mem35 = val;
        36: force dut.mem36 = val;
        37: force dut.mem37 = val;
        38: force dut.mem38 = val;
        39: force dut.mem39 = val;
        40: force dut.mem40 = val;
        41: force dut.mem41 = val;
        42: force dut.mem42 = val;
        43: force dut.mem43 = val;
        44: force dut.mem44 = val;
        45: force dut.mem45 = val;
        46: force dut.mem46 = val;
        47: force dut.mem47 = val;
        48: force dut.mem48 = val;
        49: force dut.mem49 = val;
        50: force dut.mem50 = val;
        51: force dut.mem51 = val;
        52: force dut.mem52 = val;
        53: force dut.mem53 = val;
        54: force dut.mem54 = val;
        55: force dut.mem55 = val;
        56: force dut.mem56 = val;
        57: force dut.mem57 = val;
        58: force dut.mem58 = val;
        59: force dut.mem59 = val;
        60: force dut.mem60 = val;
        61: force dut.mem61 = val;
        62: force dut.mem62 = val;
        63: force dut.mem63 = val;
        64: force dut.mem64 = val;
        65: force dut.mem65 = val;
        66: force dut.mem66 = val;
        67: force dut.mem67 = val;
        68: force dut.mem68 = val;
        69: force dut.mem69 = val;
        70: force dut.mem70 = val;
        71: force dut.mem71 = val;
        72: force dut.mem72 = val;
        73: force dut.mem73 = val;
        74: force dut.mem74 = val;
        75: force dut.mem75 = val;
        76: force dut.mem76 = val;
        77: force dut.mem77 = val;
        78: force dut.mem78 = val;
        79: force dut.mem79 = val;
        80: force dut.mem80 = val;
        81: force dut.mem81 = val;
        82: force dut.mem82 = val;
        83: force dut.mem83 = val;
        84: force dut.mem84 = val;
        85: force dut.mem85 = val;
        86: force dut.mem86 = val;
        87: force dut.mem87 = val;
        88: force dut.mem88 = val;
        89: force dut.mem89 = val;
        90: force dut.mem90 = val;
        91: force dut.mem91 = val;
        92: force dut.mem92 = val;
        93: force dut.mem93 = val;
        94: force dut.mem94 = val;
        95: force dut.mem95 = val;
        96: force dut.mem96 = val;
        97: force dut.mem97 = val;
        98: force dut.mem98 = val;
        99: force dut.mem99 = val;
        100: force dut.mem100 = val;
        101: force dut.mem101 = val;
        102: force dut.mem102 = val;
        103: force dut.mem103 = val;
        104: force dut.mem104 = val;
        105: force dut.mem105 = val;
        106: force dut.mem106 = val;
        107: force dut.mem107 = val;
        108: force dut.mem108 = val;
        109: force dut.mem109 = val;
        110: force dut.mem110 = val;
        111: force dut.mem111 = val;
        112: force dut.mem112 = val;
        113: force dut.mem113 = val;
        114: force dut.mem114 = val;
        115: force dut.mem115 = val;
        116: force dut.mem116 = val;
        117: force dut.mem117 = val;
        118: force dut.mem118 = val;
        119: force dut.mem119 = val;
        120: force dut.mem120 = val;
        121: force dut.mem121 = val;
        122: force dut.mem122 = val;
        123: force dut.mem123 = val;
        124: force dut.mem124 = val;
        125: force dut.mem125 = val;
        126: force dut.mem126 = val;
        127: force dut.mem127 = val;
        128: force dut.mem128 = val;
        129: force dut.mem129 = val;
        130: force dut.mem130 = val;
        131: force dut.mem131 = val;
        132: force dut.mem132 = val;
        133: force dut.mem133 = val;
        134: force dut.mem134 = val;
        135: force dut.mem135 = val;
        136: force dut.mem136 = val;
        137: force dut.mem137 = val;
        138: force dut.mem138 = val;
        139: force dut.mem139 = val;
        140: force dut.mem140 = val;
        141: force dut.mem141 = val;
        142: force dut.mem142 = val;
        143: force dut.mem143 = val;
        144: force dut.mem144 = val;
        145: force dut.mem145 = val;
        146: force dut.mem146 = val;
        147: force dut.mem147 = val;
        148: force dut.mem148 = val;
        149: force dut.mem149 = val;
        150: force dut.mem150 = val;
        151: force dut.mem151 = val;
        152: force dut.mem152 = val;
        153: force dut.mem153 = val;
        154: force dut.mem154 = val;
        155: force dut.mem155 = val;
        156: force dut.mem156 = val;
        157: force dut.mem157 = val;
        158: force dut.mem158 = val;
        159: force dut.mem159 = val;
        160: force dut.mem160 = val;
        161: force dut.mem161 = val;
        162: force dut.mem162 = val;
        163: force dut.mem163 = val;
        164: force dut.mem164 = val;
        165: force dut.mem165 = val;
        166: force dut.mem166 = val;
        167: force dut.mem167 = val;
        168: force dut.mem168 = val;
        169: force dut.mem169 = val;
        170: force dut.mem170 = val;
        171: force dut.mem171 = val;
        172: force dut.mem172 = val;
        173: force dut.mem173 = val;
        174: force dut.mem174 = val;
        175: force dut.mem175 = val;
        176: force dut.mem176 = val;
        177: force dut.mem177 = val;
        178: force dut.mem178 = val;
        179: force dut.mem179 = val;
        180: force dut.mem180 = val;
        181: force dut.mem181 = val;
        182: force dut.mem182 = val;
        183: force dut.mem183 = val;
        184: force dut.mem184 = val;
        185: force dut.mem185 = val;
        186: force dut.mem186 = val;
        187: force dut.mem187 = val;
        188: force dut.mem188 = val;
        189: force dut.mem189 = val;
        190: force dut.mem190 = val;
        191: force dut.mem191 = val;
        192: force dut.mem192 = val;
        193: force dut.mem193 = val;
        194: force dut.mem194 = val;
        195: force dut.mem195 = val;
        196: force dut.mem196 = val;
        197: force dut.mem197 = val;
        198: force dut.mem198 = val;
        199: force dut.mem199 = val;
        200: force dut.mem200 = val;
        201: force dut.mem201 = val;
        202: force dut.mem202 = val;
        203: force dut.mem203 = val;
        204: force dut.mem204 = val;
        205: force dut.mem205 = val;
        206: force dut.mem206 = val;
        207: force dut.mem207 = val;
        208: force dut.mem208 = val;
        209: force dut.mem209 = val;
        210: force dut.mem210 = val;
        211: force dut.mem211 = val;
        212: force dut.mem212 = val;
        213: force dut.mem213 = val;
        214: force dut.mem214 = val;
        215: force dut.mem215 = val;
        216: force dut.mem216 = val;
        217: force dut.mem217 = val;
        218: force dut.mem218 = val;
        219: force dut.mem219 = val;
        220: force dut.mem220 = val;
        221: force dut.mem221 = val;
        222: force dut.mem222 = val;
        223: force dut.mem223 = val;
        224: force dut.mem224 = val;
        225: force dut.mem225 = val;
        226: force dut.mem226 = val;
        227: force dut.mem227 = val;
        228: force dut.mem228 = val;
        229: force dut.mem229 = val;
        230: force dut.mem230 = val;
        231: force dut.mem231 = val;
        232: force dut.mem232 = val;
        233: force dut.mem233 = val;
        234: force dut.mem234 = val;
        235: force dut.mem235 = val;
        236: force dut.mem236 = val;
        237: force dut.mem237 = val;
        238: force dut.mem238 = val;
        239: force dut.mem239 = val;
        240: force dut.mem240 = val;
        241: force dut.mem241 = val;
        242: force dut.mem242 = val;
        243: force dut.mem243 = val;
        244: force dut.mem244 = val;
        245: force dut.mem245 = val;
        246: force dut.mem246 = val;
        247: force dut.mem247 = val;
        248: force dut.mem248 = val;
        249: force dut.mem249 = val;
        250: force dut.mem250 = val;
        251: force dut.mem251 = val;
        252: force dut.mem252 = val;
        253: force dut.mem253 = val;
        254: force dut.mem254 = val;
        255: force dut.mem255 = val;
        default: ;
      endcase
    end
  endtask

  task release_mem_word(input integer idx);
    begin
      case (idx)
        0: release dut.mem0;
        1: release dut.mem1;
        2: release dut.mem2;
        3: release dut.mem3;
        4: release dut.mem4;
        5: release dut.mem5;
        6: release dut.mem6;
        7: release dut.mem7;
        8: release dut.mem8;
        9: release dut.mem9;
        10: release dut.mem10;
        11: release dut.mem11;
        12: release dut.mem12;
        13: release dut.mem13;
        14: release dut.mem14;
        15: release dut.mem15;
        16: release dut.mem16;
        17: release dut.mem17;
        18: release dut.mem18;
        19: release dut.mem19;
        20: release dut.mem20;
        21: release dut.mem21;
        22: release dut.mem22;
        23: release dut.mem23;
        24: release dut.mem24;
        25: release dut.mem25;
        26: release dut.mem26;
        27: release dut.mem27;
        28: release dut.mem28;
        29: release dut.mem29;
        30: release dut.mem30;
        31: release dut.mem31;
        32: release dut.mem32;
        33: release dut.mem33;
        34: release dut.mem34;
        35: release dut.mem35;
        36: release dut.mem36;
        37: release dut.mem37;
        38: release dut.mem38;
        39: release dut.mem39;
        40: release dut.mem40;
        41: release dut.mem41;
        42: release dut.mem42;
        43: release dut.mem43;
        44: release dut.mem44;
        45: release dut.mem45;
        46: release dut.mem46;
        47: release dut.mem47;
        48: release dut.mem48;
        49: release dut.mem49;
        50: release dut.mem50;
        51: release dut.mem51;
        52: release dut.mem52;
        53: release dut.mem53;
        54: release dut.mem54;
        55: release dut.mem55;
        56: release dut.mem56;
        57: release dut.mem57;
        58: release dut.mem58;
        59: release dut.mem59;
        60: release dut.mem60;
        61: release dut.mem61;
        62: release dut.mem62;
        63: release dut.mem63;
        64: release dut.mem64;
        65: release dut.mem65;
        66: release dut.mem66;
        67: release dut.mem67;
        68: release dut.mem68;
        69: release dut.mem69;
        70: release dut.mem70;
        71: release dut.mem71;
        72: release dut.mem72;
        73: release dut.mem73;
        74: release dut.mem74;
        75: release dut.mem75;
        76: release dut.mem76;
        77: release dut.mem77;
        78: release dut.mem78;
        79: release dut.mem79;
        80: release dut.mem80;
        81: release dut.mem81;
        82: release dut.mem82;
        83: release dut.mem83;
        84: release dut.mem84;
        85: release dut.mem85;
        86: release dut.mem86;
        87: release dut.mem87;
        88: release dut.mem88;
        89: release dut.mem89;
        90: release dut.mem90;
        91: release dut.mem91;
        92: release dut.mem92;
        93: release dut.mem93;
        94: release dut.mem94;
        95: release dut.mem95;
        96: release dut.mem96;
        97: release dut.mem97;
        98: release dut.mem98;
        99: release dut.mem99;
        100: release dut.mem100;
        101: release dut.mem101;
        102: release dut.mem102;
        103: release dut.mem103;
        104: release dut.mem104;
        105: release dut.mem105;
        106: release dut.mem106;
        107: release dut.mem107;
        108: release dut.mem108;
        109: release dut.mem109;
        110: release dut.mem110;
        111: release dut.mem111;
        112: release dut.mem112;
        113: release dut.mem113;
        114: release dut.mem114;
        115: release dut.mem115;
        116: release dut.mem116;
        117: release dut.mem117;
        118: release dut.mem118;
        119: release dut.mem119;
        120: release dut.mem120;
        121: release dut.mem121;
        122: release dut.mem122;
        123: release dut.mem123;
        124: release dut.mem124;
        125: release dut.mem125;
        126: release dut.mem126;
        127: release dut.mem127;
        128: release dut.mem128;
        129: release dut.mem129;
        130: release dut.mem130;
        131: release dut.mem131;
        132: release dut.mem132;
        133: release dut.mem133;
        134: release dut.mem134;
        135: release dut.mem135;
        136: release dut.mem136;
        137: release dut.mem137;
        138: release dut.mem138;
        139: release dut.mem139;
        140: release dut.mem140;
        141: release dut.mem141;
        142: release dut.mem142;
        143: release dut.mem143;
        144: release dut.mem144;
        145: release dut.mem145;
        146: release dut.mem146;
        147: release dut.mem147;
        148: release dut.mem148;
        149: release dut.mem149;
        150: release dut.mem150;
        151: release dut.mem151;
        152: release dut.mem152;
        153: release dut.mem153;
        154: release dut.mem154;
        155: release dut.mem155;
        156: release dut.mem156;
        157: release dut.mem157;
        158: release dut.mem158;
        159: release dut.mem159;
        160: release dut.mem160;
        161: release dut.mem161;
        162: release dut.mem162;
        163: release dut.mem163;
        164: release dut.mem164;
        165: release dut.mem165;
        166: release dut.mem166;
        167: release dut.mem167;
        168: release dut.mem168;
        169: release dut.mem169;
        170: release dut.mem170;
        171: release dut.mem171;
        172: release dut.mem172;
        173: release dut.mem173;
        174: release dut.mem174;
        175: release dut.mem175;
        176: release dut.mem176;
        177: release dut.mem177;
        178: release dut.mem178;
        179: release dut.mem179;
        180: release dut.mem180;
        181: release dut.mem181;
        182: release dut.mem182;
        183: release dut.mem183;
        184: release dut.mem184;
        185: release dut.mem185;
        186: release dut.mem186;
        187: release dut.mem187;
        188: release dut.mem188;
        189: release dut.mem189;
        190: release dut.mem190;
        191: release dut.mem191;
        192: release dut.mem192;
        193: release dut.mem193;
        194: release dut.mem194;
        195: release dut.mem195;
        196: release dut.mem196;
        197: release dut.mem197;
        198: release dut.mem198;
        199: release dut.mem199;
        200: release dut.mem200;
        201: release dut.mem201;
        202: release dut.mem202;
        203: release dut.mem203;
        204: release dut.mem204;
        205: release dut.mem205;
        206: release dut.mem206;
        207: release dut.mem207;
        208: release dut.mem208;
        209: release dut.mem209;
        210: release dut.mem210;
        211: release dut.mem211;
        212: release dut.mem212;
        213: release dut.mem213;
        214: release dut.mem214;
        215: release dut.mem215;
        216: release dut.mem216;
        217: release dut.mem217;
        218: release dut.mem218;
        219: release dut.mem219;
        220: release dut.mem220;
        221: release dut.mem221;
        222: release dut.mem222;
        223: release dut.mem223;
        224: release dut.mem224;
        225: release dut.mem225;
        226: release dut.mem226;
        227: release dut.mem227;
        228: release dut.mem228;
        229: release dut.mem229;
        230: release dut.mem230;
        231: release dut.mem231;
        232: release dut.mem232;
        233: release dut.mem233;
        234: release dut.mem234;
        235: release dut.mem235;
        236: release dut.mem236;
        237: release dut.mem237;
        238: release dut.mem238;
        239: release dut.mem239;
        240: release dut.mem240;
        241: release dut.mem241;
        242: release dut.mem242;
        243: release dut.mem243;
        244: release dut.mem244;
        245: release dut.mem245;
        246: release dut.mem246;
        247: release dut.mem247;
        248: release dut.mem248;
        249: release dut.mem249;
        250: release dut.mem250;
        251: release dut.mem251;
        252: release dut.mem252;
        253: release dut.mem253;
        254: release dut.mem254;
        255: release dut.mem255;
        default: ;
      endcase
    end
  endtask

  function automatic [31:0] read_mem_word(input integer idx);
    begin
      case (idx)
        0: read_mem_word = dut.mem0;
        1: read_mem_word = dut.mem1;
        2: read_mem_word = dut.mem2;
        3: read_mem_word = dut.mem3;
        4: read_mem_word = dut.mem4;
        5: read_mem_word = dut.mem5;
        6: read_mem_word = dut.mem6;
        7: read_mem_word = dut.mem7;
        8: read_mem_word = dut.mem8;
        9: read_mem_word = dut.mem9;
        10: read_mem_word = dut.mem10;
        11: read_mem_word = dut.mem11;
        12: read_mem_word = dut.mem12;
        13: read_mem_word = dut.mem13;
        14: read_mem_word = dut.mem14;
        15: read_mem_word = dut.mem15;
        16: read_mem_word = dut.mem16;
        17: read_mem_word = dut.mem17;
        18: read_mem_word = dut.mem18;
        19: read_mem_word = dut.mem19;
        20: read_mem_word = dut.mem20;
        21: read_mem_word = dut.mem21;
        22: read_mem_word = dut.mem22;
        23: read_mem_word = dut.mem23;
        24: read_mem_word = dut.mem24;
        25: read_mem_word = dut.mem25;
        26: read_mem_word = dut.mem26;
        27: read_mem_word = dut.mem27;
        28: read_mem_word = dut.mem28;
        29: read_mem_word = dut.mem29;
        30: read_mem_word = dut.mem30;
        31: read_mem_word = dut.mem31;
        32: read_mem_word = dut.mem32;
        33: read_mem_word = dut.mem33;
        34: read_mem_word = dut.mem34;
        35: read_mem_word = dut.mem35;
        36: read_mem_word = dut.mem36;
        37: read_mem_word = dut.mem37;
        38: read_mem_word = dut.mem38;
        39: read_mem_word = dut.mem39;
        40: read_mem_word = dut.mem40;
        41: read_mem_word = dut.mem41;
        42: read_mem_word = dut.mem42;
        43: read_mem_word = dut.mem43;
        44: read_mem_word = dut.mem44;
        45: read_mem_word = dut.mem45;
        46: read_mem_word = dut.mem46;
        47: read_mem_word = dut.mem47;
        48: read_mem_word = dut.mem48;
        49: read_mem_word = dut.mem49;
        50: read_mem_word = dut.mem50;
        51: read_mem_word = dut.mem51;
        52: read_mem_word = dut.mem52;
        53: read_mem_word = dut.mem53;
        54: read_mem_word = dut.mem54;
        55: read_mem_word = dut.mem55;
        56: read_mem_word = dut.mem56;
        57: read_mem_word = dut.mem57;
        58: read_mem_word = dut.mem58;
        59: read_mem_word = dut.mem59;
        60: read_mem_word = dut.mem60;
        61: read_mem_word = dut.mem61;
        62: read_mem_word = dut.mem62;
        63: read_mem_word = dut.mem63;
        64: read_mem_word = dut.mem64;
        65: read_mem_word = dut.mem65;
        66: read_mem_word = dut.mem66;
        67: read_mem_word = dut.mem67;
        68: read_mem_word = dut.mem68;
        69: read_mem_word = dut.mem69;
        70: read_mem_word = dut.mem70;
        71: read_mem_word = dut.mem71;
        72: read_mem_word = dut.mem72;
        73: read_mem_word = dut.mem73;
        74: read_mem_word = dut.mem74;
        75: read_mem_word = dut.mem75;
        76: read_mem_word = dut.mem76;
        77: read_mem_word = dut.mem77;
        78: read_mem_word = dut.mem78;
        79: read_mem_word = dut.mem79;
        80: read_mem_word = dut.mem80;
        81: read_mem_word = dut.mem81;
        82: read_mem_word = dut.mem82;
        83: read_mem_word = dut.mem83;
        84: read_mem_word = dut.mem84;
        85: read_mem_word = dut.mem85;
        86: read_mem_word = dut.mem86;
        87: read_mem_word = dut.mem87;
        88: read_mem_word = dut.mem88;
        89: read_mem_word = dut.mem89;
        90: read_mem_word = dut.mem90;
        91: read_mem_word = dut.mem91;
        92: read_mem_word = dut.mem92;
        93: read_mem_word = dut.mem93;
        94: read_mem_word = dut.mem94;
        95: read_mem_word = dut.mem95;
        96: read_mem_word = dut.mem96;
        97: read_mem_word = dut.mem97;
        98: read_mem_word = dut.mem98;
        99: read_mem_word = dut.mem99;
        100: read_mem_word = dut.mem100;
        101: read_mem_word = dut.mem101;
        102: read_mem_word = dut.mem102;
        103: read_mem_word = dut.mem103;
        104: read_mem_word = dut.mem104;
        105: read_mem_word = dut.mem105;
        106: read_mem_word = dut.mem106;
        107: read_mem_word = dut.mem107;
        108: read_mem_word = dut.mem108;
        109: read_mem_word = dut.mem109;
        110: read_mem_word = dut.mem110;
        111: read_mem_word = dut.mem111;
        112: read_mem_word = dut.mem112;
        113: read_mem_word = dut.mem113;
        114: read_mem_word = dut.mem114;
        115: read_mem_word = dut.mem115;
        116: read_mem_word = dut.mem116;
        117: read_mem_word = dut.mem117;
        118: read_mem_word = dut.mem118;
        119: read_mem_word = dut.mem119;
        120: read_mem_word = dut.mem120;
        121: read_mem_word = dut.mem121;
        122: read_mem_word = dut.mem122;
        123: read_mem_word = dut.mem123;
        124: read_mem_word = dut.mem124;
        125: read_mem_word = dut.mem125;
        126: read_mem_word = dut.mem126;
        127: read_mem_word = dut.mem127;
        128: read_mem_word = dut.mem128;
        129: read_mem_word = dut.mem129;
        130: read_mem_word = dut.mem130;
        131: read_mem_word = dut.mem131;
        132: read_mem_word = dut.mem132;
        133: read_mem_word = dut.mem133;
        134: read_mem_word = dut.mem134;
        135: read_mem_word = dut.mem135;
        136: read_mem_word = dut.mem136;
        137: read_mem_word = dut.mem137;
        138: read_mem_word = dut.mem138;
        139: read_mem_word = dut.mem139;
        140: read_mem_word = dut.mem140;
        141: read_mem_word = dut.mem141;
        142: read_mem_word = dut.mem142;
        143: read_mem_word = dut.mem143;
        144: read_mem_word = dut.mem144;
        145: read_mem_word = dut.mem145;
        146: read_mem_word = dut.mem146;
        147: read_mem_word = dut.mem147;
        148: read_mem_word = dut.mem148;
        149: read_mem_word = dut.mem149;
        150: read_mem_word = dut.mem150;
        151: read_mem_word = dut.mem151;
        152: read_mem_word = dut.mem152;
        153: read_mem_word = dut.mem153;
        154: read_mem_word = dut.mem154;
        155: read_mem_word = dut.mem155;
        156: read_mem_word = dut.mem156;
        157: read_mem_word = dut.mem157;
        158: read_mem_word = dut.mem158;
        159: read_mem_word = dut.mem159;
        160: read_mem_word = dut.mem160;
        161: read_mem_word = dut.mem161;
        162: read_mem_word = dut.mem162;
        163: read_mem_word = dut.mem163;
        164: read_mem_word = dut.mem164;
        165: read_mem_word = dut.mem165;
        166: read_mem_word = dut.mem166;
        167: read_mem_word = dut.mem167;
        168: read_mem_word = dut.mem168;
        169: read_mem_word = dut.mem169;
        170: read_mem_word = dut.mem170;
        171: read_mem_word = dut.mem171;
        172: read_mem_word = dut.mem172;
        173: read_mem_word = dut.mem173;
        174: read_mem_word = dut.mem174;
        175: read_mem_word = dut.mem175;
        176: read_mem_word = dut.mem176;
        177: read_mem_word = dut.mem177;
        178: read_mem_word = dut.mem178;
        179: read_mem_word = dut.mem179;
        180: read_mem_word = dut.mem180;
        181: read_mem_word = dut.mem181;
        182: read_mem_word = dut.mem182;
        183: read_mem_word = dut.mem183;
        184: read_mem_word = dut.mem184;
        185: read_mem_word = dut.mem185;
        186: read_mem_word = dut.mem186;
        187: read_mem_word = dut.mem187;
        188: read_mem_word = dut.mem188;
        189: read_mem_word = dut.mem189;
        190: read_mem_word = dut.mem190;
        191: read_mem_word = dut.mem191;
        192: read_mem_word = dut.mem192;
        193: read_mem_word = dut.mem193;
        194: read_mem_word = dut.mem194;
        195: read_mem_word = dut.mem195;
        196: read_mem_word = dut.mem196;
        197: read_mem_word = dut.mem197;
        198: read_mem_word = dut.mem198;
        199: read_mem_word = dut.mem199;
        200: read_mem_word = dut.mem200;
        201: read_mem_word = dut.mem201;
        202: read_mem_word = dut.mem202;
        203: read_mem_word = dut.mem203;
        204: read_mem_word = dut.mem204;
        205: read_mem_word = dut.mem205;
        206: read_mem_word = dut.mem206;
        207: read_mem_word = dut.mem207;
        208: read_mem_word = dut.mem208;
        209: read_mem_word = dut.mem209;
        210: read_mem_word = dut.mem210;
        211: read_mem_word = dut.mem211;
        212: read_mem_word = dut.mem212;
        213: read_mem_word = dut.mem213;
        214: read_mem_word = dut.mem214;
        215: read_mem_word = dut.mem215;
        216: read_mem_word = dut.mem216;
        217: read_mem_word = dut.mem217;
        218: read_mem_word = dut.mem218;
        219: read_mem_word = dut.mem219;
        220: read_mem_word = dut.mem220;
        221: read_mem_word = dut.mem221;
        222: read_mem_word = dut.mem222;
        223: read_mem_word = dut.mem223;
        224: read_mem_word = dut.mem224;
        225: read_mem_word = dut.mem225;
        226: read_mem_word = dut.mem226;
        227: read_mem_word = dut.mem227;
        228: read_mem_word = dut.mem228;
        229: read_mem_word = dut.mem229;
        230: read_mem_word = dut.mem230;
        231: read_mem_word = dut.mem231;
        232: read_mem_word = dut.mem232;
        233: read_mem_word = dut.mem233;
        234: read_mem_word = dut.mem234;
        235: read_mem_word = dut.mem235;
        236: read_mem_word = dut.mem236;
        237: read_mem_word = dut.mem237;
        238: read_mem_word = dut.mem238;
        239: read_mem_word = dut.mem239;
        240: read_mem_word = dut.mem240;
        241: read_mem_word = dut.mem241;
        242: read_mem_word = dut.mem242;
        243: read_mem_word = dut.mem243;
        244: read_mem_word = dut.mem244;
        245: read_mem_word = dut.mem245;
        246: read_mem_word = dut.mem246;
        247: read_mem_word = dut.mem247;
        248: read_mem_word = dut.mem248;
        249: read_mem_word = dut.mem249;
        250: read_mem_word = dut.mem250;
        251: read_mem_word = dut.mem251;
        252: read_mem_word = dut.mem252;
        253: read_mem_word = dut.mem253;
        254: read_mem_word = dut.mem254;
        255: read_mem_word = dut.mem255;
        default: read_mem_word = 32'd0;
      endcase
    end
  endfunction

  // Physical runtime assertions:
  //  - μ ledger must be monotone non-decreasing
  //  - halted must be caused by HALT opcode or bianchi alarm
  always @(posedge clk) begin
    if (!rst_n) begin
      prev_mu_valid <= 1'b0;
      prev_mu <= 32'd0;
    end else if (shadow_executing) begin
      if (prev_mu_valid) begin
        assert (mu_out >= prev_mu)
          else $fatal(1, "PHYS_ASSERT_FAIL: mu decreased (%0d -> %0d)", prev_mu, mu_out);
      end

      if (halted_out) begin
        assert (bianchi_alarm_out || (current_opcode == 8'hFF))
          else $fatal(1, "PHYS_ASSERT_FAIL: halted without HALT opcode or bianchi alarm");
      end

      prev_mu <= mu_out;
      prev_mu_valid <= 1'b1;
    end
  end

endmodule
