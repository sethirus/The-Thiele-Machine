// thiele_cpu_kami_tb.v — Testbench for Kami-generated mkModule1
//
// Loads a program into the CPU via loadInstr, then lets it execute.
// After halt, dumps all state as JSON.
//
// Signal naming matches BSC-generated RTL:
//   - regs:  reg [511:0] — 16 x 32-bit registers, reg[i] = regs[i*32 +: 32]
//   - imem:  RegFile submodule — imem.arr[0:127] (128-bit words)
//   - mem:   RegFile submodule — mem.arr[0:127] (32-bit words)
//   - loadInstr_x_0: 135-bit (7-bit addr [134:128] + 128-bit data [127:0])
//     (was 144-bit; addr width tracks MemAddrSz=7 in ThieleTypes.v)

`timescale 1ns/1ps

module thiele_cpu_kami_tb;

  parameter NUM_SHADOW_MODS = 64;

  reg clk = 0;
  reg rst_n = 0;
  always #5 clk = ~clk;

  reg [134:0] load_data;
  reg load_en;


  wire [31:0] pc_out, mu_out;
  wire [31:0] partition_ops_out, mdl_ops_out, info_gain_out, error_code_out;
  wire [31:0] mstatus_out, mcycle_lo_out, mcycle_hi_out, minstret_lo_out, minstret_hi_out, logic_acc_out, cert_addr_out;
  wire [31:0] mu_tensor_0, mu_tensor_1, mu_tensor_2, mu_tensor_3;
  wire [31:0] pt_next_id_out;
  wire [31:0] pt_size_out;
  wire err_out, halted_out, bianchi_alarm_out;
  wire certified_out;
  wire [31:0] wc_same_00_out, wc_diff_00_out, wc_same_01_out, wc_diff_01_out;
  wire [31:0] wc_same_10_out, wc_diff_10_out, wc_same_11_out, wc_diff_11_out;
  wire rdy_load;

  mkModule1 dut (
    .CLK(clk),
    .RST_N(rst_n),
    .loadInstr_x_0(load_data),
    .EN_loadInstr(load_en),
    .RDY_loadInstr(rdy_load),
    .EN_getPC(1'b1), .getPC(pc_out), .RDY_getPC(),
    .EN_getMu(1'b1), .getMu(mu_out), .RDY_getMu(),
    .EN_getErr(1'b1), .getErr(err_out), .RDY_getErr(),
    .EN_getHalted(1'b1), .getHalted(halted_out), .RDY_getHalted(),
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
    .EN_getCertified(1'b1), .getCertified(certified_out), .RDY_getCertified(),
    .EN_getWcSame00(1'b1), .getWcSame00(wc_same_00_out), .RDY_getWcSame00(),
    .EN_getWcDiff00(1'b1), .getWcDiff00(wc_diff_00_out), .RDY_getWcDiff00(),
    .EN_getWcSame01(1'b1), .getWcSame01(wc_same_01_out), .RDY_getWcSame01(),
    .EN_getWcDiff01(1'b1), .getWcDiff01(wc_diff_01_out), .RDY_getWcDiff01(),
    .EN_getWcSame10(1'b1), .getWcSame10(wc_same_10_out), .RDY_getWcSame10(),
    .EN_getWcDiff10(1'b1), .getWcDiff10(wc_diff_10_out), .RDY_getWcDiff10(),
    .EN_getWcSame11(1'b1), .getWcSame11(wc_same_11_out), .RDY_getWcSame11(),
    .EN_getWcDiff11(1'b1), .getWcDiff11(wc_diff_11_out), .RDY_getWcDiff11()
  );

  reg [127:0] instr_memory [0:127];
  reg [31:0] data_memory [0:127];

  integer i;
  integer cycle_count;
  integer num_instrs;
  integer init_mu_en, init_mu_value;
  integer init_active_module_en, init_active_module_value;
  integer init_pt_en, init_pt_idx, init_pt_value;
  integer init_tensor_en, init_tensor_idx, init_tensor_value;
  integer init_logic_acc_en, init_logic_acc_value;

  reg [63:0] shadow_masks [0:NUM_SHADOW_MODS-1];
  reg [7:0] shadow_next_mid;
  reg shadow_executing;
  reg [127:0] exec_word;
  integer exec_op_i, exec_a_i, exec_b_i;
  integer sh_e, sh_m;
  integer sh_pred_mode_i, sh_pred_param_i;
  reg [63:0] sh_left, sh_right;
  integer shadow_found_dup;
  reg [63:0] shadow_new_mask;
  integer mod_j, bit_b, first_mod, first_bit;
  integer morph_j, first_morph;


  reg [1023:0] program_hex_path;
  reg [1023:0] data_hex_path;
  reg [1023:0] vcd_path;
  integer vcd_en;

  reg [31:0] prev_mu;
  reg prev_mu_valid;

  // Current instruction: updated procedurally from exec_word in the main loop.
  // Cannot use continuous assign on RegFile submodule arr[] — iverilog doesn't
  // support dynamic array indexing in continuous assigns across hierarchy.
  reg [127:0] current_instr;
  reg [7:0] current_opcode;

  initial begin
    for (i = 0; i < 128; i = i + 1) begin
      instr_memory[i] = 128'h00000000000000000000000000000000;
      data_memory[i] = 32'h00000000;
    end
    for (i = 0; i < NUM_SHADOW_MODS; i = i + 1)
      shadow_masks[i] = 64'd0;
    shadow_next_mid = 8'd1;
    shadow_executing = 1'b0;
    exec_word = 128'd0;
    shadow_found_dup = 0;
    prev_mu = 32'd0;
    prev_mu_valid = 1'b0;
    vcd_en = 0;

    init_mu_en = 0; init_active_module_en = 0; init_pt_en = 0; init_tensor_en = 0;
    init_logic_acc_en = 0;
    if ($value$plusargs("INIT_MU=%d", init_mu_value)) init_mu_en = 1;
    if ($value$plusargs("INIT_ACTIVE_MODULE=%d", init_active_module_value)) init_active_module_en = 1;
    if ($value$plusargs("INIT_PT_IDX=%d", init_pt_idx)) init_pt_en = 1;
    if ($value$plusargs("INIT_PT_VAL=%d", init_pt_value)) init_pt_en = init_pt_en & 1;
    if ($value$plusargs("INIT_TENSOR_IDX=%d", init_tensor_idx)) init_tensor_en = 1;
    if ($value$plusargs("INIT_TENSOR_VAL=%d", init_tensor_value)) init_tensor_en = init_tensor_en & 1;
    if ($value$plusargs("INIT_LOGIC_ACC=%d", init_logic_acc_value)) init_logic_acc_en = 1;

    if ($value$plusargs("PROGRAM=%s", program_hex_path)) begin
      $readmemh(program_hex_path, instr_memory);
    end else begin
      instr_memory[0] = 128'h020000000000000000000000FF000000;
    end
    if ($value$plusargs("VCD=%s", vcd_path)) begin
      vcd_en = 1;
      $dumpfile(vcd_path);
      $dumpvars(0, thiele_cpu_kami_tb);
    end
    if ($value$plusargs("DATA=%s", data_hex_path)) begin
      $readmemh(data_hex_path, data_memory);
    end

    if (!$value$plusargs("N_INSTRS=%d", num_instrs))
      num_instrs = 128;

    rst_n = 0;
    load_en = 0;
    load_data = 135'd0;
    @(posedge clk);
    @(posedge clk);

    rst_n = 1;
    // Fast-init: force BSC RegFile init flags permanently high, bypassing
    // the 131K-cycle hardware zero-init loop.  We zero the arrays directly
    // and write the real program/data via the normal loadInstr port.
    // These forces are NEVER released — the flags would stay at 1 in
    // normal operation anyway, and forcing prevents the clocked always
    // block from reverting them to the reset value on the first posedge.
    force dut.imem_init = 1'b1;
    force dut.mem_init = 1'b1;
    force dut.lassert_cbuf_init = 1'b1;
    force dut.lassert_fbuf_init = 1'b1;
    // Also hold halted=1 during loadInstr to prevent RL_step from
    // executing garbage while instructions are being loaded.
    force dut.halted = 1'b1;
    // Memory sizes track ThieleTypes.v: imem/mem = 2^MemAddrSz = 256.
    // lassert_cbuf/lassert_fbuf are 64-entry RegFiles
    // (LassertCbufIdxSz=LassertFbufIdxSz=6 in ThieleTypes.v).
    for (i = 0; i < 128; i = i + 1) begin
      dut.imem.arr[i] = 128'd0;
      dut.mem.arr[i] = 32'd0;
    end
    for (i = 0; i < 64; i = i + 1) begin
      dut.lassert_cbuf.arr[i] = 32'd0;
      dut.lassert_fbuf.arr[i] = 32'd0;
    end

    // loadInstr port is 135-bit: {addr[6:0], data[127:0]} (MemAddrSz=7)
    for (i = 0; i < num_instrs; i = i + 1) begin
      load_data = {i[6:0], instr_memory[i]};
      load_en = 1;
      @(posedge clk);
    end
    load_en = 0;

    // Initialize state: zero all registers and state, load data memory
    @(negedge clk);
    force dut.pc = 32'd0;
    force dut.mu = 32'd0;
    force dut.err = 1'b0;
    force dut.halted = 1'b0;
    force dut.lassert_phase = 3'd0;
    force dut.regs = {512{1'b0}};   // RegCount=16 × WordSz=32 = 512 bits
    // Data memory: direct assignment to RegFile arr (per BSC convention)
    // RTL mem has hi=127 (128 words); limit loop to match
    for (i = 0; i < 128; i = i + 1) begin
      dut.mem.arr[i] = data_memory[i];
    end
    force dut.partition_ops = 32'd0; force dut.mdl_ops = 32'd0; force dut.info_gain = 32'd0; force dut.error_code = 32'd0;
    force dut.pt_next_id = 32'd1;
    for (i = 0; i < 16; i = i + 1) dut.mt_arr[i] = 32'd0;
    force dut.logic_acc = 32'd0;
    force dut.cert_addr = 32'd0;
    @(posedge clk); @(negedge clk);
    release dut.pc; release dut.mu; release dut.err; release dut.halted;
    release dut.lassert_phase;
    release dut.regs;
    release dut.partition_ops; release dut.mdl_ops; release dut.info_gain; release dut.error_code; release dut.pt_next_id;
    release dut.logic_acc;
    release dut.cert_addr;

    if (init_mu_en != 0) force dut.mu = init_mu_value[31:0];
    if (init_active_module_en != 0) force dut.active_module = init_active_module_value[5:0];
    if (init_pt_en != 0) force_pt_word(init_pt_idx, init_pt_value[31:0]);
    if (init_tensor_en != 0) force_tensor_word(init_tensor_idx, init_tensor_value[31:0]);
    if (init_logic_acc_en != 0) force dut.logic_acc = init_logic_acc_value[31:0];
    if (init_mu_en != 0 || init_active_module_en != 0 || init_pt_en != 0 || init_tensor_en != 0 || init_logic_acc_en != 0) begin
      @(posedge clk); @(negedge clk);
    end
    if (init_mu_en != 0) release dut.mu;
    if (init_active_module_en != 0) release dut.active_module;
    if (init_pt_en != 0) release_pt_word(init_pt_idx);
    if (init_tensor_en != 0) release_tensor_word(init_tensor_idx);
    if (init_logic_acc_en != 0) release dut.logic_acc;

    shadow_executing = 1'b1;
    cycle_count = 0;
    current_instr = 128'd0;
    current_opcode = 8'd0;
    while (!halted_out && !err_out && cycle_count < 10000) begin
      exec_word = dut.imem.arr[pc_out[6:0]];
      current_instr = exec_word;
      current_opcode = exec_word[31:24];

      @(posedge clk);
      cycle_count = cycle_count + 1;
      exec_op_i = exec_word[31:24]; exec_a_i = exec_word[23:16]; exec_b_i = exec_word[15:8];

      case (exec_op_i)
        8'h00: begin
          shadow_new_mask = (64'h1 << (exec_a_i & 8'h3F));
          shadow_found_dup = 0;
          for (sh_m = 1; sh_m < shadow_next_mid; sh_m = sh_m + 1)
            if (shadow_masks[sh_m] == shadow_new_mask) shadow_found_dup = 1;
          if (!shadow_found_dup && shadow_next_mid < NUM_SHADOW_MODS) begin
            shadow_masks[shadow_next_mid] = shadow_new_mask;
            shadow_next_mid = shadow_next_mid + 1;
          end
        end
        8'h02: begin
          if (exec_a_i < shadow_next_mid && exec_b_i < shadow_next_mid && shadow_next_mid < NUM_SHADOW_MODS) begin
            shadow_masks[shadow_next_mid] = shadow_masks[exec_a_i] | shadow_masks[exec_b_i];
            shadow_masks[exec_a_i] = 64'd0;
            shadow_masks[exec_b_i] = 64'd0;
            shadow_next_mid = shadow_next_mid + 1;
          end
        end
        8'h01: begin
          if (exec_a_i < shadow_next_mid && (shadow_next_mid + 1) < NUM_SHADOW_MODS) begin
            sh_pred_mode_i = (exec_b_i >> 6) & 3;
            sh_pred_param_i = exec_b_i & 8'h3F;
            sh_left = 64'd0; sh_right = 64'd0;
            for (sh_e = 0; sh_e < 64; sh_e = sh_e + 1) begin
              if ((shadow_masks[exec_a_i] >> sh_e) & 64'h1) begin
                case (sh_pred_mode_i)
                  0: begin if ((sh_e & 1) == (sh_pred_param_i & 1)) sh_left = sh_left | (64'h1 << sh_e); else sh_right = sh_right | (64'h1 << sh_e); end
                  1: begin if (sh_e >= sh_pred_param_i) sh_left = sh_left | (64'h1 << sh_e); else sh_right = sh_right | (64'h1 << sh_e); end
                  2: begin if (((sh_e >> sh_pred_param_i) & 1) != 0) sh_left = sh_left | (64'h1 << sh_e); else sh_right = sh_right | (64'h1 << sh_e); end
                  default: begin sh_right = sh_right | (64'h1 << sh_e); end
                endcase
              end
            end
            shadow_masks[shadow_next_mid] = sh_left;
            shadow_masks[shadow_next_mid + 1] = sh_right;
            shadow_masks[exec_a_i] = 64'd0;
            shadow_next_mid = shadow_next_mid + 2;
          end
        end
      endcase

      if (current_opcode == 8'h09) begin
        $display("CHSH_TRIAL %0d %0d %0d %0d", current_instr[17], current_instr[16], current_instr[9], current_instr[8]);
      end
    end

    // Update current_instr for the final state (used by assertions)
    current_instr = dut.imem.arr[pc_out[6:0]];
    current_opcode = current_instr[31:24];

    #1;
    $display("{");
    $display("  \"status\": %0d,", halted_out ? 32'd2 : (err_out ? 32'd3 : 32'd0));
    $display("  \"error_code\": %0d,", error_code_out);
    $display("  \"partition_ops\": %0d,", partition_ops_out);
    $display("  \"mdl_ops\": %0d,", mdl_ops_out);
    $display("  \"info_gain\": %0d,", info_gain_out);
    $display("  \"mu\": %0d,", mu_out);
    $display("  \"logic_acc\": %0d,", logic_acc_out);
    $display("  \"mstatus\": %0d,", mstatus_out);
    $display("  \"cert_addr\": %0d,", cert_addr_out);
    $display("  \"csr_heap_base\": 0,");
    $display("  \"mu_tensor_0\": %0d,", mu_tensor_0);
    $display("  \"mu_tensor_1\": %0d,", mu_tensor_1);
    $display("  \"mu_tensor_2\": %0d,", mu_tensor_2);
    $display("  \"mu_tensor_3\": %0d,", mu_tensor_3);
    $display("  \"mu_tensor\": [");
    for (i = 0; i < 16; i = i + 1) begin
      if (i < 15) $display("    %0d,", dut.mt_arr[i]);
      else $display("    %0d", dut.mt_arr[i]);
    end
    $display("  ],");
    $display("  \"bianchi_alarm\": %0d,", bianchi_alarm_out);
    $display("  \"certified\": %0d,", certified_out);
    $display("  \"wc_same_00\": %0d,", wc_same_00_out);
    $display("  \"wc_diff_00\": %0d,", wc_diff_00_out);
    $display("  \"wc_same_01\": %0d,", wc_same_01_out);
    $display("  \"wc_diff_01\": %0d,", wc_diff_01_out);
    $display("  \"wc_same_10\": %0d,", wc_same_10_out);
    $display("  \"wc_diff_10\": %0d,", wc_diff_10_out);
    $display("  \"wc_same_11\": %0d,", wc_same_11_out);
    $display("  \"wc_diff_11\": %0d,", wc_diff_11_out);
    $display(
      "  \"witness\": [%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d],",
      wc_same_00_out, wc_diff_00_out, wc_same_01_out, wc_diff_01_out,
      wc_same_10_out, wc_diff_10_out, wc_same_11_out, wc_diff_11_out
    );
    $display("  \"cycles\": %0d,", cycle_count);
    $display("  \"pc\": %0d,", pc_out);
    $display("  \"err\": %0d,", err_out);
    $display("  \"pt0_size\": %0d,", pt_size_out);
    $display("  \"pt_next_id\": %0d,", pt_next_id_out);
    // Dump registers from flat regs[1023:0] — reg[i] = regs[i*32 +: 32]
    $display("  \"regs\": [");
    for (i = 0; i < 16; i = i + 1) begin
      if (i < 15) $display("    %0d,", dut.regs[i*32 +: 32]);
      else $display("    %0d", dut.regs[i*32 +: 32]);
    end
    $display("  ],");
    // Dump data memory from mem RegFile submodule (RTL has 128 words, hi=127)
    $display("  \"mem\": [");
    for (i = 0; i < 128; i = i + 1) begin
      if (i < 127) $display("    %0d,", dut.mem.arr[i]);
      else $display("    %0d", dut.mem.arr[i]);
    end
    $display("  ],");
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
    $display("],");
    $display("  \"morph_next_id\": %0d,", dut.morph_next_id);
    $write("  \"morphisms\": [");
    first_morph = 1;
    // MorphTableSz=16 after May 2026 xc7a35t (Artix-7) fit reduction; slot index width
    // is MorphTableIdxSz=4 but each src/dst entry is PTableIdxSz=6 bits.
    for (morph_j = 0; morph_j < 16; morph_j = morph_j + 1) begin
      if (dut.morph_valid_table[morph_j]) begin
        if (!first_morph) $write(", ");
        $write(
          "{\"id\": %0d, \"source\": %0d, \"target\": %0d, \"is_identity\": %0d, \"coupling\": {\"label\": \"empty\", \"pairs\": []}}",
          morph_j,
          dut.morph_src_table[morph_j*6 +: 6],
          dut.morph_dst_table[morph_j*6 +: 6],
          dut.morph_identity_table[morph_j]
        );
        first_morph = 0;
      end
    end
    $display("]");
    $display("}");
    $finish;
  end

  // dut.ptTable is the live partition-size table (`reg [2047:0]`, 64×32-bit).
  // It is intentionally NOT folded into ptTable_arr by Pass 11b — see the
  // comment in scripts/verilog_synth_transform.py:PACKED_TABLES. We need
  // whole-register `force` here so the testbench can pre-seed
  // active_region_size = ptTable[active_module*32 +: 32] before the CPU
  // starts executing locality-guarded ops. Force-on-array-element is not
  // supported in iverilog 12; force-on-whole-packed-reg is.
  task force_pt_word(input integer idx, input [31:0] val);
    reg [2047:0] pt_tmp;
    begin
      pt_tmp = dut.ptTable;
      case (idx)
        0: pt_tmp[31:0] = val; 1: pt_tmp[63:32] = val; 2: pt_tmp[95:64] = val; 3: pt_tmp[127:96] = val;
        4: pt_tmp[159:128] = val; 5: pt_tmp[191:160] = val; 6: pt_tmp[223:192] = val; 7: pt_tmp[255:224] = val;
        8: pt_tmp[287:256] = val; 9: pt_tmp[319:288] = val; 10: pt_tmp[351:320] = val; 11: pt_tmp[383:352] = val;
        12: pt_tmp[415:384] = val; 13: pt_tmp[447:416] = val; 14: pt_tmp[479:448] = val; 15: pt_tmp[511:480] = val;
        default: ;
      endcase
      force dut.ptTable = pt_tmp;
    end
  endtask

  task release_pt_word(input integer idx); begin release dut.ptTable; end endtask

  task force_tensor_word(input integer idx, input [31:0] val);
    begin
      dut.mt_arr[idx] = val;
    end
  endtask

  task release_tensor_word(input integer idx); begin end endtask

  always @(posedge clk) begin
    if (!rst_n) begin prev_mu_valid <= 1'b0; prev_mu <= 32'd0; end
    else if (shadow_executing) begin
      if (prev_mu_valid) begin
        assert (mu_out >= prev_mu)
          else $fatal(1, "PHYS_ASSERT_FAIL: mu decreased (%0d -> %0d)", prev_mu, mu_out);
      end
      if (halted_out) begin
        // Read opcode directly from imem RegFile — avoids race with initial block
        assert (bianchi_alarm_out || (dut.imem.arr[pc_out[6:0]][31:24] == 8'hFF))
          else $fatal(1, "PHYS_ASSERT_FAIL: halted without HALT opcode or bianchi alarm");
      end
      prev_mu <= mu_out;
      prev_mu_valid <= 1'b1;
    end
  end

endmodule
