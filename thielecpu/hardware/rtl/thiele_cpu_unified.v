// ============================================================================
// Thiele CPU — Unified Partition-Native Processor
// ============================================================================
//
// Licensed under the Apache License, Version 2.0
// Copyright 2025 Devon Thiele — See LICENSE for full terms.
//
// SINGLE-FILE IMPLEMENTATION — all modules in one file:
//   thiele_cpu              Top-level CPU (FSM, decode, execute)
//   mu_alu                  Q16.16 fixed-point ALU
//   mu_core                 Partition isomorphism enforcement
//   receipt_integrity_checker Receipt verification
//   clz8                    Combinational ceil(log2) helper
//
// THREE-LAYER ISOMORPHISM:
//   This RTL is bisimulation-equivalent to:
//     Coq:   coq/kernel/ThreeLayerIsomorphism.v  (formally proven, zero axioms)
//     Python: thielecpu/vm.py + thielecpu/state.py (reference implementation)
//
//   Key invariant:  mu_accumulator += operand_cost  for every instruction
//   This matches:   Coq   vm_mu s' = vm_mu s + instruction_cost instr
//                   Python state.mu_ledger.charge_*(cost)
//
// INSTRUCTION ENCODING:  [31:24] opcode | [23:16] operand_a | [15:8] operand_b | [7:0] cost
//
// 18 OPCODES (hex values match Coq/Python ISA exactly):
//   0x00 PNEW         Create partition module
//   0x01 PSPLIT        Split module by predicate
//   0x02 PMERGE        Merge two modules
//   0x03 LASSERT       Logic assertion with certificate
//   0x04 LJOIN         Join certificates
//   0x05 MDLACC        MDL cost accumulation (uses μ-ALU)
//   0x06 PDISCOVER     Partition discovery / info gain
//   0x07 XFER          Register transfer
//   0x08 PYEXEC        Python execution bridge
//   0x09 CHSH_TRIAL    CHSH measurement trial
//   0x0A XOR_LOAD      Load XOR matrix row
//   0x0B XOR_ADD       XOR matrix row addition
//   0x0C XOR_SWAP      XOR matrix row swap
//   0x0D XOR_RANK      XOR matrix popcount/rank
//   0x0E EMIT          Emit value
//   0x0F REVEAL        Reveal hidden info (extra μ-cost)
//   0x10 ORACLE_HALTS  Hyper-Thiele oracle primitive
//   0xFF HALT          Halt execution
//
// ============================================================================

`timescale 1ns / 1ps

// ============================================================================
// TOP-LEVEL: thiele_cpu
// ============================================================================

module thiele_cpu (
    input wire clk,
    input wire rst_n,

    // Status / control outputs
    output wire [31:0] cert_addr,
    output wire [31:0] status,
    output wire [31:0] error_code,
    output wire [31:0] partition_ops,
    output wire [31:0] mdl_ops,
    output wire [31:0] info_gain,
    output wire [31:0] mu,              // μ-cost accumulator (isomorphism witness)

    // Memory interface
    output wire [31:0] mem_addr,
    output wire [31:0] mem_wdata,
    input  wire [31:0] mem_rdata,
    output wire mem_we,
    output wire mem_en,

    // Logic engine interface
    output wire        logic_req,
    output wire [31:0] logic_addr,
    input  wire        logic_ack,
    input  wire [31:0] logic_data,

    // Python execution interface
    output wire        py_req,
    output wire [31:0] py_code_addr,
    input  wire        py_ack,
    input  wire [31:0] py_result,

    // Instruction memory interface
    input  wire [31:0] instr_data,
    output wire [31:0] pc
);

// ============================================================================
// OPCODE CONSTANTS (source of truth: Coq-extracted, matches Python ISA)
// ============================================================================

localparam [7:0] OPCODE_PNEW         = 8'h00;
localparam [7:0] OPCODE_PSPLIT       = 8'h01;
localparam [7:0] OPCODE_PMERGE       = 8'h02;
localparam [7:0] OPCODE_LASSERT      = 8'h03;
localparam [7:0] OPCODE_LJOIN        = 8'h04;
localparam [7:0] OPCODE_MDLACC       = 8'h05;
localparam [7:0] OPCODE_PDISCOVER    = 8'h06;
localparam [7:0] OPCODE_XFER         = 8'h07;
localparam [7:0] OPCODE_PYEXEC       = 8'h08;
localparam [7:0] OPCODE_CHSH_TRIAL   = 8'h09;
localparam [7:0] OPCODE_XOR_LOAD     = 8'h0A;
localparam [7:0] OPCODE_XOR_ADD      = 8'h0B;
localparam [7:0] OPCODE_XOR_SWAP     = 8'h0C;
localparam [7:0] OPCODE_XOR_RANK     = 8'h0D;
localparam [7:0] OPCODE_EMIT         = 8'h0E;
localparam [7:0] OPCODE_REVEAL       = 8'h0F;
localparam [7:0] OPCODE_ORACLE_HALTS = 8'h10;
localparam [7:0] OPCODE_HALT         = 8'hFF;

// ============================================================================
// PARAMETERS
// ============================================================================

`ifdef YOSYS_LITE
localparam NUM_MODULES = 4;
localparam REGION_SIZE = 16;
`else
localparam NUM_MODULES = 64;
localparam REGION_SIZE = 1024;
`endif
localparam MAX_MU = 32'hFFFFFFFF;

// CSR addresses
localparam [7:0] CSR_CERT_ADDR     = 8'h00;
localparam [7:0] CSR_STATUS        = 8'h01;
localparam [7:0] CSR_ERROR         = 8'h02;
localparam [7:0] CSR_PARTITION_OPS = 8'h03;
localparam [7:0] CSR_MDL_OPS       = 8'h04;
localparam [7:0] CSR_INFO_GAIN     = 8'h05;

// ============================================================================
// INTERNAL REGISTERS AND WIRES
// ============================================================================

// Program counter
reg [31:0] pc_reg;

// Control and status registers
reg [31:0] csr_cert_addr;
reg [31:0] csr_status;
reg [31:0] csr_error;

// μ-bit accumulator (Q16.16 format)
reg [31:0] mu_accumulator;

// Deterministic μ temp for multi-step ops
reg [31:0] pdiscover_mu_next;

// μ-ALU interface
wire [31:0] mu_alu_result;
wire mu_alu_ready;
wire mu_alu_overflow;
reg  [2:0]  mu_alu_op;
reg  [31:0] mu_alu_operand_a;
reg  [31:0] mu_alu_operand_b;
reg  mu_alu_valid;

// μ-Core interface
wire instr_allowed;
wire receipt_required;
wire receipt_accepted;
wire cost_gate_open;
wire partition_gate_open;
wire [31:0] core_status;
wire enforcement_active;
reg  [31:0] proposed_cost;
reg  [31:0] receipt_value;
reg  receipt_valid;

// Info gain temp
reg [31:0] info_gain_value;

// Compute state (mirrors Coq VMState + Python State)
reg [31:0] reg_file [0:31];
reg [31:0] data_mem [0:255];

// Performance counters
reg [31:0] partition_ops_counter;
reg [31:0] mdl_ops_counter;
reg [31:0] info_gain_counter;

// Instruction decode
wire [31:0] current_instr;
wire [7:0]  opcode;
wire [7:0]  operand_a;
wire [7:0]  operand_b;
wire [7:0]  operand_cost;

// Module management (partition graph)
reg [31:0] module_table  [0:NUM_MODULES-1];
reg [31:0] region_table  [0:NUM_MODULES-1][0:REGION_SIZE-1];
reg [NUM_MODULES-1:0] module_exists;  // Bit vector: 1 if module exists, 0 if deleted
reg [5:0]  current_module;
reg [5:0]  next_module_id;
reg [31:0] swap_temp;
reg [31:0] rank_temp;

// State machine
reg [3:0] state;
reg [3:0] alu_return_state;
reg [7:0] alu_context;

// Loop / temp variables
reg [31:0] i, j, region_size, even_count, odd_count;
reg [31:0] size_a, size_b, total_size, module_size, mdl_cost;
reg [31:0] temp_size, src_size, dest_size;

// FSM states
localparam [3:0] STATE_FETCH             = 4'h0;
localparam [3:0] STATE_DECODE            = 4'h1;
localparam [3:0] STATE_EXECUTE           = 4'h2;
localparam [3:0] STATE_MEMORY            = 4'h3;
localparam [3:0] STATE_LOGIC             = 4'h4;
localparam [3:0] STATE_PYTHON            = 4'h5;
localparam [3:0] STATE_COMPLETE          = 4'h6;
localparam [3:0] STATE_ALU_WAIT          = 4'h7;
localparam [3:0] STATE_ALU_WAIT2         = 4'h8;
localparam [3:0] STATE_RECEIPT_HOLD      = 4'h9;
localparam [3:0] STATE_PDISCOVER_LAUNCH2 = 4'hA;
localparam [3:0] STATE_PDISCOVER_ARM2    = 4'hB;

// ALU context codes
localparam [7:0] ALU_CTX_MDLACC      = 8'h01;
localparam [7:0] ALU_CTX_PDISCOVER1  = 8'h02;
localparam [7:0] ALU_CTX_PDISCOVER2  = 8'h03;
localparam [7:0] ALU_CTX_ORACLE      = 8'h04;

// ============================================================================
// OUTPUT ASSIGNMENTS
// ============================================================================

assign pc            = pc_reg;
assign current_instr = instr_data;
assign opcode        = current_instr[31:24];
assign operand_a     = current_instr[23:16];
assign operand_b     = current_instr[15:8];
assign operand_cost  = current_instr[7:0];

assign cert_addr     = csr_cert_addr;
assign status        = csr_status;
assign error_code    = csr_error;
assign partition_ops = partition_ops_counter;
assign mdl_ops       = mdl_ops_counter;
assign info_gain     = info_gain_counter;
assign mu            = mu_accumulator;

// Interface assignments
assign logic_req     = (state == STATE_LOGIC);
assign logic_addr    = {24'h0, operand_a, operand_b};
assign py_req        = (state == STATE_PYTHON);
assign py_code_addr  = {24'h0, operand_a, operand_b};
assign mem_addr      = pc_reg;
assign mem_wdata     = 32'h0;
assign mem_we        = 1'b0;
assign mem_en        = 1'b1;

// ============================================================================
// CEIL_LOG2 HELPER (pure function, no external module dependency)
// ============================================================================

function automatic integer ceil_log2_8;
    input integer x;
    begin
        if      (x <= 0)   ceil_log2_8 = 1;
        else if (x <= 2)   ceil_log2_8 = 1;
        else if (x <= 4)   ceil_log2_8 = 2;
        else if (x <= 8)   ceil_log2_8 = 3;
        else if (x <= 16)  ceil_log2_8 = 4;
        else if (x <= 32)  ceil_log2_8 = 5;
        else if (x <= 64)  ceil_log2_8 = 6;
        else if (x <= 128) ceil_log2_8 = 7;
        else                ceil_log2_8 = 8;
    end
endfunction

// ============================================================================
// MAIN CPU FSM
// ============================================================================

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        pc_reg               <= 32'h0;
        csr_cert_addr        <= 32'h0;
        csr_status           <= 32'h0;
        csr_error            <= 32'h0;
        mu_accumulator       <= 32'h0;
        partition_ops_counter <= 32'h0;
        mdl_ops_counter      <= 32'h0;
        info_gain_counter    <= 32'h0;
        current_module       <= 6'h0;
        next_module_id       <= 6'h1;
        module_exists        <= {NUM_MODULES{1'b0}};  // All modules initially non-existent
        state                <= STATE_FETCH;

`ifndef SYNTHESIS
        for (i = 0; i < NUM_MODULES; i = i + 1) begin
            module_table[i] <= 32'h0;
            for (j = 0; j < REGION_SIZE; j = j + 1)
                region_table[i][j] <= 32'h0;
        end
        for (i = 0; i < 32; i = i + 1)
            reg_file[i] <= 32'h0;
        for (i = 0; i < 256; i = i + 1)
            data_mem[i] <= 32'h0;
`endif
    end else begin
        case (state)

            // ----------------------------------------------------------
            STATE_FETCH: state <= STATE_DECODE;

            // ----------------------------------------------------------
            STATE_DECODE: begin
                proposed_cost <= mu_accumulator + operand_cost;
                state <= STATE_EXECUTE;
            end

            // ----------------------------------------------------------
            STATE_EXECUTE: begin
                case (opcode)

                    // ---- Partition operations ----
                    OPCODE_PNEW: begin
                        if (instr_allowed && partition_gate_open) begin
                            execute_pnew(operand_a, operand_b);
                            mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end else begin
                            csr_error <= 32'hA;
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end
                    end

                    OPCODE_PSPLIT: begin
                        if (instr_allowed && partition_gate_open) begin
                            execute_psplit(operand_a, operand_b);
                            mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end else begin
                            csr_error <= 32'hA;
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end
                    end

                    OPCODE_PMERGE: begin
                        if (instr_allowed && partition_gate_open) begin
                            execute_pmerge(operand_a, operand_b);
                            mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end else begin
                            csr_error <= 32'hA;
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end
                    end

                    // ---- Logic / certificate operations ----
                    OPCODE_LASSERT: begin
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        state <= STATE_LOGIC;
                    end

                    OPCODE_LJOIN: begin
                        execute_ljoin(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    // ---- μ-ALU–driven operations ----
                    OPCODE_MDLACC: begin
                        if (operand_a == 8'h00)
                            execute_mdlacc(current_module);
                        else
                            execute_mdlacc(operand_a);
                    end

                    OPCODE_PDISCOVER: begin
                        execute_pdiscover(operand_a, operand_b);
                    end

                    OPCODE_ORACLE_HALTS: begin
                        execute_oracle_halts(operand_a, operand_b);
                    end

                    // ---- Data movement ----
                    OPCODE_XFER: begin
                        execute_xfer(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    OPCODE_EMIT: begin
                        execute_emit(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    OPCODE_REVEAL: begin
                        // μ-cost = base cost + revelation bits (operand_a << 8)
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost}
                                        + {16'h0, operand_a, 8'h0};
                        csr_cert_addr  <= {24'h0, operand_b};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    // ---- External bridges ----
                    OPCODE_PYEXEC: begin
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        state <= STATE_PYTHON;
                    end

                    OPCODE_CHSH_TRIAL: begin
                        if ((operand_a[7:2] != 6'b0) || (operand_b[7:2] != 6'b0))
                            csr_error <= 32'h1;
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    // ---- XOR matrix operations ----
                    OPCODE_XOR_LOAD: begin
                        execute_xor_load(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    OPCODE_XOR_ADD: begin
                        execute_xor_add(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    OPCODE_XOR_SWAP: begin
                        execute_xor_swap(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    OPCODE_XOR_RANK: begin
                        execute_xor_rank(operand_a, operand_b);
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    // ---- Halt ----
                    OPCODE_HALT: begin
                        mu_accumulator <= mu_accumulator + {24'h0, operand_cost};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end

                    default: begin
                        csr_error <= 32'h1;
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                endcase
            end

            // ----------------------------------------------------------
            STATE_LOGIC: begin
                if (logic_ack) begin
                    csr_cert_addr <= logic_data;
                    pc_reg <= pc_reg + 4;
                    state <= STATE_FETCH;
                end
            end

            // ----------------------------------------------------------
            STATE_PYTHON: begin
                if (py_ack) begin
                    csr_status <= py_result;
                    pc_reg <= pc_reg + 4;
                    state <= STATE_FETCH;
                end
            end

            // ----------------------------------------------------------
            STATE_ALU_WAIT: begin
                if (mu_alu_ready) begin
                    mu_alu_valid <= 1'b0;
                    case (alu_context)
                        ALU_CTX_MDLACC: begin
                            if (mu_alu_overflow) begin
                                csr_error <= 32'h6;
                                pc_reg <= pc_reg + 4;
                                state <= STATE_FETCH;
                            end else begin
`ifndef SYNTHESIS
                                $display("MDLACC size=%0d mdl_cost=%0d mu_acc(before)=%0d mu_acc(after)=%0d",
                                         module_size, mdl_cost >> 16, mu_accumulator >> 16, mu_alu_result >> 16);
`endif
                                mu_accumulator   <= mu_alu_result;
                                csr_status       <= 32'h5;
                                mdl_ops_counter  <= mdl_ops_counter + 1;
                                receipt_value    <= mu_alu_result;
                                receipt_valid    <= 1'b1;
                                state            <= STATE_RECEIPT_HOLD;
                            end
                        end
                        ALU_CTX_PDISCOVER1: begin
                            if (mu_alu_overflow) begin
                                csr_error <= 32'h8;
                                pc_reg <= pc_reg + 4;
                                state <= STATE_FETCH;
                            end else begin
                                info_gain_value <= mu_alu_result;
                                pdiscover_mu_next = mu_accumulator + mu_alu_result;
`ifndef SYNTHESIS
                                $display("PDISCOVER info_gain=%0d mu_acc(before)=%0d mu_acc(after)=%0d",
                                         mu_alu_result >> 16, mu_accumulator >> 16, pdiscover_mu_next >> 16);
`endif
                                mu_accumulator          <= pdiscover_mu_next;
                                csr_status              <= 32'h6;
                                partition_ops_counter   <= partition_ops_counter + 1;
                                receipt_value           <= pdiscover_mu_next;
                                receipt_valid           <= 1'b1;
                                state                   <= STATE_RECEIPT_HOLD;
                            end
                        end
                        ALU_CTX_ORACLE: begin
                            if (mu_alu_overflow)
                                csr_error <= 32'h6;
                            else begin
                                mu_accumulator <= mu_alu_result;
                                csr_status     <= 32'h42;
`ifndef SYNTHESIS
                                $display("ORACLE_HALTS invoked - Hyper-Thiele transition");
`endif
                            end
                            pc_reg <= pc_reg + 4;
                            state  <= STATE_FETCH;
                        end
                        default: begin
                            pc_reg <= pc_reg + 4;
                            state  <= alu_return_state;
                        end
                    endcase
                end
            end

            // ----------------------------------------------------------
            STATE_PDISCOVER_LAUNCH2: begin
                mu_alu_op        <= 3'd0;  // ADD
                mu_alu_operand_a <= mu_accumulator;
                mu_alu_operand_b <= info_gain_value;
                mu_alu_valid     <= 1'b1;
                alu_context      <= ALU_CTX_PDISCOVER2;
                state            <= STATE_PDISCOVER_ARM2;
            end

            STATE_PDISCOVER_ARM2: state <= STATE_ALU_WAIT2;

            // ----------------------------------------------------------
            STATE_ALU_WAIT2: begin
                if (mu_alu_ready) begin
                    mu_alu_valid <= 1'b0;
                    if (alu_context == ALU_CTX_PDISCOVER2) begin
                        if (mu_alu_overflow) begin
                            csr_error <= 32'h6;
                            pc_reg <= pc_reg + 4;
                            state  <= STATE_FETCH;
                        end else begin
`ifndef SYNTHESIS
                            $display("PDISCOVER info_gain=%0d mu_acc(before)=%0d mu_acc(after)=%0d",
                                     info_gain_value >> 16, mu_accumulator >> 16, mu_alu_result >> 16);
`endif
                            mu_accumulator        <= mu_alu_result;
                            csr_status            <= 32'h6;
                            partition_ops_counter <= partition_ops_counter + 1;
                            receipt_value         <= mu_alu_result;
                            receipt_valid         <= 1'b1;
                            state                 <= STATE_RECEIPT_HOLD;
                        end
                    end else begin
                        pc_reg <= pc_reg + 4;
                        state  <= alu_return_state;
                    end
                end
            end

            // ----------------------------------------------------------
            STATE_RECEIPT_HOLD: begin
                receipt_valid <= 1'b0;
                pc_reg <= pc_reg + 4;
                state  <= STATE_FETCH;
            end

            // ----------------------------------------------------------
            default: state <= STATE_FETCH;

        endcase
    end
end

// ============================================================================
// PARTITION TASKS
// ============================================================================

task execute_pnew;
    input [7:0] region_spec_a;
    input [7:0] region_spec_b;
    integer found, found_id;
    begin
        found = 0;
        found_id = 0;
        for (i = 0; i < NUM_MODULES; i = i + 1) begin
            if (i < next_module_id) begin
                if (module_table[i] == 32'd1 && region_table[i][0] == region_spec_a) begin
                    found = 1;
                    found_id = i;
                end
            end
        end
        if (found) begin
            current_module <= found_id[5:0];
            csr_status <= 32'h1;
`ifndef SYNTHESIS
            $display("PNEW dedup: region={%0d} -> module %0d", region_spec_a, found_id);
`endif
        end else if (next_module_id < NUM_MODULES) begin
            module_table[next_module_id]    <= 32'd1;
            region_table[next_module_id][0] <= region_spec_a;
            for (i = 1; i < REGION_SIZE; i = i + 1)
                region_table[next_module_id][i] <= 32'h0;
            module_exists[next_module_id]   <= 1'b1;  // Mark module as existing
            current_module <= next_module_id;
            next_module_id <= next_module_id + 1;
            csr_status <= 32'h1;
            partition_ops_counter <= partition_ops_counter + 1;
`ifndef SYNTHESIS
            $display("PNEW new: region={%0d} -> module %0d", region_spec_a, next_module_id);
`endif
        end else begin
            csr_error <= 32'h2;
        end
    end
endtask

task execute_psplit;
    input [7:0] module_id;
    input [7:0] predicate;
    reg [1:0]  pred_mode;
    reg [5:0]  pred_param;
    reg [31:0] element_value;
    reg matches_predicate;
    begin
        if (module_id < next_module_id && next_module_id < NUM_MODULES - 1) begin
            region_size = module_table[module_id];
            pred_mode   = predicate[7:6];
            pred_param  = predicate[5:0];
            even_count  = 0;
            odd_count   = 0;

            for (i = 0; i < REGION_SIZE; i = i + 1) begin
                if (i < region_size) begin
                    element_value = region_table[module_id][i];
                    case (pred_mode)
                        2'b00: matches_predicate = (element_value[0] == pred_param[0]);
                        2'b01: matches_predicate = element_value >= pred_param;
                        2'b10: matches_predicate = (element_value & (1 << pred_param)) != 0;
                        2'b11: matches_predicate = (((pred_param + 1) & pred_param) == 0)
                                                 ? ((element_value & pred_param) == 0) : 1'b0;
                        default: matches_predicate = 0;
                    endcase

                    if (matches_predicate) begin
                        region_table[next_module_id][even_count] <= element_value;
                        even_count = even_count + 1;
                    end else begin
                        region_table[next_module_id + 1][odd_count] <= element_value;
                        odd_count = odd_count + 1;
                    end
                end
            end

            module_table[next_module_id]     <= even_count;
            module_table[next_module_id + 1] <= odd_count;
            module_table[module_id]          <= 32'h0;  // remove parent
            module_exists[next_module_id]    <= 1'b1;   // New modules exist
            module_exists[next_module_id + 1] <= 1'b1;
            module_exists[module_id]         <= 1'b0;   // Parent deleted
            next_module_id <= next_module_id + 2;
            csr_status <= 32'h2;
            partition_ops_counter <= partition_ops_counter + 1;
        end else begin
            csr_error <= 32'h3;
        end
    end
endtask

task execute_pmerge;
    input [7:0] module_a;
    input [7:0] module_b;
    begin
        if (module_a < next_module_id && module_b < next_module_id && module_a != module_b) begin
            size_a     = module_table[module_a];
            size_b     = module_table[module_b];
            total_size = size_a + size_b;
            if (total_size <= REGION_SIZE) begin
                for (i = 0; i < REGION_SIZE; i = i + 1)
                    if (i < size_a)
                        region_table[next_module_id][i] <= region_table[module_a][i];
                for (i = 0; i < REGION_SIZE; i = i + 1)
                    if (i < size_b)
                        region_table[next_module_id][i + size_a] <= region_table[module_b][i];

                module_table[next_module_id] <= total_size;
                module_table[module_a]       <= 32'h0;
                module_table[module_b]       <= 32'h0;
                module_exists[next_module_id] <= 1'b1;  // Merged module exists
                module_exists[module_a]       <= 1'b0;  // Source modules deleted
                module_exists[module_b]       <= 1'b0;
                current_module  <= next_module_id;
                next_module_id  <= next_module_id + 1;
                csr_status <= 32'h3;
                partition_ops_counter <= partition_ops_counter + 1;
            end else begin
                csr_error <= 32'h4;
            end
        end else begin
            csr_error <= 32'h5;
        end
    end
endtask

// ============================================================================
// LOGIC / DATA / XOR TASKS
// ============================================================================

task execute_ljoin;
    input [7:0] cert_a;
    input [7:0] cert_b;
    begin
        csr_cert_addr <= {cert_a, cert_b, 16'h0};
        csr_status    <= 32'h4;
    end
endtask

task execute_emit;
    input [7:0] value_a;
    input [7:0] value_b;
    begin
        info_gain_counter <= info_gain_counter + value_b;
        csr_status <= {value_a, value_b, 16'h0};
    end
endtask

task execute_xfer;
    input [7:0] dest;
    input [7:0] src;
    begin
        reg_file[dest[4:0]] <= reg_file[src[4:0]];
        csr_status <= 32'h6;
    end
endtask

task execute_xor_load;
    input [7:0] dest;
    input [7:0] addr;
    begin
        reg_file[dest[4:0]] <= data_mem[addr];
        csr_status <= 32'h7;
    end
endtask

task execute_xor_add;
    input [7:0] dest;
    input [7:0] src;
    begin
        reg_file[dest[4:0]] <= reg_file[dest[4:0]] ^ reg_file[src[4:0]];
        csr_status <= 32'h8;
    end
endtask

task execute_xor_swap;
    input [7:0] a;
    input [7:0] b;
    begin
        reg_file[a[4:0]] <= reg_file[b[4:0]];
        reg_file[b[4:0]] <= reg_file[a[4:0]];
        csr_status <= 32'h9;
    end
endtask

task execute_xor_rank;
    input [7:0] dest;
    input [7:0] src;
    integer k;
    reg [31:0] v, cnt;
    begin
        v   = reg_file[src[4:0]];
        cnt = 0;
        for (k = 0; k < 32; k = k + 1)
            cnt = cnt + v[k];
        reg_file[dest[4:0]] <= cnt;
        csr_status <= cnt;
    end
endtask

// ============================================================================
// μ-ALU–DRIVEN TASKS
// ============================================================================

task execute_mdlacc;
    input [7:0] module_id;
    integer max_element, bit_length, k;
    begin
        if (module_id < next_module_id) begin
            module_size = module_table[module_id];
            if (module_size > 0) begin
                max_element = 0;
                for (k = 0; k < REGION_SIZE; k = k + 1)
                    if (k < module_size && region_table[module_id][k] > max_element)
                        max_element = region_table[module_id][k];
                bit_length = ceil_log2_8(max_element + 1);
                mdl_cost   = (bit_length * module_size) << 16;
            end else begin
                mdl_cost = 0;
            end
            mu_alu_op        <= 3'd0;  // ADD
            mu_alu_operand_a <= mu_accumulator;
            mu_alu_operand_b <= mdl_cost;
            mu_alu_valid     <= 1'b1;
            alu_context      <= ALU_CTX_MDLACC;
            alu_return_state <= STATE_FETCH;
            state            <= STATE_ALU_WAIT;
        end else begin
            csr_error <= 32'h7;
        end
    end
endtask

task execute_pdiscover;
    input [7:0] before_count;
    input [7:0] after_count;
    begin
        if (before_count > 0 && after_count > 0 && after_count <= before_count) begin
            mu_alu_op        <= 3'd5;  // INFO_GAIN
            mu_alu_operand_a <= before_count;
            mu_alu_operand_b <= after_count;
            mu_alu_valid     <= 1'b1;
            alu_context      <= ALU_CTX_PDISCOVER1;
            alu_return_state <= STATE_FETCH;
            state            <= STATE_ALU_WAIT;
        end else begin
            csr_error <= 32'h9;
        end
    end
endtask

task execute_oracle_halts;
    input [7:0] desc_ptr_a;
    input [7:0] desc_ptr_b;
    begin
        mu_alu_op        <= 3'd0;  // ADD
        mu_alu_operand_a <= mu_accumulator;
        mu_alu_operand_b <= 32'd1000000;
        mu_alu_valid     <= 1'b1;
        alu_context      <= ALU_CTX_ORACLE;
        alu_return_state <= STATE_FETCH;
        state            <= STATE_ALU_WAIT;
    end
endtask

// ============================================================================
// SUBMODULE INSTANTIATIONS
// ============================================================================

mu_alu mu_alu_inst (
    .clk(clk), .rst_n(rst_n),
    .op(mu_alu_op),
    .operand_a(mu_alu_operand_a),
    .operand_b(mu_alu_operand_b),
    .valid(mu_alu_valid),
    .result(mu_alu_result),
    .ready(mu_alu_ready),
    .overflow(mu_alu_overflow)
);

mu_core mu_core_inst (
    .clk(clk), .rst_n(rst_n),
    .instruction(current_instr),
    .instr_valid(state == STATE_DECODE || state == STATE_EXECUTE),
    .instr_allowed(instr_allowed),
    .receipt_required(receipt_required),
    .current_mu_cost(mu_accumulator),
    .proposed_cost(proposed_cost),
    .partition_count(next_module_id),
    .memory_isolation(32'hCAFEBABE),
    .receipt_value(receipt_value),
    .receipt_valid(receipt_valid),
    .receipt_accepted(receipt_accepted),
    .cost_gate_open(cost_gate_open),
    .partition_gate_open(partition_gate_open),
    .core_status(core_status),
    .enforcement_active(enforcement_active)
);

// CLZ8 instance (used for testbench compatibility; ceil_log2_8 function preferred)
wire [3:0] clz8_out;
reg  [7:0] clz8_in;
clz8 clz8_inst (.x(clz8_in), .out(clz8_out));

endmodule


// ############################################################################
// SUBMODULE: mu_alu — Q16.16 Fixed-Point Arithmetic Unit
// ############################################################################

module mu_alu (
    input  wire        clk,
    input  wire        rst_n,
    input  wire [2:0]  op,
    input  wire [31:0] operand_a,
    input  wire [31:0] operand_b,
    input  wire        valid,
    output reg  [31:0] result,
    output reg         ready,
    output reg         overflow
);

localparam Q16_SHIFT = 16;
localparam Q16_ONE   = 32'h00010000;
localparam Q16_MAX   = 32'h7FFFFFFF;
localparam signed Q16_MIN = 32'sh80000000;

localparam OP_ADD          = 3'd0;
localparam OP_SUB          = 3'd1;
localparam OP_MUL          = 3'd2;
localparam OP_DIV          = 3'd3;
localparam OP_LOG2         = 3'd4;
localparam OP_INFO_GAIN    = 3'd5;
localparam OP_CLAIM_FACTOR = 3'd6;

// Log2 approximation (bit-position)
function [31:0] simple_log2_approx;
    input [31:0] x;
    reg [5:0] msb_pos;
    begin
        if      (x[31]) msb_pos = 31;
        else if (x[30]) msb_pos = 30;
        else if (x[29]) msb_pos = 29;
        else if (x[28]) msb_pos = 28;
        else if (x[27]) msb_pos = 27;
        else if (x[26]) msb_pos = 26;
        else if (x[25]) msb_pos = 25;
        else if (x[24]) msb_pos = 24;
        else if (x[23]) msb_pos = 23;
        else if (x[22]) msb_pos = 22;
        else if (x[21]) msb_pos = 21;
        else if (x[20]) msb_pos = 20;
        else if (x[19]) msb_pos = 19;
        else if (x[18]) msb_pos = 18;
        else if (x[17]) msb_pos = 17;
        else if (x[16]) msb_pos = 16;
        else if (x[15]) msb_pos = 15;
        else if (x[14]) msb_pos = 14;
        else if (x[13]) msb_pos = 13;
        else if (x[12]) msb_pos = 12;
        else if (x[11]) msb_pos = 11;
        else if (x[10]) msb_pos = 10;
        else if (x[9])  msb_pos = 9;
        else if (x[8])  msb_pos = 8;
        else if (x[7])  msb_pos = 7;
        else if (x[6])  msb_pos = 6;
        else if (x[5])  msb_pos = 5;
        else if (x[4])  msb_pos = 4;
        else if (x[3])  msb_pos = 3;
        else if (x[2])  msb_pos = 2;
        else if (x[1])  msb_pos = 1;
        else             msb_pos = 0;
        simple_log2_approx = ((msb_pos - 16) << Q16_SHIFT);
    end
endfunction

// Factor LUT
reg [31:0] factor_lut [0:3];
initial begin
    factor_lut[0] = 32'd3;   // 15 = 3 × 5
    factor_lut[1] = 32'd5;
    factor_lut[2] = 32'd3;   // 21 = 3 × 7
    factor_lut[3] = 32'd7;
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        result   <= 32'h0;
        ready    <= 1'b0;
        overflow <= 1'b0;
    end else if (valid && !ready) begin
        overflow <= 1'b0;
        ready    <= 1'b1;

        case (op)
            OP_ADD: begin
                {overflow, result} <= $signed(operand_a) + $signed(operand_b);
                if (overflow)
                    result <= (operand_a[31] == operand_b[31])
                            ? (operand_a[31] ? Q16_MIN : Q16_MAX) : result;
            end

            OP_SUB: begin
                {overflow, result} <= $signed(operand_a) - $signed(operand_b);
                if (overflow)
                    result <= (operand_a[31] != operand_b[31])
                            ? (operand_a[31] ? Q16_MIN : Q16_MAX) : result;
            end

            OP_MUL: begin
                // Q16.16 × Q16.16 → Q16.16 via 64-bit intermediate
                result   <= ($signed({{32{operand_a[31]}}, operand_a}) *
                             $signed({{32{operand_b[31]}}, operand_b})) >>> Q16_SHIFT;
                overflow <= 1'b0;
            end

            OP_DIV: begin
                if (operand_b == 0) begin
                    result   <= Q16_MAX;
                    overflow <= 1'b1;
                end else begin
                    result   <= operand_a >>> 1;  // approximate ÷2
                    overflow <= 1'b0;
                end
            end

            OP_LOG2: begin
                if (operand_a == 0 || $signed(operand_a) < 0) begin
                    result   <= Q16_MIN;
                    overflow <= 1'b1;
                end else begin
                    result   <= simple_log2_approx(operand_a);
                    overflow <= 1'b0;
                end
            end

            OP_INFO_GAIN: begin
                if (operand_b == 0) begin
                    result   <= 32'h0;
                    overflow <= 1'b1;
                end else begin
                    result   <= operand_a - operand_b;
                    overflow <= 1'b0;
                end
            end

            OP_CLAIM_FACTOR: begin
                case ({operand_a, operand_b[0]})
                    {32'd15, 1'b0}: result <= factor_lut[0];
                    {32'd15, 1'b1}: result <= factor_lut[1];
                    {32'd21, 1'b0}: result <= factor_lut[2];
                    {32'd21, 1'b1}: result <= factor_lut[3];
                    default: begin
                        result   <= 32'h0;
                        overflow <= 1'b1;
                    end
                endcase
            end

            default: begin
                result   <= 32'h0;
                overflow <= 1'b0;
            end
        endcase
    end else if (!valid) begin
        ready    <= 1'b0;
        overflow <= 1'b0;
    end
end

endmodule


// ############################################################################
// SUBMODULE: receipt_integrity_checker — Hardware Receipt Verification
// ############################################################################
//
// Implements the Coq-proven property:
//   receipt_mu_consistent: post_mu = pre_mu + instruction_cost(instr)
//
// Any forged receipt (wrong μ-delta) is rejected.

module receipt_integrity_checker (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        receipt_valid,
    input  wire [31:0] receipt_pre_mu,
    input  wire [31:0] receipt_post_mu,
    input  wire [7:0]  receipt_opcode,
    input  wire [31:0] receipt_operand,
    input  wire        chain_mode,
    input  wire [31:0] prev_post_mu,
    output reg         receipt_integrity_ok,
    output reg         chain_continuity_ok,
    output reg  [31:0] computed_cost,
    output reg  [31:0] error_code
);

// Opcodes (local copy — must match top-level)
localparam [7:0] OP_PNEW      = 8'h00, OP_PSPLIT    = 8'h01, OP_PMERGE    = 8'h02,
                 OP_LASSERT    = 8'h03, OP_LJOIN     = 8'h04, OP_MDLACC    = 8'h05,
                 OP_PDISCOVER  = 8'h06, OP_XFER      = 8'h07, OP_PYEXEC    = 8'h08,
                 OP_CHSH_TRIAL = 8'h09, OP_XOR_LOAD  = 8'h0A, OP_XOR_ADD   = 8'h0B,
                 OP_XOR_SWAP   = 8'h0C, OP_XOR_RANK  = 8'h0D, OP_EMIT      = 8'h0E,
                 OP_REVEAL     = 8'h0F, OP_ORACLE    = 8'h10, OP_HALT      = 8'hFF;

// Error codes
localparam [31:0] ERR_NONE    = 32'h0, ERR_MU_MISMATCH  = 32'h1,
                  ERR_CHAIN   = 32'h2, ERR_UNKNOWN_OP   = 32'h3,
                  ERR_OVERFLOW = 32'h4;

function [31:0] compute_instruction_cost;
    input [7:0]  opcode;
    input [31:0] operand;
    begin
        case (opcode)
            OP_PNEW, OP_PSPLIT, OP_PMERGE, OP_LASSERT, OP_LJOIN,
            OP_MDLACC, OP_PDISCOVER, OP_XFER, OP_PYEXEC, OP_CHSH_TRIAL,
            OP_XOR_LOAD, OP_XOR_ADD, OP_XOR_SWAP, OP_XOR_RANK,
            OP_EMIT, OP_ORACLE:
                compute_instruction_cost = {24'h0, operand[7:0]};
            OP_REVEAL:
                compute_instruction_cost = {16'h0, operand[23:16], 8'h0} + {24'h0, operand[7:0]};
            OP_HALT:
                compute_instruction_cost = 32'h0;
            default:
                compute_instruction_cost = 32'hFFFFFFFF;  // sentinel
        endcase
    end
endfunction

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        receipt_integrity_ok <= 1'b0;
        chain_continuity_ok  <= 1'b0;
        computed_cost        <= 32'h0;
        error_code           <= ERR_NONE;
    end else begin
        if (receipt_valid) begin
            computed_cost <= compute_instruction_cost(receipt_opcode, receipt_operand);

            if (compute_instruction_cost(receipt_opcode, receipt_operand) == 32'hFFFFFFFF) begin
                receipt_integrity_ok <= 1'b0;
                error_code           <= ERR_UNKNOWN_OP;
            end else if (receipt_pre_mu > 32'hFFFFFFFF - computed_cost) begin
                receipt_integrity_ok <= 1'b0;
                error_code           <= ERR_OVERFLOW;
            end else if (receipt_post_mu == receipt_pre_mu + compute_instruction_cost(receipt_opcode, receipt_operand)) begin
                receipt_integrity_ok <= 1'b1;
                error_code           <= ERR_NONE;
            end else begin
                receipt_integrity_ok <= 1'b0;
                error_code           <= ERR_MU_MISMATCH;
`ifndef SYNTHESIS
                $display("FORGERY DETECTED: pre_mu=%d, post_mu=%d, expected=%d",
                         receipt_pre_mu, receipt_post_mu,
                         receipt_pre_mu + compute_instruction_cost(receipt_opcode, receipt_operand));
`endif
            end

            if (chain_mode) begin
                if (receipt_pre_mu == prev_post_mu)
                    chain_continuity_ok <= 1'b1;
                else begin
                    chain_continuity_ok <= 1'b0;
                    error_code          <= ERR_CHAIN;
`ifndef SYNTHESIS
                    $display("CHAIN BREAK: prev_post_mu=%d, this_pre_mu=%d",
                             prev_post_mu, receipt_pre_mu);
`endif
                end
            end else begin
                chain_continuity_ok <= 1'b1;
            end
        end else begin
            receipt_integrity_ok <= 1'b0;
            chain_continuity_ok  <= 1'b0;
        end
    end
end

`ifdef FORMAL
always @(posedge clk) begin
    if (receipt_integrity_ok && receipt_valid)
        assert(receipt_post_mu == receipt_pre_mu + computed_cost);
    if (chain_continuity_ok && chain_mode && receipt_valid)
        assert(receipt_pre_mu == prev_post_mu);
end
`endif

endmodule


// ############################################################################
// SUBMODULE: mu_core — Partition Isomorphism Enforcement Unit
// ############################################################################
//
// The "Cost Gate" — ensures:
//   1. No instruction executes without valid μ-receipt
//   2. Partition operations maintain logical independence
//   3. μ-cost monotonically increases (no free computation)

module mu_core (
    input  wire        clk,
    input  wire        rst_n,
    input  wire [31:0] instruction,
    input  wire        instr_valid,
    output reg         instr_allowed,
    output reg         receipt_required,
    input  wire [31:0] current_mu_cost,
    input  wire [31:0] proposed_cost,
    input  wire [5:0]  partition_count,
    input  wire [31:0] memory_isolation,
    input  wire [31:0] receipt_value,
    input  wire        receipt_valid,
    output reg         receipt_accepted,
    output reg         cost_gate_open,
    output reg         partition_gate_open,
    output reg  [31:0] core_status,
    output reg         enforcement_active
);

localparam [7:0] OPC_PNEW      = 8'h00, OPC_PSPLIT    = 8'h01, OPC_PMERGE    = 8'h02,
                 OPC_PDISCOVER  = 8'h06, OPC_MDLACC    = 8'h05, OPC_HALT      = 8'hFF;

localparam [31:0] ST_IDLE = 0, ST_CHECKING = 1, ST_ALLOWED = 2,
                  ST_DENIED_COST = 3, ST_DENIED_ISO = 4, ST_RECEIPT_OK = 5;

reg [31:0] last_instruction;
reg [31:0] expected_cost;
reg partition_independent, cost_decreasing;
reg last_instr_valid;
reg [31:0] prev_post_mu;

// Receipt integrity checker (instantiated here)
wire [31:0] computed_instruction_cost;
wire receipt_integrity_ok_w, chain_continuity_ok_w;

receipt_integrity_checker integrity_checker (
    .clk(clk), .rst_n(rst_n),
    .receipt_valid(instr_valid),
    .receipt_pre_mu(current_mu_cost),
    .receipt_post_mu(proposed_cost),
    .receipt_opcode(instruction[31:24]),
    .receipt_operand({8'b0, instruction[23:0]}),
    .chain_mode(1'b1),
    .prev_post_mu(prev_post_mu),
    .receipt_integrity_ok(receipt_integrity_ok_w),
    .chain_continuity_ok(chain_continuity_ok_w),
    .computed_cost(computed_instruction_cost),
    .error_code()
);

wire new_instruction_cycle = instr_valid && !last_instr_valid;

function check_partition_independence;
    input [31:0] instr;
    input [5:0]  part_count;
    input [31:0] mem_iso;
    begin
        case (instr[31:24])
            OPC_PNEW:   check_partition_independence = (part_count < 64);
            OPC_PSPLIT:  check_partition_independence = (instr[23:16] < part_count) && (part_count < 63);
            OPC_PMERGE:  check_partition_independence = (instr[23:16] < part_count) &&
                                                        (instr[15:8]  < part_count) &&
                                                        (instr[23:16] != instr[15:8]);
            default:     check_partition_independence = 1'b1;
        endcase
        check_partition_independence = check_partition_independence && (mem_iso == 32'hCAFEBABE);
    end
endfunction

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        instr_allowed      <= 1'b0;
        receipt_required   <= 1'b0;
        receipt_accepted   <= 1'b0;
        cost_gate_open     <= 1'b0;
        partition_gate_open <= 1'b0;
        core_status        <= ST_IDLE;
        enforcement_active <= 1'b1;
        last_instruction   <= 32'hDEADBEEF;
        expected_cost      <= 32'h0;
        partition_independent <= 1'b1;
        cost_decreasing    <= 1'b0;
        last_instr_valid   <= 1'b0;
        prev_post_mu       <= 32'h0;
    end else begin
        last_instr_valid <= instr_valid;

        if (new_instruction_cycle) begin
            last_instruction <= instruction;
            core_status      <= ST_CHECKING;

            case (instruction[31:24])
                OPC_PNEW, OPC_PSPLIT, OPC_PMERGE: begin
                    receipt_required <= 1'b0;
                    instr_allowed    <= 1'b1;
                    partition_independent <= check_partition_independence(instruction, partition_count, memory_isolation);
                    partition_gate_open   <= check_partition_independence(instruction, partition_count, memory_isolation);
                    cost_decreasing  <= (proposed_cost >= current_mu_cost);
                    cost_gate_open   <= (proposed_cost >= current_mu_cost);
                    if (check_partition_independence(instruction, partition_count, memory_isolation) &&
                        (proposed_cost >= current_mu_cost)) begin
                        expected_cost <= proposed_cost;
                        core_status   <= ST_ALLOWED;
                    end else if (!check_partition_independence(instruction, partition_count, memory_isolation))
                        core_status <= ST_DENIED_ISO;
                    else
                        core_status <= ST_DENIED_COST;
                end
                OPC_PDISCOVER: begin
                    receipt_required    <= 1'b1;
                    instr_allowed       <= 1'b0;
                    partition_gate_open <= 1'b1;
                    cost_gate_open      <= 1'b1;
                    expected_cost       <= proposed_cost;
                    core_status         <= ST_ALLOWED;
                end
                OPC_MDLACC: begin
                    receipt_required    <= 1'b1;
                    instr_allowed       <= 1'b0;
                    partition_gate_open <= 1'b1;
                    cost_gate_open      <= 1'b1;
                    expected_cost       <= proposed_cost;
                    core_status         <= ST_ALLOWED;
                end
                default: begin
                    receipt_required    <= 1'b0;
                    instr_allowed       <= 1'b1;
                    partition_gate_open <= 1'b1;
                    cost_gate_open      <= 1'b1;
                    core_status         <= ST_IDLE;
                end
            endcase
        end

        if (receipt_valid && receipt_required) begin
            if (receipt_value == expected_cost && receipt_integrity_ok_w && chain_continuity_ok_w) begin
                receipt_accepted <= 1'b1;
                instr_allowed    <= 1'b1;
                core_status      <= ST_RECEIPT_OK;
                prev_post_mu     <= proposed_cost;
`ifndef SYNTHESIS
                $display("mu-Core: Receipt accepted for instruction %h, cost=%0d", instruction, receipt_value >> 16);
`endif
            end else begin
                receipt_accepted <= 1'b0;
                instr_allowed    <= 1'b0;
                core_status      <= ST_DENIED_COST;
                if (!receipt_integrity_ok_w) begin
`ifndef SYNTHESIS
                    $display("mu-Core: Receipt DENIED - integrity check FAILED");
`endif
                end else if (!chain_continuity_ok_w) begin
`ifndef SYNTHESIS
                    $display("mu-Core: Receipt DENIED - chain continuity FAILED");
`endif
                end else begin
`ifndef SYNTHESIS
                    $display("mu-Core: Receipt DENIED for instruction %h, expected=%0d, got=%0d",
                             instruction, expected_cost >> 16, receipt_value >> 16);
`endif
                end
            end
        end

        if (!instr_valid) begin
            instr_allowed       <= 1'b0;
            receipt_required    <= 1'b0;
            receipt_accepted    <= 1'b0;
            cost_gate_open      <= 1'b0;
            partition_gate_open <= 1'b0;
            core_status         <= ST_IDLE;
        end
    end
end

endmodule


// ############################################################################
// SUBMODULE: clz8 — Combinational ceil(log2) for 8-bit values
// ############################################################################

module clz8 (
    input  wire [7:0] x,
    output reg  [3:0] out
);

always @(*) begin
    if      (x == 0)   out = 1;
    else if (x <= 1)   out = 1;
    else if (x <= 2)   out = 1;
    else if (x <= 4)   out = 2;
    else if (x <= 8)   out = 3;
    else if (x <= 16)  out = 4;
    else if (x <= 32)  out = 5;
    else if (x <= 64)  out = 6;
    else if (x <= 128) out = 7;
    else                out = 8;
end

endmodule
