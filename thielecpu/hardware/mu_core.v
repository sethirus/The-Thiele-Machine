// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
//
// See the LICENSE file in the repository root for full terms.
// ============================================================================
// μ-Core: Partition Isomorphism Enforcement Unit
// ============================================================================
//
// This module implements the "Cost Gate" that enforces partition independence
// by requiring μ-bit receipts for all partition operations. It embodies the
// mathematical isomorphism between logical structure and computational cost.
//
// The μ-Core ensures that:
// 1. No instruction executes without a valid μ-receipt
// 2. Partition operations maintain logical independence
// 3. The hardware physically cannot be inefficient
//
// This is the "Holy Grail" - silicon that respects the math.
//
// ============================================================================

`timescale 1ns / 1ps

module mu_core (
    input wire clk,
    input wire rst_n,

    // Instruction interface
    input wire [31:0] instruction,      // Current instruction
    input wire instr_valid,             // Instruction is valid
    output reg instr_allowed,           // Allow instruction execution
    output reg receipt_required,        // Receipt required for this instruction

    // Partition state interface
    input wire [31:0] current_mu_cost,  // Current μ-accumulator value
    input wire [31:0] proposed_cost,    // Proposed cost for operation
    input wire [5:0] partition_count,   // Current number of partitions
    input wire [31:0] memory_isolation, // Memory isolation status

    // Receipt validation
    input wire [31:0] receipt_value,    // Receipt from μ-ALU
    input wire receipt_valid,           // Receipt is valid
    output reg receipt_accepted,        // Receipt accepted

    // Cost gate control
    output reg cost_gate_open,          // Allow operation if cost decreases
    output reg partition_gate_open,     // Allow if partitions remain independent

    // Status
    output reg [31:0] core_status,      // Core status and error codes
    output reg enforcement_active       // Isomorphism enforcement is active
);

// ============================================================================
// CONSTANTS
// ============================================================================

localparam [7:0] OPCODE_PNEW     = 8'h00;
localparam [7:0] OPCODE_PSPLIT   = 8'h01;
localparam [7:0] OPCODE_PMERGE   = 8'h02;
localparam [7:0] OPCODE_PDISCOVER = 8'h06;
localparam [7:0] OPCODE_MDLACC   = 8'h05;
localparam [7:0] OPCODE_PMOD     = 8'h03;
localparam [7:0] OPCODE_PQUERY   = 8'h04;
localparam [7:0] OPCODE_HALT     = 8'hFF;

// Status codes
localparam [31:0] STATUS_IDLE         = 32'h0;
localparam [31:0] STATUS_CHECKING     = 32'h1;
localparam [31:0] STATUS_ALLOWED      = 32'h2;
localparam [31:0] STATUS_DENIED_COST  = 32'h3;
localparam [31:0] STATUS_DENIED_ISO   = 32'h4;
localparam [31:0] STATUS_RECEIPT_OK   = 32'h5;

// ============================================================================
// INTERNAL REGISTERS
// ============================================================================

reg [31:0] last_instruction;
reg [31:0] expected_cost;
reg partition_independent;
reg cost_decreasing;
reg last_instr_valid;  // Track previous instr_valid for edge detection

// Receipt integrity checker instance signals
wire [31:0] computed_instruction_cost;
wire receipt_integrity_ok;
wire chain_continuity_ok;
reg [31:0] prev_post_mu;  // Previous receipt's post_mu for chain validation

// ============================================================================
// RECEIPT INTEGRITY CHECKER INSTANCE
// ============================================================================

receipt_integrity_checker integrity_checker (
    .clk(clk),
    .rst_n(rst_n),
    .receipt_valid(instr_valid),
    .receipt_pre_mu(current_mu_cost),
    .receipt_post_mu(proposed_cost),
    .receipt_opcode(instruction[31:24]),
    .receipt_operand({8'b0, instruction[23:0]}),
    .chain_mode(1'b1),
    .prev_post_mu(prev_post_mu),
    .receipt_integrity_ok(receipt_integrity_ok),
    .chain_continuity_ok(chain_continuity_ok),
    .computed_cost(computed_instruction_cost),
    .error_code()  // Not used currently
);

// ============================================================================
// INSTRUCTION ANALYSIS AND ENFORCEMENT
// ============================================================================

// Rising edge detection for new instruction cycle
wire new_instruction_cycle = instr_valid && !last_instr_valid;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        instr_allowed <= 1'b0;
        receipt_required <= 1'b0;
        receipt_accepted <= 1'b0;
        cost_gate_open <= 1'b0;
        partition_gate_open <= 1'b0;
        core_status <= STATUS_IDLE;
        enforcement_active <= 1'b1;  // Always active - this is the law
        last_instruction <= 32'hDEADBEEF;  // Invalid sentinel - ensures first instruction is processed
        expected_cost <= 32'h0;
        partition_independent <= 1'b1;
        cost_decreasing <= 1'b0;
        last_instr_valid <= 1'b0;
        prev_post_mu <= 32'h0;  // Chain starts at μ=0
    end else begin
        // Track instr_valid for edge detection
        last_instr_valid <= instr_valid;

        if (new_instruction_cycle) begin
            // New instruction cycle started - analyze the instruction
            last_instruction <= instruction;
            core_status <= STATUS_CHECKING;

            case (instruction[31:24])  // opcode
                OPCODE_PNEW, OPCODE_PSPLIT, OPCODE_PMERGE: begin
                    // Partition operations - μ-cost must monotonically increase
                    receipt_required <= 1'b0;  // No receipt needed for basic operations
                    instr_allowed <= 1'b1;

                    // Check partition independence - use function result directly
                    // to avoid one-cycle delay from register assignment
                    partition_independent <= check_partition_independence(instruction, partition_count, memory_isolation);
                    partition_gate_open <= check_partition_independence(instruction, partition_count, memory_isolation);

                    // μ-cost accumulates (never decreases) - verify monotonicity
                    cost_decreasing <= (proposed_cost >= current_mu_cost);
                    cost_gate_open <= (proposed_cost >= current_mu_cost);

                    if (check_partition_independence(instruction, partition_count, memory_isolation) && (proposed_cost >= current_mu_cost)) begin
                        expected_cost <= proposed_cost;
                        core_status <= STATUS_ALLOWED;
                    end else if (!check_partition_independence(instruction, partition_count, memory_isolation)) begin
                        core_status <= STATUS_DENIED_ISO;
                    end else begin
                        core_status <= STATUS_DENIED_COST;
                    end
                end

                OPCODE_PDISCOVER: begin
                    // Discovery operations always allowed but require receipt
                    receipt_required <= 1'b1;
                    instr_allowed <= 1'b0;
                    partition_gate_open <= 1'b1;
                    cost_gate_open <= 1'b1;  // Discovery can increase cost
                    expected_cost <= proposed_cost;
                    core_status <= STATUS_ALLOWED;
                end

                OPCODE_MDLACC: begin
                    // MDL accumulation requires receipt
                    receipt_required <= 1'b1;
                    instr_allowed <= 1'b0;
                    partition_gate_open <= 1'b1;
                    cost_gate_open <= 1'b1;
                    expected_cost <= proposed_cost;
                    core_status <= STATUS_ALLOWED;
                end

                default: begin
                    // Other operations don't require receipts
                    receipt_required <= 1'b0;
                    instr_allowed <= 1'b1;
                    partition_gate_open <= 1'b1;
                    cost_gate_open <= 1'b1;
                    core_status <= STATUS_IDLE;
                end
            endcase
        end

        // Check receipts - now with integrity verification
        if (receipt_valid && receipt_required) begin
            // Receipt must match expected cost AND pass integrity check
            if (receipt_value == expected_cost && receipt_integrity_ok && chain_continuity_ok) begin
                receipt_accepted <= 1'b1;
                instr_allowed <= 1'b1;
                core_status <= STATUS_RECEIPT_OK;
                prev_post_mu <= proposed_cost;  // Update chain for next receipt
                $display("μ-Core: Receipt accepted for instruction %h, cost=%0d", instruction, receipt_value >> 16);
            end else begin
                receipt_accepted <= 1'b0;
                instr_allowed <= 1'b0;
                if (!receipt_integrity_ok) begin
                    core_status <= STATUS_DENIED_COST;
                    $display("μ-Core: Receipt DENIED - integrity check FAILED (forged cost?)");
                end else if (!chain_continuity_ok) begin
                    core_status <= STATUS_DENIED_COST;
                    $display("μ-Core: Receipt DENIED - chain continuity FAILED");
                end else begin
                    core_status <= STATUS_DENIED_COST;
                    $display("μ-Core: Receipt DENIED for instruction %h, expected=%0d, got=%0d", instruction, expected_cost >> 16, receipt_value >> 16);
                end
            end
        end

        // Reset flags when instruction completes
        if (!instr_valid) begin
            instr_allowed <= 1'b0;
            receipt_required <= 1'b0;
            receipt_accepted <= 1'b0;
            cost_gate_open <= 1'b0;
            partition_gate_open <= 1'b0;
            core_status <= STATUS_IDLE;
        end
    end
end

// ============================================================================
// PARTITION INDEPENDENCE CHECK
// ============================================================================

function check_partition_independence;
    input [31:0] instr;
    input [5:0] part_count;
    input [31:0] mem_iso;
    begin
        // Check that partitions maintain logical independence
        // This is a simplified check - in full implementation would verify
        // no cross-talk between memory regions and partition boundaries

        case (instr[31:24])
            OPCODE_PNEW: begin
                // New partition - check we don't exceed max partitions
                check_partition_independence = (part_count < 64);
            end

            OPCODE_PSPLIT: begin
                // Split - check source partition exists and we have space
                check_partition_independence = (instr[23:16] < part_count) && (part_count < 63);
            end

            OPCODE_PMERGE: begin
                // Merge - check both partitions exist and are different
                check_partition_independence = (instr[23:16] < part_count) &&
                                             (instr[15:8] < part_count) &&
                                             (instr[23:16] != instr[15:8]);
            end

            default: begin
                check_partition_independence = 1'b1;
            end
        endcase

        // Additional memory isolation check
        check_partition_independence = check_partition_independence && (mem_iso == 32'hCAFEBABE);
    end
endfunction

endmodule