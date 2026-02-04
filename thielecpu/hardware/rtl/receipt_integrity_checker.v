// receipt_integrity_checker.v
// Receipt Integrity Enforcement Module for Thiele Machine
//
// This module implements the Coq-proven receipt integrity property:
//   receipt_mu_consistent: post_mu = pre_mu + instruction_cost(instr)
//
// Addresses the forgery vulnerability found in Python receipt system.
// Receipts MUST bind μ-cost to actual computation.
//
// Specification (from coq/kernel/ReceiptIntegrity.v):
//   - receipt_mu_consistent: post_mu = pre_mu + instruction_cost
//   - chain_links: consecutive receipts must chain (post_n = pre_{n+1})
//   - forged_receipt_fails_validation: any wrong mu_delta is rejected
//
// STATUS: December 24, 2025 - Implements fix for receipt forgery attack

`timescale 1ns / 1ps

module receipt_integrity_checker (
    input wire clk,
    input wire rst_n,
    
    // Receipt inputs
    input wire receipt_valid,           // New receipt to verify
    input wire [31:0] receipt_pre_mu,   // Claimed pre-state μ
    input wire [31:0] receipt_post_mu,  // Claimed post-state μ
    input wire [7:0]  receipt_opcode,   // Instruction opcode
    input wire [31:0] receipt_operand,  // Instruction operand (for cost calc)
    
    // Chain verification
    input wire chain_mode,              // 1 = verify chain continuity
    input wire [31:0] prev_post_mu,     // Previous receipt's post_mu
    
    // Outputs
    output reg receipt_integrity_ok,    // Receipt passes integrity check
    output reg chain_continuity_ok,     // Chain links correctly
    output reg [31:0] computed_cost,    // Actual computed instruction cost
    output reg [31:0] error_code        // Error details
);

// ============================================================================
// INSTRUCTION COST TABLE (matches Coq instruction_cost)
// ============================================================================

// Must match coq/kernel/VMStep.v instruction_cost definition
localparam [7:0] OPCODE_PNEW      = 8'h00;
localparam [7:0] OPCODE_PSPLIT    = 8'h01;
localparam [7:0] OPCODE_PMERGE    = 8'h02;
localparam [7:0] OPCODE_LASSERT   = 8'h03;
localparam [7:0] OPCODE_LJOIN     = 8'h04;
localparam [7:0] OPCODE_MDLACC    = 8'h05;
localparam [7:0] OPCODE_PDISCOVER = 8'h06;
localparam [7:0] OPCODE_XFER      = 8'h07;
localparam [7:0] OPCODE_PYEXEC    = 8'h08;
localparam [7:0] OPCODE_CHSH_TRIAL = 8'h09;
localparam [7:0] OPCODE_XOR_LOAD  = 8'h0A;
localparam [7:0] OPCODE_XOR_ADD   = 8'h0B;
localparam [7:0] OPCODE_XOR_SWAP  = 8'h0C;
localparam [7:0] OPCODE_XOR_RANK  = 8'h0D;
localparam [7:0] OPCODE_EMIT      = 8'h0E;
localparam [7:0] OPCODE_REVEAL    = 8'h0F;
localparam [7:0] OPCODE_ORACLE_HALTS = 8'h10;
localparam [7:0] OPCODE_HALT      = 8'hFF;

// Error codes
localparam [31:0] ERR_NONE           = 32'h00000000;
localparam [31:0] ERR_MU_MISMATCH    = 32'h00000001;
localparam [31:0] ERR_CHAIN_BREAK    = 32'h00000002;
localparam [31:0] ERR_UNKNOWN_OPCODE = 32'h00000003;
localparam [31:0] ERR_OVERFLOW       = 32'h00000004;

// ============================================================================
// COST COMPUTATION FUNCTION
// ============================================================================
// 
// This function computes the ACTUAL cost of an instruction.
// Forged receipts will claim a different cost than this computes.
//
// In Coq: instruction_cost extracts the mu_delta from the instruction.
// Here we recompute what it SHOULD be based on the operation.

function [31:0] compute_instruction_cost;
    input [7:0] opcode;
    input [31:0] operand;
    begin
        case (opcode)
            OPCODE_PNEW: begin
                // Cost = size of region being created (in bits)
                // operand contains region size
                compute_instruction_cost = {24'h0, operand[7:0]}; 
            end
            
            OPCODE_PSPLIT: begin
                // Cost = log2(partition size) - structural cost of split
                compute_instruction_cost = {24'h0, operand[7:0]};
            end
            
            OPCODE_PMERGE: begin
                // Cost = cost of merging two partitions
                compute_instruction_cost = {24'h0, operand[7:0]};
            end
            
            OPCODE_LASSERT: begin
                // Cost = certification cost
                compute_instruction_cost = {24'h0, operand[7:0]};
            end
            
            OPCODE_LJOIN: begin
                // Cost = join certification cost
                compute_instruction_cost = {24'h0, operand[7:0]};
            end
            
            OPCODE_MDLACC: begin
                // Cost = MDL accumulation cost
                // NOTE: This actually depends on dynamic state which isn't available here.
                // For simulation purposes, we match the static base cost.
                compute_instruction_cost = {24'h0, operand[7:0]};
            end
            
            OPCODE_PDISCOVER: begin
                // Cost = discovery cost (evidence size)
                 compute_instruction_cost = {24'h0, operand[7:0]};
            end
            
            OPCODE_XFER, OPCODE_PYEXEC, OPCODE_CHSH_TRIAL,
            OPCODE_XOR_LOAD, OPCODE_XOR_ADD, OPCODE_XOR_SWAP, OPCODE_XOR_RANK,
            OPCODE_EMIT, OPCODE_ORACLE_HALTS: begin
                // All other operations use operand[7:0] as cost
                compute_instruction_cost = {24'h0, operand[7:0]};
            end

            OPCODE_REVEAL: begin
                // Cost = (operand_a << 8) + cost
                // operand_a is operand[23:16]
                compute_instruction_cost = {16'h0, operand[23:16], 8'h0} + {24'h0, operand[7:0]};
            end

            
            OPCODE_HALT: begin
                // HALT has zero cost
                compute_instruction_cost = 32'h0;
            end
            
            default: begin
                // Unknown opcode - flag error but return 0
                compute_instruction_cost = 32'hFFFFFFFF; // Sentinel for error
            end
        endcase
    end
endfunction

// ============================================================================
// RECEIPT INTEGRITY VERIFICATION
// ============================================================================
//
// Core property (from Coq receipt_mu_consistent):
//   post_mu = pre_mu + instruction_cost(instruction)
//
// If this doesn't hold, the receipt is FORGED.

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        receipt_integrity_ok <= 1'b0;
        chain_continuity_ok <= 1'b0;
        computed_cost <= 32'h0;
        error_code <= ERR_NONE;
    end else begin
        if (receipt_valid) begin
            // Compute what the cost SHOULD be
            computed_cost <= compute_instruction_cost(receipt_opcode, receipt_operand);
            
            // Check for unknown opcode
            if (compute_instruction_cost(receipt_opcode, receipt_operand) == 32'hFFFFFFFF) begin
                receipt_integrity_ok <= 1'b0;
                error_code <= ERR_UNKNOWN_OPCODE;
            end
            // Check for overflow
            else if (receipt_pre_mu > 32'hFFFFFFFF - computed_cost) begin
                receipt_integrity_ok <= 1'b0;
                error_code <= ERR_OVERFLOW;
            end
            // CRITICAL: Verify receipt_mu_consistent property
            else if (receipt_post_mu == receipt_pre_mu + compute_instruction_cost(receipt_opcode, receipt_operand)) begin
                // Receipt integrity PASSED
                receipt_integrity_ok <= 1'b1;
                error_code <= ERR_NONE;
            end else begin
                // FORGERY DETECTED: post_mu doesn't match computed cost
                receipt_integrity_ok <= 1'b0;
                error_code <= ERR_MU_MISMATCH;
                $display("FORGERY DETECTED: pre_mu=%d, post_mu=%d, expected=%d",
                         receipt_pre_mu, receipt_post_mu,
                         receipt_pre_mu + compute_instruction_cost(receipt_opcode, receipt_operand));
            end
            
            // Chain continuity check (if in chain mode)
            if (chain_mode) begin
                if (receipt_pre_mu == prev_post_mu) begin
                    chain_continuity_ok <= 1'b1;
                end else begin
                    chain_continuity_ok <= 1'b0;
                    error_code <= ERR_CHAIN_BREAK;
                    $display("CHAIN BREAK: prev_post_mu=%d, this_pre_mu=%d",
                             prev_post_mu, receipt_pre_mu);
                end
            end else begin
                chain_continuity_ok <= 1'b1; // No chain check requested
            end
        end else begin
            // No receipt to verify
            receipt_integrity_ok <= 1'b0;
            chain_continuity_ok <= 1'b0;
        end
    end
end

// ============================================================================
// ASSERTIONS (for simulation/formal verification)
// ============================================================================

`ifdef FORMAL
// Property: If receipt_integrity_ok, then mu arithmetic is correct
always @(posedge clk) begin
    if (receipt_integrity_ok && receipt_valid) begin
        assert(receipt_post_mu == receipt_pre_mu + computed_cost);
    end
end

// Property: If chain_continuity_ok, then chain links correctly  
always @(posedge clk) begin
    if (chain_continuity_ok && chain_mode && receipt_valid) begin
        assert(receipt_pre_mu == prev_post_mu);
    end
end
`endif

endmodule
