/*
 * Partition Core - Synthesizable Thiele Machine Partition Operations
 * 
 * This module implements the core partition operations that are isomorphic to:
 * - Coq: BlindSighted.v (PNEW, PSPLIT, PMERGE, PDISCOVER)
 * - Python: thielecpu/state.py, thielecpu/discovery.py
 * 
 * ISOMORPHISM REQUIREMENTS (spec/thiele_machine_spec.md):
 * 1. Same partition representation across all implementations
 * 2. Same μ-cost accounting (mu_discovery + mu_execution)
 * 3. Same structural/chaotic classification
 * 
 * μ-COST RULES:
 * - PNEW:   mu_discovery += popcount(region)
 * - PSPLIT: mu_execution += MASK_WIDTH (64)
 * - PMERGE: mu_execution += 4
 * 
 * Licensed under Apache 2.0 - Copyright 2025 Devon Thiele
 */

module partition_core #(
    parameter MAX_MODULES = 8,
    parameter REGION_WIDTH = 64,    // Must match MASK_WIDTH in spec
    parameter MU_WIDTH = 32         // 32-bit μ counters
) (
    input wire clk,
    input wire rst_n,
    
    // Operation select - Opcode encoding matches Python ISA
    input wire [7:0] op,
    input wire op_valid,
    
    // PNEW inputs
    input wire [REGION_WIDTH-1:0] pnew_region,
    
    // PSPLIT inputs
    input wire [7:0] psplit_module_id,
    input wire [REGION_WIDTH-1:0] psplit_mask,  // Which elements go to new module
    
    // PMERGE inputs
    input wire [7:0] pmerge_m1,
    input wire [7:0] pmerge_m2,
    
    // Outputs
    output reg [7:0] num_modules,
    output reg [7:0] result_module_id,
    output reg op_done,
    output reg is_structured,  // Classification result
    
    // μ-Ledger (canonical - matches spec/thiele_machine_spec.md)
    output reg [MU_WIDTH-1:0] mu_discovery,    // Cost of partition discovery
    output reg [MU_WIDTH-1:0] mu_execution,    // Cost of instruction execution
    
    // Legacy mu_cost output (sum of discovery + execution)
    output wire [MU_WIDTH-1:0] mu_cost,
    
    // Flattened partition state (MAX_MODULES × REGION_WIDTH bits)
    output reg [MAX_MODULES*REGION_WIDTH-1:0] partitions
);

    // Operation codes (must match Python VM thielecpu/isa.py)
    localparam [7:0] OPC_PNEW     = 8'h00;
    localparam [7:0] OPC_PSPLIT   = 8'h01;
    localparam [7:0] OPC_PMERGE   = 8'h02;
    localparam [7:0] OPC_LASSERT  = 8'h03;
    localparam [7:0] OPC_LJOIN    = 8'h04;
    localparam [7:0] OPC_MDLACC   = 8'h05;
    localparam [7:0] OPC_XFER     = 8'h07;
    localparam [7:0] OPC_PYEXEC   = 8'h08;
    localparam [7:0] OPC_XOR_LOAD = 8'h0A;
    localparam [7:0] OPC_XOR_ADD  = 8'h0B;
    localparam [7:0] OPC_XOR_SWAP = 8'h0C;
    localparam [7:0] OPC_XOR_RANK = 8'h0D;
    localparam [7:0] OPC_EMIT     = 8'h0E;
    localparam [7:0] OPC_HALT     = 8'hFF;
    
    // Internal state
    reg [7:0] next_id;
    reg [2:0] fsm_state;
    
    localparam ST_IDLE = 3'd0;
    localparam ST_EXEC = 3'd1;
    localparam ST_DONE = 3'd2;
    
    // Total μ-cost is sum of discovery and execution
    assign mu_cost = mu_discovery + mu_execution;
    
    // Helper: count set bits (popcount)
    function [7:0] popcount;
        input [REGION_WIDTH-1:0] val;
        integer i;
        begin
            popcount = 0;
            for (i = 0; i < REGION_WIDTH; i = i + 1)
                popcount = popcount + val[i];
        end
    endfunction
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num_modules <= 0;
            next_id <= 0;
            mu_discovery <= 0;
            mu_execution <= 0;
            op_done <= 0;
            is_structured <= 0;
            result_module_id <= 0;
            partitions <= 0;
            fsm_state <= ST_IDLE;
        end else begin
            case (fsm_state)
                ST_IDLE: begin
                    op_done <= 0;
                    if (op_valid) begin
                        fsm_state <= ST_EXEC;
                    end
                end
                
                ST_EXEC: begin
                    case (op)
                        OPC_PNEW: begin
                            // Create new partition module
                            // Note: Hardware does not check for existing regions like Python VM.
                            // This is acceptable because duplicate regions are avoided at
                            // the program level, and hardware prioritizes synthesis efficiency.
                            // μ-update: mu_discovery += popcount(region)
                            if (num_modules < MAX_MODULES) begin
                                partitions[num_modules*REGION_WIDTH +: REGION_WIDTH] <= pnew_region;
                                result_module_id <= next_id;
                                num_modules <= num_modules + 1;
                                next_id <= next_id + 1;
                                mu_discovery <= mu_discovery + popcount(pnew_region);
                            end
                        end
                        
                        OPC_PSPLIT: begin
                            // Split module into two
                            // μ-update: mu_execution += REGION_WIDTH
                            if (psplit_module_id < num_modules && num_modules < MAX_MODULES) begin
                                partitions[num_modules*REGION_WIDTH +: REGION_WIDTH] <= 
                                    partitions[psplit_module_id*REGION_WIDTH +: REGION_WIDTH] & psplit_mask;
                                partitions[psplit_module_id*REGION_WIDTH +: REGION_WIDTH] <= 
                                    partitions[psplit_module_id*REGION_WIDTH +: REGION_WIDTH] & ~psplit_mask;
                                result_module_id <= next_id;
                                num_modules <= num_modules + 1;
                                next_id <= next_id + 1;
                                mu_execution <= mu_execution + REGION_WIDTH;
                            end
                        end
                        
                        OPC_PMERGE: begin
                            // Merge two modules
                            // μ-update: mu_execution += 4
                            if (pmerge_m1 < num_modules && pmerge_m2 < num_modules && pmerge_m1 != pmerge_m2) begin
                                partitions[pmerge_m1*REGION_WIDTH +: REGION_WIDTH] <=
                                    partitions[pmerge_m1*REGION_WIDTH +: REGION_WIDTH] |
                                    partitions[pmerge_m2*REGION_WIDTH +: REGION_WIDTH];
                                // Compact the partition table so module indices remain dense
                                // after merging. Move the final active module into the slot
                                // vacated by pmerge_m2 (unless pmerge_m2 already references
                                // the last active entry), then clear the old tail.
                                if (pmerge_m2 != num_modules - 1) begin
                                    partitions[pmerge_m2*REGION_WIDTH +: REGION_WIDTH] <=
                                        partitions[(num_modules-1)*REGION_WIDTH +: REGION_WIDTH];
                                end else begin
                                    partitions[pmerge_m2*REGION_WIDTH +: REGION_WIDTH] <= 0;
                                end
                                partitions[(num_modules-1)*REGION_WIDTH +: REGION_WIDTH] <= 0;
                                result_module_id <= pmerge_m1;
                                num_modules <= num_modules - 1;
                                mu_execution <= mu_execution + 4;
                            end
                        end
                        
                        OPC_MDLACC: begin
                            // Discover structure
                            // Classification: STRUCTURED if multiple non-trivial modules
                            if (num_modules >= 2) begin
                                is_structured <= 1;
                            end else begin
                                is_structured <= 0;
                            end
                            result_module_id <= num_modules;
                            mu_execution <= mu_execution + num_modules * 8;
                        end
                        
                        default: begin
                            // NOP or unhandled opcode
                        end
                    endcase
                    fsm_state <= ST_DONE;
                end
                
                ST_DONE: begin
                    op_done <= 1;
                    fsm_state <= ST_IDLE;
                end
            endcase
        end
    end

endmodule
