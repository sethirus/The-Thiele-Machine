/*
 * Partition Core - Synthesizable Thiele Machine Partition Operations
 * 
 * This module implements the core partition operations that are isomorphic to:
 * - Coq: BlindSighted.v (PNEW, PSPLIT, PMERGE, PDISCOVER)
 * - Python: thielecpu/state.py, thielecpu/discovery.py
 * 
 * ISOMORPHISM REQUIREMENTS:
 * 1. Same partition representation across all implementations
 * 2. Same μ-cost accounting
 * 3. Same structural/chaotic classification
 * 
 * Licensed under Apache 2.0 - Copyright 2025 Devon Thiele
 */

module partition_core #(
    parameter MAX_MODULES = 8,
    parameter REGION_WIDTH = 32,
    parameter MU_WIDTH = 16
) (
    input wire clk,
    input wire rst_n,
    
    // Operation select
    input wire [2:0] op,  // 0=NOP, 1=PNEW, 2=PSPLIT, 3=PMERGE, 4=PDISCOVER
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
    output reg [MU_WIDTH-1:0] mu_cost,
    output reg op_done,
    output reg is_structured,  // Classification result
    
    // Flattened partition state (MAX_MODULES × REGION_WIDTH bits)
    output reg [MAX_MODULES*REGION_WIDTH-1:0] partitions
);

    // Operation codes (must match Python VM)
    localparam OP_NOP = 3'd0;
    localparam OP_PNEW = 3'd1;
    localparam OP_PSPLIT = 3'd2;
    localparam OP_PMERGE = 3'd3;
    localparam OP_PDISCOVER = 3'd4;
    
    // Internal state
    reg [7:0] next_id;
    reg [2:0] state;
    
    localparam ST_IDLE = 3'd0;
    localparam ST_EXEC = 3'd1;
    localparam ST_DONE = 3'd2;
    
    // Helper: count set bits (for structure detection)
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
            mu_cost <= 0;
            op_done <= 0;
            is_structured <= 0;
            result_module_id <= 0;
            partitions <= 0;
            state <= ST_IDLE;
        end else begin
            case (state)
                ST_IDLE: begin
                    op_done <= 0;
                    if (op_valid && op != OP_NOP) begin
                        state <= ST_EXEC;
                    end
                end
                
                ST_EXEC: begin
                    case (op)
                        OP_PNEW: begin
                            // Create new partition module
                            if (num_modules < MAX_MODULES) begin
                                partitions[num_modules*REGION_WIDTH +: REGION_WIDTH] <= pnew_region;
                                result_module_id <= next_id;
                                num_modules <= num_modules + 1;
                                next_id <= next_id + 1;
                                // μ-cost: log2(|region|) bits
                                mu_cost <= mu_cost + popcount(pnew_region);
                            end
                        end
                        
                        OP_PSPLIT: begin
                            // Split module into two
                            if (psplit_module_id < num_modules && num_modules < MAX_MODULES) begin
                                // Get current region
                                // Split based on mask
                                partitions[num_modules*REGION_WIDTH +: REGION_WIDTH] <= 
                                    partitions[psplit_module_id*REGION_WIDTH +: REGION_WIDTH] & psplit_mask;
                                partitions[psplit_module_id*REGION_WIDTH +: REGION_WIDTH] <= 
                                    partitions[psplit_module_id*REGION_WIDTH +: REGION_WIDTH] & ~psplit_mask;
                                result_module_id <= next_id;
                                num_modules <= num_modules + 1;
                                next_id <= next_id + 1;
                                // μ-cost: split costs more
                                mu_cost <= mu_cost + REGION_WIDTH;
                            end
                        end
                        
                        OP_PMERGE: begin
                            // Merge two modules
                            if (pmerge_m1 < num_modules && pmerge_m2 < num_modules && pmerge_m1 != pmerge_m2) begin
                                partitions[pmerge_m1*REGION_WIDTH +: REGION_WIDTH] <= 
                                    partitions[pmerge_m1*REGION_WIDTH +: REGION_WIDTH] |
                                    partitions[pmerge_m2*REGION_WIDTH +: REGION_WIDTH];
                                partitions[pmerge_m2*REGION_WIDTH +: REGION_WIDTH] <= 0;
                                result_module_id <= pmerge_m1;
                                // μ-cost: merge is cheap
                                mu_cost <= mu_cost + 4;
                            end
                        end
                        
                        OP_PDISCOVER: begin
                            // Discover structure
                            // Classification: STRUCTURED if multiple non-trivial modules
                            if (num_modules >= 2) begin
                                is_structured <= 1;
                            end else begin
                                is_structured <= 0;
                            end
                            result_module_id <= num_modules;
                            // μ-cost: discovery costs based on region sizes
                            mu_cost <= mu_cost + num_modules * 8;
                        end
                        
                        default: begin
                            // NOP
                        end
                    endcase
                    state <= ST_DONE;
                end
                
                ST_DONE: begin
                    op_done <= 1;
                    state <= ST_IDLE;
                end
            endcase
        end
    end

endmodule
