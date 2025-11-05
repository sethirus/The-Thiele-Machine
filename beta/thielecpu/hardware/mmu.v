// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Thiele CPU Memory Management Unit (MMU)
// ============================================================================

module mmu (
    input wire clk,
    input wire rst_n,

    // CPU interface
    input wire [31:0] cpu_addr,
    input wire [31:0] cpu_wdata,
    output wire [31:0] cpu_rdata,
    input wire cpu_we,
    input wire cpu_en,

    // Module control
    input wire [5:0] current_module,
    input wire [5:0] target_module,

    // External memory interface
    output wire [31:0] mem_addr,
    output wire [31:0] mem_wdata,
    input wire [31:0] mem_rdata,
    output wire mem_we,
    output wire mem_en,

    // Status
    output wire access_allowed,
    output wire [31:0] error_code
);

// ============================================================================
// PARAMETERS
// ============================================================================

localparam NUM_MODULES = 64;
localparam PAGE_SIZE = 4096; // 4KB pages
localparam MAX_PAGES_PER_MODULE = 256;

// Error codes
localparam ERR_NONE = 32'h0;
localparam ERR_INVALID_MODULE = 32'h1001;
localparam ERR_ACCESS_DENIED = 32'h1002;
localparam ERR_OUT_OF_BOUNDS = 32'h1003;
localparam ERR_PAGE_FAULT = 32'h1004;

// ============================================================================
// INTERNAL REGISTERS
// ============================================================================

// Page tables: module -> page -> physical address
reg [31:0] page_table [0:NUM_MODULES-1][0:MAX_PAGES_PER_MODULE-1];
reg [31:0] page_valid [0:NUM_MODULES-1][0:MAX_PAGES_PER_MODULE-1];

// Module permissions
reg [31:0] module_perms [0:NUM_MODULES-1]; // Read/write/execute permissions

// TLB (Translation Lookaside Buffer) for fast lookups
reg [31:0] tlb_virtual_addr [0:7];
reg [31:0] tlb_physical_addr [0:7];
reg [5:0] tlb_module [0:7];
reg tlb_valid [0:7];

// Current operation state
reg [31:0] current_error;
reg access_granted;

// Region configuration (simplified - could be loaded from memory)
reg [31:0] region_base [0:63];
reg [31:0] region_size [0:63];

// Loop variables for initialization
reg [5:0] init_module_var;
reg [7:0] init_page_var;

// ============================================================================
// ADDRESS TRANSLATION LOGIC
// ============================================================================

wire [5:0] addr_module;
wire [25:0] addr_offset;
wire [7:0] page_index;
wire [11:0] page_offset;

assign addr_module = cpu_addr[31:26];  // Top 6 bits = module ID
assign addr_offset = cpu_addr[25:0];   // Bottom 26 bits = offset
assign page_index = addr_offset[25:18]; // Next 8 bits = page index
assign page_offset = addr_offset[17:0]; // Bottom 18 bits = page offset

// ============================================================================
// ACCESS CONTROL LOGIC
// ============================================================================

wire module_exists;
wire page_exists;
wire permission_ok;

assign module_exists = (addr_module < NUM_MODULES) &&
                      (region_size[addr_module] > 0);

assign page_exists = module_exists &&
                    (page_index < MAX_PAGES_PER_MODULE) &&
                    page_valid[addr_module][page_index];

assign permission_ok = module_exists &&
                      ((cpu_we == 1'b0) || (module_perms[addr_module] & 32'h1)); // Write permission check

assign access_allowed = module_exists && page_exists && permission_ok;

// ============================================================================
// TLB LOOKUP
// ============================================================================

wire tlb_hit;
wire [2:0] tlb_index;
wire [31:0] tlb_physical_addr_match;

assign tlb_hit = 1'b0; // Simplified - no TLB implementation yet
assign tlb_index = 3'h0;
assign tlb_physical_addr_match = 32'h0;

// ============================================================================
// PHYSICAL ADDRESS CALCULATION
// ============================================================================

wire [31:0] physical_addr;

assign physical_addr = page_exists ?
    (page_table[addr_module][page_index] + page_offset) :
    32'h0;

// ============================================================================
// MEMORY ACCESS LOGIC
// ============================================================================

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        current_error <= ERR_NONE;
        access_granted <= 1'b0;
        init_module_var <= 6'h0;
        init_page_var <= 8'h0;

    end else begin
        if (cpu_en) begin
            if (access_allowed) begin
                current_error <= ERR_NONE;
                access_granted <= 1'b1;
            end else begin
                access_granted <= 1'b0;
                if (!module_exists) begin
                    current_error <= ERR_INVALID_MODULE;
                end else if (!page_exists) begin
                    current_error <= ERR_PAGE_FAULT;
                end else if (!permission_ok) begin
                    current_error <= ERR_ACCESS_DENIED;
                end else begin
                    current_error <= ERR_OUT_OF_BOUNDS;
                end
            end
        end else begin
            access_granted <= 1'b0;
            current_error <= ERR_NONE;
        end
    end
end

// Separate always block for page table initialization
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        init_module_var <= 6'h0;
        init_page_var <= 8'h0;
    end else if (init_module_var < NUM_MODULES) begin
        if (init_page_var < MAX_PAGES_PER_MODULE) begin
            page_table[init_module_var][init_page_var] <= 32'h0;
            page_valid[init_module_var][init_page_var] <= 1'b0;
            init_page_var <= init_page_var + 1;
        end else begin
            module_perms[init_module_var] <= 32'h3; // Read/write by default
            init_page_var <= 8'h0;
            init_module_var <= init_module_var + 1;
        end
    end
end

// Separate always block for region initialization
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        init_module_var <= 6'h0; // Reuse for region init
    end else if (init_module_var < 64) begin
        region_base[init_module_var] <= 32'h0;
        region_size[init_module_var] <= 32'h1000; // 4KB default
        init_module_var <= init_module_var + 1;
    end
end

// ============================================================================
// PAGE MANAGEMENT TASKS
// ============================================================================

task allocate_page;
    input [5:0] module_id;
    input [7:0] page_idx;
    input [31:0] physical_base;
    begin
        if (module_id < NUM_MODULES && page_idx < MAX_PAGES_PER_MODULE) begin
            page_table[module_id][page_idx] <= physical_base;
            page_valid[module_id][page_idx] <= 1'b1;
        end
    end
endtask

task free_page;
    input [5:0] module_id;
    input [7:0] page_idx;
    begin
        if (module_id < NUM_MODULES && page_idx < MAX_PAGES_PER_MODULE) begin
            page_valid[module_id][page_idx] <= 1'b0;
        end
    end
endtask

task set_module_permissions;
    input [5:0] module_id;
    input [31:0] permissions;
    begin
        if (module_id < NUM_MODULES) begin
            module_perms[module_id] <= permissions;
        end
    end
endtask

// ============================================================================
// OUTPUT ASSIGNMENTS
// ============================================================================

assign mem_addr = access_allowed ? physical_addr : 32'h0;
assign mem_wdata = cpu_wdata;
assign cpu_rdata = access_allowed ? mem_rdata : 32'h0;
assign mem_we = cpu_we && access_allowed;
assign mem_en = cpu_en && access_allowed;
assign error_code = current_error;

endmodule