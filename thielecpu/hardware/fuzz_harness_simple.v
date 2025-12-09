// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Simplified Fuzz Harness for Adversarial Falsification Testing
// ============================================================================
// 
// This is a SIMPLIFIED testbench for testing basic instruction execution
// without the full μ-core enforcement. This allows us to test isomorphism
// of basic operations between Python VM and Verilog.
//
// Features:
// 1. Reads program from fuzz_program.hex
// 2. Executes instructions with simple state tracking
// 3. Computes state hash on HALT
// 4. Outputs hash and μ-total to stdout
//
// Used by tests/adversarial_fuzzing.py to verify Python ↔ Verilog isomorphism

`timescale 1ns / 1ps

module fuzz_harness_simple;

// ============================================================================
// PARAMETERS
// ============================================================================

localparam MAX_INSTRUCTIONS = 256;
localparam MAX_MEMORY = 1024;

// Opcodes (matching ISA)
localparam [7:0] OPCODE_PNEW      = 8'h00;
localparam [7:0] OPCODE_PSPLIT    = 8'h01;
localparam [7:0] OPCODE_PMERGE    = 8'h02;
localparam [7:0] OPCODE_XOR_LOAD  = 8'h0A;
localparam [7:0] OPCODE_XOR_ADD   = 8'h0B;
localparam [7:0] OPCODE_XOR_SWAP  = 8'h0C;
localparam [7:0] OPCODE_EMIT      = 8'h0E;
localparam [7:0] OPCODE_HALT      = 8'hFF;

// ============================================================================
// SIGNALS
// ============================================================================

reg clk;
reg rst_n;

// Instruction memory
reg [31:0] instr_memory [0:MAX_INSTRUCTIONS-1];
reg [31:0] pc;
wire [31:0] current_instr;
wire [7:0] opcode;
wire [7:0] operand_a;
wire [7:0] operand_b;

// Data memory
reg [31:0] data_memory [0:MAX_MEMORY-1];

// State tracking
reg [31:0] num_modules;
reg [31:0] module_ids [0:63];
reg [63:0] partition_masks [0:63];  // Bitmask for each module
reg [31:0] next_id;

// μ-cost tracking (simplified)
reg [63:0] mu_discovery;
reg [63:0] mu_execution;
reg [63:0] mu_total;

// Step counter
reg [31:0] step_count;

// State hash (computed at end)
reg [255:0] final_hash;

// Loop variables
integer i, j;
integer program_length;
integer halted;
integer timeout_counter;

// ============================================================================
// INSTRUCTION DECODE
// ============================================================================

assign current_instr = instr_memory[pc[7:0]];
assign opcode = current_instr[31:24];
assign operand_a = current_instr[23:16];
assign operand_b = current_instr[15:8];

// ============================================================================
// CLOCK GENERATION
// ============================================================================

initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100MHz clock
end

// ============================================================================
// LOAD PROGRAM
// ============================================================================

initial begin
    // Initialize memories
    for (i = 0; i < MAX_INSTRUCTIONS; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end
    for (i = 0; i < MAX_MEMORY; i = i + 1) begin
        data_memory[i] = 32'h00000000;
    end
    
    // Load program from hex file
    $display("Loading program from fuzz_program.hex");
    $readmemh("fuzz_program.hex", instr_memory);
    
    // Count non-zero instructions
    program_length = 0;
    for (i = 0; i < MAX_INSTRUCTIONS; i = i + 1) begin
        if (instr_memory[i] != 32'h00000000) begin
            program_length = i + 1;
        end
    end
    $display("Program length: %d instructions", program_length);
    
    // Display loaded program
    for (i = 0; i < program_length && i < 20; i = i + 1) begin
        $display("  [%02d] %08h", i, instr_memory[i]);
    end
    if (program_length > 20) begin
        $display("  ... (%d more instructions)", program_length - 20);
    end
end

// ============================================================================
// EXECUTION ENGINE
// ============================================================================

initial begin
    // Initialize state
    rst_n = 0;
    pc = 0;
    num_modules = 0;
    next_id = 0;
    mu_discovery = 0;
    mu_execution = 0;
    mu_total = 0;
    step_count = 0;
    halted = 0;
    timeout_counter = 0;
    
    // Initialize module tables
    for (i = 0; i < 64; i = i + 1) begin
        module_ids[i] = 0;
        partition_masks[i] = 0;
    end
    
    // Reset
    #20 rst_n = 1;
    #10;
    
    $display("Starting execution...");
    
    // Execution loop
    while (!halted && timeout_counter < 10000) begin
        @(posedge clk);
        
        if (rst_n) begin
            // Fetch and execute
            case (opcode)
                OPCODE_PNEW: begin
                    $display("[%04d] PC=%02h: PNEW region={%0d}", 
                             step_count, pc, operand_a);
                    
                    // Create new module
                    if (num_modules < 64) begin
                        module_ids[num_modules] = next_id;
                        // Set bit for the region index
                        partition_masks[num_modules] = (64'h1 << operand_a);
                        next_id = next_id + 1;
                        num_modules = num_modules + 1;
                        
                        // μ-cost: popcount of region = 1 (single element)
                        mu_discovery = mu_discovery + 1;
                    end
                    
                    pc = pc + 1;
                    step_count = step_count + 1;
                end
                
                OPCODE_XOR_LOAD: begin
                    $display("[%04d] PC=%02h: XOR_LOAD %0d, %0d", 
                             step_count, pc, operand_a, operand_b);
                    
                    // Load value into XOR matrix
                    data_memory[operand_a] = operand_b;
                    
                    // μ-cost: 1 for memory operation
                    mu_execution = mu_execution + 1;
                    
                    pc = pc + 1;
                    step_count = step_count + 1;
                end
                
                OPCODE_XOR_ADD: begin
                    $display("[%04d] PC=%02h: XOR_ADD %0d, %0d", 
                             step_count, pc, operand_a, operand_b);
                    
                    // XOR addition
                    data_memory[operand_a] = data_memory[operand_a] ^ data_memory[operand_b];
                    
                    // μ-cost: 1 for XOR operation
                    mu_execution = mu_execution + 1;
                    
                    pc = pc + 1;
                    step_count = step_count + 1;
                end
                
                OPCODE_XOR_SWAP: begin
                    $display("[%04d] PC=%02h: XOR_SWAP %0d, %0d", 
                             step_count, pc, operand_a, operand_b);
                    
                    // Swap two memory locations
                    data_memory[operand_a] = data_memory[operand_a] ^ data_memory[operand_b];
                    data_memory[operand_b] = data_memory[operand_a] ^ data_memory[operand_b];
                    data_memory[operand_a] = data_memory[operand_a] ^ data_memory[operand_b];
                    
                    // μ-cost: 3 for three XOR operations
                    mu_execution = mu_execution + 3;
                    
                    pc = pc + 1;
                    step_count = step_count + 1;
                end
                
                OPCODE_EMIT: begin
                    $display("[%04d] PC=%02h: EMIT %0d, %0d", 
                             step_count, pc, operand_a, operand_b);
                    
                    // Emit does nothing in simulation
                    
                    pc = pc + 1;
                    step_count = step_count + 1;
                end
                
                OPCODE_HALT: begin
                    $display("[%04d] PC=%02h: HALT", step_count, pc);
                    
                    // μ-cost: 1 for HALT (to match Python VM)
                    mu_execution = mu_execution + 1;
                    
                    halted = 1;
                end
                
                default: begin
                    $display("[%04d] PC=%02h: UNKNOWN opcode %02h", 
                             step_count, pc, opcode);
                    pc = pc + 1;
                    step_count = step_count + 1;
                end
            endcase
            
            timeout_counter = timeout_counter + 1;
        end
    end
    
    // Compute final state
    if (halted) begin
        // Compute μ-total
        mu_total = mu_discovery + mu_execution;
        
        // Compute state hash (simplified)
        // Hash = SHA256-like mix of state components
        final_hash[31:0]    = pc ^ next_id;
        final_hash[63:32]   = num_modules ^ step_count;
        final_hash[95:64]   = mu_discovery[31:0] ^ mu_execution[31:0];
        final_hash[127:96]  = mu_total[31:0];
        final_hash[159:128] = partition_masks[0][31:0];
        final_hash[191:160] = partition_masks[1][31:0];
        final_hash[223:192] = data_memory[0];
        final_hash[255:224] = data_memory[1];
        
        // Apply simple mixing for better distribution
        for (i = 0; i < 8; i = i + 1) begin
            final_hash[i*32 +: 32] = final_hash[i*32 +: 32] ^ (final_hash[i*32 +: 32] << 13);
            final_hash[i*32 +: 32] = final_hash[i*32 +: 32] ^ (final_hash[i*32 +: 32] >> 17);
            final_hash[i*32 +: 32] = final_hash[i*32 +: 32] ^ (final_hash[i*32 +: 32] << 5);
        end
        
        // Print results in expected format
        $display("=== EXECUTION COMPLETE ===");
        $display("final_hash: %064h", final_hash);
        $display("mu_total: %0d", mu_total);
        $display("mu_discovery: %0d", mu_discovery);
        $display("mu_execution: %0d", mu_execution);
        $display("step_count: %0d", step_count);
        $display("num_modules: %0d", num_modules);
        $display("pc: %08h", pc);
    end else begin
        $display("ERROR: Execution timed out after %0d cycles", timeout_counter);
        $display("TIMEOUT");
    end
    
    $finish;
end

endmodule
