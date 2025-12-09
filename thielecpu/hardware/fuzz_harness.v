// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Fuzz Harness for Adversarial Falsification Testing
// ============================================================================
// 
// This testbench:
// 1. Reads a program from fuzz_program.hex
// 2. Executes it on the Thiele Core
// 3. Upon HALT, prints the final state_hash (256-bit hex)
// 4. Prints the mu_total to stdout
//
// Used by tests/adversarial_fuzzing.py to verify Python ↔ Verilog isomorphism

`timescale 1ns / 1ps

module fuzz_harness;

// ============================================================================
// SIGNALS
// ============================================================================

reg clk;
reg rst_n;

// CPU outputs
wire [31:0] cert_addr;
wire [31:0] status;
wire [31:0] error_code;
wire [31:0] partition_ops;
wire [31:0] mdl_ops;
wire [31:0] info_gain;

// Memory interface
wire [31:0] mem_addr;
wire [31:0] mem_wdata;
reg [31:0] mem_rdata;
wire mem_we;
wire mem_en;

// Logic engine interface
wire logic_req;
wire [31:0] logic_addr;
reg logic_ack;
reg [31:0] logic_data;

// Python execution interface
wire py_req;
wire [31:0] py_code_addr;
reg py_ack;
reg [31:0] py_result;

// Instruction memory
reg [31:0] instr_memory [0:255];
wire [31:0] pc;

// Data memory
reg [31:0] data_memory [0:1023];

// Loop variables
integer i, j;
integer program_length;

// Crypto receipt tracking
reg [255:0] state_hash;
reg [63:0] mu_total;
reg halted;

// ============================================================================
// CPU INSTANCE
// ============================================================================

thiele_cpu dut (
    .clk(clk),
    .rst_n(rst_n),
    .cert_addr(cert_addr),
    .status(status),
    .error_code(error_code),
    .partition_ops(partition_ops),
    .mdl_ops(mdl_ops),
    .info_gain(info_gain),
    .mem_addr(mem_addr),
    .mem_wdata(mem_wdata),
    .mem_rdata(mem_rdata),
    .mem_we(mem_we),
    .mem_en(mem_en),
    .logic_req(logic_req),
    .logic_addr(logic_addr),
    .logic_ack(logic_ack),
    .logic_data(logic_data),
    .py_req(py_req),
    .py_code_addr(py_code_addr),
    .py_ack(py_ack),
    .py_result(py_result),
    .instr_data(instr_memory[pc[31:2]]), // Word-aligned access
    .pc(pc)
);

// ============================================================================
// CLOCK GENERATION
// ============================================================================

initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100MHz clock
end

// ============================================================================
// LOAD PROGRAM FROM HEX FILE
// ============================================================================

initial begin
    // Initialize memories
    for (i = 0; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end
    for (i = 0; i < 1024; i = i + 1) begin
        data_memory[i] = 32'h00000000;
    end
    
    // Load program from hex file
    // Format: one 32-bit instruction per line in hex (e.g., "00000100")
    $display("Loading program from fuzz_program.hex");
    $readmemh("fuzz_program.hex", instr_memory);
    
    // Count non-zero instructions to determine program length
    program_length = 0;
    for (i = 0; i < 256; i = i + 1) begin
        if (instr_memory[i] != 32'h00000000) begin
            program_length = i + 1;
        end
    end
    $display("Program length: %d instructions", program_length);
    
    // Display loaded program for debugging
    for (i = 0; i < program_length && i < 10; i = i + 1) begin
        $display("  [%02d] %08h", i, instr_memory[i]);
    end
    if (program_length > 10) begin
        $display("  ... (%d more instructions)", program_length - 10);
    end
end

// ============================================================================
// EXTERNAL INTERFACE SIMULATION
// ============================================================================

// Memory simulation
always @(posedge clk) begin
    if (mem_en) begin
        if (mem_we) begin
            // Write operation
            data_memory[mem_addr[31:2]] <= mem_wdata;
        end else begin
            // Read operation
            mem_rdata <= data_memory[mem_addr[31:2]];
        end
    end
end

// Logic engine simulation (stub)
always @(posedge clk) begin
    if (logic_req && !logic_ack) begin
        #10 logic_data <= 32'h00000000;
        logic_ack <= 1'b1;
    end else begin
        logic_ack <= 1'b0;
    end
end

// Python execution simulation (stub)
always @(posedge clk) begin
    if (py_req && !py_ack) begin
        #15 py_result <= 32'h00000000;
        py_ack <= 1'b1;
    end else begin
        py_ack <= 1'b0;
    end
end

// ============================================================================
// STATE HASH COMPUTATION (SIMPLIFIED)
// ============================================================================
// 
// In a full implementation, this would use crypto_receipt_controller.v
// For fuzzing, we compute a simplified hash based on observable CPU state

always @(posedge clk) begin
    if (rst_n) begin
        // Compute simple state hash from CPU state
        // This is a placeholder - in production, use crypto_receipt_controller
        state_hash[31:0]    <= pc ^ cert_addr;
        state_hash[63:32]   <= status ^ error_code;
        state_hash[95:64]   <= partition_ops ^ mdl_ops;
        state_hash[127:96]  <= info_gain;
        state_hash[159:128] <= mem_addr ^ mem_wdata;
        state_hash[191:160] <= {16'h0, instr_memory[pc[31:2]][31:16]};
        state_hash[223:192] <= {16'h0, instr_memory[pc[31:2]][15:0]};
        state_hash[255:224] <= 32'hFACEB00C; // Magic constant
        
        // Track μ-total (simplified - sum of operation counters)
        mu_total <= partition_ops + mdl_ops + info_gain;
    end
end

// ============================================================================
// TEST SEQUENCE
// ============================================================================

initial begin
    // Initialize
    rst_n = 0;
    logic_ack = 0;
    py_ack = 0;
    mem_rdata = 32'h0;
    halted = 0;

    // Reset
    #20 rst_n = 1;
    
    $display("Starting execution...");

    // Wait for program completion or timeout
    fork
        begin
            #100000; // Timeout after 100us
            $display("ERROR: Simulation timed out");
            $display("TIMEOUT");
            $finish;
        end
        begin
            // Wait for HALT opcode
            forever begin
                @(posedge clk);
                if (rst_n && instr_memory[pc[31:2]][31:24] == 8'hFF) begin
                    // Found HALT instruction
                    #100; // Wait a few cycles for state to settle
                    halted = 1;
                    
                    // Print results in format expected by fuzzing script
                    $display("=== EXECUTION COMPLETE ===");
                    $display("final_hash: %064h", state_hash);
                    $display("mu_total: %d", mu_total);
                    $display("pc: %08h", pc);
                    $display("status: %08h", status);
                    $display("error: %08h", error_code);
                    $display("partition_ops: %d", partition_ops);
                    $display("mdl_ops: %d", mdl_ops);
                    $display("info_gain: %d", info_gain);
                    
                    $finish;
                end
            end
        end
    join
end

// ============================================================================
// MONITORING (Optional - disable for performance)
// ============================================================================

// Uncomment for detailed debugging
// always @(posedge clk) begin
//     if (rst_n) begin
//         $display("Time: %t, PC: %h, Instr: %h",
//                  $time, pc, instr_memory[pc[31:2]]);
//     end
// end

endmodule
