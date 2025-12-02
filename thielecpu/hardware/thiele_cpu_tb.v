// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Thiele CPU Testbench
// ============================================================================

`timescale 1ns / 1ps

module thiele_cpu_tb;

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
wire [31:0] mu_total_hw;  // Total μ-cost from hardware

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
reg [31:0] data_memory [0:255];

// Loop variable
integer i;

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
    .mu_total(mu_total_hw),
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
// TEST PROGRAM
// ============================================================================

initial begin
    // Initialize instruction memory with test program
    // Aligned with examples/neural_crystallizer.thm for cross-substrate verification.
    // Includes PNEW {1} at start and MDLACC before HALT to verify thermodynamic accounting.
    instr_memory[0] = {8'h00, 8'h00, 8'h01, 8'h00}; // PNEW {1} - create partition with region {1}
    // XOR operations for Gaussian elimination
    instr_memory[1] = {8'h0B, 8'h03, 8'h00, 8'h00}; // XOR_ADD 3, 0
    instr_memory[2] = {8'h0B, 8'h03, 8'h01, 8'h00}; // XOR_ADD 3, 1
    instr_memory[3] = {8'h0B, 8'h03, 8'h02, 8'h00}; // XOR_ADD 3, 2
    instr_memory[4] = {8'h0B, 8'h00, 8'h03, 8'h00}; // XOR_ADD 0, 3
    instr_memory[5] = {8'h0B, 8'h01, 8'h03, 8'h00}; // XOR_ADD 1, 3
    instr_memory[6] = {8'h0B, 8'h02, 8'h03, 8'h00}; // XOR_ADD 2, 3
    instr_memory[7] = {8'h0B, 8'h03, 8'h00, 8'h00}; // XOR_ADD 3, 0
    instr_memory[8] = {8'h0B, 8'h01, 8'h02, 8'h00}; // XOR_ADD 1, 2
    instr_memory[9] = {8'h0E, 8'h00, 8'h06, 8'h00}; // EMIT 0, 6
    instr_memory[10] = {8'h05, 8'h00, 8'h00, 8'h00}; // MDLACC - accumulate μ-cost for partition
    // HALT
    instr_memory[11] = {8'hFF, 8'h00, 8'h00, 8'h00}; // HALT

    // Initialize data memory with XOR matrix
    // Row 0: 1 0 0 1 0 1 -> 0x29 (bits 0,3,5)
    data_memory[0] = 32'h00000029;
    // Row 1: 0 1 0 0 1 0 -> 0x12 (bits 1,4)
    data_memory[6] = 32'h00000012;
    // Row 2: 0 0 1 0 0 1 -> 0x22 (bits 1,5)
    data_memory[12] = 32'h00000022;
    // Row 3: 1 1 0 0 0 0 -> 0x03 (bits 0,1)
    data_memory[18] = 32'h00000003;
    // Parity
    data_memory[24] = 32'h00000000; // row 0 parity 0
    data_memory[25] = 32'h00000001; // row 1 parity 1
    data_memory[26] = 32'h00000001; // row 2 parity 1
    data_memory[27] = 32'h00000000; // row 3 parity 0

    // Initialize other memory locations
    for (i = 12; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end
    for (i = 0; i < 256; i = i + 1) begin
        if (i != 0 && i != 6 && i != 12 && i != 18 && i != 24 && i != 25 && i != 26 && i != 27) begin
            data_memory[i] = 32'h00000000;
        end
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

// Logic engine simulation
always @(posedge clk) begin
    if (logic_req && !logic_ack) begin
        // Simulate logic engine response
        #10 logic_data <= 32'hABCD1234;
        logic_ack <= 1'b1;
    end else begin
        logic_ack <= 1'b0;
    end
end

// Python execution simulation
always @(posedge clk) begin
    if (py_req && !py_ack) begin
        // Simulate Python execution response
        #15 py_result <= 32'h12345678;
        py_ack <= 1'b1;
    end else begin
        py_ack <= 1'b0;
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

    // Reset
    #20 rst_n = 1;

    // Wait for program completion or timeout
    fork
        begin
            #10000; // Timeout after 10000 ns
            $display("Simulation timed out");
            $finish;
        end
        begin
            wait (pc == 32'h30); // Wait for PC to reach HALT address (12 instructions * 4 bytes = 0x30)
            #10; // Small delay
            // Check results
            $display("Test completed!");
            $display("Final PC: %h", pc);
            $display("Status: %h", status);
            $display("Error: %h", error_code);
            $display("Cert Addr: %h", cert_addr);
            $display("Partition Ops: %d", partition_ops);
            $display("MDL Ops: %d", mdl_ops);
            $display("Info Gain: %d", info_gain);
            $display("Mu Total: %d", mu_total_hw);
            $display("{");
            $display("  \"partition_ops\": %d,", partition_ops);
            $display("  \"mdl_ops\": %d,", mdl_ops);
            $display("  \"info_gain\": %d,", info_gain);
            $display("  \"mu_total\": %d", mu_total_hw);
            $display("}");
            $finish;
        end
    join
end

// ============================================================================
// MONITORING
// ============================================================================

always @(posedge clk) begin
    if (rst_n) begin
        $display("Time: %t, PC: %h, State: %h, Status: %h, Error: %h, Mu: %d",
                 $time, pc, dut.state, status, error_code, mu_total_hw);
    end
end

endmodule