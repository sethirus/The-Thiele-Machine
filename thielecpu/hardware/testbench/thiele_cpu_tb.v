// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Thiele CPU Testbench
// ============================================================================

`timescale 1ns / 1ps

module thiele_cpu_tb;

// Opcodes are generated from Coq extraction and must match the RTL decode.
`include "generated_opcodes.vh"

`ifdef YOSYS_LITE
localparam NUM_MODULES = 4;
`else
localparam NUM_MODULES = 64;
`endif

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
wire [31:0] mu;

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

// Optional file inputs
reg [1023:0] program_hex_path;
reg [1023:0] data_hex_path;
integer have_program_hex;
integer have_data_hex;

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
    .mu(mu),
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
    have_program_hex = $value$plusargs("PROGRAM=%s", program_hex_path);
    have_data_hex = $value$plusargs("DATA=%s", data_hex_path);

    // Initialize instruction memory
    for (i = 0; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end

    if (have_program_hex) begin
        $display("Loading PROGRAM=%0s", program_hex_path);
        $readmemh(program_hex_path, instr_memory);
    end else begin
        // Default compute program using only VALID opcodes from generated_opcodes.vh
        // Tests: XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK, XFER, EMIT, HALT
        
        // 1) Load 4 values from memory into r0..r3
        instr_memory[0] = {8'h0A, 8'h00, 8'h00, 8'h00}; // XOR_LOAD r0 <= mem[0] = 0x29
        instr_memory[1] = {8'h0A, 8'h01, 8'h01, 8'h00}; // XOR_LOAD r1 <= mem[1] = 0x12
        instr_memory[2] = {8'h0A, 8'h02, 8'h02, 8'h00}; // XOR_LOAD r2 <= mem[2] = 0x22
        instr_memory[3] = {8'h0A, 8'h03, 8'h03, 8'h00}; // XOR_LOAD r3 <= mem[3] = 0x03

        // 2) XOR algebra operations
        instr_memory[4] = {8'h0B, 8'h03, 8'h00, 8'h00}; // XOR_ADD r3 ^= r0 => 0x03 ^ 0x29 = 0x2A
        instr_memory[5] = {8'h0B, 8'h03, 8'h01, 8'h00}; // XOR_ADD r3 ^= r1 => 0x2A ^ 0x12 = 0x38
        instr_memory[6] = {8'h0C, 8'h00, 8'h03, 8'h00}; // XOR_SWAP r0 <-> r3 => r0=0x38, r3=0x29
        
        // 3) Rank and transfer operations
        instr_memory[7] = {8'h07, 8'h04, 8'h02, 8'h00}; // XFER r4 <- r2 = 0x22 (dest, src operand order)
        instr_memory[8] = {8'h0D, 8'h05, 8'h04, 8'h00}; // XOR_RANK r5 := popcount(r4) = popcount(0x22) = 2
        
        // 4) EMIT instruction (0x0E) - adds to info_gain counter
        instr_memory[9] = {8'h0E, 8'h00, 8'h04, 8'h00}; // EMIT with info_gain = operand_b = 4
        
        // 5) HALT
        instr_memory[10] = {8'hFF, 8'h00, 8'h00, 8'h00}; // HALT
    end

    // Initialize external data memory (kept for legacy mem interface)
    for (i = 0; i < 256; i = i + 1) begin
        data_memory[i] = 32'h00000000;
    end

    // Load initial compute-memory image into testbench buffer.
    // NOTE: we copy this into dut.data_mem *after* reset deassert,
    // otherwise the DUT reset logic will overwrite it.
    if (have_data_hex) begin
        $display("Loading DATA=%0s", data_hex_path);
        $readmemh(data_hex_path, data_memory);
    end else begin
        // Default data values used by the default program
        data_memory[0] = 32'h00000029;
        data_memory[1] = 32'h00000012;
        data_memory[2] = 32'h00000022;
        data_memory[3] = 32'h00000003;
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
    
    // Enable VCD dumping for waveform generation
    $dumpfile("thiele_cpu_tb.vcd");
    $dumpvars(0, thiele_cpu_tb);

    // Reset
    #20 rst_n = 1;

    // After reset deassert and before the next clock edge, preload DUT compute memory.
    #1;
    for (i = 0; i < 256; i = i + 1) begin
        dut.data_mem[i] = data_memory[i];
    end

    // Wait for program completion or timeout
    fork
        begin
            #10000; // Timeout after 10000 ns
            $display("Simulation timed out");
            $finish;
        end
        begin
            // Stop when the CPU is executing the HALT opcode.
            // This allows external +PROGRAM hex files of arbitrary length.
            wait (dut.state == 4'h2 && dut.opcode == OPCODE_HALT);
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
            $display("{");
            $display("  \"status\": %d,", status);
            $display("  \"partition_ops\": %d,", partition_ops);
            $display("  \"mdl_ops\": %d,", mdl_ops);
            $display("  \"info_gain\": %d,", info_gain);
            $display("  \"mu\": %d,", mu);
            $display("  \"regs\": [");
            for (i = 0; i < 32; i = i + 1) begin
                if (i < 31) $display("    %0d,", dut.reg_file[i]);
                else $display("    %0d", dut.reg_file[i]);
            end
            $display("  ],");
            $display("  \"mem\": [");
            for (i = 0; i < 256; i = i + 1) begin
                if (i < 255) $display("    %0d,", dut.data_mem[i]);
                else $display("    %0d", dut.data_mem[i]);
            end
            $display("  ],");
            $display("  \"modules\": [");
            for (i = 0; i < NUM_MODULES; i = i + 1) begin
                if (dut.module_table[i] != 0) begin
                    integer k;
                    $display("    {\"id\": %0d, \"region\": [", i);
                    for (k = 0; k < dut.module_table[i]; k = k + 1) begin
                        if (k < dut.module_table[i]-1) $display("      %0d,", dut.region_table[i][k]);
                        else $display("      %0d", dut.region_table[i][k]);
                    end
                    $display("    ]},");
                end
            end
            $display("    {\"id\": -1, \"region\": []}");
            $display("  ]");
            $display("}");
            $finish;
        end
    join
end

// ============================================================================
// MONITORING
// ============================================================================

`ifdef VERBOSE
always @(posedge clk) begin
    if (rst_n) begin
        $display("Time: %t, PC: %h, State: %h, Status: %h, Error: %h, MU: %h",
                 $time, pc, dut.state, status, error_code, mu);
    end
end
`endif

// Emit CHSH trial events as traceable stdout lines.
// These are parsed by the 3-layer pytest gate and converted into canonical
// step receipts for CHSH computation.
always @(posedge clk) begin
    if (rst_n) begin
        // STATE_EXECUTE is 4'h2 in thiele_cpu.v.
        if (dut.state == 4'h2 && dut.opcode == OPCODE_CHSH_TRIAL) begin
            $display(
                "CHSH_TRIAL %0d %0d %0d %0d",
                dut.operand_a[1],
                dut.operand_a[0],
                dut.operand_b[1],
                dut.operand_b[0]
            );
        end
    end
end

endmodule