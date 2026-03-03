// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Thiele CPU Inverse Genesis Hardware-CoSim Testbench
//
// Goal: drive the end-to-end inverse_genesis receipt generation + verification
// through the *Verilog CPU* using the PYEXEC interface.
//
// The CPU runs a tiny program:
//   1) PYEXEC code_addr=0x0001  (generate receipt)
//   2) PYEXEC code_addr=0x0002  (verify receipt)
//   3) HALT
//
// The testbench services `py_req` via file-based IPC to a long-running Python
// bridge system task ($pyexec) implemented via Icarus VPI. This avoids relying
// on `$system`, which is not available in this Icarus build.
// ============================================================================

`timescale 1ns / 1ps

`include "generated_opcodes.vh"

module thiele_cpu_inverse_genesis_tb;

reg clk;
reg rst_n;

wire [31:0] cert_addr;
wire [31:0] status;
wire [31:0] error_code;
wire [31:0] partition_ops;
wire [31:0] mdl_ops;
wire [31:0] info_gain;
wire [31:0] mu;

wire [31:0] mem_addr;
wire [31:0] mem_wdata;
reg  [31:0] mem_rdata;
wire mem_we;
wire mem_en;

wire logic_req;
wire [31:0] logic_addr;
reg logic_ack;
reg [31:0] logic_data;

wire py_req;
wire [31:0] py_code_addr;
reg py_ack;
reg [31:0] py_result;

reg [31:0] instr_memory [0:255];
wire [31:0] pc;

integer i;

// Plusargs
reg [1023:0] repo_root;
integer have_repo_root;

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
    .instr_data(instr_memory[pc[31:2]]),
    .pc(pc)
);

// 100MHz clock
initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

initial begin
    have_repo_root = $value$plusargs("REPO_ROOT=%s", repo_root);
    if (!have_repo_root) begin
        $display("ERROR: missing +REPO_ROOT=<path> plusarg");
        $finish;
    end

    for (i = 0; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end

    // Program: PYEXEC(0x0001) -> PYEXEC(0x0002) -> HALT
    instr_memory[0] = {OPCODE_PYEXEC, 8'h00, 8'h01, 8'h01};
    instr_memory[1] = {OPCODE_PYEXEC, 8'h00, 8'h02, 8'h01};
    instr_memory[2] = {OPCODE_HALT,   8'h00, 8'h00, 8'h00};

end

// Simple memory interface (unused by this program but keep stable)
always @(posedge clk) begin
    if (mem_en) begin
        if (mem_we) begin
            // ignore writes
        end else begin
            mem_rdata <= 32'h0;
        end
    end
end

// Stub logic engine
always @(posedge clk) begin
    if (logic_req && !logic_ack) begin
        #10 logic_data <= 32'h0;
        logic_ack <= 1'b1;
    end else begin
        logic_ack <= 1'b0;
    end
end

// Python execution co-sim ($pyexec VPI)
initial begin
    forever begin
        @(posedge clk);
        if (py_req && !py_ack) begin
            integer rc;

            $display("[RTL] PYEXEC request: code_addr=0x%0h", py_code_addr);
            $pyexec(py_code_addr, rc);
            py_result <= rc;
            $display("[RTL] PYEXEC complete: rc=%0d", rc);

            // Enforce success for all PYEXEC calls.
            if (rc !== 0) begin
                $display("[RTL] ERROR: PYEXEC failed for code_addr=0x%0h rc=%0d", py_code_addr, rc);
                $finish;
            end

            // Pulse ack for one cycle.
            py_ack <= 1'b1;
            @(posedge clk);
            py_ack <= 1'b0;
        end
    end
end

initial begin
    rst_n = 0;
    logic_ack = 0;
    py_ack = 0;
    mem_rdata = 32'h0;

    $dumpfile("thiele_cpu_inverse_genesis_tb.vcd");
    $dumpvars(0, thiele_cpu_inverse_genesis_tb);

    #20 rst_n = 1;

    fork
        begin
            #200000; // generous timeout
            $display("[RTL] Simulation timed out");
            $finish;
        end
        begin
            wait (dut.state == 4'h2 && dut.opcode == OPCODE_HALT);
            #10;
            $display("[RTL] Test completed!");
            $display("[RTL] Final PC: %h", pc);
            $display("[RTL] Final Status: %h", status);
            $display("[RTL] Error: %h", error_code);
            $finish;
        end
    join
end

endmodule
