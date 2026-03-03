// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Thiele CPU External Engines Integration Smoke Test
// - Instantiates thiele_cpu + LEI + PEE
// - Runs a tiny program that exercises LASSERT and PYEXEC handshakes
// ============================================================================

`timescale 1ns / 1ps

module thiele_cpu_engines_tb;

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

// Memory interface (currently stubbed in thiele_cpu)
wire [31:0] mem_addr;
wire [31:0] mem_wdata;
reg  [31:0] mem_rdata;
wire mem_we;
wire mem_en;

// Logic engine interface
wire logic_req;
wire [31:0] logic_addr;
wire logic_ack;
wire [31:0] logic_data;

// Python execution interface
wire py_req;
wire [31:0] py_code_addr;
wire py_ack;
wire [31:0] py_result;

// Instruction memory
reg [31:0] instr_memory [0:255];
wire [31:0] pc;
wire [31:0] instr_data;

`include "generated_opcodes.vh"

assign instr_data = instr_memory[pc[31:2]];

// ============================================================================
// DUT: CPU
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
    .instr_data(instr_data),
    .pc(pc)
);

// ============================================================================
// LEI: internal Z3 mock (purely combinational response)
// ============================================================================

wire z3_req;
wire [31:0] z3_formula_addr;
wire z3_ack;
wire [31:0] z3_result;
wire z3_sat;
wire [31:0] z3_cert_hash;

assign z3_ack = 1'b1;
assign z3_result = z3_formula_addr ^ 32'hDEADBEEF;
assign z3_sat = 1'b1;
assign z3_cert_hash = z3_formula_addr ^ 32'hC0FFEE00;

wire cert_write;
wire [31:0] cert_addr_int;
wire [31:0] cert_data_int;
wire [31:0] lei_status;
wire lei_error;

lei lei_inst (
    .clk(clk),
    .rst_n(rst_n),
    .logic_req(logic_req),
    .logic_addr(logic_addr),
    .logic_ack(logic_ack),
    .logic_data(logic_data),
    .z3_req(z3_req),
    .z3_formula_addr(z3_formula_addr),
    .z3_ack(z3_ack),
    .z3_result(z3_result),
    .z3_sat(z3_sat),
    .z3_cert_hash(z3_cert_hash),
    .cert_write(cert_write),
    .cert_addr(cert_addr_int),
    .cert_data(cert_data_int),
    .lei_status(lei_status),
    .lei_error(lei_error)
);

// ============================================================================
// PEE: internal Python mock (purely combinational response)
// ============================================================================

wire python_req;
wire [31:0] python_code_addr;
wire python_ack;
wire [31:0] python_result;
wire python_error;

assign python_ack = 1'b1;
assign python_result = python_code_addr ^ 32'h12345678;
assign python_error = 1'b0;

wire symbolic_req;
wire [31:0] symbolic_vars;
wire symbolic_ack;
wire [31:0] symbolic_assignment;

assign symbolic_ack = 1'b1;
assign symbolic_assignment = 32'h0;

wire [31:0] pee_status;
wire pee_error;

pee pee_inst (
    .clk(clk),
    .rst_n(rst_n),
    .py_req(py_req),
    .py_code_addr(py_code_addr),
    .py_ack(py_ack),
    .py_result(py_result),
    .python_req(python_req),
    .python_code_addr(python_code_addr),
    .python_ack(python_ack),
    .python_result(python_result),
    .python_error(python_error),
    .symbolic_req(symbolic_req),
    .symbolic_vars(symbolic_vars),
    .symbolic_ack(symbolic_ack),
    .symbolic_assignment(symbolic_assignment),
    .pee_status(pee_status),
    .pee_error(pee_error)
);

// ============================================================================
// Clock + reset
// ============================================================================

initial begin
    clk = 1'b0;
    forever #5 clk = ~clk;
end

integer i;

initial begin
    mem_rdata = 32'h0;

    for (i = 0; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h0;
    end

    // Tiny program:
    //   0: LASSERT 0x12 0x34 -> expects cert_addr = (0x00001234 ^ 0xDEADBEEF) = 0xDEADACDB
    //   1: PYEXEC  0xAB 0xCD -> expects status   = (0x0000ABCD ^ 0x12345678) = 0x1234FDB5
    //   2: HALT (does not stop CPU; used as a PC marker)
    instr_memory[0] = {OPCODE_LASSERT, 8'h12, 8'h34, 8'h00};
    instr_memory[1] = {OPCODE_PYEXEC,  8'hAB, 8'hCD, 8'h00};
    instr_memory[2] = {OPCODE_HALT,    8'h00, 8'h00, 8'h00};

    rst_n = 1'b0;
    #20 rst_n = 1'b1;

    // Wait for program to advance past HALT (pc==12)
    for (i = 0; i < 300; i = i + 1) begin
        @(posedge clk);
        if (pc == 32'd12) begin
            if (cert_addr !== 32'hDEADACDB) begin
                $fatal(1, "LASSERT failed: expected cert_addr=0xDEADACDB got=0x%08h", cert_addr);
            end
            if (status !== 32'h1234FDB5) begin
                $fatal(1, "PYEXEC failed: expected status=0x1234FDB5 got=0x%08h", status);
            end
            $display("ENGINES_SMOKE_OK cert=0x%08h status=0x%08h", cert_addr, status);
            $finish;
        end
    end

    $fatal(1, "Timeout waiting for pc==12 (pc=0x%08h cert=0x%08h status=0x%08h)", pc, cert_addr, status);
end

endmodule
