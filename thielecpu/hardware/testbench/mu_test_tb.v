// μ-cost verification testbench
`timescale 1ns / 1ps
`include "generated_opcodes.vh"

module mu_test_tb;

localparam NUM_MODULES = 64;

reg clk;
reg rst_n;
wire [31:0] mu;
wire [31:0] status;
wire [31:0] error_code;

// Other outputs
wire [31:0] cert_addr, partition_ops, mdl_ops, info_gain;
wire [31:0] mem_addr, mem_wdata, logic_addr, py_code_addr;
wire mem_we, mem_en, logic_req, py_req;
reg [31:0] mem_rdata, logic_data, py_result;
reg logic_ack, py_ack;

reg [31:0] instr_memory [0:255];
wire [31:0] pc;

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
    .py_result(py_result)
);

assign pc = dut.pc;
integer i;

initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

// Initialize data memory in DUT after reset
initial begin
    #100;  // Wait for reset
    dut.data_mem[0] = 41;
    dut.data_mem[1] = 18;
    dut.data_mem[2] = 34;
    dut.data_mem[3] = 3;
end

initial begin
    $dumpfile("mu_test_tb.vcd");
    $dumpvars(0, mu_test_tb);

    rst_n = 0;
    mem_rdata = 0;
    logic_ack = 0;
    py_ack = 0;

    // Initialize instruction memory with COST=1 for each instruction
    // Format: {opcode[7:0], operand_a[7:0], operand_b[7:0], cost[7:0]}
    for (i = 0; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end

    // XOR_LOAD r0 <= mem[0], cost=1
    instr_memory[0] = {8'h0A, 8'h00, 8'h00, 8'h01};
    // XOR_LOAD r1 <= mem[1], cost=1
    instr_memory[1] = {8'h0A, 8'h01, 8'h01, 8'h01};
    // XOR_LOAD r2 <= mem[2], cost=1
    instr_memory[2] = {8'h0A, 8'h02, 8'h02, 8'h01};
    // XOR_LOAD r3 <= mem[3], cost=1
    instr_memory[3] = {8'h0A, 8'h03, 8'h03, 8'h01};
    // XOR_ADD r3 ^= r0, cost=1
    instr_memory[4] = {8'h0B, 8'h03, 8'h00, 8'h01};
    // XOR_ADD r3 ^= r1, cost=1
    instr_memory[5] = {8'h0B, 8'h03, 8'h01, 8'h01};
    // XOR_SWAP r0 <-> r3, cost=1
    instr_memory[6] = {8'h0C, 8'h00, 8'h03, 8'h01};
    // XFER r4 <- r2, cost=1
    instr_memory[7] = {8'h07, 8'h04, 8'h02, 8'h01};
    // XOR_RANK r5 := popcount(r4), cost=1
    instr_memory[8] = {8'h0D, 8'h05, 8'h04, 8'h01};
    // HALT, cost=0
    instr_memory[9] = {8'hFF, 8'h00, 8'h00, 8'h00};

    #10;
    rst_n = 1;

    // Wait for completion
    wait(dut.state == 6);  // STATE_HALT
    #50;

    $display("======================================================================");
    $display("μ-COST VERIFICATION");
    $display("======================================================================");
    $display("Final μ:     %d (expected: 9)", mu);
    $display("Registers:");
    $display("  r0 = %d (expected: 56)", dut.reg_file[0]);
    $display("  r1 = %d (expected: 18)", dut.reg_file[1]);
    $display("  r2 = %d (expected: 34)", dut.reg_file[2]);
    $display("  r3 = %d (expected: 41)", dut.reg_file[3]);
    $display("  r4 = %d (expected: 34)", dut.reg_file[4]);
    $display("  r5 = %d (expected: 2)", dut.reg_file[5]);
    $display("======================================================================");
    
    if (mu == 9 && 
        dut.reg_file[0] == 56 && dut.reg_file[1] == 18 &&
        dut.reg_file[2] == 34 && dut.reg_file[3] == 41 &&
        dut.reg_file[4] == 34 && dut.reg_file[5] == 2) begin
        $display("✅ VERILOG MATCHES COQ AND PYTHON - BIT-FOR-BIT IDENTICAL");
    end else begin
        $display("❌ MISMATCH DETECTED");
    end
    $display("======================================================================");

    $finish;
end

// Instruction fetch
always @(posedge clk) begin
    if (mem_en && !mem_we) begin
        if (mem_addr < 256 * 4) begin
            mem_rdata <= instr_memory[mem_addr[9:2]];
        end else begin
            mem_rdata <= 32'h0;
        end
    end
end

endmodule
