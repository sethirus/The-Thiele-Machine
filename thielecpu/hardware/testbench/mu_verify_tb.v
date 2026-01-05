// Minimal μ-cost verification testbench
`timescale 1ns / 1ps
`include "generated_opcodes.vh"

module mu_verify_tb;

reg clk = 0;
always #5 clk = ~clk;

reg rst_n = 0;
wire [31:0] mu, status, error_code, cert_addr, pc;
wire [31:0] partition_ops, mdl_ops, info_gain;
wire [31:0] mem_addr, mem_wdata, logic_addr, py_code_addr;
wire mem_we, mem_en, logic_req, py_req;
reg [31:0] mem_rdata = 0;
reg logic_ack = 0, py_ack = 0;
reg [31:0] logic_data = 0, py_result = 0;

// Instruction memory - connected via instr_data port
reg [31:0] instr_rom [0:255];
wire [31:0] instr_data = instr_rom[pc[9:2]];

thiele_cpu dut (
    .clk(clk), .rst_n(rst_n),
    .cert_addr(cert_addr), .status(status), .error_code(error_code),
    .partition_ops(partition_ops), .mdl_ops(mdl_ops), 
    .info_gain(info_gain), .mu(mu),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_rdata(mem_rdata),
    .mem_we(mem_we), .mem_en(mem_en),
    .logic_req(logic_req), .logic_addr(logic_addr),
    .logic_ack(logic_ack), .logic_data(logic_data),
    .py_req(py_req), .py_code_addr(py_code_addr),
    .py_ack(py_ack), .py_result(py_result),
    .instr_data(instr_data),
    .pc(pc)
);

integer i;

initial begin
    $dumpfile("mu_verify_tb.vcd");
    $dumpvars(0, mu_verify_tb);
    
    // Initialize all instruction memory to NOP/HALT
    for (i = 0; i < 256; i = i + 1) begin
        instr_rom[i] = {8'hFF, 8'h00, 8'h00, 8'h00};  // HALT
    end
    
    // Simple program: 4 XOR_LOADs with cost=1 each, then HALT
    // Format: {opcode[31:24], operand_a[23:16], operand_b[15:8], cost[7:0]}
    instr_rom[0] = {8'h0A, 8'h00, 8'h00, 8'h01};  // XOR_LOAD r0 mem[0] cost=1
    instr_rom[1] = {8'h0A, 8'h01, 8'h01, 8'h01};  // XOR_LOAD r1 mem[1] cost=1
    instr_rom[2] = {8'h0A, 8'h02, 8'h02, 8'h01};  // XOR_LOAD r2 mem[2] cost=1
    instr_rom[3] = {8'h0A, 8'h03, 8'h03, 8'h01};  // XOR_LOAD r3 mem[3] cost=1
    instr_rom[4] = {8'hFF, 8'h00, 8'h00, 8'h00};  // HALT cost=0
    
    // Set initial data memory
    #1;
    dut.data_mem[0] = 41;
    dut.data_mem[1] = 18;
    dut.data_mem[2] = 34;
    dut.data_mem[3] = 3;
    
    #20 rst_n = 1;
    
    // Wait for halt state or timeout
    repeat(200) @(posedge clk);
    
    $display("=========================================");
    $display("μ-COST VERIFICATION RESULTS");
    $display("=========================================");
    $display("PC = %d", pc);
    $display("μ = %d (expected: 4)", mu);
    $display("r0 = %d (expected: 41)", dut.reg_file[0]);
    $display("r1 = %d (expected: 18)", dut.reg_file[1]);
    $display("r2 = %d (expected: 34)", dut.reg_file[2]);
    $display("r3 = %d (expected: 3)", dut.reg_file[3]);
    $display("=========================================");
    
    if (mu == 4 && dut.reg_file[0] == 41 && dut.reg_file[1] == 18 &&
        dut.reg_file[2] == 34 && dut.reg_file[3] == 3) begin
        $display("✅ PASS: Verilog μ and registers match expected values");
    end else begin
        $display("❌ FAIL: Mismatch detected");
        if (mu != 4) $display("  μ mismatch: got %d, expected 4", mu);
    end
    
    $finish;
end

endmodule
