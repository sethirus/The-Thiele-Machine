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
    // PNEW {10} - Create module with region size 10
    instr_memory[0] = {8'h00, 8'h00, 8'h0A, 8'h00}; // PNEW 0, 10

    // PSPLIT 1, 0 - Split module 1 with predicate 0 (even/odd)
    instr_memory[1] = {8'h01, 8'h01, 8'h00, 8'h00}; // PSPLIT 1, 0

    // PMERGE 2, 3 - Merge modules 2 and 3
    instr_memory[2] = {8'h02, 8'h02, 8'h03, 8'h00}; // PMERGE 2, 3

    // MDLACC 4 - Accumulate μ-bits for module 4
    instr_memory[3] = {8'h05, 8'h04, 8'h00, 8'h00}; // MDLACC 4

    // EMIT 1, 2 - Emit value
    instr_memory[4] = {8'h06, 8'h01, 8'h02, 8'h00}; // EMIT 1, 2

    // HALT (unknown opcode)
    instr_memory[5] = {8'hFF, 8'h00, 8'h00, 8'h00}; // HALT

    // Initialize other memory locations
    for (i = 6; i < 256; i = i + 1) begin
        instr_memory[i] = 32'h00000000;
    end
end

// ============================================================================
// EXTERNAL INTERFACE SIMULATION
// ============================================================================

// Memory simulation
always @(posedge clk) begin
    if (mem_en) begin
        if (mem_we) begin
            // Write operation (not used in this test)
        end else begin
            // Read operation - return instruction data
            mem_rdata <= instr_memory[mem_addr[31:2]];
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

    // Wait for program execution
    #1000;

    // Check results
    $display("Test completed!");
    $display("Final PC: %h", pc);
    $display("Status: %h", status);
    $display("Error: %h", error_code);
    $display("Cert Addr: %h", cert_addr);

    // End simulation
    #100 $finish;
end

// ============================================================================
// MONITORING
// ============================================================================

always @(posedge clk) begin
    if (rst_n) begin
        $display("Time: %t, PC: %h, State: %h, Status: %h, Error: %h",
                 $time, pc, dut.state, status, error_code);
    end
end

endmodule