// Minimal generated testbench for Trinity
`timescale 1ns / 1ps
module thiele_cpu_tb;
reg clk; reg rst_n;
wire [31:0] cert_addr, status, error_code, partition_ops, mdl_ops, info_gain;
wire [31:0] mem_addr, mem_wdata, pc; wire mem_we, mem_en; reg [31:0] mem_rdata;
wire logic_req; wire [31:0] logic_addr; reg logic_ack; reg [31:0] logic_data;
wire py_req; wire [31:0] py_code_addr; reg py_ack; reg [31:0] py_result;
reg [31:0] instr_memory [0:255]; reg [31:0] data_memory [0:255];
integer i;
thiele_cpu dut (
    .clk(clk), .rst_n(rst_n), .cert_addr(cert_addr), .status(status), .error_code(error_code),
    .partition_ops(partition_ops), .mdl_ops(mdl_ops), .info_gain(info_gain),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_rdata(mem_rdata), .mem_we(mem_we), .mem_en(mem_en),
    .logic_req(logic_req), .logic_addr(logic_addr), .logic_ack(logic_ack), .logic_data(logic_data),
    .py_req(py_req), .py_code_addr(py_code_addr), .py_ack(py_ack), .py_result(py_result),
    .instr_data(instr_memory[pc[31:2]]), .pc(pc)
);
initial begin clk = 0; forever #5 clk = ~clk; end
initial begin
  $readmemh("artifacts/trinity_cost_test/program.mem", instr_memory);
  for (i = 0; i < 256; i = i + 1) data_memory[i] = 32'h00000000;
  rst_n = 0; logic_ack = 0; py_ack = 0; mem_rdata = 32'h0;
  #20 rst_n = 1;
    fork
        begin
            #10000;
            $display("Simulation timed out");
            $finish;
        end
        begin
            wait (pc == 32'h28);
            #10;
            $display("Test completed!");
            $display("Final PC: %h", pc);
            $display("Status: %h", status);
            $display("Error: %h", error_code);
            $display("Partition Ops: %d", partition_ops);
            $display("MDL Ops: %d", mdl_ops);
            $display("Info Gain: %d", info_gain);
            $display("{\"partition_ops\": %d, \"mdl_ops\": %d, \"info_gain\": %d, \"mu_total\": %d}", partition_ops, mdl_ops, info_gain, dut.mu_accumulator);
            
            $finish;
        end
  join
end
always @(posedge clk) begin if (mem_en) begin if (mem_we) data_memory[mem_addr[31:2]] <= mem_wdata; else mem_rdata <= data_memory[mem_addr[31:2]]; end end
always @(posedge clk) begin if (logic_req && !logic_ack) begin #10 logic_data <= 32'hABCD1234; logic_ack <= 1'b1; end else logic_ack <= 1'b0; end
always @(posedge clk) begin if (py_req && !py_ack) begin #15 py_result <= 32'h12345678; py_ack <= 1'b1; end else py_ack <= 1'b0; end
always @(posedge clk) begin if (rst_n) $display("Time: %t, PC: %h, State: %h, Status: %h, Error: %h", $time, pc, dut.state, status, error_code); end
endmodule
