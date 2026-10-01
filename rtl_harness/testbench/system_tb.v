// system_tb.v: drives the extracted system (mkThieleSystem) only through its
// pins, the way a host computer would over the board's USB-UART.
//
// It sends a program as serial frames (+BYTES=<hex file>, +N_BYTES=<count>):
// two bytes of instruction count, then sixteen bytes per instruction, least
// significant first, one start bit, eight data bits and one stop bit each, at
// CPB clock cycles per bit. It then receives the fifteen-byte report the
// system sends when the program stops and prints it as JSON.
//
// The same testbench runs against the extracted Verilog and against a gate
// netlist synthesized from it; the two reports must be equal.
`timescale 1ns/1ps

module system_tb;
  localparam CPB = 174;  // ClksPerBit in coq/kami_hw/ThieleLoader.v

  reg clk = 1'b0;
  always #5 clk = ~clk;

  reg rst_n = 1'b0;
  reg rx = 1'b1;
  wire tx;
  wire [3:0] leds;

  mkThieleSystem dut (
    .CLK(clk), .RST_N(rst_n),
    .rxSample_x_0(rx), .EN_rxSample(1'b1), .RDY_rxSample(),
    .EN_getTx(1'b1), .getTx(tx), .RDY_getTx(),
    .EN_getLeds(1'b1), .getLeds(leds), .RDY_getLeds()
  );

  reg [7:0] stream [0:4095];
  reg [7:0] report [0:14];
  reg [1023:0] bytes_path;
  integer n_bytes, i, j, ks, kr, max_cycles;
  reg [7:0] v;

  task send_byte(input [7:0] value);
    begin
      rx = 1'b0;
      repeat (CPB) @(posedge clk);
      for (ks = 0; ks < 8; ks = ks + 1) begin
        rx = value[ks];
        repeat (CPB) @(posedge clk);
      end
      rx = 1'b1;
      repeat (CPB) @(posedge clk);
    end
  endtask

  task recv_byte(output [7:0] value);
    begin
      @(negedge tx);
      repeat (CPB / 2) @(posedge clk);
      for (kr = 0; kr < 8; kr = kr + 1) begin
        repeat (CPB) @(posedge clk);
        value[kr] = tx;
      end
      repeat (CPB) @(posedge clk);
    end
  endtask

  initial begin
    if (!$value$plusargs("MAX_CYCLES=%d", max_cycles)) max_cycles = 20000000;
    repeat (max_cycles) @(posedge clk);
    $display("{\"timeout\": 1}");
    $finish;
  end

  initial begin
    if (!$value$plusargs("BYTES=%s", bytes_path)) begin
      $display("{\"error\": \"no +BYTES\"}");
      $finish;
    end
    if (!$value$plusargs("N_BYTES=%d", n_bytes)) n_bytes = 0;
    $readmemh(bytes_path, stream);
    repeat (4) @(posedge clk);
    rst_n = 1'b1;
    // Let the CPU clear its memories before the first frame.
    repeat (2000) @(posedge clk);
    // The receiver listens while the program is sent, as a host's does: a
    // short program halts and starts its report before the last stop bit
    // has ended.
    fork
      for (i = 0; i < n_bytes; i = i + 1) send_byte(stream[i]);
      for (j = 0; j < 15; j = j + 1) begin
        recv_byte(v);
        report[j] = v;
      end
    join
    $display("{\"sync\": %0d, \"status\": %0d, \"pc\": %0d, \"mu\": %0d, \"error_code\": %0d, \"end\": %0d, \"leds\": %0d}",
             report[0], report[1],
             {report[5], report[4], report[3], report[2]},
             {report[9], report[8], report[7], report[6]},
             {report[13], report[12], report[11], report[10]},
             report[14], leds);
    $finish;
  end
endmodule
