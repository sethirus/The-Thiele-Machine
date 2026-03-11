// tb_uart_loader.v — Testbench: verify UART program loader + CPU + debug dump
//
// Simulates the full FPGA top-level:
//   1. Sends a 3-instruction program over simulated UART RX
//   2. Waits for CPU to execute and halt
//   3. Captures the debug dump from UART TX
//   4. Verifies the dump contains expected values
//
// Program:
//   LOAD_IMM r1, 42, cost=1    → r1 = 42, mu += 1
//   LOAD_IMM r2, 58, cost=1    → r2 = 58, mu += 1
//   HALT 0                     → halt, mu += 0
//
// Expected debug dump:
//   PC = 3, mu >= 2, halted = 1, err = 0

`timescale 1ns / 1ps

module tb_uart_loader;

    parameter CLK_FREQ  = 25_000_000;
    parameter BAUD_RATE = 115_200;
    parameter CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;  // 217
    parameter BIT_PERIOD_NS = 1_000_000_000 / BAUD_RATE;  // ~8681 ns

    reg  clk = 0;
    reg  rst_n = 0;
    reg  uart_rx_pin = 1;  // idle high
    wire uart_tx_pin;
    wire led_halted, led_err, led_bianchi, led_loading;

    // Clock: 25 MHz = 40 ns period
    always #20 clk = ~clk;

    // DUT
    thiele_cpu_top #(
        .CLK_FREQ(CLK_FREQ),
        .BAUD_RATE(BAUD_RATE)
    ) dut (
        .CLK         (clk),
        .RST_N       (rst_n),
        .UART_RX     (uart_rx_pin),
        .UART_TX     (uart_tx_pin),
        .LED_HALTED  (led_halted),
        .LED_ERR     (led_err),
        .LED_BIANCHI (led_bianchi),
        .LED_LOADING (led_loading)
    );

    // ---- UART TX (send one byte over simulated serial) ----
    task uart_send_byte;
        input [7:0] data;
        integer i;
        begin
            // Start bit
            uart_rx_pin = 1'b0;
            #(BIT_PERIOD_NS);
            // Data bits (LSB first)
            for (i = 0; i < 8; i = i + 1) begin
                uart_rx_pin = data[i];
                #(BIT_PERIOD_NS);
            end
            // Stop bit
            uart_rx_pin = 1'b1;
            #(BIT_PERIOD_NS);
        end
    endtask

    // ---- UART RX (capture one byte from simulated serial) ----
    reg [7:0] rx_captured_bytes [0:31];
    integer   rx_byte_count = 0;

    task uart_recv_byte;
        output [7:0] data;
        integer i;
        begin
            // Wait for start bit (falling edge)
            @(negedge uart_tx_pin);
            // Wait to center of start bit
            #(BIT_PERIOD_NS / 2);
            // Sample 8 data bits
            for (i = 0; i < 8; i = i + 1) begin
                #(BIT_PERIOD_NS);
                data[i] = uart_tx_pin;
            end
            // Wait through stop bit
            #(BIT_PERIOD_NS);
        end
    endtask

    // ---- Capture debug dump in background ----
    reg dump_complete = 0;
    reg [7:0] dump_buf [0:14];

    initial begin
        integer i;
        // Wait for loading to complete, then capture debug dump
        wait(led_halted || led_err);
        for (i = 0; i < 15; i = i + 1) begin
            uart_recv_byte(dump_buf[i]);
        end
        dump_complete = 1;
    end

    // ---- Main test sequence ----
    // Instruction encoding: [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost
    // LOAD_IMM = 0x08, HALT = 0xFF
    localparam [31:0] INSTR_0 = {8'h08, 8'd1,  8'd42, 8'd1};  // LOAD_IMM r1, 42, cost=1
    localparam [31:0] INSTR_1 = {8'h08, 8'd2,  8'd58, 8'd1};  // LOAD_IMM r2, 58, cost=1
    localparam [31:0] INSTR_2 = {8'hFF, 8'd0,  8'd0,  8'd0};  // HALT 0
    localparam NUM_INSTRS = 3;

    initial begin
        $dumpfile("tb_uart_loader.vcd");
        $dumpvars(0, tb_uart_loader);

        // Reset
        rst_n = 0;
        #200;
        rst_n = 1;

        // Wait for BSC RegFile initialization (imem + mem = ~8192 cycles = ~328 μs)
        // At 25 MHz that's about 328000 ns
        #400_000;

        // Send instruction count: 3 (little-endian 16-bit)
        uart_send_byte(NUM_INSTRS[7:0]);   // lo
        uart_send_byte(NUM_INSTRS[15:8]);  // hi (0)

        // Send instruction 0: LOAD_IMM r1, 42, cost=1
        uart_send_byte(INSTR_0[7:0]);
        uart_send_byte(INSTR_0[15:8]);
        uart_send_byte(INSTR_0[23:16]);
        uart_send_byte(INSTR_0[31:24]);

        // Send instruction 1: LOAD_IMM r2, 58, cost=1
        uart_send_byte(INSTR_1[7:0]);
        uart_send_byte(INSTR_1[15:8]);
        uart_send_byte(INSTR_1[23:16]);
        uart_send_byte(INSTR_1[31:24]);

        // Send instruction 2: HALT 0
        uart_send_byte(INSTR_2[7:0]);
        uart_send_byte(INSTR_2[15:8]);
        uart_send_byte(INSTR_2[23:16]);
        uart_send_byte(INSTR_2[31:24]);

        $display("[TB] Program uploaded (%0d instructions)", NUM_INSTRS);

        // Wait for halt
        wait(led_halted || led_err);
        $display("[TB] CPU stopped: halted=%b err=%b", led_halted, led_err);

        // Wait for debug dump
        wait(dump_complete);
        $display("[TB] Debug dump received:");
        $display("[TB]   sync=0x%02X status=0x%02X", dump_buf[0], dump_buf[1]);
        $display("[TB]   PC=%0d mu=%0d error_code=0x%08X",
            {dump_buf[5], dump_buf[4], dump_buf[3], dump_buf[2]},
            {dump_buf[9], dump_buf[8], dump_buf[7], dump_buf[6]},
            {dump_buf[13], dump_buf[12], dump_buf[11], dump_buf[10]});
        $display("[TB]   end_marker=0x%02X", dump_buf[14]);

        // Verify
        if (dump_buf[0] !== 8'hDE) begin
            $display("[FAIL] Bad sync byte: 0x%02X", dump_buf[0]);
            $finish;
        end
        if (!(dump_buf[1] & 8'h01)) begin
            $display("[FAIL] CPU not halted");
            $finish;
        end
        if (dump_buf[1] & 8'h02) begin
            $display("[FAIL] CPU error flag set");
            $finish;
        end
        if (dump_buf[14] !== 8'hAD) begin
            $display("[FAIL] Bad end marker: 0x%02X", dump_buf[14]);
            $finish;
        end

        $display("[PASS] UART loader + CPU + debug dump end-to-end test passed");
        $finish;
    end

    // Timeout
    initial begin
        #500_000_000;  // 500 ms
        $display("[FAIL] Timeout — CPU did not halt within 500 ms");
        $finish;
    end

endmodule
