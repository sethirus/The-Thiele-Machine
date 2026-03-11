// uart_rx.v — UART receiver (8N1, configurable baud rate)
//
// Receives one byte at a time. When a full byte is ready, o_valid pulses
// high for one clock cycle and o_data holds the received byte.
//
// Parameters:
//   CLKS_PER_BIT = clock_freq / baud_rate
//   (e.g., 25 MHz / 115200 = 217)

module uart_rx #(
    parameter CLKS_PER_BIT = 217  // 25 MHz / 115200
)(
    input        clk,
    input        rst_n,
    input        i_rx,        // serial input
    output reg   o_valid,     // pulses high for 1 cycle when byte ready
    output reg [7:0] o_data   // received byte
);

    localparam S_IDLE  = 2'd0;
    localparam S_START = 2'd1;
    localparam S_DATA  = 2'd2;
    localparam S_STOP  = 2'd3;

    reg [1:0]  state;
    reg [15:0] clk_count;
    reg [2:0]  bit_index;
    reg [7:0]  rx_shift;
    reg        rx_sync0, rx_sync1;  // double-sync for metastability

    // Double-synchronize the async RX input
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_sync0 <= 1'b1;
            rx_sync1 <= 1'b1;
        end else begin
            rx_sync0 <= i_rx;
            rx_sync1 <= rx_sync0;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state     <= S_IDLE;
            clk_count <= 0;
            bit_index <= 0;
            rx_shift  <= 0;
            o_valid   <= 1'b0;
            o_data    <= 8'd0;
        end else begin
            o_valid <= 1'b0;  // default: no data ready

            case (state)
                S_IDLE: begin
                    if (rx_sync1 == 1'b0) begin
                        // Falling edge detected — possible start bit
                        state     <= S_START;
                        clk_count <= 0;
                    end
                end

                S_START: begin
                    // Sample at midpoint of start bit
                    if (clk_count == (CLKS_PER_BIT - 1) / 2) begin
                        if (rx_sync1 == 1'b0) begin
                            // Confirmed start bit
                            clk_count <= 0;
                            bit_index <= 0;
                            state     <= S_DATA;
                        end else begin
                            // False start — glitch
                            state <= S_IDLE;
                        end
                    end else begin
                        clk_count <= clk_count + 1;
                    end
                end

                S_DATA: begin
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        clk_count <= 0;
                        rx_shift[bit_index] <= rx_sync1; // LSB first
                        if (bit_index == 3'd7) begin
                            state <= S_STOP;
                        end else begin
                            bit_index <= bit_index + 1;
                        end
                    end else begin
                        clk_count <= clk_count + 1;
                    end
                end

                S_STOP: begin
                    // Wait for stop bit midpoint
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        o_valid <= 1'b1;
                        o_data  <= rx_shift;
                        state   <= S_IDLE;
                    end else begin
                        clk_count <= clk_count + 1;
                    end
                end
            endcase
        end
    end

endmodule
