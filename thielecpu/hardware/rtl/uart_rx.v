// uart_rx.v — UART receiver (8N1)
//
// Oversamples at CLKS_PER_BIT to centre-sample each bit.
// Active-low async reset.

module uart_rx #(
    parameter CLKS_PER_BIT = 217   // CLK_FREQ / BAUD_RATE
)(
    input        clk,
    input        rst_n,
    input        i_rx,
    output reg   o_valid,
    output reg [7:0] o_data
);

    localparam S_IDLE  = 2'd0,
               S_START = 2'd1,
               S_DATA  = 2'd2,
               S_STOP  = 2'd3;

    reg [1:0]  state;
    reg [15:0] clk_cnt;
    reg [2:0]  bit_idx;
    reg [7:0]  shift;
    reg        rx_sync_0, rx_sync_1;

    // Double-flop synchroniser
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_sync_0 <= 1'b1;
            rx_sync_1 <= 1'b1;
        end else begin
            rx_sync_0 <= i_rx;
            rx_sync_1 <= rx_sync_0;
        end
    end

    wire rx_in = rx_sync_1;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= S_IDLE;
            clk_cnt <= 0;
            bit_idx <= 0;
            shift   <= 0;
            o_valid <= 1'b0;
            o_data  <= 8'd0;
        end else begin
            o_valid <= 1'b0;  // pulse
            case (state)
                S_IDLE: begin
                    if (rx_in == 1'b0) begin      // start-bit falling edge
                        state   <= S_START;
                        clk_cnt <= 0;
                    end
                end
                S_START: begin
                    if (clk_cnt == (CLKS_PER_BIT - 1) / 2) begin
                        if (rx_in == 1'b0) begin  // still low at mid-start
                            state   <= S_DATA;
                            clk_cnt <= 0;
                            bit_idx <= 0;
                        end else begin
                            state <= S_IDLE;       // false start
                        end
                    end else begin
                        clk_cnt <= clk_cnt + 1;
                    end
                end
                S_DATA: begin
                    if (clk_cnt == CLKS_PER_BIT - 1) begin
                        clk_cnt <= 0;
                        shift[bit_idx] <= rx_in;
                        if (bit_idx == 7) begin
                            state <= S_STOP;
                        end else begin
                            bit_idx <= bit_idx + 1;
                        end
                    end else begin
                        clk_cnt <= clk_cnt + 1;
                    end
                end
                S_STOP: begin
                    if (clk_cnt == CLKS_PER_BIT - 1) begin
                        o_valid <= 1'b1;
                        o_data  <= shift;
                        state   <= S_IDLE;
                        clk_cnt <= 0;
                    end else begin
                        clk_cnt <= clk_cnt + 1;
                    end
                end
            endcase
        end
    end

endmodule
