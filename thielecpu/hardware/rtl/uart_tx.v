// uart_tx.v — UART transmitter (8N1)
//
// Accepts byte + valid pulse, shifts out start + 8 data + stop.
// Active-low async reset.

module uart_tx #(
    parameter CLKS_PER_BIT = 217   // CLK_FREQ / BAUD_RATE
)(
    input        clk,
    input        rst_n,
    input        i_valid,
    input  [7:0] i_data,
    output reg   o_tx,
    output       o_busy
);

    localparam S_IDLE  = 2'd0,
               S_START = 2'd1,
               S_DATA  = 2'd2,
               S_STOP  = 2'd3;

    reg [1:0]  state;
    reg [15:0] clk_cnt;
    reg [2:0]  bit_idx;
    reg [7:0]  shift;

    assign o_busy = (state != S_IDLE);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= S_IDLE;
            clk_cnt <= 0;
            bit_idx <= 0;
            shift   <= 0;
            o_tx    <= 1'b1;       // idle high
        end else begin
            case (state)
                S_IDLE: begin
                    o_tx <= 1'b1;
                    if (i_valid) begin
                        shift   <= i_data;
                        state   <= S_START;
                        clk_cnt <= 0;
                    end
                end
                S_START: begin
                    o_tx <= 1'b0;                 // start bit
                    if (clk_cnt == CLKS_PER_BIT - 1) begin
                        state   <= S_DATA;
                        clk_cnt <= 0;
                        bit_idx <= 0;
                    end else begin
                        clk_cnt <= clk_cnt + 1;
                    end
                end
                S_DATA: begin
                    o_tx <= shift[bit_idx];
                    if (clk_cnt == CLKS_PER_BIT - 1) begin
                        clk_cnt <= 0;
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
                    o_tx <= 1'b1;                 // stop bit
                    if (clk_cnt == CLKS_PER_BIT - 1) begin
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
