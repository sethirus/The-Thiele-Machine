// uart_tx.v — UART transmitter (8N1, configurable baud rate)
//
// Load a byte into i_data and pulse i_valid high for one clock. The module
// shifts out start + 8 data bits + stop bit. o_busy is high while transmitting.
//
// Parameters:
//   CLKS_PER_BIT = clock_freq / baud_rate
//   (e.g., 25 MHz / 115200 = 217)

module uart_tx #(
    parameter CLKS_PER_BIT = 217  // 25 MHz / 115200
)(
    input        clk,
    input        rst_n,
    input        i_valid,     // pulse high to start transmission
    input  [7:0] i_data,      // byte to transmit
    output reg   o_tx,        // serial output
    output reg   o_busy       // high while transmitting
);

    localparam S_IDLE  = 2'd0;
    localparam S_START = 2'd1;
    localparam S_DATA  = 2'd2;
    localparam S_STOP  = 2'd3;

    reg [1:0]  state;
    reg [15:0] clk_count;
    reg [2:0]  bit_index;
    reg [7:0]  tx_shift;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state     <= S_IDLE;
            clk_count <= 0;
            bit_index <= 0;
            tx_shift  <= 0;
            o_tx      <= 1'b1;  // idle high
            o_busy    <= 1'b0;
        end else begin
            case (state)
                S_IDLE: begin
                    o_tx   <= 1'b1;
                    o_busy <= 1'b0;
                    if (i_valid) begin
                        tx_shift  <= i_data;
                        state     <= S_START;
                        clk_count <= 0;
                        o_busy    <= 1'b1;
                    end
                end

                S_START: begin
                    o_tx <= 1'b0;  // start bit
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        clk_count <= 0;
                        bit_index <= 0;
                        state     <= S_DATA;
                    end else begin
                        clk_count <= clk_count + 1;
                    end
                end

                S_DATA: begin
                    o_tx <= tx_shift[bit_index]; // LSB first
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        clk_count <= 0;
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
                    o_tx <= 1'b1;  // stop bit
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        state  <= S_IDLE;
                        o_busy <= 1'b0;
                    end else begin
                        clk_count <= clk_count + 1;
                    end
                end
            endcase
        end
    end

endmodule
