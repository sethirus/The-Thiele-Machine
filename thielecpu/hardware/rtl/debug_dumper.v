// debug_dumper.v — On CPU halt/error, dumps key state over UART TX
//
// When the CPU signals halt or error, this FSM reads out state registers
// and transmits them as a structured binary packet over UART:
//
//   Packet format (all fields little-endian):
//     [0]      0xDE            — sync byte
//     [1]      status          — bit 0: halted, bit 1: err, bit 2: certified
//     [2:5]    pc              — 32-bit program counter
//     [6:9]    mu              — 32-bit mu cost
//     [10:13]  error_code      — 32-bit error code
//     [14]     0xAD            — end marker
//
//   Total: 15 bytes per dump
//
// The FSM waits for o_tx_busy to deassert before sending each byte.

module debug_dumper (
    input         clk,
    input         rst_n,

    // CPU status inputs
    input         i_halted,
    input         i_err,
    input         i_certified,
    input  [31:0] i_pc,
    input  [31:0] i_mu,
    input  [31:0] i_error_code,

    // UART TX interface
    output reg       o_tx_valid,
    output reg [7:0] o_tx_data,
    input            i_tx_busy
);

    localparam PACKET_LEN = 15;

    localparam S_IDLE     = 2'd0;
    localparam S_LATCH    = 2'd1;
    localparam S_SEND     = 2'd2;
    localparam S_WAIT_TX  = 2'd3;

    reg [1:0]  state;
    reg [3:0]  byte_index;
    reg        triggered;

    // Latched state (captured at trigger time)
    reg [7:0]  status_byte;
    reg [31:0] lat_pc;
    reg [31:0] lat_mu;
    reg [31:0] lat_error_code;

    // Packet buffer — computed combinationally from latched state
    function [7:0] packet_byte;
        input [3:0] idx;
        begin
            case (idx)
                4'd0:  packet_byte = 8'hDE;                    // sync
                4'd1:  packet_byte = status_byte;
                4'd2:  packet_byte = lat_pc[7:0];
                4'd3:  packet_byte = lat_pc[15:8];
                4'd4:  packet_byte = lat_pc[23:16];
                4'd5:  packet_byte = lat_pc[31:24];
                4'd6:  packet_byte = lat_mu[7:0];
                4'd7:  packet_byte = lat_mu[15:8];
                4'd8:  packet_byte = lat_mu[23:16];
                4'd9:  packet_byte = lat_mu[31:24];
                4'd10: packet_byte = lat_error_code[7:0];
                4'd11: packet_byte = lat_error_code[15:8];
                4'd12: packet_byte = lat_error_code[23:16];
                4'd13: packet_byte = lat_error_code[31:24];
                4'd14: packet_byte = 8'hAD;                    // end marker
                default: packet_byte = 8'h00;
            endcase
        end
    endfunction

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state      <= S_IDLE;
            byte_index <= 0;
            triggered  <= 1'b0;
            o_tx_valid <= 1'b0;
            o_tx_data  <= 8'd0;
            status_byte    <= 8'd0;
            lat_pc         <= 32'd0;
            lat_mu         <= 32'd0;
            lat_error_code <= 32'd0;
        end else begin
            o_tx_valid <= 1'b0;  // default

            case (state)
                S_IDLE: begin
                    if ((i_halted || i_err) && !triggered) begin
                        state <= S_LATCH;
                    end
                end

                S_LATCH: begin
                    // Capture state snapshot
                    status_byte    <= {5'd0, i_certified, i_err, i_halted};
                    lat_pc         <= i_pc;
                    lat_mu         <= i_mu;
                    lat_error_code <= i_error_code;
                    byte_index     <= 0;
                    triggered      <= 1'b1;
                    state          <= S_SEND;
                end

                S_SEND: begin
                    if (!i_tx_busy) begin
                        o_tx_valid <= 1'b1;
                        o_tx_data  <= packet_byte(byte_index);
                        state      <= S_WAIT_TX;
                    end
                end

                S_WAIT_TX: begin
                    // Wait for TX to pick up the byte
                    if (i_tx_busy) begin
                        if (byte_index == PACKET_LEN - 1) begin
                            state <= S_IDLE;
                            // Stay triggered — only dump once per halt
                        end else begin
                            byte_index <= byte_index + 1;
                            state      <= S_SEND;
                        end
                    end
                end
            endcase
        end
    end

endmodule
