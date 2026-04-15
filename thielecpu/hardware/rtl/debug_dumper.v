// debug_dumper.v — Serialise CPU state to UART TX on halt or error
//
// Sends a fixed-length binary packet when the CPU halts or errors:
//   [0]    0xDE (sync marker)
//   [1]    status  (bit0=halted, bit1=err, bit2=certified)
//   [2:5]  PC      (little-endian 32-bit)
//   [6:9]  mu      (little-endian 32-bit)
//   [10:13] error_code (little-endian 32-bit)
//   [14]   0xAD (end marker)
//
// Total: 15 bytes per dump.  Waits for tx_busy to deassert between bytes.
// One-shot: sends only once per halt/error event.

module debug_dumper (
    input         clk,
    input         rst_n,
    input         i_halted,
    input         i_err,
    input         i_certified,
    input  [31:0] i_pc,
    input  [31:0] i_mu,
    input  [31:0] i_error_code,
    output reg    o_tx_valid,
    output reg [7:0] o_tx_data,
    input         i_tx_busy
);

    localparam PACKET_LEN = 15;

    reg [3:0] byte_idx;
    reg       sending;
    reg       triggered;
    reg [7:0] packet [0:PACKET_LEN-1];

    wire trigger = (i_halted | i_err) & ~triggered;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            byte_idx   <= 0;
            sending    <= 1'b0;
            triggered  <= 1'b0;
            o_tx_valid <= 1'b0;
            o_tx_data  <= 8'd0;
        end else begin
            o_tx_valid <= 1'b0;  // pulse

            if (!sending && trigger) begin
                // Latch packet
                packet[0]  <= 8'hDE;
                packet[1]  <= {5'd0, i_certified, i_err, i_halted};
                packet[2]  <= i_pc[7:0];
                packet[3]  <= i_pc[15:8];
                packet[4]  <= i_pc[23:16];
                packet[5]  <= i_pc[31:24];
                packet[6]  <= i_mu[7:0];
                packet[7]  <= i_mu[15:8];
                packet[8]  <= i_mu[23:16];
                packet[9]  <= i_mu[31:24];
                packet[10] <= i_error_code[7:0];
                packet[11] <= i_error_code[15:8];
                packet[12] <= i_error_code[23:16];
                packet[13] <= i_error_code[31:24];
                packet[14] <= 8'hAD;
                sending    <= 1'b1;
                triggered  <= 1'b1;
                byte_idx   <= 0;
            end else if (sending && !i_tx_busy) begin
                o_tx_valid <= 1'b1;
                o_tx_data  <= packet[byte_idx];
                if (byte_idx == PACKET_LEN - 1) begin
                    sending <= 1'b0;
                end else begin
                    byte_idx <= byte_idx + 1;
                end
            end
        end
    end

endmodule
