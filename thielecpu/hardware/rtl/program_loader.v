// program_loader.v — UART byte-stream to 44-bit instruction loader
//
// Protocol (binary, little-endian):
//   1. Receive 2 bytes: instruction count N (little-endian 16-bit)
//   2. Receive N × 6 bytes: each 44-bit instruction padded to 48 bits
//      (6 bytes little-endian, top 4 bits ignored)
//   3. Assert o_done — CPU starts executing
//
// Each complete instruction pulses o_load_en with o_load_data valid for
// one clock cycle.

module program_loader (
    input         clk,
    input         rst_n,
    input         i_byte_valid,
    input  [7:0]  i_byte_data,
    output reg    o_load_en,
    output reg [43:0] o_load_data,
    output reg    o_done,
    output        o_loading
);

    localparam BYTES_PER_INSTR = 6;   // 48 bits, top 4 ignored

    reg [15:0] instr_count;           // total instructions to load
    reg [15:0] instr_loaded;          // instructions loaded so far
    reg [2:0]  byte_idx;              // byte position within current instruction
    reg [47:0] instr_accum;           // accumulator for current instruction
    reg        got_count;             // have we received the 2-byte count?
    reg        count_lo;              // received first count byte?

    assign o_loading = rst_n && !o_done;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            instr_count  <= 0;
            instr_loaded <= 0;
            byte_idx     <= 0;
            instr_accum  <= 0;
            got_count    <= 1'b0;
            count_lo     <= 1'b0;
            o_load_en    <= 1'b0;
            o_load_data  <= 44'd0;
            o_done       <= 1'b0;
        end else begin
            o_load_en <= 1'b0;  // pulse

            if (o_done) begin
                // stay done
            end else if (i_byte_valid) begin
                if (!got_count) begin
                    if (!count_lo) begin
                        instr_count[7:0] <= i_byte_data;
                        count_lo <= 1'b1;
                    end else begin
                        instr_count[15:8] <= i_byte_data;
                        got_count <= 1'b1;
                        // Handle zero-length programs
                        if ({i_byte_data, instr_count[7:0]} == 16'd0)
                            o_done <= 1'b1;
                    end
                end else begin
                    // Accumulate instruction bytes (little-endian)
                    instr_accum <= instr_accum | ({40'd0, i_byte_data} << (byte_idx * 8));

                    if (byte_idx == BYTES_PER_INSTR - 1) begin
                        // Emit completed instruction
                        o_load_en   <= 1'b1;
                        o_load_data <= (instr_accum | ({40'd0, i_byte_data} << (byte_idx * 8)));
                        instr_accum <= 48'd0;
                        byte_idx    <= 0;
                        instr_loaded <= instr_loaded + 1;
                        if (instr_loaded + 1 == instr_count) begin
                            o_done <= 1'b1;
                        end
                    end else begin
                        byte_idx <= byte_idx + 1;
                    end
                end
            end
        end
    end

endmodule
