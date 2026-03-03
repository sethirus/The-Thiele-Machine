// ############################################################################
// SUBMODULE: mu_alu — Q16.16 Fixed-Point Arithmetic Unit
// ############################################################################
//
// Standalone extraction from thiele_cpu_unified.v

module mu_alu (
    input  wire        clk,
    input  wire        rst_n,
    input  wire [2:0]  op,
    input  wire [31:0] operand_a,
    input  wire [31:0] operand_b,
    input  wire        valid,
    output reg  [31:0] result,
    output reg         ready,
    output reg         overflow
);

localparam Q16_SHIFT = 16;
localparam Q16_ONE   = 32'h00010000;
localparam Q16_MAX   = 32'h7FFFFFFF;
localparam signed Q16_MIN = 32'sh80000000;

localparam OP_ADD          = 3'd0;
localparam OP_SUB          = 3'd1;
localparam OP_MUL          = 3'd2;
localparam OP_DIV          = 3'd3;
localparam OP_LOG2         = 3'd4;
localparam OP_INFO_GAIN    = 3'd5;
localparam OP_CLAIM_FACTOR = 3'd6;

// Log2 approximation (bit-position)
function [31:0] simple_log2_approx;
    input [31:0] x;
    reg [5:0] msb_pos;
    begin
        if      (x[31]) msb_pos = 31;
        else if (x[30]) msb_pos = 30;
        else if (x[29]) msb_pos = 29;
        else if (x[28]) msb_pos = 28;
        else if (x[27]) msb_pos = 27;
        else if (x[26]) msb_pos = 26;
        else if (x[25]) msb_pos = 25;
        else if (x[24]) msb_pos = 24;
        else if (x[23]) msb_pos = 23;
        else if (x[22]) msb_pos = 22;
        else if (x[21]) msb_pos = 21;
        else if (x[20]) msb_pos = 20;
        else if (x[19]) msb_pos = 19;
        else if (x[18]) msb_pos = 18;
        else if (x[17]) msb_pos = 17;
        else if (x[16]) msb_pos = 16;
        else if (x[15]) msb_pos = 15;
        else if (x[14]) msb_pos = 14;
        else if (x[13]) msb_pos = 13;
        else if (x[12]) msb_pos = 12;
        else if (x[11]) msb_pos = 11;
        else if (x[10]) msb_pos = 10;
        else if (x[9])  msb_pos = 9;
        else if (x[8])  msb_pos = 8;
        else if (x[7])  msb_pos = 7;
        else if (x[6])  msb_pos = 6;
        else if (x[5])  msb_pos = 5;
        else if (x[4])  msb_pos = 4;
        else if (x[3])  msb_pos = 3;
        else if (x[2])  msb_pos = 2;
        else if (x[1])  msb_pos = 1;
        else             msb_pos = 0;
        simple_log2_approx = ((msb_pos - 16) << Q16_SHIFT);
    end
endfunction

// Factor LUT
reg [31:0] factor_lut [0:3];
initial begin
    factor_lut[0] = 32'd3;   // 15 = 3 × 5
    factor_lut[1] = 32'd5;
    factor_lut[2] = 32'd3;   // 21 = 3 × 7
    factor_lut[3] = 32'd7;
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        result   <= 32'h0;
        ready    <= 1'b0;
        overflow <= 1'b0;
    end else if (valid && !ready) begin
        overflow <= 1'b0;
        ready    <= 1'b1;

        case (op)
            OP_ADD: begin
                {overflow, result} <= $signed(operand_a) + $signed(operand_b);
                if (overflow)
                    result <= (operand_a[31] == operand_b[31])
                            ? (operand_a[31] ? Q16_MIN : Q16_MAX) : result;
            end

            OP_SUB: begin
                {overflow, result} <= $signed(operand_a) - $signed(operand_b);
                if (overflow)
                    result <= (operand_a[31] != operand_b[31])
                            ? (operand_a[31] ? Q16_MIN : Q16_MAX) : result;
            end

            OP_MUL: begin
                // Q16.16 × Q16.16 → Q16.16 via 64-bit intermediate
                result   <= ($signed({{32{operand_a[31]}}, operand_a}) *
                             $signed({{32{operand_b[31]}}, operand_b})) >>> Q16_SHIFT;
                overflow <= 1'b0;
            end

            OP_DIV: begin
                if (operand_b == 0) begin
                    result   <= Q16_MAX;
                    overflow <= 1'b1;
                end else begin
                    result   <= operand_a >>> 1;  // approximate ÷2
                    overflow <= 1'b0;
                end
            end

            OP_LOG2: begin
                if (operand_a == 0 || $signed(operand_a) < 0) begin
                    result   <= Q16_MIN;
                    overflow <= 1'b1;
                end else begin
                    result   <= simple_log2_approx(operand_a);
                    overflow <= 1'b0;
                end
            end

            OP_INFO_GAIN: begin
                if (operand_b == 0) begin
                    result   <= 32'h0;
                    overflow <= 1'b1;
                end else begin
                    result   <= operand_a - operand_b;
                    overflow <= 1'b0;
                end
            end

            OP_CLAIM_FACTOR: begin
                case ({operand_a, operand_b[0]})
                    {32'd15, 1'b0}: result <= factor_lut[0];
                    {32'd15, 1'b1}: result <= factor_lut[1];
                    {32'd21, 1'b0}: result <= factor_lut[2];
                    {32'd21, 1'b1}: result <= factor_lut[3];
                    default: begin
                        result   <= 32'h0;
                        overflow <= 1'b1;
                    end
                endcase
            end

            default: begin
                result   <= 32'h0;
                overflow <= 1'b0;
            end
        endcase
    end else if (!valid) begin
        ready    <= 1'b0;
        overflow <= 1'b0;
    end
end

endmodule
