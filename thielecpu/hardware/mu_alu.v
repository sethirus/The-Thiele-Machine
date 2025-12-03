// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
//
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// μ-ALU: Q16.16 Fixed-Point Arithmetic Unit
// ============================================================================
//
// This module implements the μ-ALU specification v1.0 for bit-exact
// μ-bit calculations. All operations use Q16.16 fixed-point format
// to ensure identical results between Python VM and Verilog hardware.
//
// Specification: spec/mu_alu_v1.md
// Reference implementation: thielecpu/mu_fixed.py
//
// ============================================================================

`timescale 1ns / 1ps

module mu_alu (
    input wire clk,
    input wire rst_n,
    
    // Operation control
    input wire [2:0] op,           // Operation: 0=add, 1=sub, 2=mul, 3=div, 4=log2, 5=info_gain
    input wire [31:0] operand_a,   // Q16.16 operand A (or integer for info_gain)
    input wire [31:0] operand_b,   // Q16.16 operand B (or integer for info_gain)
    input wire valid,              // Operation valid
    
    // Result
    output reg [31:0] result,      // Q16.16 result
    output reg ready,              // Result ready
    output reg overflow            // Overflow/saturation occurred
);

// ============================================================================
// CONSTANTS
// ============================================================================

localparam Q16_SHIFT = 16;
localparam Q16_ONE = 32'h00010000;  // 1.0 in Q16.16
localparam Q16_MAX = 32'h7FFFFFFF;  // Maximum positive value
localparam signed Q16_MIN = 32'sh80000000;  // Minimum negative value

// Operation codes
localparam OP_ADD = 3'd0;
localparam OP_SUB = 3'd1;
localparam OP_MUL = 3'd2;
localparam OP_DIV = 3'd3;
localparam OP_LOG2 = 3'd4;
localparam OP_INFO_GAIN = 3'd5;

// ============================================================================
// LOG2 LUT (256 entries for [1.0, 2.0) in Q16.16 format)
// ============================================================================

// Precomputed log2 LUT matching Python implementation
reg [31:0] log2_lut [0:255];

initial begin
    log2_lut[0] = 32'h00000000; log2_lut[1] = 32'h00000170; log2_lut[2] = 32'h000002DF; log2_lut[3] = 32'h0000044D;
    log2_lut[4] = 32'h000005B9; log2_lut[5] = 32'h00000724; log2_lut[6] = 32'h0000088E; log2_lut[7] = 32'h000009F6;
    log2_lut[8] = 32'h00000B5D; log2_lut[9] = 32'h00000CC2; log2_lut[10] = 32'h00000E26; log2_lut[11] = 32'h00000F89;
    log2_lut[12] = 32'h000010EB; log2_lut[13] = 32'h0000124B; log2_lut[14] = 32'h000013AA; log2_lut[15] = 32'h00001507;
    log2_lut[16] = 32'h00001663; log2_lut[17] = 32'h000017BE; log2_lut[18] = 32'h00001918; log2_lut[19] = 32'h00001A71;
    log2_lut[20] = 32'h00001BC8; log2_lut[21] = 32'h00001D1E; log2_lut[22] = 32'h00001E72; log2_lut[23] = 32'h00001FC6;
    log2_lut[24] = 32'h00002118; log2_lut[25] = 32'h00002269; log2_lut[26] = 32'h000023B9; log2_lut[27] = 32'h00002508;
    log2_lut[28] = 32'h00002655; log2_lut[29] = 32'h000027A2; log2_lut[30] = 32'h000028ED; log2_lut[31] = 32'h00002A37;
    log2_lut[32] = 32'h00002B80; log2_lut[33] = 32'h00002CC7; log2_lut[34] = 32'h00002E0E; log2_lut[35] = 32'h00002F53;
    log2_lut[36] = 32'h00003098; log2_lut[37] = 32'h000031DB; log2_lut[38] = 32'h0000331D; log2_lut[39] = 32'h0000345E;
    log2_lut[40] = 32'h0000359E; log2_lut[41] = 32'h000036DD; log2_lut[42] = 32'h0000381B; log2_lut[43] = 32'h00003958;
    log2_lut[44] = 32'h00003A93; log2_lut[45] = 32'h00003BCE; log2_lut[46] = 32'h00003D08; log2_lut[47] = 32'h00003E40;
    log2_lut[48] = 32'h00003F78; log2_lut[49] = 32'h000040AE; log2_lut[50] = 32'h000041E4; log2_lut[51] = 32'h00004318;
    log2_lut[52] = 32'h0000444C; log2_lut[53] = 32'h0000457E; log2_lut[54] = 32'h000046B0; log2_lut[55] = 32'h000047E0;
    log2_lut[56] = 32'h00004910; log2_lut[57] = 32'h00004A3E; log2_lut[58] = 32'h00004B6C; log2_lut[59] = 32'h00004C98;
    log2_lut[60] = 32'h00004DC4; log2_lut[61] = 32'h00004EEF; log2_lut[62] = 32'h00005019; log2_lut[63] = 32'h00005141;
    log2_lut[64] = 32'h00005269; log2_lut[65] = 32'h00005390; log2_lut[66] = 32'h000054B6; log2_lut[67] = 32'h000055DC;
    log2_lut[68] = 32'h00005700; log2_lut[69] = 32'h00005823; log2_lut[70] = 32'h00005946; log2_lut[71] = 32'h00005A67;
    log2_lut[72] = 32'h00005B88; log2_lut[73] = 32'h00005CA8; log2_lut[74] = 32'h00005DC7; log2_lut[75] = 32'h00005EE5;
    log2_lut[76] = 32'h00006002; log2_lut[77] = 32'h0000611E; log2_lut[78] = 32'h0000623A; log2_lut[79] = 32'h00006355;
    log2_lut[80] = 32'h0000646E; log2_lut[81] = 32'h00006587; log2_lut[82] = 32'h000066A0; log2_lut[83] = 32'h000067B7;
    log2_lut[84] = 32'h000068CD; log2_lut[85] = 32'h000069E3; log2_lut[86] = 32'h00006AF8; log2_lut[87] = 32'h00006C0C;
    log2_lut[88] = 32'h00006D1F; log2_lut[89] = 32'h00006E32; log2_lut[90] = 32'h00006F43; log2_lut[91] = 32'h00007054;
    log2_lut[92] = 32'h00007164; log2_lut[93] = 32'h00007274; log2_lut[94] = 32'h00007382; log2_lut[95] = 32'h00007490;
    log2_lut[96] = 32'h0000759D; log2_lut[97] = 32'h000076A9; log2_lut[98] = 32'h000077B4; log2_lut[99] = 32'h000078BF;
    log2_lut[100] = 32'h000079C9; log2_lut[101] = 32'h00007AD2; log2_lut[102] = 32'h00007BDB; log2_lut[103] = 32'h00007CE3;
    log2_lut[104] = 32'h00007DEA; log2_lut[105] = 32'h00007EF0; log2_lut[106] = 32'h00007FF5; log2_lut[107] = 32'h000080FA;
    log2_lut[108] = 32'h000081FE; log2_lut[109] = 32'h00008302; log2_lut[110] = 32'h00008404; log2_lut[111] = 32'h00008506;
    log2_lut[112] = 32'h00008608; log2_lut[113] = 32'h00008708; log2_lut[114] = 32'h00008808; log2_lut[115] = 32'h00008907;
    log2_lut[116] = 32'h00008A06; log2_lut[117] = 32'h00008B04; log2_lut[118] = 32'h00008C01; log2_lut[119] = 32'h00008CFD;
    log2_lut[120] = 32'h00008DF9; log2_lut[121] = 32'h00008EF4; log2_lut[122] = 32'h00008FEF; log2_lut[123] = 32'h000090E8;
    log2_lut[124] = 32'h000091E2; log2_lut[125] = 32'h000092DA; log2_lut[126] = 32'h000093D2; log2_lut[127] = 32'h000094C9;
    log2_lut[128] = 32'h000095C0; log2_lut[129] = 32'h000096B6; log2_lut[130] = 32'h000097AB; log2_lut[131] = 32'h0000989F;
    log2_lut[132] = 32'h00009993; log2_lut[133] = 32'h00009A87; log2_lut[134] = 32'h00009B79; log2_lut[135] = 32'h00009C6C;
    log2_lut[136] = 32'h00009D5D; log2_lut[137] = 32'h00009E4E; log2_lut[138] = 32'h00009F3E; log2_lut[139] = 32'h0000A02E;
    log2_lut[140] = 32'h0000A11D; log2_lut[141] = 32'h0000A20B; log2_lut[142] = 32'h0000A2F9; log2_lut[143] = 32'h0000A3E7;
    log2_lut[144] = 32'h0000A4D3; log2_lut[145] = 32'h0000A5BF; log2_lut[146] = 32'h0000A6AB; log2_lut[147] = 32'h0000A796;
    log2_lut[148] = 32'h0000A880; log2_lut[149] = 32'h0000A96A; log2_lut[150] = 32'h0000AA53; log2_lut[151] = 32'h0000AB3C;
    log2_lut[152] = 32'h0000AC24; log2_lut[153] = 32'h0000AD0B; log2_lut[154] = 32'h0000ADF2; log2_lut[155] = 32'h0000AED8;
    log2_lut[156] = 32'h0000AFBE; log2_lut[157] = 32'h0000B0A3; log2_lut[158] = 32'h0000B188; log2_lut[159] = 32'h0000B26C;
    log2_lut[160] = 32'h0000B350; log2_lut[161] = 32'h0000B433; log2_lut[162] = 32'h0000B515; log2_lut[163] = 32'h0000B5F7;
    log2_lut[164] = 32'h0000B6D8; log2_lut[165] = 32'h0000B7B9; log2_lut[166] = 32'h0000B899; log2_lut[167] = 32'h0000B979;
    log2_lut[168] = 32'h0000BA58; log2_lut[169] = 32'h0000BB37; log2_lut[170] = 32'h0000BC15; log2_lut[171] = 32'h0000BCF3;
    log2_lut[172] = 32'h0000BDD0; log2_lut[173] = 32'h0000BEAD; log2_lut[174] = 32'h0000BF89; log2_lut[175] = 32'h0000C065;
    log2_lut[176] = 32'h0000C140; log2_lut[177] = 32'h0000C21A; log2_lut[178] = 32'h0000C2F5; log2_lut[179] = 32'h0000C3CE;
    log2_lut[180] = 32'h0000C4A7; log2_lut[181] = 32'h0000C580; log2_lut[182] = 32'h0000C658; log2_lut[183] = 32'h0000C730;
    log2_lut[184] = 32'h0000C807; log2_lut[185] = 32'h0000C8DD; log2_lut[186] = 32'h0000C9B3; log2_lut[187] = 32'h0000CA89;
    log2_lut[188] = 32'h0000CB5E; log2_lut[189] = 32'h0000CC33; log2_lut[190] = 32'h0000CD07; log2_lut[191] = 32'h0000CDDB;
    log2_lut[192] = 32'h0000CEAE; log2_lut[193] = 32'h0000CF81; log2_lut[194] = 32'h0000D053; log2_lut[195] = 32'h0000D125;
    log2_lut[196] = 32'h0000D1F7; log2_lut[197] = 32'h0000D2C8; log2_lut[198] = 32'h0000D398; log2_lut[199] = 32'h0000D468;
    log2_lut[200] = 32'h0000D538; log2_lut[201] = 32'h0000D607; log2_lut[202] = 32'h0000D6D6; log2_lut[203] = 32'h0000D7A4;
    log2_lut[204] = 32'h0000D872; log2_lut[205] = 32'h0000D93F; log2_lut[206] = 32'h0000DA0C; log2_lut[207] = 32'h0000DAD8;
    log2_lut[208] = 32'h0000DBA4; log2_lut[209] = 32'h0000DC70; log2_lut[210] = 32'h0000DD3B; log2_lut[211] = 32'h0000DE05;
    log2_lut[212] = 32'h0000DED0; log2_lut[213] = 32'h0000DF9A; log2_lut[214] = 32'h0000E063; log2_lut[215] = 32'h0000E12C;
    log2_lut[216] = 32'h0000E1F4; log2_lut[217] = 32'h0000E2BC; log2_lut[218] = 32'h0000E384; log2_lut[219] = 32'h0000E44B;
    log2_lut[220] = 32'h0000E512; log2_lut[221] = 32'h0000E5D9; log2_lut[222] = 32'h0000E69F; log2_lut[223] = 32'h0000E764;
    log2_lut[224] = 32'h0000E829; log2_lut[225] = 32'h0000E8EE; log2_lut[226] = 32'h0000E9B3; log2_lut[227] = 32'h0000EA77;
    log2_lut[228] = 32'h0000EB3A; log2_lut[229] = 32'h0000EBFD; log2_lut[230] = 32'h0000ECC0; log2_lut[231] = 32'h0000ED82;
    log2_lut[232] = 32'h0000EE44; log2_lut[233] = 32'h0000EF06; log2_lut[234] = 32'h0000EFC7; log2_lut[235] = 32'h0000F088;
    log2_lut[236] = 32'h0000F148; log2_lut[237] = 32'h0000F208; log2_lut[238] = 32'h0000F2C8; log2_lut[239] = 32'h0000F387;
    log2_lut[240] = 32'h0000F446; log2_lut[241] = 32'h0000F504; log2_lut[242] = 32'h0000F5C2; log2_lut[243] = 32'h0000F680;
    log2_lut[244] = 32'h0000F73D; log2_lut[245] = 32'h0000F7FA; log2_lut[246] = 32'h0000F8B7; log2_lut[247] = 32'h0000F973;
    log2_lut[248] = 32'h0000FA2F; log2_lut[249] = 32'h0000FAEA; log2_lut[250] = 32'h0000FBA5; log2_lut[251] = 32'h0000FC60;
    log2_lut[252] = 32'h0000FD1A; log2_lut[253] = 32'h0000FDD4; log2_lut[254] = 32'h0000FE8D; log2_lut[255] = 32'h0000FF47;
end

// ============================================================================
// INTERNAL SIGNALS
// ============================================================================

reg [31:0] temp_result;
reg temp_overflow;
reg [5:0] state;
reg [7:0] lut_index;
reg signed [63:0] mul_temp;
reg signed [63:0] div_temp;

// LOG2 computation state
reg [31:0] log2_input;
reg [5:0] leading_zeros;
reg [5:0] highest_bit;
reg signed [31:0] integer_log2;
reg [31:0] normalized;
reg signed [31:0] shift_amount;
reg [31:0] frac_part;
reg [31:0] frac_log;
reg signed [31:0] result_temp;

// ============================================================================
// ARITHMETIC OPERATIONS
// ============================================================================

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        result <= 32'h0;
        ready <= 1'b0;
        overflow <= 1'b0;
        state <= 6'd0;
    end else begin
        if (valid && state == 6'd0) begin
            ready <= 1'b0;
            overflow <= 1'b0;
            
            case (op)
                OP_ADD: begin
                    // Q16.16 addition with saturation
                    temp_result = $signed(operand_a) + $signed(operand_b);
                    if ($signed(temp_result) > $signed(Q16_MAX)) begin
                        result <= Q16_MAX;
                        overflow <= 1'b1;
                    end else if ($signed(temp_result) < Q16_MIN) begin
                        result <= Q16_MIN;
                        overflow <= 1'b1;
                    end else begin
                        result <= temp_result;
                        overflow <= 1'b0;
                    end
                    ready <= 1'b1;
                end
                
                OP_SUB: begin
                    // Q16.16 subtraction with saturation
                    temp_result = $signed(operand_a) - $signed(operand_b);
                    if ($signed(temp_result) > $signed(Q16_MAX)) begin
                        result <= Q16_MAX;
                        overflow <= 1'b1;
                    end else if ($signed(temp_result) < Q16_MIN) begin
                        result <= Q16_MIN;
                        overflow <= 1'b1;
                    end else begin
                        result <= temp_result;
                        overflow <= 1'b0;
                    end
                    ready <= 1'b1;
                end
                
                OP_MUL: begin
                    // Q16.16 multiplication: (a * b) >> 16
                    mul_temp = $signed(operand_a) * $signed(operand_b);
                    temp_result = mul_temp[47:16];  // Take bits [47:16] for Q16.16 result
                    if ($signed(temp_result) > $signed(Q16_MAX)) begin
                        result <= Q16_MAX;
                        overflow <= 1'b1;
                    end else if ($signed(temp_result) < Q16_MIN) begin
                        result <= Q16_MIN;
                        overflow <= 1'b1;
                    end else begin
                        result <= temp_result;
                        overflow <= 1'b0;
                    end
                    ready <= 1'b1;
                end
                
                OP_DIV: begin
                    // Q16.16 division: (a << 16) / b
                    if (operand_b == 32'h0) begin
                        result <= 32'h0;
                        overflow <= 1'b1;
                        ready <= 1'b1;
                    end else begin
                        div_temp = ({$signed(operand_a), 16'h0}) / $signed(operand_b);
                        temp_result = div_temp[31:0];
                        if ($signed(temp_result) > $signed(Q16_MAX)) begin
                            result <= Q16_MAX;
                            overflow <= 1'b1;
                        end else if ($signed(temp_result) < Q16_MIN) begin
                            result <= Q16_MIN;
                            overflow <= 1'b1;
                        end else begin
                            result <= temp_result;
                            overflow <= 1'b0;
                        end
                        ready <= 1'b1;
                    end
                end
                
                OP_LOG2: begin
                    // Start log2 computation (multi-cycle)
                    state <= 6'd1;
                end
                
                OP_INFO_GAIN: begin
                    // Start information gain computation (multi-cycle)
                    // operand_a = before (integer count)
                    // operand_b = after (integer count)
                    state <= 6'd10;
                end
                
                default: begin
                    result <= 32'h0;
                    ready <= 1'b1;
                    overflow <= 1'b0;
                end
            endcase
        end else if (state == 6'd1) begin
            // LOG2 operation - compute log2 of Q16.16 value
            // Implementation matches Python log2_q16 function
            if (operand_a == 32'h0 || $signed(operand_a) < 0) begin
                result <= Q16_MIN;
                overflow <= 1'b1;
                ready <= 1'b1;
                state <= 6'd0;
            end else if (operand_a == Q16_ONE) begin
                result <= 32'h0;
                overflow <= 1'b0;
                ready <= 1'b1;
                state <= 6'd0;
            end else begin
                log2_input <= operand_a;
                state <= 6'd2;
            end
        end else if (state == 6'd2) begin
            // Count leading zeros to find MSB position
            // This matches the Python implementation's loop
            leading_zeros <= 6'd0;
            temp_result <= log2_input;
            state <= 6'd3;
        end else if (state == 6'd3) begin
            // Continue counting leading zeros
            if (temp_result[31] == 1'b1 || leading_zeros >= 6'd31) begin
                // Found MSB or reached end
                highest_bit <= 6'd31 - leading_zeros;
                state <= 6'd4;
            end else begin
                temp_result <= temp_result << 1;
                leading_zeros <= leading_zeros + 6'd1;
                state <= 6'd3;
            end
        end else if (state == 6'd4) begin
            // Calculate integer part of log2
            // integer_log2 = highest_bit - 16 (relative to Q16.16 format)
            integer_log2 <= $signed({1'b0, highest_bit}) - 16;
            shift_amount <= $signed({1'b0, highest_bit}) - 16;
            state <= 6'd5;
        end else if (state == 6'd5) begin
            // Normalize to [1.0, 2.0) range
            if (shift_amount > 0) begin
                normalized <= log2_input >> shift_amount;
            end else if (shift_amount < 0) begin
                normalized <= log2_input << (-shift_amount);
            end else begin
                normalized <= log2_input;
            end
            state <= 6'd6;
        end else if (state == 6'd6) begin
            // Extract fractional part
            if ($signed(normalized - Q16_ONE) < 0) begin
                frac_part <= 32'h0;
            end else begin
                frac_part <= normalized - Q16_ONE;
            end
            state <= 6'd7;
        end else if (state == 6'd7) begin
            // Extract LUT index from top 8 bits of fractional part
            lut_index <= (frac_part >> 8) & 8'hFF;
            state <= 6'd8;
        end else if (state == 6'd8) begin
            // Look up fractional log from LUT
            frac_log <= log2_lut[lut_index];
            state <= 6'd9;
        end else if (state == 6'd9) begin
            // Combine integer and fractional parts
            result_temp <= (integer_log2 << Q16_SHIFT) + $signed(frac_log);
            state <= 6'd20;
        end else if (state == 6'd20) begin
            // Saturate and output result
            if (result_temp > $signed(Q16_MAX)) begin
                result <= Q16_MAX;
                overflow <= 1'b1;
            end else if (result_temp < Q16_MIN) begin
                result <= Q16_MIN;
                overflow <= 1'b1;
            end else begin
                result <= result_temp[31:0];
                overflow <= 1'b0;
            end
            ready <= 1'b1;
            state <= 6'd0;
        end else if (state == 6'd10) begin
            // INFO_GAIN operation
            // Compute ratio first: (before << 16) / after
            if (operand_b == 32'h0 || operand_a == 32'h0) begin
                result <= 32'h0;
                overflow <= 1'b1;
                ready <= 1'b1;
                state <= 6'd0;
            end else if (operand_a == operand_b) begin
                result <= 32'h0;
                overflow <= 1'b0;
                ready <= 1'b1;
                state <= 6'd0;
            end else begin
                // Compute ratio in Q16.16: (before << 16) / after
                div_temp = ({operand_a, 16'h0}) / operand_b;
                temp_result = div_temp[31:0];
                state <= 6'd11;
            end
        end else if (state == 6'd11) begin
            // Now compute log2 of the ratio (stored in temp_result)
            // This reuses the LOG2 logic starting from state 6'd1
            log2_input <= temp_result;
            state <= 6'd12;
        end else if (state == 6'd12) begin
            // Check special cases for log2
            if (temp_result == 32'h0 || $signed(temp_result) < 0) begin
                result <= Q16_MIN;
                overflow <= 1'b1;
                ready <= 1'b1;
                state <= 6'd0;
            end else if (temp_result == Q16_ONE) begin
                result <= 32'h0;
                overflow <= 1'b0;
                ready <= 1'b1;
                state <= 6'd0;
            end else begin
                // Jump to LOG2 computation (reuse states 2-9)
                state <= 6'd2;
            end
        end
    end
end

endmodule
