// Simple combinational module returning ceiling(log2(x)) for up to 8-bit input
module clz8(
    input [7:0] x,
    output reg [3:0] out
);

always @(*) begin
    if (x == 0) out = 1;
    else if (x <= 1) out = 1;
    else if (x <= 2) out = 1;
    else if (x <= 4) out = 2;
    else if (x <= 8) out = 3;
    else if (x <= 16) out = 4;
    else if (x <= 32) out = 5;
    else if (x <= 64) out = 6;
    else if (x <= 128) out = 7;
    else out = 8;
end
endmodule
