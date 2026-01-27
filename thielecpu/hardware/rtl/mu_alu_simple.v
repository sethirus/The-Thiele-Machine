// ============================================================================
// SIMPLE μ-ALU - Synthesis-Friendly Version
// ============================================================================
// Simplified arithmetic logic unit for μ-cost calculations

module mu_alu_simple (
    input wire clk,
    input wire rst_n,
    
    input wire [31:0] operand_a,
    input wire [31:0] operand_b,
    
    output wire [31:0] result,
    output wire ready
);

// Simple combinational adder (synthesis-friendly)
assign result = operand_a + operand_b;
assign ready = 1'b1;  // Always ready for simple operations

endmodule
