// ############################################################################
// SUBMODULE: receipt_integrity_checker — Hardware Receipt Verification
// ############################################################################
//
// Standalone extraction from thiele_cpu_unified.v
//
// Implements the Coq-proven property:
//   receipt_mu_consistent: post_mu = pre_mu + instruction_cost(instr)
//
// Any forged receipt (wrong μ-delta) is rejected.

module receipt_integrity_checker (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        receipt_valid,
    input  wire [31:0] receipt_pre_mu,
    input  wire [31:0] receipt_post_mu,
    input  wire [7:0]  receipt_opcode,
    input  wire [31:0] receipt_operand,
    input  wire        chain_mode,
    input  wire [31:0] prev_post_mu,
    output reg         receipt_integrity_ok,
    output reg         chain_continuity_ok,
    output reg  [31:0] computed_cost,
    output reg  [31:0] error_code
);

// Opcodes (local copy — must match top-level)
localparam [7:0] OP_PNEW      = 8'h00, OP_PSPLIT    = 8'h01, OP_PMERGE    = 8'h02,
                 OP_LASSERT    = 8'h03, OP_LJOIN     = 8'h04, OP_MDLACC    = 8'h05,
                 OP_PDISCOVER  = 8'h06, OP_XFER      = 8'h07, OP_PYEXEC    = 8'h08,
                 OP_CHSH_TRIAL = 8'h09, OP_XOR_LOAD  = 8'h0A, OP_XOR_ADD   = 8'h0B,
                 OP_XOR_SWAP   = 8'h0C, OP_XOR_RANK  = 8'h0D, OP_EMIT      = 8'h0E,
                 OP_REVEAL     = 8'h0F, OP_ORACLE    = 8'h10, OP_HALT      = 8'hFF;

// Error codes
localparam [31:0] ERR_NONE    = 32'h0, ERR_MU_MISMATCH  = 32'h1,
                  ERR_CHAIN   = 32'h2, ERR_UNKNOWN_OP   = 32'h3,
                  ERR_OVERFLOW = 32'h4;

function [31:0] compute_instruction_cost;
    input [7:0]  opcode;
    input [31:0] operand;
    begin
        case (opcode)
            OP_PNEW, OP_PSPLIT, OP_PMERGE, OP_LASSERT, OP_LJOIN,
            OP_MDLACC, OP_PDISCOVER, OP_XFER, OP_PYEXEC, OP_CHSH_TRIAL,
            OP_XOR_LOAD, OP_XOR_ADD, OP_XOR_SWAP, OP_XOR_RANK,
            OP_EMIT, OP_ORACLE:
                compute_instruction_cost = {24'h0, operand[7:0]};
            OP_REVEAL:
                compute_instruction_cost = {16'h0, operand[23:16], 8'h0} + {24'h0, operand[7:0]};
            OP_HALT:
                compute_instruction_cost = 32'h0;
            default:
                compute_instruction_cost = 32'hFFFFFFFF;  // sentinel
        endcase
    end
endfunction

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        receipt_integrity_ok <= 1'b0;
        chain_continuity_ok  <= 1'b0;
        computed_cost        <= 32'h0;
        error_code           <= ERR_NONE;
    end else begin
        if (receipt_valid) begin
            computed_cost <= compute_instruction_cost(receipt_opcode, receipt_operand);

            if (compute_instruction_cost(receipt_opcode, receipt_operand) == 32'hFFFFFFFF) begin
                receipt_integrity_ok <= 1'b0;
                error_code           <= ERR_UNKNOWN_OP;
            end else if (receipt_pre_mu > 32'hFFFFFFFF - computed_cost) begin
                receipt_integrity_ok <= 1'b0;
                error_code           <= ERR_OVERFLOW;
            end else if (receipt_post_mu == receipt_pre_mu + compute_instruction_cost(receipt_opcode, receipt_operand)) begin
                receipt_integrity_ok <= 1'b1;
                error_code           <= ERR_NONE;
            end else begin
                receipt_integrity_ok <= 1'b0;
                error_code           <= ERR_MU_MISMATCH;
`ifndef SYNTHESIS
                $display("FORGERY DETECTED: pre_mu=%d, post_mu=%d, expected=%d",
                         receipt_pre_mu, receipt_post_mu,
                         receipt_pre_mu + compute_instruction_cost(receipt_opcode, receipt_operand));
`endif
            end

            if (chain_mode) begin
                if (receipt_pre_mu == prev_post_mu)
                    chain_continuity_ok <= 1'b1;
                else begin
                    chain_continuity_ok <= 1'b0;
                    error_code          <= ERR_CHAIN;
`ifndef SYNTHESIS
                    $display("CHAIN BREAK: prev_post_mu=%d, this_pre_mu=%d",
                             prev_post_mu, receipt_pre_mu);
`endif
                end
            end else begin
                chain_continuity_ok <= 1'b1;
            end
        end else begin
            receipt_integrity_ok <= 1'b0;
            chain_continuity_ok  <= 1'b0;
        end
    end
end

`ifdef FORMAL
always @(posedge clk) begin
    if (receipt_integrity_ok && receipt_valid)
        assert(receipt_post_mu == receipt_pre_mu + computed_cost);
    if (chain_continuity_ok && chain_mode && receipt_valid)
        assert(receipt_pre_mu == prev_post_mu);
end
`endif

endmodule
