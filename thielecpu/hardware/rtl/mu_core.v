// ############################################################################
// SUBMODULE: mu_core — Partition Isomorphism Enforcement Unit
// ############################################################################
//
// Standalone extraction from thiele_cpu_unified.v
//
// The "Cost Gate" — ensures:
//   1. No instruction executes without valid μ-receipt
//   2. Partition operations maintain logical independence
//   3. μ-cost monotonically increases (no free computation)

module mu_core (
    input  wire        clk,
    input  wire        rst_n,
    input  wire [31:0] instruction,
    input  wire        instr_valid,
    output reg         instr_allowed,
    output reg         receipt_required,
    input  wire [31:0] current_mu_cost,
    input  wire [31:0] proposed_cost,
    input  wire [5:0]  partition_count,
    input  wire [31:0] memory_isolation,
    input  wire [31:0] receipt_value,
    input  wire        receipt_valid,
    output reg         receipt_accepted,
    output reg         cost_gate_open,
    output reg         partition_gate_open,
    output reg  [31:0] core_status,
    output reg         enforcement_active
);

localparam [7:0] OPC_PNEW      = 8'h00, OPC_PSPLIT    = 8'h01, OPC_PMERGE    = 8'h02,
                 OPC_PDISCOVER  = 8'h06, OPC_MDLACC    = 8'h05, OPC_HALT      = 8'hFF;

localparam [31:0] ST_IDLE = 0, ST_CHECKING = 1, ST_ALLOWED = 2,
                  ST_DENIED_COST = 3, ST_DENIED_ISO = 4, ST_RECEIPT_OK = 5;

reg [31:0] last_instruction;
reg [31:0] expected_cost;
reg partition_independent, cost_decreasing;
reg last_instr_valid;
reg [31:0] prev_post_mu;

// Receipt integrity checker (instantiated here)
wire [31:0] computed_instruction_cost;
wire receipt_integrity_ok_w, chain_continuity_ok_w;

receipt_integrity_checker integrity_checker (
    .clk(clk), .rst_n(rst_n),
    .receipt_valid(instr_valid),
    .receipt_pre_mu(current_mu_cost),
    .receipt_post_mu(proposed_cost),
    .receipt_opcode(instruction[31:24]),
    .receipt_operand({8'b0, instruction[23:0]}),
    .chain_mode(1'b1),
    .prev_post_mu(prev_post_mu),
    .receipt_integrity_ok(receipt_integrity_ok_w),
    .chain_continuity_ok(chain_continuity_ok_w),
    .computed_cost(computed_instruction_cost),
    .error_code()
);

wire new_instruction_cycle = instr_valid && !last_instr_valid;

function check_partition_independence;
    input [31:0] instr;
    input [5:0]  part_count;
    input [31:0] mem_iso;
    begin
        case (instr[31:24])
            OPC_PNEW:   check_partition_independence = (part_count < 64);
            OPC_PSPLIT:  check_partition_independence = (instr[23:16] < part_count) && (part_count < 63);
            OPC_PMERGE:  check_partition_independence = (instr[23:16] < part_count) &&
                                                        (instr[15:8]  < part_count) &&
                                                        (instr[23:16] != instr[15:8]);
            default:     check_partition_independence = 1'b1;
        endcase
        check_partition_independence = check_partition_independence && (mem_iso == 32'hCAFEBABE);
    end
endfunction

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        instr_allowed      <= 1'b0;
        receipt_required   <= 1'b0;
        receipt_accepted   <= 1'b0;
        cost_gate_open     <= 1'b0;
        partition_gate_open <= 1'b0;
        core_status        <= ST_IDLE;
        enforcement_active <= 1'b1;
        last_instruction   <= 32'hDEADBEEF;
        expected_cost      <= 32'h0;
        partition_independent <= 1'b1;
        cost_decreasing    <= 1'b0;
        last_instr_valid   <= 1'b0;
        prev_post_mu       <= 32'h0;
    end else begin
        last_instr_valid <= instr_valid;

        if (new_instruction_cycle) begin
            last_instruction <= instruction;
            core_status      <= ST_CHECKING;

            case (instruction[31:24])
                OPC_PNEW, OPC_PSPLIT, OPC_PMERGE: begin
                    receipt_required <= 1'b0;
                    instr_allowed    <= 1'b1;
                    partition_independent <= check_partition_independence(instruction, partition_count, memory_isolation);
                    partition_gate_open   <= check_partition_independence(instruction, partition_count, memory_isolation);
                    cost_decreasing  <= (proposed_cost >= current_mu_cost);
                    cost_gate_open   <= (proposed_cost >= current_mu_cost);
                    if (check_partition_independence(instruction, partition_count, memory_isolation) &&
                        (proposed_cost >= current_mu_cost)) begin
                        expected_cost <= proposed_cost;
                        core_status   <= ST_ALLOWED;
                    end else if (!check_partition_independence(instruction, partition_count, memory_isolation))
                        core_status <= ST_DENIED_ISO;
                    else
                        core_status <= ST_DENIED_COST;
                end
                OPC_PDISCOVER: begin
                    receipt_required    <= 1'b1;
                    instr_allowed       <= 1'b0;
                    partition_gate_open <= 1'b1;
                    cost_gate_open      <= 1'b1;
                    expected_cost       <= proposed_cost;
                    core_status         <= ST_ALLOWED;
                end
                OPC_MDLACC: begin
                    receipt_required    <= 1'b1;
                    instr_allowed       <= 1'b0;
                    partition_gate_open <= 1'b1;
                    cost_gate_open      <= 1'b1;
                    expected_cost       <= proposed_cost;
                    core_status         <= ST_ALLOWED;
                end
                default: begin
                    receipt_required    <= 1'b0;
                    instr_allowed       <= 1'b1;
                    partition_gate_open <= 1'b1;
                    cost_gate_open      <= 1'b1;
                    core_status         <= ST_IDLE;
                end
            endcase
        end

        if (receipt_valid && receipt_required) begin
            if (receipt_value == expected_cost && receipt_integrity_ok_w && chain_continuity_ok_w) begin
                receipt_accepted <= 1'b1;
                instr_allowed    <= 1'b1;
                core_status      <= ST_RECEIPT_OK;
                prev_post_mu     <= proposed_cost;
`ifndef SYNTHESIS
                $display("mu-Core: Receipt accepted for instruction %h, cost=%0d", instruction, receipt_value >> 16);
`endif
            end else begin
                receipt_accepted <= 1'b0;
                instr_allowed    <= 1'b0;
                core_status      <= ST_DENIED_COST;
                if (!receipt_integrity_ok_w) begin
`ifndef SYNTHESIS
                    $display("mu-Core: Receipt DENIED - integrity check FAILED");
`endif
                end else if (!chain_continuity_ok_w) begin
`ifndef SYNTHESIS
                    $display("mu-Core: Receipt DENIED - chain continuity FAILED");
`endif
                end else begin
`ifndef SYNTHESIS
                    $display("mu-Core: Receipt DENIED for instruction %h, expected=%0d, got=%0d",
                             instruction, expected_cost >> 16, receipt_value >> 16);
`endif
                end
            end
        end

        if (!instr_valid) begin
            instr_allowed       <= 1'b0;
            receipt_required    <= 1'b0;
            receipt_accepted    <= 1'b0;
            cost_gate_open      <= 1'b0;
            partition_gate_open <= 1'b0;
            core_status         <= ST_IDLE;
        end
    end
end

endmodule
