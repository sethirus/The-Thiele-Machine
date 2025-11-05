// reasoning_core.v -- combinational reasoning fabric for three-colour graphs.
//
// The module accepts a snapshot of per-vertex colour masks (three one-hot bits
// per node) together with a runtime-programmable adjacency matrix.  For every
// vertex it derives the colours forbidden by single-colour neighbours, computes
// the residual candidate mask, and reports newly forced assignments.  In
// addition to the legacy "activity count" used by the original Cornerstone
// evaluation, the core now emits μ-spec v2.0 accounting terms: the question-bit
// expenditure attributed to each forced oracle query and the Shannon
// information gain (expressed as Q16 fixed-point bits) delivered by the
// propagation step.  Sequential controllers can therefore accumulate the
// information-theoretic μ-cost without relying on host-side instrumentation.

module reasoning_core #(
    parameter int NODES = 9,
    parameter int MU_PRECISION = 16
)(
    input  wire [3*NODES-1:0]      node_masks,
    input  wire [NODES*NODES-1:0]  adjacency,
    input  wire [32*NODES-1:0]     node_question_bits,
    output logic [3*NODES-1:0]     forced_masks,
    output logic [NODES-1:0]       force_valid,
    output logic [$clog2((4*NODES)+1)-1:0] activity_count,
    output logic [31:0]            question_bits,
    output logic [31:0]            information_gain_q16
);
    localparam int LOG2_2_Q16       = 1 << MU_PRECISION;              // log₂ 2
    localparam int LOG2_3_Q16       = 103872;                          // round(log₂ 3 × 2¹⁶)
    localparam int LOG2_3_OVER_2_Q16 = LOG2_3_Q16 - LOG2_2_Q16;        // log₂(3/2)

    function automatic bit is_single(input logic [2:0] mask);
        case (mask)
            3'b001, 3'b010, 3'b100: is_single = 1'b1;
            default:                is_single = 1'b0;
        endcase
    endfunction

    function automatic int popcount3(input logic [2:0] mask);
        popcount3 = mask[0] + mask[1] + mask[2];
    endfunction

    function automatic int log_ratio_q16(input int before_count, input int after_count);
        if (before_count <= after_count) begin
            log_ratio_q16 = 0;
        end else begin
            case ({before_count[1:0], after_count[1:0]})
                4'b11_01: log_ratio_q16 = LOG2_3_Q16;       // 3 → 1
                4'b10_01: log_ratio_q16 = LOG2_2_Q16;       // 2 → 1
                4'b11_10: log_ratio_q16 = LOG2_3_OVER_2_Q16; // 3 → 2
                default:   log_ratio_q16 = 0;
            endcase
        end
    endfunction

    logic [2:0] masks      [0:NODES-1];
    logic [2:0] candidates [0:NODES-1];
    logic [2:0] removed    [0:NODES-1];

    integer i, j;
    integer activity_tmp;
    integer question_tmp;
    integer info_tmp;

    always @* begin
        for (i = 0; i < NODES; i = i + 1) begin
            masks[i] = node_masks[(i*3)+2 -: 3];
            candidates[i] = 3'b000;
            removed[i] = 3'b000;
        end

        force_valid          = '0;
        forced_masks         = '0;
        activity_tmp         = 0;
        question_tmp         = 0;
        info_tmp             = 0;

        for (i = 0; i < NODES; i = i + 1) begin
            logic [2:0] forbid;
            forbid = 3'b000;

            for (j = 0; j < NODES; j = j + 1) begin
                if (adjacency[(i*NODES)+j]) begin
                    if (is_single(masks[j])) begin
                        forbid |= masks[j];
                    end
                end
            end

            candidates[i] = masks[i] & ~forbid;
            forced_masks[(i*3)+2 -: 3] = candidates[i];

            if (is_single(candidates[i]) && !is_single(masks[i]) && (candidates[i] != 3'b000)) begin
                force_valid[i] = 1'b1;
                removed[i] = masks[i] & ~candidates[i];

                activity_tmp = activity_tmp + popcount3(removed[i]) + 1;
                question_tmp = question_tmp + node_question_bits[(i*32)+31 -: 32];
                info_tmp = info_tmp + log_ratio_q16(popcount3(masks[i]), popcount3(candidates[i]));
            end
        end

        activity_count       = activity_tmp[$clog2((4*NODES)+1)-1:0];
        question_bits        = question_tmp[31:0];
        information_gain_q16 = info_tmp[31:0];
    end
endmodule
