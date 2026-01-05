// thiele_autonomous_solver.v -- autonomous backtracking controller for the
// reasoning_core fabric.
//
// The module accepts a graph adjacency matrix together with configurable per-node
// µ-question costs.  It orchestrates the combinational reasoning core to
// propagate constraints, makes speculative colouring decisions when the core can
// no longer force progress, and performs chronological backtracking upon
// contradiction.  Every interaction with the core contributes to the hardware
// µ-ledger: speculative claims consume question bits and log₂(3) information
// allowance, while forced deductions add their reported activity, question, and
// information figures.  The controller therefore implements a self-contained
// spatial search oracle for 3-colouring instances up to N nodes.

module thiele_autonomous_solver #(
    parameter int NODES = 9,
    parameter int MU_PRECISION = 16,
    parameter [32*NODES-1:0] NODE_QUESTION_BITS = {{NODES{32'd136}}},
    parameter [32*NODES-1:0] DECISION_QUESTION_BITS = {{NODES{32'd136}}}
)(
    input  wire                       clk,
    input  wire                       reset,
    input  wire                       start,
    input  wire [NODES*NODES-1:0]     adjacency,
    output reg                        done,
    output reg                        success,
    output reg [(NODES*2)-1:0]        colouring,
    output reg [31:0]                 mu_question_bits,
    output reg [31:0]                 mu_information_q16,
    output reg [31:0]                 mu_total_q16,
    output reg [$clog2((4*NODES)+1)-1:0] mu_activity_legacy,
    output reg [7:0]                  decision_depth,
    output reg [7:0]                  backtrack_count
);
    localparam [2:0] FULL  = 3'b111;
    localparam [2:0] RED   = 3'b001;
    localparam [2:0] GREEN = 3'b010;
    localparam [2:0] BLUE  = 3'b100;

    localparam int LOG2_2_Q16 = 1 << MU_PRECISION;
    localparam int LOG2_3_Q16 = 103872;

    // State encoding.
    localparam [3:0] ST_IDLE          = 4'd0;
    localparam [3:0] ST_INIT          = 4'd1;
    localparam [3:0] ST_PROPAGATE     = 4'd2;
    localparam [3:0] ST_APPLY_FORCES  = 4'd3;
    localparam [3:0] ST_EVALUATE      = 4'd4;
    localparam [3:0] ST_DECIDE_NEW    = 4'd5;
    localparam [3:0] ST_COMMIT_DECISION = 4'd6;
    localparam [3:0] ST_BACKTRACK     = 4'd7;
    localparam [3:0] ST_ADVANCE_CHOICE = 4'd8;
    localparam [3:0] ST_ACCUM_CONFLICT = 4'd9;
    localparam [3:0] ST_FINISHED      = 4'd10;

    reg [3:0] state;

    // Working storage for node masks and reasoning outputs.
    reg  [2:0] node_masks       [0:NODES-1];
    reg  [2:0] candidate_masks  [0:NODES-1];
    reg  [2:0] pending_masks    [0:NODES-1];
    reg  [NODES-1:0] pending_force_valid;
    reg  [$clog2((4*NODES)+1)-1:0] pending_activity;
    reg  [31:0] pending_question_bits;
    reg  [31:0] pending_information_q16;
    reg         pending_conflict;

    // Decision stack for chronological backtracking.
    reg  [7:0] decision_node     [0:NODES-1];
    reg  [2:0] decision_available[0:NODES-1];
    reg  [2:0] decision_tried    [0:NODES-1];
    reg  [2:0] stack_masks       [0:NODES-1][0:NODES-1];

    reg  [7:0] selected_node;
    reg  [2:0] selected_colour_mask;
    reg        new_decision_level;

    wire [3*NODES-1:0] mask_bus;
    wire [3*NODES-1:0] forced_bus;
    wire [NODES-1:0]   force_valid_bus;
    wire [$clog2((4*NODES)+1)-1:0] activity_bus;
    wire [31:0]        question_bits_bus;
    wire [31:0]        information_q16_bus;

    genvar gi;
    generate
        for (gi = 0; gi < NODES; gi = gi + 1) begin : PACK_MASKS
            assign mask_bus[(gi*3)+2 -: 3] = node_masks[gi];
        end
    endgenerate

    reasoning_core #(
        .NODES(NODES),
        .MU_PRECISION(MU_PRECISION)
    ) core (
        .node_masks(mask_bus),
        .adjacency(adjacency),
        .node_question_bits(NODE_QUESTION_BITS),
        .forced_masks(forced_bus),
        .force_valid(force_valid_bus),
        .activity_count(activity_bus),
        .question_bits(question_bits_bus),
        .information_gain_q16(information_q16_bus)
    );

    // Utility functions.
    function automatic bit is_single(input [2:0] mask);
        case (mask)
            RED, GREEN, BLUE: is_single = 1'b1;
            default:          is_single = 1'b0;
        endcase
    endfunction

    function automatic bit is_zero(input [2:0] mask);
        begin
            is_zero = (mask == 3'b000);
        end
    endfunction

    function automatic int popcount3(input [2:0] mask);
        begin
            popcount3 = mask[0] + mask[1] + mask[2];
        end
    endfunction

    function automatic [2:0] pick_first(input [2:0] mask);
        begin
            if (mask[0]) begin
                pick_first = 3'b001;
            end else if (mask[1]) begin
                pick_first = 3'b010;
            end else if (mask[2]) begin
                pick_first = 3'b100;
            end else begin
                pick_first = 3'b000;
            end
        end
    endfunction

    function automatic [1:0] mask_to_colour(input [2:0] mask);
        begin
            case (mask)
                RED:   mask_to_colour = 2'd0;
                GREEN: mask_to_colour = 2'd1;
                BLUE:  mask_to_colour = 2'd2;
                default: mask_to_colour = 2'd0;
            endcase
        end
    endfunction

    function automatic bit all_single(input [3*NODES-1:0] masks);
        integer idx;
        begin
            all_single = 1'b1;
            for (idx = 0; idx < NODES; idx = idx + 1) begin
                if (!is_single(masks[(idx*3)+2 -: 3])) begin
                    all_single = 1'b0;
                end
            end
        end
    endfunction

    function automatic int get_decision_question_bits(input int idx);
        begin
            get_decision_question_bits = DECISION_QUESTION_BITS[(idx*32)+31 -: 32];
        end
    endfunction

    integer i;
    integer j;
    integer best_node;
    integer best_score;
    integer prev_depth;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state              <= ST_IDLE;
            done               <= 1'b0;
            success            <= 1'b0;
            colouring          <= {(NODES*2){1'b0}};
            mu_question_bits   <= 32'd0;
            mu_information_q16 <= 32'd0;
            mu_total_q16       <= 32'd0;
            mu_activity_legacy <= '0;
            decision_depth     <= 8'd0;
            backtrack_count    <= 8'd0;
            pending_force_valid <= {NODES{1'b0}};
            pending_activity    <= '0;
            pending_question_bits   <= 32'd0;
            pending_information_q16 <= 32'd0;
            pending_conflict    <= 1'b0;
            selected_node       <= 8'd0;
            selected_colour_mask <= 3'b000;
            new_decision_level  <= 1'b0;
            for (i = 0; i < NODES; i = i + 1) begin
                node_masks[i]        <= FULL;
                candidate_masks[i]   <= FULL;
                pending_masks[i]     <= FULL;
                decision_node[i]     <= 8'd0;
                decision_available[i]<= 3'b000;
                decision_tried[i]    <= 3'b000;
                for (j = 0; j < NODES; j = j + 1) begin
                    stack_masks[i][j] <= FULL;
                end
            end
        end else begin
            case (state)
                ST_IDLE: begin
                    done    <= 1'b0;
                    success <= 1'b0;
                    if (start) begin
                        mu_question_bits   <= 32'd0;
                        mu_information_q16 <= 32'd0;
                        mu_total_q16       <= 32'd0;
                        mu_activity_legacy <= '0;
                        decision_depth     <= 8'd0;
                        backtrack_count    <= 8'd0;
                        for (i = 0; i < NODES; i = i + 1) begin
                            node_masks[i]      <= FULL;
                            decision_tried[i]  <= 3'b000;
                            decision_available[i] <= 3'b000;
                        end
                        state <= ST_INIT;
                    end
                end

                ST_INIT: begin
                    state <= ST_PROPAGATE;
                end

                ST_PROPAGATE: begin
                    bit conflict_now;
                    pending_force_valid    <= force_valid_bus;
                    pending_activity       <= activity_bus;
                    pending_question_bits  <= question_bits_bus;
                    pending_information_q16<= information_q16_bus;
                    conflict_now           = 1'b0;
                    for (i = 0; i < NODES; i = i + 1) begin
                        candidate_masks[i] <= forced_bus[(i*3)+2 -: 3];
                        pending_masks[i]   <= forced_bus[(i*3)+2 -: 3];
                        if (is_zero(forced_bus[(i*3)+2 -: 3])) begin
                            conflict_now = 1'b1;
                        end
                    end
                    pending_conflict <= conflict_now;

                    if (conflict_now) begin
                        state <= ST_ACCUM_CONFLICT;
                    end else if ((|force_valid_bus) == 1'b0) begin
                        state <= ST_EVALUATE;
                    end else begin
                        state <= ST_APPLY_FORCES;
                    end
                end

                ST_APPLY_FORCES: begin
                    for (i = 0; i < NODES; i = i + 1) begin
                        if (pending_force_valid[i]) begin
                            node_masks[i] <= pending_masks[i];
                        end
                    end
                    mu_activity_legacy <= mu_activity_legacy + pending_activity;
                    mu_question_bits   <= mu_question_bits + pending_question_bits;
                    mu_information_q16 <= mu_information_q16 + pending_information_q16;
                    mu_total_q16       <= ((mu_question_bits + pending_question_bits) << MU_PRECISION)
                                          + (mu_information_q16 + pending_information_q16);
                    state <= ST_PROPAGATE;
                end

                ST_ACCUM_CONFLICT: begin
                    mu_activity_legacy <= mu_activity_legacy + pending_activity;
                    mu_question_bits   <= mu_question_bits + pending_question_bits;
                    mu_information_q16 <= mu_information_q16 + pending_information_q16;
                    mu_total_q16       <= ((mu_question_bits + pending_question_bits) << MU_PRECISION)
                                          + (mu_information_q16 + pending_information_q16);
                    state <= ST_BACKTRACK;
                end

                ST_EVALUATE: begin
                    if (all_single(mask_bus)) begin
                        done    <= 1'b1;
                        success <= 1'b1;
                        for (i = 0; i < NODES; i = i + 1) begin
                            colouring[(i*2)+1 -: 2] <= mask_to_colour(node_masks[i]);
                        end
                        state <= ST_FINISHED;
                    end else begin
                        state <= ST_DECIDE_NEW;
                    end
                end

                ST_DECIDE_NEW: begin
                    best_node  = -1;
                    best_score = 4;
                    for (i = 0; i < NODES; i = i + 1) begin
                        if (!is_single(candidate_masks[i]) && !is_zero(candidate_masks[i])) begin
                            int score;
                            score = popcount3(candidate_masks[i]);
                            if (score < best_score) begin
                                best_score = score;
                                best_node  = i;
                            end
                        end
                    end

                    if (best_node < 0) begin
                        state <= ST_BACKTRACK;
                    end else begin
                        selected_node         <= best_node[7:0];
                        selected_colour_mask  <= pick_first(candidate_masks[best_node]);
                        decision_available[decision_depth] <= candidate_masks[best_node];
                        decision_tried[decision_depth]     <= 3'b000;
                        decision_node[decision_depth]      <= best_node[7:0];
                        new_decision_level <= 1'b1;
                        state <= ST_COMMIT_DECISION;
                    end
                end

                ST_ADVANCE_CHOICE: begin
                    int node_idx;
                    logic [2:0] remaining;
                    node_idx = decision_node[decision_depth];
                    remaining = decision_available[decision_depth] & ~decision_tried[decision_depth];
                    if (remaining == 3'b000) begin
                        state <= ST_BACKTRACK;
                    end else begin
                        selected_node        <= node_idx[7:0];
                        selected_colour_mask <= pick_first(remaining);
                        new_decision_level   <= 1'b0;
                        state <= ST_COMMIT_DECISION;
                    end
                end

                ST_COMMIT_DECISION: begin
                    int decision_idx;
                    int question_cost;
                    int info_gain;
                    decision_idx  = decision_depth;
                    question_cost = get_decision_question_bits(selected_node);
                    info_gain     = LOG2_3_Q16;
                    for (i = 0; i < NODES; i = i + 1) begin
                        stack_masks[decision_idx][i] <= node_masks[i];
                    end
                    node_masks[selected_node] <= selected_colour_mask;
                    if (new_decision_level) begin
                        decision_tried[decision_idx] <= selected_colour_mask;
                    end else begin
                        decision_tried[decision_idx] <= decision_tried[decision_idx] | selected_colour_mask;
                    end
                    decision_node[decision_idx] <= selected_node;
                    decision_depth <= decision_depth + 1'b1;
                    mu_activity_legacy <= mu_activity_legacy + 1'b1;
                    mu_question_bits   <= mu_question_bits + question_cost;
                    mu_information_q16 <= mu_information_q16 + info_gain;
                    mu_total_q16       <= ((mu_question_bits + question_cost) << MU_PRECISION)
                                          + (mu_information_q16 + info_gain);
`ifdef DEBUG_AUTONOMOUS_SOLVER
                    $display("[auto] commit depth=%0d node=%0d mask=%03b cost=%0d info=%0d", decision_idx, selected_node,
                             selected_colour_mask, question_cost, info_gain);
`endif
                    state <= ST_PROPAGATE;
                end

                ST_BACKTRACK: begin
                    if (decision_depth == 0) begin
                        done    <= 1'b1;
                        success <= 1'b0;
                        state   <= ST_FINISHED;
                    end else begin
                        prev_depth = decision_depth - 1;
                        decision_depth <= prev_depth;
                        backtrack_count <= backtrack_count + 1'b1;
                        for (i = 0; i < NODES; i = i + 1) begin
                            node_masks[i] <= stack_masks[prev_depth][i];
                        end
                        state <= ST_ADVANCE_CHOICE;
                    end
                end

                ST_FINISHED: begin
                    if (!start) begin
                        state <= ST_IDLE;
                    end
                end

                default: state <= ST_IDLE;
            endcase
        end
    end
endmodule
