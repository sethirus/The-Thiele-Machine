// thiele_graph_solver.v -- Sequential Thiele-style solver that orchestrates the
// reasoning_core to colour the triadic_cascade graph.
//
// The controller performs three phases:
//   1. Anchor µ-funded claims (node 0 = red, node 1 = green).
//   2. Iterate the reasoning core until no additional nodes are forced.
//   3. Report the final colouring alongside the accumulated µ-cost.
//
// Knowledge expenditure is physically measured: every forced deduction reports
// the number of colours eliminated plus one bookkeeping tick, and the state
// machine accrues that activity count into the µ-cost register alongside the
// explicit anchor claims.

module thiele_graph_solver #(
    parameter int NODES = 9,
    parameter int MU_PRECISION = 16,
    parameter int NUM_ANCHORS = 2,
    parameter [NUM_ANCHORS*8-1:0]  ANCHOR_NODE_IDS    = {8'd1, 8'd0},
    parameter [NUM_ANCHORS*3-1:0]  ANCHOR_COLOUR_MASKS = {3'b010, 3'b001},
    parameter [NUM_ANCHORS*32-1:0] ANCHOR_QUESTION_BITS = {32'd176, 32'd160},
    parameter [32*NODES-1:0]       NODE_QUESTION_BITS   = {{NODES{32'd136}}},
    parameter [NODES*NODES-1:0]    ADJACENCY            = {
        9'b000011000,
        9'b000101000,
        9'b000110000,
        9'b011000011,
        9'b101000101,
        9'b110000110,
        9'b000011011,
        9'b000101101,
        9'b000110110
    }
)(
    input  wire        clk,
    input  wire        reset,
    input  wire        start,
    output reg         done,
    output reg         success,
    output reg [((NODES*2)-1):0] colouring,
    output reg [31:0]   mu_question_bits,
    output reg [31:0]   mu_information_q16,
    output reg [31:0]   mu_total_q16,
    output reg [$clog2((4*NODES)+1)-1:0] mu_activity_legacy
);

    localparam [2:0] FULL  = 3'b111;
    localparam [2:0] RED   = 3'b001;
    localparam [2:0] GREEN = 3'b010;
    localparam [2:0] BLUE  = 3'b100;

    // Packed per-node masks and staging buffers for forced updates.
    reg [2:0] node_masks   [0:NODES-1];
    reg [2:0] pending_masks[0:NODES-1];
    reg [NODES-1:0] pending_force_valid;
    reg [$clog2((4*NODES)+1)-1:0] pending_activity;
    reg [31:0] pending_question_bits;
    reg [31:0] pending_information_q16;

    wire [3*NODES-1:0] mask_bus;
    wire [3*NODES-1:0] forced_bus;
    wire [NODES-1:0]  force_valid_bus;
    wire [$clog2((4*NODES)+1)-1:0] activity_bus;
    wire [31:0] question_bits_bus;
    wire [31:0] information_q16_bus;

    // Pack the array for the combinational reasoning core.
    genvar gi;
    generate
        for (gi = 0; gi < NODES; gi = gi + 1) begin : PACK_MASKS
            assign mask_bus[(gi*3)+2 -: 3] = node_masks[gi];
        end
    endgenerate

    wire [NODES*NODES-1:0] adjacency_bus = ADJACENCY;

    reasoning_core #(
        .NODES(NODES),
        .MU_PRECISION(MU_PRECISION)
    ) core (
        .node_masks(mask_bus),
        .adjacency(adjacency_bus),
        .node_question_bits(NODE_QUESTION_BITS),
        .forced_masks(forced_bus),
        .force_valid(force_valid_bus),
        .activity_count(activity_bus),
        .question_bits(question_bits_bus),
        .information_gain_q16(information_q16_bus)
    );

    // Utility functions reused inside the controller.
    function automatic [0:0] is_single(input [2:0] mask);
        begin
            case (mask)
                RED, GREEN, BLUE: is_single = 1'b1;
                default:          is_single = 1'b0;
            endcase
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

    function automatic [0:0] all_single(input [26:0] masks);
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

    // Controller state machine.
    localparam [2:0] ST_IDLE      = 3'd0;
    localparam [2:0] ST_CLAIM     = 3'd1;
    localparam [2:0] ST_PROPAGATE = 3'd2;
    localparam [2:0] ST_UPDATE    = 3'd3;
    localparam [2:0] ST_FINISHED  = 3'd4;

    reg [2:0] state;

    integer i;
    integer a;

    function automatic int get_anchor_node(input int idx);
        get_anchor_node = ANCHOR_NODE_IDS[(idx*8)+7 -: 8];
    endfunction

    function automatic [2:0] get_anchor_colour(input int idx);
        get_anchor_colour = ANCHOR_COLOUR_MASKS[(idx*3)+2 -: 3];
    endfunction

    function automatic int get_anchor_question(input int idx);
        get_anchor_question = ANCHOR_QUESTION_BITS[(idx*32)+31 -: 32];
    endfunction

    function automatic int sum_anchor_question_bits();
        int acc;
        int idx;
        begin
            acc = 0;
            for (idx = 0; idx < NUM_ANCHORS; idx = idx + 1) begin
                acc += get_anchor_question(idx);
            end
            sum_anchor_question_bits = acc;
        end
    endfunction

    localparam int ANCHOR_QUESTION_TOTAL = sum_anchor_question_bits();
    localparam int LOG2_3_Q16 = 103872;
    localparam int ANCHOR_INFORMATION_Q16 = NUM_ANCHORS * LOG2_3_Q16;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state    <= ST_IDLE;
            done     <= 1'b0;
            success  <= 1'b0;
            colouring <= {(NODES*2){1'b0}};
            mu_question_bits     <= 32'd0;
            mu_information_q16   <= 32'd0;
            mu_total_q16         <= 32'd0;
            mu_activity_legacy   <= '0;
            pending_force_valid  <= {NODES{1'b0}};
            pending_activity     <= '0;
            pending_question_bits   <= 32'd0;
            pending_information_q16 <= 32'd0;
            for (i = 0; i < NODES; i = i + 1) begin
                node_masks[i]    <= FULL;
                pending_masks[i] <= FULL;
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
                        for (i = 0; i < NODES; i = i + 1) begin
                            node_masks[i] <= FULL;
                        end
                        state <= ST_CLAIM;
                    end
                end

                ST_CLAIM: begin
                    for (a = 0; a < NUM_ANCHORS; a = a + 1) begin
                        int anchor_node;
                        anchor_node = get_anchor_node(a);
                        if (anchor_node < NODES) begin
                            node_masks[anchor_node] <= get_anchor_colour(a);
                        end
                    end
                    mu_activity_legacy <= NUM_ANCHORS;
                    mu_question_bits   <= ANCHOR_QUESTION_TOTAL;
                    mu_information_q16 <= ANCHOR_INFORMATION_Q16;
                    mu_total_q16       <= (ANCHOR_QUESTION_TOTAL << MU_PRECISION) + ANCHOR_INFORMATION_Q16;
                    state         <= ST_PROPAGATE;
                end

                ST_PROPAGATE: begin
                    pending_force_valid <= force_valid_bus;
                    pending_activity    <= activity_bus;
                    pending_question_bits   <= question_bits_bus;
                    pending_information_q16 <= information_q16_bus;
                    for (i = 0; i < NODES; i = i + 1) begin
                        pending_masks[i] <= forced_bus[(i*3)+2 -: 3];
                    end

                    if (force_valid_bus == {NODES{1'b0}}) begin
                        done    <= 1'b1;
                        success <= all_single(mask_bus);
                        for (i = 0; i < NODES; i = i + 1) begin
                            colouring[(i*2)+1 -: 2] <= mask_to_colour(node_masks[i]);
                        end
                        state <= ST_FINISHED;
                    end else begin
                        state <= ST_UPDATE;
                    end
                end

                ST_UPDATE: begin
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
                    state   <= ST_PROPAGATE;
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
