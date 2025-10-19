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

module thiele_graph_solver (
    input  wire        clk,
    input  wire        reset,
    input  wire        start,
    output reg         done,
    output reg         success,
    output reg [17:0]  colouring,
    output reg [7:0]   mu_cost
);
    localparam integer NODES = 9;

    localparam [2:0] FULL  = 3'b111;
    localparam [2:0] RED   = 3'b001;
    localparam [2:0] GREEN = 3'b010;
    localparam [2:0] BLUE  = 3'b100;

    // Packed per-node masks and staging buffers for forced updates.
    reg [2:0] node_masks   [0:NODES-1];
    reg [2:0] pending_masks[0:NODES-1];
    reg [8:0] pending_force_valid;
    reg [5:0] pending_activity;

    wire [26:0] mask_bus;
    wire [26:0] forced_bus;
    wire [8:0]  force_valid_bus;
    wire [5:0]  activity_bus;

    // Pack the array for the combinational reasoning core.
    genvar gi;
    generate
        for (gi = 0; gi < NODES; gi = gi + 1) begin : PACK_MASKS
            assign mask_bus[(gi*3)+2 -: 3] = node_masks[gi];
        end
    endgenerate

    reasoning_core core (
        .node_masks(mask_bus),
        .forced_masks(forced_bus),
        .force_valid(force_valid_bus),
        .activity_count(activity_bus)
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

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state    <= ST_IDLE;
            done     <= 1'b0;
            success  <= 1'b0;
            colouring <= 18'd0;
            mu_cost  <= 8'd0;
            pending_force_valid <= 9'd0;
            pending_activity    <= 6'd0;
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
                        mu_cost <= 8'd0;
                        for (i = 0; i < NODES; i = i + 1) begin
                            node_masks[i] <= FULL;
                        end
                        state <= ST_CLAIM;
                    end
                end

                ST_CLAIM: begin
                    node_masks[0] <= RED;
                    node_masks[1] <= GREEN;
                    mu_cost       <= 8'd2; // two anchor claims
                    state         <= ST_PROPAGATE;
                end

                ST_PROPAGATE: begin
                    pending_force_valid <= force_valid_bus;
                    pending_activity    <= activity_bus;
                    for (i = 0; i < NODES; i = i + 1) begin
                        pending_masks[i] <= forced_bus[(i*3)+2 -: 3];
                    end

                    if (force_valid_bus == 9'd0) begin
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
                    mu_cost <= mu_cost + {2'b00, pending_activity};
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
