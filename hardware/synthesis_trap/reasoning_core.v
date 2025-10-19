// reasoning_core.v -- combinational constraint propagation engine for the
// triadic_cascade graph-colouring instance.
//
// The module accepts a snapshot of per-vertex colour masks (three one-hot bits
// per node) and computes the residual search pressure that follows from the
// currently committed anchors.  The logic removes colours that clash with
// single-colour neighbours and detects nodes that become forced to a unique
// hue.  Every forced vertex contributes a physical µ-cost equal to the number
// of eliminated colours plus one bookkeeping unit; the aggregate activity count
// is reported alongside the per-node updates so that sequential controllers can
// account for the knowledge expenditure performed in gates.

module reasoning_core (
    input  wire [26:0] node_masks,
    output wire [26:0] forced_masks,
    output wire [8:0]  force_valid,
    output wire [5:0]  activity_count
);
    // Utility predicates for one-hot colour masks.
    function automatic is_single(input [2:0] mask);
        begin
            case (mask)
                3'b001, 3'b010, 3'b100: is_single = 1'b1;
                default:                is_single = 1'b0;
            endcase
        end
    endfunction

    // Convenience popcount for a three-bit mask.
    function automatic [1:0] popcount3(input [2:0] mask);
        begin
            popcount3 = mask[0] + mask[1] + mask[2];
        end
    endfunction

    // Slice the flattened bus into individual node masks.
    wire [2:0] mask0 = node_masks[2:0];
    wire [2:0] mask1 = node_masks[5:3];
    wire [2:0] mask2 = node_masks[8:6];
    wire [2:0] mask3 = node_masks[11:9];
    wire [2:0] mask4 = node_masks[14:12];
    wire [2:0] mask5 = node_masks[17:15];
    wire [2:0] mask6 = node_masks[20:18];
    wire [2:0] mask7 = node_masks[23:21];
    wire [2:0] mask8 = node_masks[26:24];

    // For each node compute the neighbour-forbidden mask produced by
    // single-colour neighbours.
    wire [2:0] forbid0 = (is_single(mask1) ? mask1 : 3'b000)
                       | (is_single(mask2) ? mask2 : 3'b000)
                       | (is_single(mask4) ? mask4 : 3'b000)
                       | (is_single(mask5) ? mask5 : 3'b000);

    wire [2:0] forbid1 = (is_single(mask0) ? mask0 : 3'b000)
                       | (is_single(mask2) ? mask2 : 3'b000)
                       | (is_single(mask3) ? mask3 : 3'b000)
                       | (is_single(mask5) ? mask5 : 3'b000);

    wire [2:0] forbid2 = (is_single(mask0) ? mask0 : 3'b000)
                       | (is_single(mask1) ? mask1 : 3'b000)
                       | (is_single(mask3) ? mask3 : 3'b000)
                       | (is_single(mask4) ? mask4 : 3'b000);

    wire [2:0] forbid3 = (is_single(mask1) ? mask1 : 3'b000)
                       | (is_single(mask2) ? mask2 : 3'b000)
                       | (is_single(mask7) ? mask7 : 3'b000)
                       | (is_single(mask8) ? mask8 : 3'b000);

    wire [2:0] forbid4 = (is_single(mask0) ? mask0 : 3'b000)
                       | (is_single(mask2) ? mask2 : 3'b000)
                       | (is_single(mask6) ? mask6 : 3'b000)
                       | (is_single(mask8) ? mask8 : 3'b000);

    wire [2:0] forbid5 = (is_single(mask0) ? mask0 : 3'b000)
                       | (is_single(mask1) ? mask1 : 3'b000)
                       | (is_single(mask6) ? mask6 : 3'b000)
                       | (is_single(mask7) ? mask7 : 3'b000);

    wire [2:0] forbid6 = (is_single(mask4) ? mask4 : 3'b000)
                       | (is_single(mask5) ? mask5 : 3'b000);

    wire [2:0] forbid7 = (is_single(mask3) ? mask3 : 3'b000)
                       | (is_single(mask5) ? mask5 : 3'b000);

    wire [2:0] forbid8 = (is_single(mask3) ? mask3 : 3'b000)
                       | (is_single(mask4) ? mask4 : 3'b000);

    // Residual masks after removing neighbour colours.
    wire [2:0] cand0 = mask0 & ~forbid0;
    wire [2:0] cand1 = mask1 & ~forbid1;
    wire [2:0] cand2 = mask2 & ~forbid2;
    wire [2:0] cand3 = mask3 & ~forbid3;
    wire [2:0] cand4 = mask4 & ~forbid4;
    wire [2:0] cand5 = mask5 & ~forbid5;
    wire [2:0] cand6 = mask6 & ~forbid6;
    wire [2:0] cand7 = mask7 & ~forbid7;
    wire [2:0] cand8 = mask8 & ~forbid8;

    // Detect newly forced nodes.
    wire force0 = is_single(cand0) && !is_single(mask0) && (cand0 != 3'b000);
    wire force1 = is_single(cand1) && !is_single(mask1) && (cand1 != 3'b000);
    wire force2 = is_single(cand2) && !is_single(mask2) && (cand2 != 3'b000);
    wire force3 = is_single(cand3) && !is_single(mask3) && (cand3 != 3'b000);
    wire force4 = is_single(cand4) && !is_single(mask4) && (cand4 != 3'b000);
    wire force5 = is_single(cand5) && !is_single(mask5) && (cand5 != 3'b000);
    wire force6 = is_single(cand6) && !is_single(mask6) && (cand6 != 3'b000);
    wire force7 = is_single(cand7) && !is_single(mask7) && (cand7 != 3'b000);
    wire force8 = is_single(cand8) && !is_single(mask8) && (cand8 != 3'b000);

    assign force_valid = {
        force8,
        force7,
        force6,
        force5,
        force4,
        force3,
        force2,
        force1,
        force0
    };

    // Forward the forced masks for sequential controllers.  Only lanes with
    // force_valid asserted will be consumed.
    assign forced_masks = {
        cand8,
        cand7,
        cand6,
        cand5,
        cand4,
        cand3,
        cand2,
        cand1,
        cand0
    };

    // Compute the µ-cost contribution for this propagation window.
    wire [2:0] removed0 = mask0 & ~cand0;
    wire [2:0] removed1 = mask1 & ~cand1;
    wire [2:0] removed2 = mask2 & ~cand2;
    wire [2:0] removed3 = mask3 & ~cand3;
    wire [2:0] removed4 = mask4 & ~cand4;
    wire [2:0] removed5 = mask5 & ~cand5;
    wire [2:0] removed6 = mask6 & ~cand6;
    wire [2:0] removed7 = mask7 & ~cand7;
    wire [2:0] removed8 = mask8 & ~cand8;

    wire [1:0] count0 = popcount3(removed0);
    wire [1:0] count1 = popcount3(removed1);
    wire [1:0] count2 = popcount3(removed2);
    wire [1:0] count3 = popcount3(removed3);
    wire [1:0] count4 = popcount3(removed4);
    wire [1:0] count5 = popcount3(removed5);
    wire [1:0] count6 = popcount3(removed6);
    wire [1:0] count7 = popcount3(removed7);
    wire [1:0] count8 = popcount3(removed8);

    wire [3:0] activity0 = force0 ? ({2'b00, count0} + 4'd1) : 4'd0;
    wire [3:0] activity1 = force1 ? ({2'b00, count1} + 4'd1) : 4'd0;
    wire [3:0] activity2 = force2 ? ({2'b00, count2} + 4'd1) : 4'd0;
    wire [3:0] activity3 = force3 ? ({2'b00, count3} + 4'd1) : 4'd0;
    wire [3:0] activity4 = force4 ? ({2'b00, count4} + 4'd1) : 4'd0;
    wire [3:0] activity5 = force5 ? ({2'b00, count5} + 4'd1) : 4'd0;
    wire [3:0] activity6 = force6 ? ({2'b00, count6} + 4'd1) : 4'd0;
    wire [3:0] activity7 = force7 ? ({2'b00, count7} + 4'd1) : 4'd0;
    wire [3:0] activity8 = force8 ? ({2'b00, count8} + 4'd1) : 4'd0;

    assign activity_count = activity0 + activity1 + activity2 + activity3 +
                            activity4 + activity5 + activity6 + activity7 +
                            activity8;
endmodule
