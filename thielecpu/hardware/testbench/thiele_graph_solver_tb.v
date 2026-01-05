`timescale 1ns/1ps

module thiele_graph_solver_tb;
    localparam int NODES = 9;
    localparam int MU_PRECISION = 16;
    localparam [NODES*NODES-1:0] ADJACENCY = {
        9'b000011000,
        9'b000101000,
        9'b000110000,
        9'b011000011,
        9'b101000101,
        9'b110000110,
        9'b000011011,
        9'b000101101,
        9'b000110110
    };
    localparam [32*NODES-1:0] NODE_QBITS = {
        32'd136, 32'd136, 32'd136, 32'd136, 32'd136,
        32'd136, 32'd136, 32'd136, 32'd136
    };
    localparam [32*NODES-1:0] DECISION_QBITS = {
        32'd136, 32'd136, 32'd136, 32'd136, 32'd136,
        32'd136, 32'd136, 32'd176, 32'd160
    };

    reg clk = 0;
    reg reset = 1;
    reg start = 0;

    wire done_seq;
    wire [(NODES*2)-1:0] colouring_seq;
    wire [31:0] mu_question_bits_seq;
    wire [31:0] mu_information_q16_seq;
    wire [31:0] mu_total_q16_seq;
    wire [5:0]  mu_activity_seq;

    wire done_auto;
    wire [(NODES*2)-1:0] colouring_auto;
    wire [31:0] mu_question_bits_auto;
    wire [31:0] mu_information_q16_auto;
    wire [31:0] mu_total_q16_auto;
    wire [5:0]  mu_activity_auto;
    wire [7:0]  decision_depth_auto;
    wire [7:0]  backtracks_auto;
    wire [3:0]  state_auto = dut_auto.state;

    integer cycle_guard = 0;
    reg seq_finished = 0;
    reg auto_finished = 0;

    thiele_graph_solver dut_seq (
        .clk(clk),
        .reset(reset),
        .start(start),
        .done(done_seq),
        .success(),
        .colouring(colouring_seq),
        .mu_question_bits(mu_question_bits_seq),
        .mu_information_q16(mu_information_q16_seq),
        .mu_total_q16(mu_total_q16_seq),
        .mu_activity_legacy(mu_activity_seq)
    );

    thiele_autonomous_solver #(
        .NODES(NODES),
        .MU_PRECISION(MU_PRECISION),
        .NODE_QUESTION_BITS(NODE_QBITS),
        .DECISION_QUESTION_BITS(DECISION_QBITS)
    ) dut_auto (
        .clk(clk),
        .reset(reset),
        .start(start),
        .adjacency(ADJACENCY),
        .done(done_auto),
        .success(),
        .colouring(colouring_auto),
        .mu_question_bits(mu_question_bits_auto),
        .mu_information_q16(mu_information_q16_auto),
        .mu_total_q16(mu_total_q16_auto),
        .mu_activity_legacy(mu_activity_auto),
        .decision_depth(decision_depth_auto),
        .backtrack_count(backtracks_auto)
    );

    always #5 clk = ~clk;

    always @(posedge clk) begin
        if (reset) begin
            cycle_guard  <= 0;
            seq_finished <= 0;
            auto_finished <= 0;
        end else begin
            if (start) begin
                cycle_guard  <= 0;
                seq_finished <= 0;
                auto_finished <= 0;
            end else begin
                if (done_seq) begin
                    seq_finished <= 1;
                end
                if (done_auto) begin
                    auto_finished <= 1;
                end
                if (!(seq_finished && auto_finished)) begin
                    cycle_guard <= cycle_guard + 1;
                    if (cycle_guard > 100000) begin
                        $display("ERROR: Timeout waiting for solvers to finish (seq=%0b auto=%0b state=%0d depth=%0d backtracks=%0d)",
                                 done_seq, done_auto, state_auto, decision_depth_auto, backtracks_auto);
                        $finish_and_return(1);
                    end
                end
            end
        end
    end

    initial begin
        $display("Starting dual solver testbench...");
        #20;
        reset = 0;
        #10;
        start = 1;
        #10;
        start = 0;

        wait (done_seq == 1'b1);
        wait (done_auto == 1'b1);
        #10; // allow register outputs to settle

        $display("Sequential solver μ_question=%0d, μ_info=%0d (Q16), μ_total=%0d (Q16)",
                 mu_question_bits_seq, mu_information_q16_seq, mu_total_q16_seq);
        if (mu_activity_seq !== 6'd23) begin
            $display("ERROR: Expected legacy µ-cost of 23, got %0d (sequential).", mu_activity_seq);
            $finish_and_return(1);
        end
        if (mu_question_bits_seq !== 32'd1288) begin
            $display("ERROR: Expected question-bit total of 1288, got %0d (sequential).", mu_question_bits_seq);
            $finish_and_return(1);
        end
        if (mu_information_q16_seq !== 32'd934848) begin
            $display("ERROR: Expected information gain of 934848 (Q16), got %0d (sequential).", mu_information_q16_seq);
            $finish_and_return(1);
        end
        if (mu_total_q16_seq !== 32'd85345216) begin
            $display("ERROR: Expected μ-total of 85345216 (Q16), got %0d (sequential).", mu_total_q16_seq);
            $finish_and_return(1);
        end
        if (colouring_seq !== 18'h24924) begin
            $display("ERROR: Unexpected sequential colouring: got 0x%05h", colouring_seq);
            $finish_and_return(1);
        end

        $display("Autonomous solver μ_question=%0d, μ_info=%0d (Q16), μ_total=%0d (Q16)",
                 mu_question_bits_auto, mu_information_q16_auto, mu_total_q16_auto);
        if (mu_activity_auto !== 6'd23) begin
            $display("ERROR: Expected legacy µ-cost of 23, got %0d (autonomous).", mu_activity_auto);
            $finish_and_return(1);
        end
        if (mu_question_bits_auto !== 32'd1288) begin
            $display("ERROR: Expected question-bit total of 1288, got %0d (autonomous).", mu_question_bits_auto);
            $finish_and_return(1);
        end
        if (mu_information_q16_auto !== 32'd934848) begin
            $display("ERROR: Expected information gain of 934848 (Q16), got %0d (autonomous).", mu_information_q16_auto);
            $finish_and_return(1);
        end
        if (mu_total_q16_auto !== 32'd85345216) begin
            $display("ERROR: Expected μ-total of 85345216 (Q16), got %0d (autonomous).", mu_total_q16_auto);
            $finish_and_return(1);
        end
        if (colouring_auto !== 18'h24924) begin
            $display("ERROR: Unexpected autonomous colouring: got 0x%05h", colouring_auto);
            $finish_and_return(1);
        end
        if (backtracks_auto !== 8'd0) begin
            $display("ERROR: Autonomous solver performed unexpected backtracking steps: %0d", backtracks_auto);
            $finish_and_return(1);
        end

        $display("PASS: Both solvers reach the target colouring with unified μ-spec accounting.");
        $finish_and_return(0);
    end
endmodule
