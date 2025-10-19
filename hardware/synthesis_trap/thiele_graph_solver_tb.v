`timescale 1ns/1ps

module thiele_graph_solver_tb;
    reg clk = 0;
    reg reset = 1;
    reg start = 0;
    wire done;
    wire success;
    wire [17:0] colouring;
    wire [7:0] mu_cost;

    thiele_graph_solver dut (
        .clk(clk),
        .reset(reset),
        .start(start),
        .done(done),
        .success(success),
        .colouring(colouring),
        .mu_cost(mu_cost)
    );

    always #5 clk = ~clk;

    initial begin
        $display("Starting thiele_graph_solver testbench...");
        #20;
        reset = 0;
        #10;
        start = 1;
        #10;
        start = 0;

        wait (done == 1'b1);
        #10; // allow register outputs to settle

        $display("Solver reports mu_cost=%0d, colouring=0x%05h, success=%0d", mu_cost, colouring, success);
        if (mu_cost !== 8'd23) begin
            $display("ERROR: Expected µ-cost of 23.");
            $finish_and_return(1);
        end
        if (colouring !== 18'h24924) begin
            $display("ERROR: Unexpected colouring: got 0x%05h", colouring);
            $finish_and_return(1);
        end
        if (!success) begin
            $display("ERROR: success flag not asserted.");
            $finish_and_return(1);
        end

        $display("PASS: thiele_graph_solver reached the target colouring with µ-cost 23.");
        $finish_and_return(0);
    end
endmodule
