// classical_period_finder.v -- reference sequential period scanner
//
// This module represents the "classical" approach used for comparison with
// the resonator.  It simply iterates the modular exponentiation one power at a
// time until the multiplicative orbit returns to the baseline.  The logic is
// compact because the heavy lifting is pushed into time rather than space.

`default_nettype none

module classical_period_finder #(
    parameter WIDTH = 8
) (
    input  wire             clk,
    input  wire             reset_n,
    input  wire             start,
    input  wire [WIDTH-1:0] modulus,
    input  wire [WIDTH-1:0] base,
    output reg              done,
    output reg  [WIDTH-1:0] period,
    output reg  [WIDTH-1:0] mu_counter
);

    localparam STATE_IDLE  = 2'b00;
    localparam STATE_RUN   = 2'b01;
    localparam STATE_DONE  = 2'b10;

    reg [1:0] state;
    reg [WIDTH-1:0] current_value;
    reg [WIDTH-1:0] baseline;
    reg [WIDTH-1:0] base_mod;

    function [WIDTH-1:0] modular_reduce;
        input [WIDTH-1:0] value;
        input [WIDTH-1:0] mod;
        begin
            if (mod == 0) begin
                modular_reduce = value;
            end else if (value >= mod) begin
                modular_reduce = value % mod;
            end else begin
                modular_reduce = value;
            end
        end
    endfunction

    function [WIDTH-1:0] modular_mul;
        input [WIDTH-1:0] lhs;
        input [WIDTH-1:0] rhs;
        input [WIDTH-1:0] mod;
        reg [WIDTH-1:0] a_local;
        reg [WIDTH-1:0] b_local;
        reg [WIDTH-1:0] result_local;
        integer i;
        begin
            if (mod == 0) begin
                modular_mul = lhs * rhs;
            end else begin
                a_local = modular_reduce(lhs, mod);
                b_local = rhs;
                result_local = {WIDTH{1'b0}};
                for (i = 0; i < WIDTH; i = i + 1) begin
                    if (b_local[0]) begin
                        result_local = result_local + a_local;
                        if (result_local >= mod) begin
                            result_local = result_local - mod;
                        end
                    end
                    b_local = b_local >> 1;
                    a_local = a_local << 1;
                    if (a_local >= mod) begin
                        a_local = a_local - mod;
                    end
                end
                modular_mul = result_local;
            end
        end
    endfunction

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            period <= {WIDTH{1'b0}};
            mu_counter <= {WIDTH{1'b0}};
            current_value <= {WIDTH{1'b0}};
            baseline <= {WIDTH{1'b0}};
            base_mod <= {WIDTH{1'b0}};
        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    if (start) begin
                        base_mod <= modular_reduce(base, modulus);
                        baseline <= modular_reduce(1, modulus);
                        current_value <= modular_reduce(base, modulus);
                        period <= {{(WIDTH-1){1'b0}}, 1'b1};
                        mu_counter <= {WIDTH{1'b0}};
                        state <= STATE_RUN;
                    end
                end
                STATE_RUN: begin
                    if (current_value == baseline || modulus == 1) begin
                        done <= 1'b1;
                        state <= STATE_DONE;
                    end else begin
                        current_value <= modular_mul(current_value, base_mod, modulus);
                        period <= period + 1'b1;
                        mu_counter <= mu_counter + 1'b1;
                    end
                end
                STATE_DONE: begin
                    if (!start) begin
                        state <= STATE_IDLE;
                    end
                end
                default: begin
                    state <= STATE_IDLE;
                end
            endcase
        end
    end

endmodule

`default_nettype wire
