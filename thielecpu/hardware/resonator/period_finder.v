// period_finder.v -- The Resonator hardware period discovery module
//
// This module embodies the "resonator" concept from the Thiele Machine
// project.  Instead of scanning through exponents sequentially, it keeps a
// physical claim for the period as state, evaluates that claim with a dense
// combinational consistency network, and perturbs the claim using modular
// structure feedback.  The combinational block is intentionally rich: it
// carries out modular exponentiation, searches the divisor lattice of the
// candidate, and analyses the resulting residues to decide how the claim
// should evolve.  The observable side effect is that most of the reasoning
// happens in space (gates) rather than time (clock cycles).

`default_nettype none

module period_finder #(
    parameter WIDTH = 4,
    parameter MAX_PERIOD = (1 << WIDTH) - 1
) (
    input  wire                 clk,
    input  wire                 reset_n,
    input  wire                 start,
    input  wire [WIDTH-1:0]     modulus,
    input  wire [WIDTH-1:0]     base,
    output reg                  done,
    output reg  [WIDTH-1:0]     period,
    output reg  [WIDTH-1:0]     r_candidate,
    output reg  [WIDTH-1:0]     mu_counter,
    output reg                  stuck
);

    localparam STATE_IDLE   = 2'b00;
    localparam STATE_CHECK  = 2'b01;
    localparam STATE_UPDATE = 2'b10;

    reg [1:0] state;
    reg [WIDTH-1:0] next_candidate;
    reg [WIDTH-1:0] residual_snapshot;
    reg [WIDTH-1:0] baseline_snapshot;
    reg is_consistent;
    reg [WIDTH-1:0] feedback_step;

    // ---------------------------------------------------------------------
    // Arithmetic helpers
    // ---------------------------------------------------------------------

    function [WIDTH-1:0] modular_reduce;
        input [WIDTH-1:0] value;
        input [WIDTH-1:0] mod;
        reg [WIDTH-1:0] reduced;
        integer iter;
        begin
            if (mod == 0) begin
                modular_reduce = value;
            end else begin
                reduced = value;
                for (iter = 0; iter < WIDTH; iter = iter + 1) begin
                    if (reduced >= mod) begin
                        reduced = reduced - mod;
                    end
                end
                modular_reduce = reduced;
            end
        end
    endfunction

    function [WIDTH-1:0] modular_add;
        input [WIDTH-1:0] lhs;
        input [WIDTH-1:0] rhs;
        input [WIDTH-1:0] mod;
        reg [WIDTH:0] acc;
        integer iter;
        begin
            acc = lhs + rhs;
            if (mod == 0) begin
                modular_add = acc[WIDTH-1:0];
            end else begin
                for (iter = 0; iter < WIDTH; iter = iter + 1) begin
                    if (acc >= mod) begin
                        acc = acc - mod;
                    end
                end
                modular_add = acc[WIDTH-1:0];
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
                        result_local = modular_add(result_local, a_local, mod);
                    end
                    b_local = b_local >> 1;
                    a_local = a_local << 1;
                    if (a_local >= mod) begin
                        a_local = modular_reduce(a_local, mod);
                    end
                end
                modular_mul = result_local;
            end
        end
    endfunction

    function [WIDTH-1:0] modular_pow;
        input [WIDTH-1:0] base_value;
        input [WIDTH-1:0] exponent_value;
        input [WIDTH-1:0] mod;
        reg [WIDTH-1:0] result_local;
        reg [WIDTH-1:0] pow_acc;
        integer bit_index;
        begin
            if (mod == 0) begin
                result_local = {{(WIDTH-1){1'b0}}, 1'b1};
                pow_acc = base_value;
                for (bit_index = 0; bit_index < WIDTH; bit_index = bit_index + 1) begin
                    if (exponent_value[bit_index]) begin
                        result_local = result_local * pow_acc;
                    end
                    pow_acc = pow_acc * pow_acc;
                end
                modular_pow = result_local;
            end else begin
                result_local = modular_reduce(1, mod);
                pow_acc = modular_reduce(base_value, mod);
                for (bit_index = 0; bit_index < WIDTH; bit_index = bit_index + 1) begin
                    if (exponent_value[bit_index]) begin
                        result_local = modular_mul(result_local, pow_acc, mod);
                    end
                    pow_acc = modular_mul(pow_acc, pow_acc, mod);
                end
                modular_pow = result_local;
            end
        end
    endfunction

    function [WIDTH-1:0] compute_gcd;
        input [WIDTH-1:0] x;
        input [WIDTH-1:0] y;
        reg [WIDTH-1:0] a_local;
        reg [WIDTH-1:0] b_local;
        integer iter;
        begin
            a_local = x;
            b_local = y;
            if (a_local == 0) begin
                compute_gcd = b_local;
            end else if (b_local == 0) begin
                compute_gcd = a_local;
            end else begin
                for (iter = 0; iter < WIDTH * 4; iter = iter + 1) begin
                    if (a_local == b_local) begin
                        iter = WIDTH * 4;
                    end else if (a_local > b_local) begin
                        a_local = a_local - b_local;
                    end else begin
                        b_local = b_local - a_local;
                    end
                end
                if (a_local == b_local) begin
                    compute_gcd = a_local;
                end else if (a_local == 0) begin
                    compute_gcd = b_local;
                end else if (b_local == 0) begin
                    compute_gcd = a_local;
                end else begin
                    compute_gcd = a_local;
                end
            end
        end
    endfunction

    function automatic [WIDTH-1:0] one_mod;
        input [WIDTH-1:0] mod;
        begin
            if (mod == 0) begin
                one_mod = 1;
            end else if (mod == {{(WIDTH-1){1'b0}}, 1'b1}) begin
                one_mod = {WIDTH{1'b0}};
            end else begin
                one_mod = {{(WIDTH-1){1'b0}}, 1'b1};
            end
        end
    endfunction

    function automatic [0:0] reg_minimal;
        input [WIDTH-1:0] candidate_value;
        input [WIDTH-1:0] base_value;
        input [WIDTH-1:0] mod;
        reg valid_flag;
        reg [WIDTH-1:0] quotient_local;
        reg divisible_three;
        reg [WIDTH-1:0] quotient_three;
        reg divisible_five;
        reg [WIDTH-1:0] quotient_five;
        begin
            if (candidate_value <= 1) begin
                reg_minimal = 1'b0;
            end else begin
                valid_flag = 1'b1;
                quotient_local = candidate_value >> 1;
                if ((candidate_value[0] == 1'b0) && (candidate_value > 4'd2)) begin
                    if (modular_pow(base_value, quotient_local, mod) == one_mod(mod)) begin
                        valid_flag = 1'b0;
                    end
                end
                divisible_three = 1'b0;
                quotient_three = {WIDTH{1'b0}};
                case (candidate_value)
                    4'd3: begin divisible_three = 1'b1; quotient_three = 4'd1; end
                    4'd6: begin divisible_three = 1'b1; quotient_three = 4'd2; end
                    4'd9: begin divisible_three = 1'b1; quotient_three = 4'd3; end
                    4'd12: begin divisible_three = 1'b1; quotient_three = 4'd4; end
                    4'd15: begin divisible_three = 1'b1; quotient_three = 4'd5; end
                    default: begin divisible_three = 1'b0; quotient_three = {WIDTH{1'b0}}; end
                endcase
                if (divisible_three && (candidate_value > 4'd3)) begin
                    if (modular_pow(base_value, quotient_three, mod) == one_mod(mod)) begin
                        valid_flag = 1'b0;
                    end
                end
                quotient_local = candidate_value >> 2;
                if ((candidate_value[1:0] == 2'b00) && (candidate_value > 4'd4)) begin
                    if (modular_pow(base_value, quotient_local, mod) == one_mod(mod)) begin
                        valid_flag = 1'b0;
                    end
                end
                divisible_five = 1'b0;
                quotient_five = {WIDTH{1'b0}};
                case (candidate_value)
                    4'd5: begin divisible_five = 1'b1; quotient_five = 4'd1; end
                    4'd10: begin divisible_five = 1'b1; quotient_five = 4'd2; end
                    4'd15: begin divisible_five = 1'b1; quotient_five = 4'd3; end
                    default: begin divisible_five = 1'b0; quotient_five = {WIDTH{1'b0}}; end
                endcase
                if (divisible_five && (candidate_value > 4'd5)) begin
                    if (modular_pow(base_value, quotient_five, mod) == one_mod(mod)) begin
                        valid_flag = 1'b0;
                    end
                end
                reg_minimal = valid_flag;
            end
        end
    endfunction

    function automatic [0:0] reg_consistency;
        input [WIDTH-1:0] candidate_value;
        input [WIDTH-1:0] base_value;
        input [WIDTH-1:0] mod;
        reg [WIDTH-1:0] residual_value;
        reg [WIDTH-1:0] baseline_value;
        begin
            residual_value = modular_pow(base_value, candidate_value, mod);
            baseline_value = modular_pow(base_value, {WIDTH{1'b0}}, mod);
            reg_consistency = (candidate_value != 0) &&
                              (residual_value == baseline_value) &&
                              reg_minimal(candidate_value, base_value, mod);
        end
    endfunction

    function automatic [WIDTH-1:0] compute_feedback_step;
        input [WIDTH-1:0] candidate_value;
        input [WIDTH-1:0] base_value;
        input [WIDTH-1:0] mod;
        reg [WIDTH-1:0] residual_value;
        reg [WIDTH-1:0] forward_value;
        reg [WIDTH-1:0] delta_forward;
        reg [WIDTH-1:0] gcd_forward;
        reg [WIDTH-1:0] blend;
        begin
            residual_value = modular_pow(base_value, candidate_value, mod);
            forward_value  = modular_mul(residual_value, modular_reduce(base_value, mod), mod);

            delta_forward = (forward_value > residual_value) ?
                              (forward_value - residual_value) :
                              (residual_value - forward_value);

            gcd_forward  = compute_gcd(delta_forward, mod);

            blend = modular_add(gcd_forward, candidate_value, mod);
            if (blend == 0) begin
                if (candidate_value[0]) begin
                    compute_feedback_step = 2;
                end else begin
                    compute_feedback_step = 1;
                end
            end else begin
                compute_feedback_step = blend;
            end
        end
    endfunction

    // ---------------------------------------------------------------------
    // Control logic
    // ---------------------------------------------------------------------
    always @(*) begin
        residual_snapshot = modular_pow(base, r_candidate, modulus);
        baseline_snapshot = modular_pow(base, {WIDTH{1'b0}}, modulus);
        is_consistent = reg_consistency(r_candidate, base, modulus);
        feedback_step = compute_feedback_step(r_candidate, base, modulus);
        if (feedback_step == 0) begin
            next_candidate = r_candidate + 1'b1;
        end else begin
            next_candidate = r_candidate + feedback_step;
        end
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= STATE_IDLE;
            done <= 1'b0;
            period <= {WIDTH{1'b0}};
            r_candidate <= {{(WIDTH-1){1'b0}}, 1'b1};
            mu_counter <= {WIDTH{1'b0}};
            stuck <= 1'b0;
        end else begin
            case (state)
                STATE_IDLE: begin
                    done <= 1'b0;
                    stuck <= 1'b0;
                    if (start) begin
                        r_candidate <= {{(WIDTH-1){1'b0}}, 1'b1};
                        mu_counter <= {WIDTH{1'b0}};
                        state <= STATE_CHECK;
                    end
                end
                STATE_CHECK: begin
                    if (is_consistent) begin
                        done <= 1'b1;
                        period <= r_candidate;
                        state <= STATE_IDLE;
                    end else begin
                        state <= STATE_UPDATE;
                    end
                end
                STATE_UPDATE: begin
                    mu_counter <= mu_counter + 1'b1;
                    if (next_candidate == r_candidate || next_candidate == {WIDTH{1'b0}}) begin
                        stuck <= 1'b1;
                        state <= STATE_IDLE;
                    end else if (next_candidate > MAX_PERIOD) begin
                        r_candidate <= {{(WIDTH-1){1'b0}}, 1'b1};
                        state <= STATE_CHECK;
                    end else begin
                        r_candidate <= next_candidate;
                        state <= STATE_CHECK;
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
