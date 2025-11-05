// Classical brute-force graph colouring solver for the triadic_cascade graph.
// The module enumerates all 3^9 assignments for the nine vertices using a
// sequential base-3 counter. Once a valid colouring is discovered the packed
// 18-bit assignment (2 bits per vertex) is latched onto the output bus.

module classical_solver (
    input  wire        clk,
    input  wire        reset,
    input  wire        start,
    output reg         done,
    output reg         success,
    output reg [17:0]  colouring
);

    localparam integer NODES = 9;

    reg [1:0] digits [0:NODES-1];
    reg [1:0] digits_next [0:NODES-1];
    reg       overflow_next;
    reg       candidate_valid;

    integer i;

    localparam [1:0] RED   = 2'd0;
    localparam [1:0] GREEN = 2'd1;
    localparam [1:0] BLUE  = 2'd2;

    reg [1:0] state;
    localparam [1:0] IDLE     = 2'd0;
    localparam [1:0] SEARCH   = 2'd1;
    localparam [1:0] FINISHED = 2'd2;

    // Increment the base-3 digit vector.
    always @* begin
        overflow_next = 1'b1;
        for (i = 0; i < NODES; i = i + 1) begin
            digits_next[i] = digits[i];
        end
        for (i = 0; i < NODES; i = i + 1) begin
            if (overflow_next) begin
                if (digits[i] == BLUE) begin
                    digits_next[i] = RED;
                end else begin
                    digits_next[i] = digits[i] + 2'd1;
                    overflow_next = 1'b0;
                end
            end
        end
    end

    // Evaluate the candidate assignment against graph constraints.
    always @* begin
        candidate_valid = 1'b1;

        if (digits[0] == digits[1]) candidate_valid = 1'b0;
        if (digits[0] == digits[2]) candidate_valid = 1'b0;
        if (digits[0] == digits[4]) candidate_valid = 1'b0;
        if (digits[0] == digits[5]) candidate_valid = 1'b0;

        if (digits[1] == digits[2]) candidate_valid = 1'b0;
        if (digits[1] == digits[3]) candidate_valid = 1'b0;
        if (digits[1] == digits[5]) candidate_valid = 1'b0;

        if (digits[2] == digits[3]) candidate_valid = 1'b0;
        if (digits[2] == digits[4]) candidate_valid = 1'b0;

        if (digits[3] == digits[7]) candidate_valid = 1'b0;
        if (digits[3] == digits[8]) candidate_valid = 1'b0;

        if (digits[4] == digits[6]) candidate_valid = 1'b0;
        if (digits[4] == digits[8]) candidate_valid = 1'b0;

        if (digits[5] == digits[6]) candidate_valid = 1'b0;
        if (digits[5] == digits[7]) candidate_valid = 1'b0;

        if (digits[6] == digits[4]) candidate_valid = 1'b0;
        if (digits[6] == digits[5]) candidate_valid = 1'b0;

        if (digits[7] == digits[3]) candidate_valid = 1'b0;
        if (digits[7] == digits[5]) candidate_valid = 1'b0;

        if (digits[8] == digits[3]) candidate_valid = 1'b0;
        if (digits[8] == digits[4]) candidate_valid = 1'b0;
    end

    // Sequential search controller.
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state    <= IDLE;
            done     <= 1'b0;
            success  <= 1'b0;
            colouring <= 18'd0;
            for (i = 0; i < NODES; i = i + 1) begin
                digits[i] <= RED;
            end
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        done    <= 1'b0;
                        success <= 1'b0;
                        colouring <= 18'd0;
                        for (i = 0; i < NODES; i = i + 1) begin
                            digits[i] <= RED;
                        end
                        state <= SEARCH;
                    end
                end
                SEARCH: begin
                    if (candidate_valid) begin
                        done    <= 1'b1;
                        success <= 1'b1;
                        for (i = 0; i < NODES; i = i + 1) begin
                            colouring[(i*2)+1 -: 2] <= digits[i];
                        end
                        state <= FINISHED;
                    end else if (overflow_next) begin
                        done    <= 1'b1;
                        success <= 1'b0;
                        state   <= FINISHED;
                    end else begin
                        for (i = 0; i < NODES; i = i + 1) begin
                            digits[i] <= digits_next[i];
                        end
                    end
                end
                FINISHED: begin
                    if (!start) begin
                        state <= IDLE;
                    end
                end
                default: state <= IDLE;
            endcase
        end
    end

endmodule
