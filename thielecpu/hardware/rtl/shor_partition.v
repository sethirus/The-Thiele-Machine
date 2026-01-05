/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * Copyright 2025 Devon Thiele
 *
 * See the LICENSE file in the repository root for full terms.
 *
 * Shor's Algorithm Period Finding Hardware Module
 * 
 * This Verilog module implements period finding for Shor's algorithm
 * using the partition framework. It corresponds to:
 *
 * - Coq: coq/shor_primitives/PeriodFinding.v
 * - Python: thielecpu/shor_oracle.py, tools/verify_shor.py
 *
 * ISOMORPHISM REQUIREMENTS:
 * 1. Period computation matches Coq's period_finding_spec
 * 2. μ-cost accounting matches Python VM
 * 3. Partition structure matches BlindSighted.v
 * 4. Factorization reduction matches Shor's theorem
 *
 * PARTITION STRUCTURE:
 * - Module 0: Residue computation (a^k mod N for k = 0..max_period)
 * - Module 1: Stabilizer search (find k where a^k ≡ 1)
 * - Module 2: Factor extraction (gcd computation)
 *
 * ALGORITHM:
 * 1. Compute residues: a^0, a^1, ..., a^max_period (mod N)
 * 2. Find period: smallest r > 0 where a^r ≡ 1 (mod N)
 * 3. Verify minimality: no smaller period exists
 * 4. Extract factors: gcd(a^(r/2) ± 1, N)
 *
 * FALSIFIABILITY:
 * - If period is wrong, factorization will fail
 * - If gcd computation is wrong, factors won't multiply to N
 * - If μ-cost is wrong, isomorphism test fails
 */

module shor_period_finding #(
    parameter WIDTH = 32,            // Bit width for numbers
    parameter MAX_PERIOD = 256,      // Maximum period to search
    parameter MU_WIDTH = 16          // Width for μ-cost counter
) (
    input wire clk,
    input wire rst_n,
    input wire start,
    
    // Input parameters
    input wire [WIDTH-1:0] N,        // Number to factor
    input wire [WIDTH-1:0] a,        // Base for period finding
    
    // Partition module IDs (from Thiele VM)
    input wire [7:0] residue_module_id,
    input wire [7:0] search_module_id,
    input wire [7:0] factor_module_id,
    
    // Outputs
    output reg [WIDTH-1:0] period,           // Discovered period r
    output reg [WIDTH-1:0] factor1,          // First factor
    output reg [WIDTH-1:0] factor2,          // Second factor
    output reg [MU_WIDTH-1:0] mu_cost,       // Total μ-bits charged
    output reg period_found,                  // Period discovery succeeded
    output reg factors_found,                 // Factor extraction succeeded
    output reg valid,
    output reg busy
);

    // ========================================================================
    // STATE MACHINE
    // ========================================================================
    
    localparam IDLE = 4'd0;
    localparam CHECK_COPRIME = 4'd1;
    localparam COMPUTE_RESIDUE = 4'd2;
    localparam SEARCH_PERIOD = 4'd3;
    localparam VERIFY_PERIOD = 4'd4;
    localparam COMPUTE_HALF_POWER = 4'd5;
    localparam COMPUTE_GCD1 = 4'd6;
    localparam COMPUTE_GCD2 = 4'd7;
    localparam VERIFY_FACTORS = 4'd8;
    localparam DONE = 4'd9;
    localparam ERROR = 4'd10;
    
    reg [3:0] state, next_state;
    
    // Working registers
    reg [WIDTH-1:0] current_residue;     // a^k mod N
    reg [WIDTH-1:0] half_power;          // a^(r/2) mod N
    reg [WIDTH-1:0] gcd_a, gcd_b;        // GCD computation registers
    reg [$clog2(MAX_PERIOD)-1:0] k;      // Current exponent
    reg [WIDTH-1:0] temp_factor1, temp_factor2;
    
    // Residue memory (stores a^k mod N for k = 0..MAX_PERIOD)
    reg [WIDTH-1:0] residues [0:MAX_PERIOD-1];
    
    // State transition
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    // Next state logic
    always @(*) begin
        case (state)
            IDLE: next_state = start ? CHECK_COPRIME : IDLE;
            CHECK_COPRIME: begin
                // Check if gcd(a, N) = 1
                if (gcd_result == 1)
                    next_state = COMPUTE_RESIDUE;
                else if (gcd_result != 0 && gcd_result != N)
                    next_state = DONE;  // Lucky! Found a factor directly
                else
                    next_state = ERROR;
            end
            COMPUTE_RESIDUE: begin
                if (current_residue == 1 && k > 0)
                    next_state = VERIFY_PERIOD;
                else if (k >= MAX_PERIOD)
                    next_state = ERROR;  // Period not found within bounds
                else
                    next_state = COMPUTE_RESIDUE;
            end
            VERIFY_PERIOD: next_state = COMPUTE_HALF_POWER;
            COMPUTE_HALF_POWER: begin
                if (period[0] == 0)  // Period is even
                    next_state = COMPUTE_GCD1;
                else
                    next_state = ERROR;  // Odd period, can't extract factors
            end
            COMPUTE_GCD1: next_state = COMPUTE_GCD2;
            COMPUTE_GCD2: next_state = VERIFY_FACTORS;
            VERIFY_FACTORS: begin
                if (temp_factor1 > 1 && temp_factor1 < N &&
                    temp_factor2 > 1 && temp_factor2 < N)
                    next_state = DONE;
                else
                    next_state = ERROR;
            end
            DONE: next_state = IDLE;
            ERROR: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end
    
    // GCD result (combinational for state machine)
    reg [WIDTH-1:0] gcd_result;
    
    // Main processing logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            period <= 0;
            factor1 <= 0;
            factor2 <= 0;
            mu_cost <= 0;
            period_found <= 0;
            factors_found <= 0;
            valid <= 0;
            busy <= 0;
            current_residue <= 1;
            k <= 0;
            gcd_a <= 0;
            gcd_b <= 0;
        end else begin
            case (state)
                IDLE: begin
                    valid <= 0;
                    period_found <= 0;
                    factors_found <= 0;
                    if (start) begin
                        busy <= 1;
                        mu_cost <= 0;
                        k <= 0;
                        current_residue <= 1;  // a^0 = 1
                        residues[0] <= 1;
                        
                        // Start GCD computation for coprimality check
                        gcd_a <= a;
                        gcd_b <= N;
                    end
                end
                
                CHECK_COPRIME: begin
                    // Euclidean GCD step
                    if (gcd_b != 0) begin
                        gcd_a <= gcd_b;
                        gcd_b <= gcd_a % gcd_b;
                    end else begin
                        gcd_result <= gcd_a;
                    end
                    
                    // Charge μ-cost for GCD computation
                    mu_cost <= mu_cost + 1;
                end
                
                COMPUTE_RESIDUE: begin
                    // Compute a^(k+1) mod N = (a^k * a) mod N
                    // Using modular multiplication
                    current_residue <= (current_residue * a) % N;
                    residues[k + 1] <= (current_residue * a) % N;
                    k <= k + 1;
                    
                    // Charge μ-cost: fixed cost per modular multiplication
                    // (log2(N) is approximately WIDTH bits)
                    mu_cost <= mu_cost + WIDTH;
                end
                
                VERIFY_PERIOD: begin
                    // Period found: r = k (smallest k > 0 where a^k ≡ 1)
                    period <= k;
                    period_found <= 1;
                    
                    // Charge μ-cost for period verification
                    mu_cost <= mu_cost + 8;
                end
                
                COMPUTE_HALF_POWER: begin
                    // Compute a^(r/2) mod N
                    // Use stored residue
                    half_power <= residues[period >> 1];
                    
                    // Charge μ-cost
                    mu_cost <= mu_cost + 4;
                end
                
                COMPUTE_GCD1: begin
                    // Compute gcd(a^(r/2) - 1, N)
                    // Using Euclidean algorithm
                    gcd_a <= (half_power > 0) ? (half_power - 1) : 0;
                    gcd_b <= N;
                    
                    // Iterative GCD (simplified - would need multiple cycles)
                    if (gcd_b != 0) begin
                        temp_factor1 <= gcd_euclidean(gcd_a, gcd_b);
                    end
                    
                    // Charge μ-cost (fixed per GCD operation)
                    mu_cost <= mu_cost + WIDTH;
                end
                
                COMPUTE_GCD2: begin
                    // Compute gcd(a^(r/2) + 1, N)
                    gcd_a <= half_power + 1;
                    gcd_b <= N;
                    
                    // Iterative GCD (simplified)
                    if (gcd_b != 0) begin
                        temp_factor2 <= gcd_euclidean(gcd_a, gcd_b);
                    end
                    
                    // Charge μ-cost (fixed per GCD operation)
                    mu_cost <= mu_cost + WIDTH;
                end
                
                VERIFY_FACTORS: begin
                    // Verify factors multiply to N
                    factor1 <= temp_factor1;
                    factor2 <= temp_factor2;
                    
                    if (temp_factor1 * temp_factor2 == N ||
                        temp_factor1 == N / temp_factor2) begin
                        factors_found <= 1;
                    end else if (temp_factor1 > 1 && temp_factor1 < N) begin
                        // temp_factor1 is valid, compute other factor
                        factor1 <= temp_factor1;
                        factor2 <= N / temp_factor1;
                        factors_found <= 1;
                    end else if (temp_factor2 > 1 && temp_factor2 < N) begin
                        // temp_factor2 is valid, compute other factor
                        factor1 <= temp_factor2;
                        factor2 <= N / temp_factor2;
                        factors_found <= 1;
                    end
                    
                    // Charge μ-cost for verification
                    mu_cost <= mu_cost + 4;
                end
                
                DONE: begin
                    valid <= 1;
                    busy <= 0;
                end
                
                ERROR: begin
                    valid <= 1;
                    busy <= 0;
                    // Leave period_found and factors_found as false
                end
            endcase
        end
    end
    
    // ========================================================================
    // GCD FUNCTION (Euclidean algorithm)
    // ========================================================================
    
    function [WIDTH-1:0] gcd_euclidean;
        input [WIDTH-1:0] x, y;
        reg [WIDTH-1:0] temp_x, temp_y, temp;
        begin
            temp_x = x;
            temp_y = y;
            while (temp_y != 0) begin
                temp = temp_y;
                temp_y = temp_x % temp_y;
                temp_x = temp;
            end
            gcd_euclidean = temp_x;
        end
    endfunction

endmodule


/*
 * Shor Partition Controller
 * 
 * Manages partition structure for Shor's algorithm execution,
 * corresponding to the Thiele VM's partition operations.
 */

module shor_partition_controller #(
    parameter NUM_PARTITIONS = 8,
    parameter WIDTH = 32
) (
    input wire clk,
    input wire rst_n,
    
    // Partition operations
    input wire pnew_enable,
    input wire [WIDTH-1:0] pnew_region,
    input wire pdiscover_enable,
    
    // Problem parameters
    input wire [WIDTH-1:0] N,
    
    // Partition state (flattened for yosys compatibility)
    output reg [NUM_PARTITIONS*WIDTH-1:0] partitions_flat,
    output reg [7:0] num_modules,
    output reg [7:0] next_module_id,
    output reg discovery_complete,
    output reg is_structured  // STRUCTURED or CHAOTIC classification
);

    // Discovery state
    localparam DISC_IDLE = 2'd0;
    localparam DISC_ANALYZE = 2'd1;
    localparam DISC_CLASSIFY = 2'd2;
    localparam DISC_DONE = 2'd3;
    
    reg [1:0] disc_state;
    integer i;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num_modules <= 0;
            next_module_id <= 0;
            discovery_complete <= 0;
            is_structured <= 1;  // Period finding is structured by default
            disc_state <= DISC_IDLE;
            partitions_flat <= 0;
        end else begin
            if (pnew_enable && num_modules < NUM_PARTITIONS) begin
                partitions_flat[num_modules*WIDTH +: WIDTH] <= pnew_region;
                num_modules <= num_modules + 1;
                next_module_id <= next_module_id + 1;
            end
            
            // Partition discovery for Shor's algorithm
            if (pdiscover_enable) begin
                case (disc_state)
                    DISC_IDLE: begin
                        disc_state <= DISC_ANALYZE;
                        discovery_complete <= 0;
                    end
                    
                    DISC_ANALYZE: begin
                        // Shor's algorithm has natural partition structure:
                        // - Residue computation is parallelizable
                        // - Period search is sequential
                        // - GCD computation is independent
                        disc_state <= DISC_CLASSIFY;
                    end
                    
                    DISC_CLASSIFY: begin
                        // Period finding problems are STRUCTURED
                        // because they have clear mathematical structure
                        is_structured <= 1;
                        disc_state <= DISC_DONE;
                    end
                    
                    DISC_DONE: begin
                        discovery_complete <= 1;
                        disc_state <= DISC_IDLE;
                    end
                endcase
            end
        end
    end

endmodule


/*
 * ARCHITECTURAL NOTES:
 *
 * This Verilog implementation corresponds to:
 *
 * 1. Coq (PeriodFinding.v):
 *    - period_finding_spec : Period finding specification
 *    - shor_reduction : Factor extraction theorem
 *    - period_finding_polynomial : Complexity bound
 *
 * 2. Python:
 *    - thielecpu/shor_oracle.py : find_period_with_claims()
 *    - tools/verify_shor.py : shor_factorize()
 *    - tests/test_shor_isomorphism.py : Verification tests
 *
 * 3. Partition Framework:
 *    - Module 0: Residue computation
 *    - Module 1: Period search
 *    - Module 2: Factor extraction
 *    - Uses same IDs as BlindSighted.v
 *
 * COMPLEXITY:
 *    - Classical: O(√N) trial division
 *    - Quantum: O((log N)³) via QFT
 *    - This module: O(N × log N) modular exponentiations
 *    - μ-cost: ~(period × log N) bits
 *
 * SYNTHESIS NOTES (for yosys):
 *
 * yosys -p "read_verilog shor_partition.v; synth -top shor_period_finding; write_json shor_period_finding.json"
 *
 * Expected resources:
 * - ~2000 LUTs for arithmetic and control
 * - ~500 FFs for state
 * - ~8KB BRAM for residue storage (256 × 32 bits)
 */
