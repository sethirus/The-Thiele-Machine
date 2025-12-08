// crypto_receipt_controller.v
// Cryptographic Receipt Controller for Thiele Machine
// 
// Top-level controller integrating:
// - state_serializer (State -> bytes)
// - sha256_interface (bytes -> hash)
// - Hash chain management (H_t = SHA256(H_{t-1} || ΔState || μ_op))
// - CPU pipeline freeze during multi-cycle operation
// 
// Implements cryptographic binding per Phase 1-3 Coq proofs

module crypto_receipt_controller #(
    parameter MAX_MODULES = 16,
    parameter MAX_VARS_PER_MODULE = 32,
    parameter MU_HASH_COST = 100  // μ-cost of hash operation (cycles)
) (
    input wire clk,
    input wire rst_n,
    
    // Control interface
    input wire compute_hash,       // CPU requests state hash
    output reg hash_ready,         // Hash computation complete
    output reg cpu_freeze,         // Freeze CPU pipeline
    
    // State inputs (from CPU)
    input wire [31:0] num_modules,
    input wire [31:0] module_ids [0:MAX_MODULES-1],
    input wire [31:0] var_counts [0:MAX_MODULES-1],
    input wire [31:0] variables [0:MAX_MODULES-1][0:MAX_VARS_PER_MODULE-1],
    input wire signed [63:0] mu_ledger,
    input wire [31:0] pc,
    input wire halted,
    input wire [31:0] result,
    input wire [255:0] program_hash,
    
    // Hash chain
    input wire [255:0] prev_hash_in,
    input wire use_chain,
    output reg [255:0] curr_hash_out,
    
    // μ-cost tracking
    output reg [31:0] hash_mu_cost
);

    // Internal signals
    wire serializer_ready;
    wire serializer_valid;
    reg serializer_start;
    wire [7:0] serializer_byte;
    wire serializer_byte_valid;
    reg serializer_byte_ready;
    
    wire sha_ready;
    wire sha_valid;
    reg sha_start;
    wire [255:0] sha_hash_out;
    
    // State machine
    localparam IDLE = 0;
    localparam SERIALIZE = 1;
    localparam HASH = 2;
    localparam DONE = 3;
    
    reg [1:0] state;
    reg [31:0] cycle_counter;
    
    // Instantiate state serializer
    state_serializer #(
        .MAX_MODULES(MAX_MODULES),
        .MAX_VARS_PER_MODULE(MAX_VARS_PER_MODULE)
    ) serializer (
        .clk(clk),
        .rst_n(rst_n),
        .start(serializer_start),
        .ready(serializer_ready),
        .valid(serializer_valid),
        .num_modules(num_modules),
        .module_ids(module_ids),
        .var_counts(var_counts),
        .variables(variables),
        .mu_ledger(mu_ledger),
        .pc(pc),
        .halted(halted),
        .result(result),
        .program_hash(program_hash),
        .out_byte(serializer_byte),
        .out_byte_valid(serializer_byte_valid),
        .out_byte_ready(serializer_byte_ready)
    );
    
    // Instantiate SHA-256 interface
    sha256_interface sha_if (
        .clk(clk),
        .rst_n(rst_n),
        .start(sha_start),
        .ready(sha_ready),
        .valid(sha_valid),
        .in_byte(serializer_byte),
        .in_byte_valid(serializer_byte_valid),
        .in_byte_ready(serializer_byte_ready),
        .hash_out(sha_hash_out),
        .prev_hash(prev_hash_in),
        .use_chain(use_chain)
    );
    
    // Main state machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            hash_ready <= 1'b0;
            cpu_freeze <= 1'b0;
            serializer_start <= 1'b0;
            sha_start <= 1'b0;
            curr_hash_out <= 256'h0;
            hash_mu_cost <= 0;
            cycle_counter <= 0;
        end else begin
            case (state)
                IDLE: begin
                    hash_ready <= 1'b0;
                    cpu_freeze <= 1'b0;
                    serializer_start <= 1'b0;
                    sha_start <= 1'b0;
                    cycle_counter <= 0;
                    
                    if (compute_hash) begin
                        // Start hash computation
                        cpu_freeze <= 1'b1;  // Freeze CPU pipeline
                        serializer_start <= 1'b1;
                        state <= SERIALIZE;
                    end
                end
                
                SERIALIZE: begin
                    serializer_start <= 1'b0;
                    cycle_counter <= cycle_counter + 1;
                    
                    if (serializer_valid) begin
                        // Serialization complete, start hashing
                        sha_start <= 1'b1;
                        state <= HASH;
                    end
                end
                
                HASH: begin
                    sha_start <= 1'b0;
                    cycle_counter <= cycle_counter + 1;
                    
                    if (sha_valid) begin
                        // Hash computation complete
                        curr_hash_out <= sha_hash_out;
                        hash_mu_cost <= cycle_counter;  // Actual cycles used
                        state <= DONE;
                    end
                end
                
                DONE: begin
                    hash_ready <= 1'b1;
                    cpu_freeze <= 1'b0;  // Unfreeze CPU pipeline
                    state <= IDLE;
                end
            endcase
        end
    end
    
    // μ-cost assertion: verify actual cost matches expected
    always @(posedge clk) begin
        if (state == DONE && hash_mu_cost > MU_HASH_COST + 20) begin
            // Warning: hash took significantly longer than expected
            $display("WARNING: Hash computation took %d cycles, expected ~%d", 
                     hash_mu_cost, MU_HASH_COST);
        end
    end

endmodule
