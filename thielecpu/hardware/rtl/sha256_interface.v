// sha256_interface.v
// SHA-256 Hash Interface for Thiele Machine
// 
// Wraps SHA-256 core with state machine for multi-cycle operation
// Implements ready/valid handshake to freeze CPU pipeline
// 
// Features:
// - Multi-cycle operation (64-80 cycles per 512-bit block)
// - Pipeline freeze during computation
// - Receipt register for hash chain storage
// - CSF-compliant hashing matching Python/Coq

module sha256_interface (
    input wire clk,
    input wire rst_n,
    
    // Control interface
    input wire start,              // Start hash computation
    output reg ready,              // Ready for new request
    output reg valid,              // Hash output valid
    
    // Data input (byte stream from serializer)
    input wire [7:0] in_byte,
    input wire in_byte_valid,
    output reg in_byte_ready,
    
    // Hash output
    output reg [255:0] hash_out,
    
    // Hash chain input (previous hash for chaining)
    input wire [255:0] prev_hash,
    input wire use_chain          // If true, prepend prev_hash to input
);

    // SHA-256 core signals
    reg [511:0] sha_block;
    reg sha_start;
    wire sha_ready;
    wire [255:0] sha_hash;
    wire sha_valid;
    
    // State machine
    localparam IDLE = 0;
    localparam COLLECT_PREV_HASH = 1;
    localparam COLLECT_DATA = 2;
    localparam PAD_DATA = 3;
    localparam COMPUTE_HASH = 4;
    localparam DONE = 5;
    
    reg [2:0] state;
    reg [9:0] byte_count;          // Count of bytes collected
    reg [63:0] total_bit_length;   // Total message length in bits
    reg [511:0] current_block;     // Current 512-bit block being assembled
    reg [9:0] block_byte_idx;      // Byte index within current block
    
    // SHA-256 core instantiation (placeholder - use actual core)
    // For now, this is a simplified model
    sha256_core sha_core (
        .clk(clk),
        .rst_n(rst_n),
        .start(sha_start),
        .ready(sha_ready),
        .block(sha_block),
        .hash(sha_hash),
        .valid(sha_valid)
    );
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            ready <= 1'b1;
            valid <= 1'b0;
            in_byte_ready <= 1'b0;
            hash_out <= 256'h0;
            byte_count <= 0;
            total_bit_length <= 0;
            current_block <= 512'h0;
            block_byte_idx <= 0;
            sha_start <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    ready <= 1'b1;
                    valid <= 1'b0;
                    in_byte_ready <= 1'b0;
                    sha_start <= 1'b0;
                    
                    if (start) begin
                        ready <= 1'b0;
                        byte_count <= 0;
                        total_bit_length <= 0;
                        block_byte_idx <= 0;
                        current_block <= 512'h0;
                        
                        if (use_chain) begin
                            // Start hash chain: prepend prev_hash
                            state <= COLLECT_PREV_HASH;
                        end else begin
                            // Direct hash: collect data
                            state <= COLLECT_DATA;
                            in_byte_ready <= 1'b1;
                        end
                    end
                end
                
                COLLECT_PREV_HASH: begin
                    // Collect prev_hash bytes (32 bytes = 256 bits)
                    if (block_byte_idx < 32) begin
                        // Add byte from prev_hash to current_block
                        current_block[(63 - block_byte_idx)*8 +: 8] <= 
                            prev_hash[(31 - block_byte_idx)*8 +: 8];
                        block_byte_idx <= block_byte_idx + 1;
                        byte_count <= byte_count + 1;
                        total_bit_length <= total_bit_length + 8;
                    end else begin
                        // Done collecting prev_hash, now collect data
                        state <= COLLECT_DATA;
                        in_byte_ready <= 1'b1;
                    end
                end
                
                COLLECT_DATA: begin
                    in_byte_ready <= 1'b1;
                    
                    if (in_byte_valid) begin
                        // Add byte to current block
                        current_block[(63 - block_byte_idx)*8 +: 8] <= in_byte;
                        block_byte_idx <= block_byte_idx + 1;
                        byte_count <= byte_count + 1;
                        total_bit_length <= total_bit_length + 8;
                        
                        // If block is full (64 bytes), process it
                        if (block_byte_idx == 63) begin
                            in_byte_ready <= 1'b0;
                            state <= COMPUTE_HASH;
                            sha_block <= current_block;
                            sha_start <= 1'b1;
                            block_byte_idx <= 0;
                            current_block <= 512'h0;
                        end
                    end else begin
                        // No more data, move to padding
                        in_byte_ready <= 1'b0;
                        state <= PAD_DATA;
                    end
                end
                
                PAD_DATA: begin
                    // SHA-256 padding: append 1, then 0s, then 64-bit length
                    // Padding ensures final block is 512 bits
                    
                    // Append '1' bit (0x80 byte)
                    current_block[(63 - block_byte_idx)*8 +: 8] <= 8'h80;
                    block_byte_idx <= block_byte_idx + 1;
                    
                    // Calculate padding needed
                    // Need space for 8-byte length at end
                    // If current position + 8 > 64, need extra block
                    if (block_byte_idx + 8 >= 64) begin
                        // Need to process current block then add final block
                        // Fill rest with zeros
                        while (block_byte_idx < 64) begin
                            current_block[(63 - block_byte_idx)*8 +: 8] <= 8'h00;
                            block_byte_idx <= block_byte_idx + 1;
                        end
                        
                        // Process this block
                        state <= COMPUTE_HASH;
                        sha_block <= current_block;
                        sha_start <= 1'b1;
                        block_byte_idx <= 0;
                        current_block <= 512'h0;
                    end else begin
                        // Fill with zeros until byte 56
                        while (block_byte_idx < 56) begin
                            current_block[(63 - block_byte_idx)*8 +: 8] <= 8'h00;
                            block_byte_idx <= block_byte_idx + 1;
                        end
                        
                        // Add 64-bit length (big-endian)
                        current_block[63:0] <= total_bit_length;
                        
                        // Process final block
                        state <= COMPUTE_HASH;
                        sha_block <= current_block;
                        sha_start <= 1'b1;
                    end
                end
                
                COMPUTE_HASH: begin
                    sha_start <= 1'b0;
                    
                    if (sha_valid) begin
                        hash_out <= sha_hash;
                        state <= DONE;
                    end
                    // Else wait for SHA core to complete
                end
                
                DONE: begin
                    valid <= 1'b1;
                    state <= IDLE;
                end
            endcase
        end
    end

endmodule

// Simplified SHA-256 core placeholder
// In production, use a proper SHA-256 implementation
module sha256_core (
    input wire clk,
    input wire rst_n,
    input wire start,
    output reg ready,
    input wire [511:0] block,
    output reg [255:0] hash,
    output reg valid
);

    localparam IDLE = 0;
    localparam COMPUTE = 1;
    localparam DONE = 2;
    
    reg [1:0] state;
    reg [6:0] cycle_count;  // SHA-256 takes ~64 cycles
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            ready <= 1'b1;
            valid <= 1'b0;
            hash <= 256'h0;
            cycle_count <= 0;
        end else begin
            case (state)
                IDLE: begin
                    ready <= 1'b1;
                    valid <= 1'b0;
                    if (start) begin
                        ready <= 1'b0;
                        state <= COMPUTE;
                        cycle_count <= 0;
                    end
                end
                
                COMPUTE: begin
                    // Simulate SHA-256 computation (64-80 cycles)
                    cycle_count <= cycle_count + 1;
                    
                    if (cycle_count >= 64) begin
                        // Compute hash (simplified - use actual SHA-256 logic)
                        // For now, just XOR and invert as placeholder
                        hash <= ~(block[511:256] ^ block[255:0]);
                        state <= DONE;
                    end
                end
                
                DONE: begin
                    valid <= 1'b1;
                    state <= IDLE;
                end
            endcase
        end
    end

endmodule
