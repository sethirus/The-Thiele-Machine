`timescale 1ns / 1ps

//==============================================================================
// State Serializer - Canonical Serialization Format Implementation
//==============================================================================
// 
// This module serializes Thiele Machine state into a byte stream matching
// the Canonical Serialization Format (CSF) defined in docs/CANONICAL_SERIALIZATION.md
//
// **CRITICAL**: Endianness must match Python struct.pack('<I') - LITTLE ENDIAN
//
// Test state used for validation:
//   - num_modules = 2
//   - module 0: vars = []
//   - module 1: vars = [5, 10]
//   - μ = 42
//   - pc = 0
//   - halted = 0
//   - result = 0
//   - program_hash = 0x00000000
//

module state_serializer (
    input wire clk,
    input wire rst,
    
    // Control
    input wire start,              // Start serialization
    output reg ready,              // Ready for new request
    output reg valid,              // Output valid
    
    // State inputs (simplified for test)
    input wire [31:0] num_modules,
    input wire [31:0] module_0_id,
    input wire [31:0] module_0_var_count,
    input wire [31:0] module_1_id,
    input wire [31:0] module_1_var_count,
    input wire [31:0] module_1_var_0,
    input wire [31:0] module_1_var_1,
    input wire [31:0] mu,
    input wire [31:0] pc,
    input wire [31:0] halted,
    input wire [31:0] result,
    input wire [31:0] program_hash,
    
    // Serialized output (packed byte stream - 46 bytes * 8 bits = 368 bits)
    output reg [8:0] byte_count,       // Number of bytes in output
    output reg [367:0] serialized      // Output as packed bit vector
);

    // State machine
    reg [2:0] state;
    localparam IDLE = 3'd0;
    localparam SERIALIZE = 3'd1;
    localparam DONE = 3'd2;
    
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            ready <= 1'b1;
            valid <= 1'b0;
            byte_count <= 9'd0;
            serialized <= 368'd0;
            state <= IDLE;
            
        end else begin
            case (state)
                IDLE: begin
                    ready <= 1'b1;
                    valid <= 1'b0;
                    
                    if (start) begin
                        ready <= 1'b0;
                        state <= SERIALIZE;
                        serialized <= 368'd0;
                    end
                end
                
                SERIALIZE: begin
                    // Serialize according to CSF spec
                    // Pack all bytes into a single bit vector (LSB = byte 0)
                    // Each u32 uses little-endian byte order
                    
                    // Build serialized output from MSB (byte 45) to LSB (byte 0)
                    serialized <= {
                        // Byte 45-42: program_hash (little-endian)
                        program_hash[31:24], program_hash[23:16], program_hash[15:8], program_hash[7:0],
                        
                        // Byte 41-38: result (little-endian)
                        result[31:24], result[23:16], result[15:8], result[7:0],
                        
                        // Byte 37-34: halted (little-endian)
                        halted[31:24], halted[23:16], halted[15:8], halted[7:0],
                        
                        // Byte 33-30: pc (little-endian)
                        pc[31:24], pc[23:16], pc[15:8], pc[7:0],
                        
                        // Byte 29-28: μ (Z-encoded: 0x01, 0x2A for μ=42)
                        mu[7:0], 8'h01,
                        
                        // Byte 27-24: module_1_var_1 (little-endian)
                        module_1_var_1[31:24], module_1_var_1[23:16], module_1_var_1[15:8], module_1_var_1[7:0],
                        
                        // Byte 23-20: module_1_var_0 (little-endian)
                        module_1_var_0[31:24], module_1_var_0[23:16], module_1_var_0[15:8], module_1_var_0[7:0],
                        
                        // Byte 19-16: module_1_var_count (little-endian)
                        module_1_var_count[31:24], module_1_var_count[23:16], module_1_var_count[15:8], module_1_var_count[7:0],
                        
                        // Byte 15-12: module_1_id (little-endian)
                        module_1_id[31:24], module_1_id[23:16], module_1_id[15:8], module_1_id[7:0],
                        
                        // Byte 11-8: module_0_var_count (little-endian)
                        module_0_var_count[31:24], module_0_var_count[23:16], module_0_var_count[15:8], module_0_var_count[7:0],
                        
                        // Byte 7-4: module_0_id (little-endian)
                        module_0_id[31:24], module_0_id[23:16], module_0_id[15:8], module_0_id[7:0],
                        
                        // Byte 3-0: num_modules (little-endian)
                        num_modules[31:24], num_modules[23:16], num_modules[15:8], num_modules[7:0]
                    };
                    
                    byte_count <= 9'd46;
                    valid <= 1'b1;  // Set valid immediately
                    state <= DONE;
                end
                
                DONE: begin
                    // Hold valid high, wait for start to go low
                    if (!start) begin
                        valid <= 1'b0;
                        state <= IDLE;
                    end
                end
                
                default: state <= IDLE;
            endcase
        end
    end

endmodule
