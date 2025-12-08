// state_serializer.v
// Canonical State Serialization for Thiele Machine
// Converts State to byte stream matching CSF specification
// 
// Key features:
// - Little-endian byte order (matches Python struct.pack)
// - Canonical partition ordering (sorted by construction)
// - Ready/valid handshake for multi-cycle operation
// - CSF-compliant output matching docs/CANONICAL_SERIALIZATION.md

module state_serializer #(
    parameter MAX_MODULES = 16,
    parameter MAX_VARS_PER_MODULE = 32
) (
    input wire clk,
    input wire rst_n,
    
    // Control interface
    input wire start,              // Start serialization
    output reg ready,              // Ready for new request
    output reg valid,              // Output valid
    
    // State inputs
    input wire [31:0] num_modules,
    input wire [31:0] module_ids [0:MAX_MODULES-1],
    input wire [31:0] var_counts [0:MAX_MODULES-1],
    input wire [31:0] variables [0:MAX_MODULES-1][0:MAX_VARS_PER_MODULE-1],
    input wire signed [63:0] mu_ledger,
    input wire [31:0] pc,
    input wire halted,
    input wire [31:0] result,
    input wire [255:0] program_hash,
    
    // Serialized output (byte stream)
    output reg [7:0] out_byte,
    output reg out_byte_valid,
    input wire out_byte_ready
);

    // State machine
    localparam IDLE = 0;
    localparam SERIALIZE_NUM_MODULES = 1;
    localparam SERIALIZE_MODULES = 2;
    localparam SERIALIZE_MU = 3;
    localparam SERIALIZE_PC = 4;
    localparam SERIALIZE_HALTED = 5;
    localparam SERIALIZE_RESULT = 6;
    localparam SERIALIZE_PROGRAM_HASH = 7;
    localparam DONE = 8;
    
    reg [3:0] state;
    reg [31:0] module_idx;
    reg [31:0] var_idx;
    reg [3:0] byte_idx;
    
    // Helper function: Convert u32 to little-endian bytes
    function [31:0] u32_to_le;
        input [31:0] value;
        begin
            u32_to_le = {value[7:0], value[15:8], value[23:16], value[31:24]};
        end
    endfunction
    
    // Helper function: Convert u64 to little-endian bytes
    function [63:0] u64_to_le;
        input [63:0] value;
        begin
            u64_to_le = {value[7:0], value[15:8], value[23:16], value[31:24],
                         value[39:32], value[47:40], value[55:48], value[63:56]};
        end
    endfunction
    
    // Serialization state machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            ready <= 1'b1;
            valid <= 1'b0;
            out_byte_valid <= 1'b0;
            module_idx <= 0;
            var_idx <= 0;
            byte_idx <= 0;
        end else begin
            case (state)
                IDLE: begin
                    ready <= 1'b1;
                    valid <= 1'b0;
                    out_byte_valid <= 1'b0;
                    if (start) begin
                        ready <= 1'b0;
                        state <= SERIALIZE_NUM_MODULES;
                        byte_idx <= 0;
                    end
                end
                
                SERIALIZE_NUM_MODULES: begin
                    // Serialize num_modules as u32 little-endian
                    if (out_byte_ready || !out_byte_valid) begin
                        case (byte_idx)
                            0: out_byte <= num_modules[7:0];
                            1: out_byte <= num_modules[15:8];
                            2: out_byte <= num_modules[23:16];
                            3: out_byte <= num_modules[31:24];
                        endcase
                        out_byte_valid <= 1'b1;
                        
                        if (byte_idx == 3) begin
                            state <= SERIALIZE_MODULES;
                            module_idx <= 0;
                            byte_idx <= 0;
                        end else begin
                            byte_idx <= byte_idx + 1;
                        end
                    end
                end
                
                SERIALIZE_MODULES: begin
                    // For each module: [module_id:u32, var_count:u32, [vars...]:u32*]
                    // Assumption: modules already sorted by ID (maintained by construction)
                    if (module_idx < num_modules) begin
                        if (out_byte_ready || !out_byte_valid) begin
                            // Serialize module_id
                            if (byte_idx < 4) begin
                                case (byte_idx)
                                    0: out_byte <= module_ids[module_idx][7:0];
                                    1: out_byte <= module_ids[module_idx][15:8];
                                    2: out_byte <= module_ids[module_idx][23:16];
                                    3: out_byte <= module_ids[module_idx][31:24];
                                endcase
                                out_byte_valid <= 1'b1;
                                byte_idx <= byte_idx + 1;
                            end
                            // Serialize var_count
                            else if (byte_idx < 8) begin
                                case (byte_idx - 4)
                                    0: out_byte <= var_counts[module_idx][7:0];
                                    1: out_byte <= var_counts[module_idx][15:8];
                                    2: out_byte <= var_counts[module_idx][23:16];
                                    3: out_byte <= var_counts[module_idx][31:24];
                                endcase
                                out_byte_valid <= 1'b1;
                                byte_idx <= byte_idx + 1;
                                if (byte_idx == 7) begin
                                    var_idx <= 0;
                                end
                            end
                            // Serialize variables
                            else if (var_idx < var_counts[module_idx]) begin
                                case ((byte_idx - 8) % 4)
                                    0: out_byte <= variables[module_idx][var_idx][7:0];
                                    1: out_byte <= variables[module_idx][var_idx][15:8];
                                    2: out_byte <= variables[module_idx][var_idx][23:16];
                                    3: out_byte <= variables[module_idx][var_idx][31:24];
                                endcase
                                out_byte_valid <= 1'b1;
                                
                                if ((byte_idx - 8) % 4 == 3) begin
                                    var_idx <= var_idx + 1;
                                end
                                byte_idx <= byte_idx + 1;
                            end
                            else begin
                                // Move to next module
                                module_idx <= module_idx + 1;
                                byte_idx <= 0;
                                var_idx <= 0;
                            end
                        end
                    end else begin
                        state <= SERIALIZE_MU;
                        byte_idx <= 0;
                    end
                end
                
                SERIALIZE_MU: begin
                    // Serialize μ-ledger as signed 64-bit big-endian
                    if (out_byte_ready || !out_byte_valid) begin
                        case (byte_idx)
                            0: out_byte <= mu_ledger[63:56];
                            1: out_byte <= mu_ledger[55:48];
                            2: out_byte <= mu_ledger[47:40];
                            3: out_byte <= mu_ledger[39:32];
                            4: out_byte <= mu_ledger[31:24];
                            5: out_byte <= mu_ledger[23:16];
                            6: out_byte <= mu_ledger[15:8];
                            7: out_byte <= mu_ledger[7:0];
                        endcase
                        out_byte_valid <= 1'b1;
                        
                        if (byte_idx == 7) begin
                            state <= SERIALIZE_PC;
                            byte_idx <= 0;
                        end else begin
                            byte_idx <= byte_idx + 1;
                        end
                    end
                end
                
                SERIALIZE_PC: begin
                    // Serialize PC as u32 little-endian
                    if (out_byte_ready || !out_byte_valid) begin
                        case (byte_idx)
                            0: out_byte <= pc[7:0];
                            1: out_byte <= pc[15:8];
                            2: out_byte <= pc[23:16];
                            3: out_byte <= pc[31:24];
                        endcase
                        out_byte_valid <= 1'b1;
                        
                        if (byte_idx == 3) begin
                            state <= SERIALIZE_HALTED;
                            byte_idx <= 0;
                        end else begin
                            byte_idx <= byte_idx + 1;
                        end
                    end
                end
                
                SERIALIZE_HALTED: begin
                    // Serialize halted as single byte
                    if (out_byte_ready || !out_byte_valid) begin
                        out_byte <= halted ? 8'h01 : 8'h00;
                        out_byte_valid <= 1'b1;
                        state <= SERIALIZE_RESULT;
                        byte_idx <= 0;
                    end
                end
                
                SERIALIZE_RESULT: begin
                    // Serialize result as u32 little-endian
                    if (out_byte_ready || !out_byte_valid) begin
                        case (byte_idx)
                            0: out_byte <= result[7:0];
                            1: out_byte <= result[15:8];
                            2: out_byte <= result[23:16];
                            3: out_byte <= result[31:24];
                        endcase
                        out_byte_valid <= 1'b1;
                        
                        if (byte_idx == 3) begin
                            state <= SERIALIZE_PROGRAM_HASH;
                            byte_idx <= 0;
                        end else begin
                            byte_idx <= byte_idx + 1;
                        end
                    end
                end
                
                SERIALIZE_PROGRAM_HASH: begin
                    // Serialize program_hash as 32 bytes (256 bits)
                    if (out_byte_ready || !out_byte_valid) begin
                        // Big-endian for hash
                        out_byte <= program_hash[(31-byte_idx)*8 +: 8];
                        out_byte_valid <= 1'b1;
                        
                        if (byte_idx == 31) begin
                            state <= DONE;
                        end else begin
                            byte_idx <= byte_idx + 1;
                        end
                    end
                end
                
                DONE: begin
                    valid <= 1'b1;
                    out_byte_valid <= 1'b0;
                    state <= IDLE;
                end
            endcase
        end
    end

endmodule
