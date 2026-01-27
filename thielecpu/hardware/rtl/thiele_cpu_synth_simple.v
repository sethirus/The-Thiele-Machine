// ============================================================================
// SYNTHESIS-FRIENDLY VERSION - Thiele CPU Core
// ============================================================================
// Simplified version that avoids complex SystemVerilog constructs
// for open-source synthesis compatibility

module thiele_cpu_synth_simple (
    input wire clk,
    input wire rst_n,
    
    // Basic instruction interface
    input wire [31:0] instr_data,
    output wire [31:0] pc,
    
    // μ-cost output (core innovation)
    output wire [31:0] mu_cost,
    
    // Status outputs
    output wire [31:0] status,
    output wire [31:0] error_code
);

// ============================================================================
// PARAMETERS (Reduced for synthesis)
// ============================================================================
localparam NUM_MODULES = 8;    // Reduced from 64
localparam REGION_SIZE = 16;   // Reduced from 1024
localparam TOTAL_REGIONS = NUM_MODULES * REGION_SIZE;  // 128

// ============================================================================
// REGISTERS (Flattened arrays for synthesis)
// ============================================================================
reg [31:0] pc_reg;
reg [31:0] mu_accumulator;
reg [31:0] status_reg;
reg [31:0] error_reg;

// Flattened module table (synthesis-friendly)
reg [31:0] module_table [0:NUM_MODULES-1];

// Flattened region data (single large array)
reg [31:0] region_data [0:TOTAL_REGIONS-1];

// Instruction decoding
wire [7:0] opcode = instr_data[31:24];
wire [7:0] operand_a = instr_data[23:16];
wire [7:0] operand_b = instr_data[15:8];
wire [7:0] operand_cost = instr_data[7:0];

// State machine
reg [3:0] state;
reg [5:0] current_module;
reg [5:0] next_module_id;

// Loop counters for synthesis-friendly operations
reg [31:0] loop_idx;
reg [31:0] temp_count;
reg [31:0] temp_value;

// ============================================================================
// STATE MACHINE DEFINITIONS
// ============================================================================
localparam [3:0] STATE_IDLE = 4'h0;
localparam [3:0] STATE_FETCH = 4'h1;
localparam [3:0] STATE_DECODE = 4'h2;
localparam [3:0] STATE_EXECUTE = 4'h3;
localparam [3:0] STATE_LOOP_INIT = 4'h4;
localparam [3:0] STATE_LOOP_WORK = 4'h5;
localparam [3:0] STATE_LOOP_DONE = 4'h6;

// ============================================================================
// μ-ALU INSTANCE (Simplified)
// ============================================================================
wire [31:0] alu_result;
wire alu_ready;

mu_alu_simple mu_alu_inst (
    .clk(clk),
    .rst_n(rst_n),
    .operand_a(mu_accumulator),
    .operand_b({24'h0, operand_cost}),
    .result(alu_result),
    .ready(alu_ready)
);

// ============================================================================
// MAIN STATE MACHINE
// ============================================================================
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        pc_reg <= 32'h0;
        mu_accumulator <= 32'h0;
        status_reg <= 32'h0;
        error_reg <= 32'h0;
        state <= STATE_IDLE;
        current_module <= 6'h0;
        next_module_id <= 6'h1;
        loop_idx <= 32'h0;
        temp_count <= 32'h0;
        temp_value <= 32'h0;
    end else begin
        case (state)
            STATE_IDLE: begin
                state <= STATE_FETCH;
            end
            
            STATE_FETCH: begin
                state <= STATE_DECODE;
            end
            
            STATE_DECODE: begin
                state <= STATE_EXECUTE;
            end
            
            STATE_EXECUTE: begin
                case (opcode)
                    8'h01: begin  // PNEW
                        if (next_module_id < NUM_MODULES) begin
                            // Create new module
                            module_table[next_module_id] <= 32'd1;
                            region_data[next_module_id * REGION_SIZE] <= {24'h0, operand_a};
                            current_module <= next_module_id;
                            next_module_id <= next_module_id + 1;
                            mu_accumulator <= alu_result;
                            status_reg <= 32'h1;  // Success
                        end else begin
                            error_reg <= 32'h2;  // No space
                        end
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                    
                    8'h02: begin  // PSPLIT
                        if (operand_a < next_module_id && next_module_id < NUM_MODULES - 1) begin
                            // Initialize loop for splitting
                            loop_idx <= 0;
                            temp_count <= 0;
                            state <= STATE_LOOP_INIT;
                        end else begin
                            error_reg <= 32'h3;  // Invalid
                            pc_reg <= pc_reg + 4;
                            state <= STATE_FETCH;
                        end
                    end
                    
                    8'h03: begin  // PMERGE
                        mu_accumulator <= alu_result;
                        status_reg <= 32'h3;  // Merge successful
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                    
                    8'h04: begin  // LASSERT
                        mu_accumulator <= alu_result;
                        status_reg <= 32'h4;  // Assert successful
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                    
                    8'h05: begin  // EMIT
                        mu_accumulator <= alu_result;
                        status_reg <= {16'h0, operand_a, operand_b};
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                    
                    8'hFF: begin  // HALT
                        mu_accumulator <= alu_result;
                        status_reg <= 32'hFF;  // Halted
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                    
                    default: begin
                        error_reg <= 32'h1;  // Unknown opcode
                        pc_reg <= pc_reg + 4;
                        state <= STATE_FETCH;
                    end
                endcase
            end
            
            STATE_LOOP_INIT: begin
                // Initialize loop variables for PSPLIT
                loop_idx <= 0;
                temp_count <= 0;
                state <= STATE_LOOP_WORK;
            end
            
            STATE_LOOP_WORK: begin
                // Simplified split logic (just count elements for now)
                if (loop_idx < REGION_SIZE) begin
                    // Simple even/odd split based on LSB
                    if (region_data[operand_a * REGION_SIZE + loop_idx][0] == operand_b[0]) begin
                        temp_count <= temp_count + 1;
                    end
                    loop_idx <= loop_idx + 1;
                end else begin
                    state <= STATE_LOOP_DONE;
                end
            end
            
            STATE_LOOP_DONE: begin
                // Complete the split operation
                mu_accumulator <= alu_result;
                status_reg <= 32'h2;  // Split successful
                pc_reg <= pc_reg + 4;
                state <= STATE_FETCH;
            end
            
            default: begin
                state <= STATE_FETCH;
            end
        endcase
    end
end

// ============================================================================
// OUTPUTS
// ============================================================================
assign pc = pc_reg;
assign mu_cost = mu_accumulator;
assign status = status_reg;
assign error_code = error_reg;

endmodule
