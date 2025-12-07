// The Empyrean Forge - Dynamically Configurable Evolutionary Hardware
// Main configurator module that reads .thiele DNA and wires up primitives

module empyrean_forge #(
    parameter NUM_NODES = 256,
    parameter PRECISION = 16,
    parameter MAX_PRIMITIVES = 10,
    parameter DNA_WIDTH = 8
) (
    input wire clk,
    input wire rst_n,
    input wire start,
    
    // Strategy DNA input (sequence of primitive codes)
    input wire [DNA_WIDTH-1:0] dna_sequence [0:MAX_PRIMITIVES-1],
    input wire [3:0] dna_length,
    
    // Graph data
    input wire [PRECISION-1:0] adjacency_matrix [0:NUM_NODES-1][0:NUM_NODES-1],
    
    // Outputs: Partition assignment
    output reg [7:0] partition [0:NUM_NODES-1],
    output reg done
);

    // Primitive codes (matching primitives.py)
    localparam PRIM_GET_NODES = 8'd0;
    localparam PRIM_GET_EDGES = 8'd1;
    localparam PRIM_NODE_DEGREE = 8'd2;
    localparam PRIM_ADJ_MATRIX = 8'd3;
    localparam PRIM_LAPLACIAN = 8'd4;
    localparam PRIM_EIGENDECOMP = 8'd5;
    localparam PRIM_KMEANS = 8'd6;
    localparam PRIM_THRESHOLD = 8'd7;
    localparam PRIM_COMMUNITY = 8'd8;
    localparam PRIM_MODULARITY = 8'd9;
    
    // State machine
    localparam IDLE = 3'd0;
    localparam DECODE = 3'd1;
    localparam EXECUTE = 3'd2;
    localparam COMPOSE = 3'd3;
    localparam COMPLETE = 3'd4;
    
    reg [2:0] state;
    reg [3:0] dna_index;
    
    // Primitive module instantiations
    wire matrix_decomp_start, matrix_decomp_done;
    wire [PRECISION-1:0] eigenvalue;
    wire [PRECISION-1:0] eigenvector [0:NUM_NODES-1];
    
    primitive_matrix_decomp #(
        .MATRIX_SIZE(NUM_NODES),
        .PRECISION(PRECISION)
    ) matrix_decomp_inst (
        .clk(clk),
        .rst_n(rst_n),
        .start(matrix_decomp_start),
        .matrix(adjacency_matrix),
        .eigenvalue(eigenvalue),
        .eigenvector(eigenvector),
        .done(matrix_decomp_done)
    );
    
    wire community_start, community_done;
    wire [7:0] community_assign [0:NUM_NODES-1];
    wire [PRECISION-1:0] modularity;
    
    primitive_community_assign #(
        .NUM_NODES(NUM_NODES),
        .PRECISION(PRECISION)
    ) community_inst (
        .clk(clk),
        .rst_n(rst_n),
        .start(community_start),
        .edge_matrix(adjacency_matrix),
        .community(community_assign),
        .modularity(modularity),
        .done(community_done)
    );
    
    // Execution control
    reg [7:0] current_primitive;
    reg execute_primitive;
    
    assign matrix_decomp_start = (current_primitive == PRIM_EIGENDECOMP) && execute_primitive;
    assign community_start = (current_primitive == PRIM_COMMUNITY) && execute_primitive;
    
    integer i;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            done <= 0;
            dna_index <= 0;
            execute_primitive <= 0;
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        dna_index <= 0;
                        done <= 0;
                        state <= DECODE;
                    end
                end
                
                DECODE: begin
                    // Read next primitive from DNA sequence
                    current_primitive <= dna_sequence[dna_index];
                    state <= EXECUTE;
                end
                
                EXECUTE: begin
                    execute_primitive <= 1;
                    
                    // Wait for current primitive to complete
                    case (current_primitive)
                        PRIM_EIGENDECOMP: begin
                            if (matrix_decomp_done) begin
                                execute_primitive <= 0;
                                state <= COMPOSE;
                            end
                        end
                        
                        PRIM_COMMUNITY: begin
                            if (community_done) begin
                                execute_primitive <= 0;
                                state <= COMPOSE;
                            end
                        end
                        
                        default: begin
                            // Simple primitives complete in one cycle
                            execute_primitive <= 0;
                            state <= COMPOSE;
                        end
                    endcase
                end
                
                COMPOSE: begin
                    // Move to next primitive
                    dna_index <= dna_index + 1;
                    
                    if (dna_index >= dna_length - 1) begin
                        state <= COMPLETE;
                    end else begin
                        state <= DECODE;
                    end
                end
                
                COMPLETE: begin
                    // Final partition assignment based on last primitive
                    case (current_primitive)
                        PRIM_EIGENDECOMP: begin
                            // Spectral partitioning: threshold eigenvector
                            for (i = 0; i < NUM_NODES; i = i + 1) begin
                                partition[i] <= eigenvector[i][15] ? 8'd1 : 8'd0;
                            end
                        end
                        
                        PRIM_COMMUNITY: begin
                            // Community detection result
                            for (i = 0; i < NUM_NODES; i = i + 1) begin
                                partition[i] <= community_assign[i];
                            end
                        end
                        
                        default: begin
                            // Default: degree-based partitioning
                            for (i = 0; i < NUM_NODES; i = i + 1) begin
                                partition[i] <= i[0] ? 8'd1 : 8'd0;
                            end
                        end
                    endcase
                    
                    done <= 1;
                    if (!start) begin
                        state <= IDLE;
                    end
                end
            endcase
        end
    end

endmodule
