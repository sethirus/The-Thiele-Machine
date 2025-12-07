// Primitive: CommunityAssignment - Modularity-Based Clustering
// Implements Louvain-style community detection
// Part of The Empyrean Forge

module primitive_community_assign #(
    parameter NUM_NODES = 256,
    parameter NUM_COMMUNITIES = 16,
    parameter PRECISION = 16
) (
    input wire clk,
    input wire rst_n,
    input wire start,
    
    // Graph structure
    input wire [PRECISION-1:0] edge_matrix [0:NUM_NODES-1][0:NUM_NODES-1],
    
    // Output: Community assignments
    output reg [7:0] community [0:NUM_NODES-1],
    output reg [PRECISION-1:0] modularity,
    output reg done
);

    // State machine
    localparam IDLE = 2'd0;
    localparam INIT = 2'd1;
    localparam OPTIMIZE = 2'd2;
    localparam COMPLETE = 2'd3;
    
    reg [1:0] state;
    reg [7:0] node_idx;
    reg [7:0] iteration;
    
    // Modularity computation registers
    reg [PRECISION-1:0] total_edges;
    reg [PRECISION-1:0] internal_edges;
    reg [PRECISION-1:0] degree_sum [0:NUM_COMMUNITIES-1];
    
    integer i, j, c;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            done <= 0;
            modularity <= 0;
            node_idx <= 0;
            iteration <= 0;
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        // Initialize each node to its own community
                        for (i = 0; i < NUM_NODES; i = i + 1) begin
                            community[i] <= i[7:0];
                        end
                        state <= INIT;
                    end
                end
                
                INIT: begin
                    // Compute total edge weight
                    total_edges = 0;
                    for (i = 0; i < NUM_NODES; i = i + 1) begin
                        for (j = i+1; j < NUM_NODES; j = j + 1) begin
                            total_edges = total_edges + edge_matrix[i][j];
                        end
                    end
                    
                    node_idx <= 0;
                    iteration <= 0;
                    state <= OPTIMIZE;
                end
                
                OPTIMIZE: begin
                    // Greedy modularity optimization
                    // For each node, try moving it to neighbor's community
                    reg [7:0] best_community;
                    reg [PRECISION-1:0] best_modularity;
                    reg [PRECISION-1:0] delta_mod;
                    
                    best_community = community[node_idx];
                    best_modularity = 0;
                    
                    // Try each neighbor's community
                    for (j = 0; j < NUM_NODES; j = j + 1) begin
                        if (edge_matrix[node_idx][j] > 0 && j != node_idx) begin
                            // Compute modularity delta for moving to j's community
                            delta_mod = edge_matrix[node_idx][j];
                            if (delta_mod > best_modularity) begin
                                best_modularity = delta_mod;
                                best_community = community[j];
                            end
                        end
                    end
                    
                    // Update community assignment
                    community[node_idx] <= best_community;
                    
                    // Move to next node
                    if (node_idx == NUM_NODES - 1) begin
                        iteration <= iteration + 1;
                        node_idx <= 0;
                        
                        // Stop after fixed iterations
                        if (iteration >= 8'd10) begin
                            state <= COMPLETE;
                        end
                    end else begin
                        node_idx <= node_idx + 1;
                    end
                end
                
                COMPLETE: begin
                    // Compute final modularity
                    internal_edges = 0;
                    for (i = 0; i < NUM_NODES; i = i + 1) begin
                        for (j = i+1; j < NUM_NODES; j = j + 1) begin
                            if (community[i] == community[j]) begin
                                internal_edges = internal_edges + edge_matrix[i][j];
                            end
                        end
                    end
                    
                    // Modularity = (internal_edges / total_edges)
                    if (total_edges > 0) begin
                        modularity <= (internal_edges << 8) / total_edges;
                    end else begin
                        modularity <= 0;
                    end
                    
                    done <= 1;
                    if (!start) begin
                        state <= IDLE;
                    end
                end
            endcase
        end
    end

endmodule
