// Primitive: GraphNode - Hardware Memory Cell for Graph Vertex
// Part of The Empyrean Forge - Dynamically Configurable Evolutionary Hardware

module primitive_graph_node #(
    parameter NODE_ID_WIDTH = 8,
    parameter WEIGHT_WIDTH = 16
) (
    input wire clk,
    input wire rst_n,
    
    // Node configuration
    input wire [NODE_ID_WIDTH-1:0] node_id,
    input wire node_enable,
    
    // Edge connections (up to MAX_DEGREE edges per node)
    input wire [3:0] degree,  // Number of edges
    input wire [NODE_ID_WIDTH-1:0] neighbor_ids [0:15],
    input wire [WEIGHT_WIDTH-1:0] edge_weights [0:15],
    
    // Community/partition assignment
    input wire [NODE_ID_WIDTH-1:0] partition_id,
    input wire partition_update,
    
    // Outputs
    output reg [NODE_ID_WIDTH-1:0] current_partition,
    output reg [WEIGHT_WIDTH-1:0] total_weight,
    output reg [3:0] node_degree
);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_partition <= 0;
            total_weight <= 0;
            node_degree <= 0;
        end else if (node_enable) begin
            // Update partition assignment
            if (partition_update) begin
                current_partition <= partition_id;
            end
            
            // Compute total edge weight
            node_degree <= degree;
            integer i;
            reg [WEIGHT_WIDTH-1:0] sum;
            sum = 0;
            for (i = 0; i < 16; i = i + 1) begin
                if (i < degree) begin
                    sum = sum + edge_weights[i];
                end
            end
            total_weight <= sum;
        end
    end

endmodule
