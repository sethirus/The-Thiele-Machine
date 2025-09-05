// ============================================================================
// Thiele CPU MDL Accounting Unit (MAU)
// ============================================================================

module mau (
    input wire clk,
    input wire rst_n,

    // CPU interface
    input wire mdl_req,
    input wire [5:0] module_id,
    input wire [31:0] module_size,
    input wire module_consistent,
    output wire [31:0] mdl_cost,
    output wire mdl_ack,
    output wire [31:0] total_mu,

    // Status
    output wire [31:0] mau_status,
    output wire mau_error
);

// ============================================================================
// PARAMETERS
// ============================================================================

localparam MAX_MU = 32'hFFFFFFFF;
localparam LOG2_MAX_SIZE = 32; // log2 of maximum module size

// Error codes
localparam ERR_NONE = 32'h0;
localparam ERR_OVERFLOW = 32'h3001;
localparam ERR_INVALID_MODULE = 32'h3002;

// ============================================================================
// INTERNAL REGISTERS
// ============================================================================

reg [31:0] mu_accumulator;
reg [31:0] current_cost;
reg ack_pending;
reg [31:0] error_code;
reg [31:0] operation_count;

// History for MDL calculation
reg [31:0] module_history [0:63]; // Size history for each module
reg [31:0] consistency_history [0:63]; // Consistency history

// ============================================================================
// MDL COST CALCULATION
// ============================================================================

function [31:0] calculate_mdl_cost;
    input [31:0] size;
    input consistent;
    begin
        if (size == 0) begin
            calculate_mdl_cost = 0;
        end else if (!consistent) begin
            // Inconsistent modules have infinite cost
            calculate_mdl_cost = 32'hFFFFFFFF;
        end else begin
            // Calculate log2(size) for structure cost
            integer i;
            reg [31:0] log_size;
            log_size = 0;
            for (i = 0; i < LOG2_MAX_SIZE; i = i + 1) begin
                if (size > (1 << i)) begin
                    log_size = i + 1;
                end
            end
            calculate_mdl_cost = log_size;
        end
    end
endfunction

// ============================================================================
// MAIN LOGIC
// ============================================================================

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        mu_accumulator <= 32'h0;
        current_cost <= 32'h0;
        ack_pending <= 1'b0;
        error_code <= ERR_NONE;
        operation_count <= 32'h0;

        // Initialize history
        integer i;
        for (i = 0; i < 64; i = i + 1) begin
            module_history[i] <= 32'h0;
            consistency_history[i] <= 32'h1; // Assume consistent initially
        end

    end else begin
        if (mdl_req && !ack_pending) begin
            // Calculate MDL cost
            current_cost <= calculate_mdl_cost(module_size, module_consistent);

            // Update history
            if (module_id < 64) begin
                module_history[module_id] <= module_size;
                consistency_history[module_id] <= module_consistent ? 32'h1 : 32'h0;
            end

            // Check for overflow
            if (mu_accumulator + current_cost > MAX_MU) begin
                error_code <= ERR_OVERFLOW;
            end else if (module_id >= 64) begin
                error_code <= ERR_INVALID_MODULE;
            end else begin
                error_code <= ERR_NONE;
                mu_accumulator <= mu_accumulator + current_cost;
                operation_count <= operation_count + 1;
            end

            ack_pending <= 1'b1;

        end else if (!mdl_req && ack_pending) begin
            ack_pending <= 1'b0;
        end
    end
end

// ============================================================================
// STATISTICAL ANALYSIS
// ============================================================================

function [31:0] get_average_cost;
    begin
        if (operation_count > 0) begin
            get_average_cost = mu_accumulator / operation_count;
        end else begin
            get_average_cost = 0;
        end
    end
endfunction

function [31:0] get_max_cost;
    integer i;
    reg [31:0] max_val;
    begin
        max_val = 0;
        for (i = 0; i < 64; i = i + 1) begin
            if (module_history[i] > max_val) begin
                max_val = module_history[i];
            end
        end
        get_max_cost = max_val;
    end
endfunction

// ============================================================================
// OUTPUT ASSIGNMENTS
// ============================================================================

assign mdl_cost = current_cost;
assign mdl_ack = ack_pending;
assign total_mu = mu_accumulator;
assign mau_status = {operation_count[15:0], 16'h0};
assign mau_error = (error_code != ERR_NONE);

endmodule