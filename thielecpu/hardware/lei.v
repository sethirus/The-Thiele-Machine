// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// Copyright 2025 Devon Thiele
// See the LICENSE file in the repository root for full terms.

// ============================================================================
// Thiele CPU Logic Engine Interface (LEI)
// ============================================================================

module lei (
    input wire clk,
    input wire rst_n,

    // CPU interface
    input wire logic_req,
    input wire [31:0] logic_addr,
    output wire logic_ack,
    output wire [31:0] logic_data,

    // External Z3 interface
    output wire z3_req,
    output wire [31:0] z3_formula_addr,
    input wire z3_ack,
    input wire [31:0] z3_result,
    input wire z3_sat,        // Satisfiability result
    input wire [31:0] z3_cert_hash, // Certificate hash

    // Certificate storage interface
    output wire cert_write,
    output wire [31:0] cert_addr,
    output wire [31:0] cert_data,

    // Status
    output wire [31:0] lei_status,
    output wire lei_error
);

// ============================================================================
// PARAMETERS AND STATES
// ============================================================================

localparam STATE_IDLE = 3'h0;
localparam STATE_REQUEST = 3'h1;
localparam STATE_WAIT = 3'h2;
localparam STATE_PROCESS = 3'h3;
localparam STATE_STORE_CERT = 3'h4;
localparam STATE_COMPLETE = 3'h5;

// Error codes
localparam ERR_NONE = 32'h0;
localparam ERR_TIMEOUT = 32'h2001;
localparam ERR_INVALID_FORMULA = 32'h2002;
localparam ERR_Z3_ERROR = 32'h2003;

// ============================================================================
// INTERNAL REGISTERS
// ============================================================================

reg [2:0] state;
reg [31:0] current_addr;
reg [31:0] result_data;
reg [31:0] cert_hash;
reg ack_pending;
reg [15:0] timeout_counter;
reg [31:0] error_code;

// Certificate storage
reg [31:0] cert_store [0:255]; // Simple certificate cache
reg [7:0] cert_index;

// ============================================================================
// STATE MACHINE
// ============================================================================

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= STATE_IDLE;
        ack_pending <= 1'b0;
        timeout_counter <= 16'h0;
        error_code <= ERR_NONE;
        cert_index <= 8'h0;
        result_data <= 32'h0;
        cert_hash <= 32'h0;
    end else begin
        case (state)
            STATE_IDLE: begin
                if (logic_req && !ack_pending) begin
                    state <= STATE_REQUEST;
                    current_addr <= logic_addr;
                    timeout_counter <= 16'hFFFF; // ~1ms timeout at 100MHz
                    error_code <= ERR_NONE;
                end
            end

            STATE_REQUEST: begin
                // Send request to Z3
                state <= STATE_WAIT;
            end

            STATE_WAIT: begin
                timeout_counter <= timeout_counter - 1;

                if (z3_ack) begin
                    state <= STATE_PROCESS;
                    result_data <= z3_result;
                    cert_hash <= z3_cert_hash;
                end else if (timeout_counter == 0) begin
                    state <= STATE_COMPLETE;
                    error_code <= ERR_TIMEOUT;
                end
            end

            STATE_PROCESS: begin
                // Process Z3 result
                if (z3_sat) begin
                    // Satisfiable - store certificate
                    state <= STATE_STORE_CERT;
                end else begin
                    // Unsatisfiable - generate proof
                    state <= STATE_STORE_CERT;
                end
            end

            STATE_STORE_CERT: begin
                // Store certificate in local cache
                if (cert_index < 255) begin
                    cert_store[cert_index] <= cert_hash;
                    cert_index <= cert_index + 1;
                end
                state <= STATE_COMPLETE;
                ack_pending <= 1'b1;
            end

            STATE_COMPLETE: begin
                if (!logic_req) begin
                    state <= STATE_IDLE;
                    ack_pending <= 1'b0;
                end
            end

            default: begin
                state <= STATE_IDLE;
            end
        endcase
    end
end

// ============================================================================
// CERTIFICATE JOINING LOGIC
// ============================================================================

task join_certificates;
    input [31:0] cert_a;
    input [31:0] cert_b;
    output [31:0] joined_cert;
    begin
        // Simple certificate joining via XOR
        // In practice, this would use proper cryptographic operations
        joined_cert = cert_a ^ cert_b;
    end
endtask

// ============================================================================
// OUTPUT ASSIGNMENTS
// ============================================================================

assign z3_req = (state == STATE_REQUEST);
assign z3_formula_addr = current_addr;
assign logic_ack = ack_pending;
assign logic_data = result_data;
assign lei_status = {29'h0, state};
assign lei_error = (error_code != ERR_NONE);

// Certificate storage interface
assign cert_write = (state == STATE_STORE_CERT);
assign cert_addr = {24'h0, cert_index};
assign cert_data = cert_hash;

endmodule