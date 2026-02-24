/*
 * Partition Core Testbench with Trace Output
 * 
 * This testbench exercises the partition_core module and produces
 * a trace file for isomorphism verification with Python VM.
 * 
 * Trace format matches spec/thiele_machine_spec.md
 * 
 * Licensed under Apache 2.0 - Copyright 2025 Devon Thiele
 */

`timescale 1ns / 1ps

module partition_core_tb;

`ifdef ATLAS_SYMBOL_ANCHOR
partition_core atlas_partition_core_anchor ();
`endif

    // Parameters matching spec
    parameter MAX_MODULES = 8;
    parameter REGION_WIDTH = 64;
    parameter MU_WIDTH = 32;
    
    // Clock and reset
    reg clk;
    reg rst_n;
    
    // Operation inputs
    reg [7:0] op;
    reg op_valid;
    reg [REGION_WIDTH-1:0] pnew_region;
    reg [7:0] psplit_module_id;
    reg [REGION_WIDTH-1:0] psplit_mask;
    reg [7:0] pmerge_m1;
    reg [7:0] pmerge_m2;
    
    // Outputs
    wire [7:0] num_modules;
    wire [7:0] result_module_id;
    wire op_done;
    wire is_structured;
    wire [MU_WIDTH-1:0] mu_discovery;
    wire [MU_WIDTH-1:0] mu_execution;
    wire [MU_WIDTH-1:0] mu_cost;
    wire [MAX_MODULES*REGION_WIDTH-1:0] partitions;
    
    // Trace file
    integer trace_fd;
    integer step_count;
    
    // Opcodes (must match Python)
    localparam [7:0] OPC_PNEW   = 8'h00;
    localparam [7:0] OPC_PSPLIT = 8'h01;
    localparam [7:0] OPC_PMERGE = 8'h02;
    
    // DUT instantiation
    partition_core #(
        .MAX_MODULES(MAX_MODULES),
        .REGION_WIDTH(REGION_WIDTH),
        .MU_WIDTH(MU_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .op(op),
        .op_valid(op_valid),
        .pnew_region(pnew_region),
        .psplit_module_id(psplit_module_id),
        .psplit_mask(psplit_mask),
        .pmerge_m1(pmerge_m1),
        .pmerge_m2(pmerge_m2),
        .num_modules(num_modules),
        .result_module_id(result_module_id),
        .op_done(op_done),
        .is_structured(is_structured),
        .mu_discovery(mu_discovery),
        .mu_execution(mu_execution),
        .mu_cost(mu_cost),
        .partitions(partitions)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Helper task: write trace entry
    task write_trace_entry;
        input [255:0] opcode_name;
        input [REGION_WIDTH-1:0] region;
        begin
            $fwrite(trace_fd, "{ \"step\": %0d, \"opcode\": \"%s\", ", step_count, opcode_name);
            $fwrite(trace_fd, "\"region\": %0d, ", region);
            $fwrite(trace_fd, "\"num_modules\": %0d, ", num_modules);
            $fwrite(trace_fd, "\"mu_discovery\": %0d, ", mu_discovery);
            $fwrite(trace_fd, "\"mu_execution\": %0d, ", mu_execution);
            $fwrite(trace_fd, "\"mu_total\": %0d }\n", mu_cost);
        end
    endtask
    
    // Helper task: execute operation and wait
    task execute_op;
        input [7:0] opcode;
        begin
            op <= opcode;
            op_valid <= 1;
            @(posedge clk);
            op_valid <= 0;
            @(posedge clk);
            while (!op_done) @(posedge clk);
            step_count <= step_count + 1;
        end
    endtask
    
    // Main test sequence
    initial begin
        // Open trace file
        trace_fd = $fopen("hw_trace.json", "w");
        $fwrite(trace_fd, "[\n");
        
        // Initialize
        rst_n = 0;
        op = 0;
        op_valid = 0;
        pnew_region = 0;
        psplit_module_id = 0;
        psplit_mask = 0;
        pmerge_m1 = 0;
        pmerge_m2 = 0;
        step_count = 0;
        
        // Reset
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test 1: PNEW with region {0,1,2} = 0b111 = 7
        $display("Test 1: PNEW region={0,1,2}");
        pnew_region <= 64'h7;
        execute_op(OPC_PNEW);
        write_trace_entry("PNEW", 64'h7);
        
        // Test 2: PNEW with region {4,5} = 0b110000 = 48
        $display("Test 2: PNEW region={4,5}");
        pnew_region <= 64'h30;
        execute_op(OPC_PNEW);
        write_trace_entry("PNEW", 64'h30);
        
        // Test 3: PSPLIT module 0 with mask selecting only bit 0
        // Split mask = 0b1 means: new module gets elements where bit 0 is set
        // Original module keeps elements where bit 0 is not set
        $display("Test 3: PSPLIT module=0, mask=0x1 (bit 0 -> new module)");
        psplit_module_id <= 0;
        psplit_mask <= 64'h1;  // Binary: 0...001 - selects only element 0
        execute_op(OPC_PSPLIT);
        write_trace_entry("PSPLIT", 64'h1);
        
        // Test 4: PMERGE modules 1 and 2
        $display("Test 4: PMERGE m1=1, m2=2");
        pmerge_m1 <= 1;
        pmerge_m2 <= 2;
        execute_op(OPC_PMERGE);
        write_trace_entry("PMERGE", 0);
        
        // Close trace file
        $fwrite(trace_fd, "]\n");
        $fclose(trace_fd);
        
        // Display final state
        $display("\n=== Final State ===");
        $display("num_modules: %0d", num_modules);
        $display("mu_discovery: %0d", mu_discovery);
        $display("mu_execution: %0d", mu_execution);
        $display("mu_total: %0d", mu_cost);
        $display("Trace written to hw_trace.json");
        
        #100;
        $finish;
    end

endmodule
