// program_loader.v — Receives program bytes over UART, loads into CPU instruction memory
//
// Protocol (simple binary):
//   1. Host sends 2-byte little-endian instruction count (N)
//   2. Host sends N * 4 bytes (each instruction is 32 bits, little-endian)
//   3. Loader feeds instructions to mkModule1's loadInstr port (44-bit: 12-bit addr + 32-bit data)
//   4. After all instructions loaded, o_done goes high — CPU starts executing
//
// While loading, o_load_en is high and o_load_data carries the 44-bit loadInstr value.
// The CPU's step rule won't fire until after RegFile initialization completes anyway,
// so there is no race between loading and execution.

module program_loader (
    input         clk,
    input         rst_n,

    // UART RX interface
    input         i_byte_valid,
    input  [7:0]  i_byte_data,

    // CPU loadInstr interface (directly drives mkModule1 ports)
    output reg        o_load_en,
    output reg [43:0] o_load_data,

    // Status
    output reg        o_done,     // high after program fully loaded
    output reg        o_loading   // high while receiving program
);

    localparam S_WAIT_COUNT_LO = 3'd0;
    localparam S_WAIT_COUNT_HI = 3'd1;
    localparam S_RECV_BYTE0    = 3'd2;
    localparam S_RECV_BYTE1    = 3'd3;
    localparam S_RECV_BYTE2    = 3'd4;
    localparam S_RECV_BYTE3    = 3'd5;
    localparam S_LOAD          = 3'd6;
    localparam S_DONE          = 3'd7;

    reg [2:0]  state;
    reg [15:0] instr_count;     // total instructions to load
    reg [15:0] instr_loaded;    // instructions loaded so far
    reg [11:0] load_addr;       // current instruction address (12-bit for 4096-word imem)
    reg [31:0] instr_accum;     // accumulates 4 bytes into one instruction

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state        <= S_WAIT_COUNT_LO;
            instr_count  <= 0;
            instr_loaded <= 0;
            load_addr    <= 0;
            instr_accum  <= 0;
            o_load_en    <= 1'b0;
            o_load_data  <= 44'd0;
            o_done       <= 1'b0;
            o_loading    <= 1'b0;
        end else begin
            o_load_en <= 1'b0;  // default: not loading

            case (state)
                S_WAIT_COUNT_LO: begin
                    o_done    <= 1'b0;
                    o_loading <= 1'b0;
                    if (i_byte_valid) begin
                        instr_count[7:0] <= i_byte_data;
                        state <= S_WAIT_COUNT_HI;
                    end
                end

                S_WAIT_COUNT_HI: begin
                    if (i_byte_valid) begin
                        instr_count[15:8] <= i_byte_data;
                        instr_loaded <= 0;
                        load_addr    <= 0;
                        o_loading    <= 1'b1;
                        state <= S_RECV_BYTE0;
                    end
                end

                S_RECV_BYTE0: begin
                    // Check if all instructions loaded
                    if (instr_loaded == instr_count) begin
                        state <= S_DONE;
                    end else if (i_byte_valid) begin
                        instr_accum[7:0] <= i_byte_data;
                        state <= S_RECV_BYTE1;
                    end
                end

                S_RECV_BYTE1: begin
                    if (i_byte_valid) begin
                        instr_accum[15:8] <= i_byte_data;
                        state <= S_RECV_BYTE2;
                    end
                end

                S_RECV_BYTE2: begin
                    if (i_byte_valid) begin
                        instr_accum[23:16] <= i_byte_data;
                        state <= S_RECV_BYTE3;
                    end
                end

                S_RECV_BYTE3: begin
                    if (i_byte_valid) begin
                        instr_accum[31:24] <= i_byte_data;
                        state <= S_LOAD;
                    end
                end

                S_LOAD: begin
                    // Present instruction to CPU's loadInstr port
                    o_load_en   <= 1'b1;
                    o_load_data <= {load_addr, instr_accum};
                    load_addr    <= load_addr + 1;
                    instr_loaded <= instr_loaded + 1;
                    state <= S_RECV_BYTE0;
                end

                S_DONE: begin
                    o_done    <= 1'b1;
                    o_loading <= 1'b0;
                    // Stay done until reset
                end
            endcase
        end
    end

endmodule
