// thiele_cpu_top.v — Physical top-level wrapper for Thiele Machine CPU
//
// Full deployment wrapper with UART program loading and debug output.
//
// Pins:
//   CLK         — 25 MHz system clock
//   RST_N       — active-low reset (active-low button)
//   UART_RX     — serial input  (program loading, 115200 8N1)
//   UART_TX     — serial output (debug dump on halt/error)
//   LED_HALTED  — high when CPU has executed HALT
//   LED_ERR     — high when CPU has set error flag
//   LED_BIANCHI — high when Bianchi conservation alarm fires
//   LED_LOADING — high while UART program loader is receiving
//
// Program loading protocol (binary, little-endian):
//   1. Send 2-byte instruction count N
//   2. Send N × 4 bytes (each 32-bit instruction, little-endian)
//   3. LED_LOADING goes low, CPU starts executing
//
// Debug dump (binary, little-endian, sent on halt or error):
//   [0]    0xDE (sync)
//   [1]    status (bit0=halted, bit1=err, bit2=certified)
//   [2:5]  PC
//   [6:9]  mu
//   [10:13] error_code
//   [14]   0xAD (end marker)

`define BSV_ASSIGNMENT_DELAY
`define BSV_RESET_VALUE 1'b0
`define BSV_RESET_EDGE  negedge

module thiele_cpu_top #(
    parameter CLK_FREQ  = 25_000_000,
    parameter BAUD_RATE = 115_200
)(
    input  CLK,
    input  RST_N,
    input  UART_RX,
    output UART_TX,
    output LED_HALTED,
    output LED_ERR,
    output LED_BIANCHI,
    output LED_LOADING
);

    localparam CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;

    // ---- UART RX ----
    wire       rx_valid;
    wire [7:0] rx_data;

    uart_rx #(.CLKS_PER_BIT(CLKS_PER_BIT)) u_rx (
        .clk     (CLK),
        .rst_n   (RST_N),
        .i_rx    (UART_RX),
        .o_valid (rx_valid),
        .o_data  (rx_data)
    );

    // ---- Program Loader ----
    wire        loader_en;
    wire [43:0] loader_data;
    wire        loader_done;
    wire        loader_loading;

    program_loader u_loader (
        .clk          (CLK),
        .rst_n        (RST_N),
        .i_byte_valid (rx_valid),
        .i_byte_data  (rx_data),
        .o_load_en    (loader_en),
        .o_load_data  (loader_data),
        .o_done       (loader_done),
        .o_loading    (loader_loading)
    );

    assign LED_LOADING = loader_loading;

    // ---- CPU Stall During Loading ----
    // The Kami step rule fires when: !halted && !err && imem_init && mem_init && !EN_apbWrite
    // We assert EN_apbWrite (with dummy data) during program loading to stall the CPU.
    // This keeps the CPU live (clocked, not in reset) but prevents it from stepping.
    // Once loading is done, EN_apbWrite deasserts and the CPU begins executing.
    wire cpu_stall = ~loader_done;

    // ---- CPU Core (Kami-generated) ----
    wire        cpu_halted;
    wire        cpu_err;
    wire        cpu_certified;
    wire [31:0] cpu_pc;
    wire [31:0] cpu_mu;
    wire [31:0] cpu_error_code;
    wire        cpu_bianchi;

    mkModule1 cpu (
        .CLK                    (CLK),
        .RST_N                  (RST_N),

        // Program loading — driven by UART loader
        .loadInstr_x_0          (loader_data),
        .EN_loadInstr           (loader_en),
        .RDY_loadInstr          (),

        // State readback
        .EN_getPC               (1'b1),
        .getPC                  (cpu_pc),
        .RDY_getPC              (),

        .EN_getMu               (1'b1),
        .getMu                  (cpu_mu),
        .RDY_getMu              (),

        .EN_getErr              (1'b1),
        .getErr                 (cpu_err),
        .RDY_getErr             (),

        .EN_getHalted           (1'b1),
        .getHalted              (cpu_halted),
        .RDY_getHalted          (),

        .EN_getCertified        (1'b1),
        .getCertified           (cpu_certified),
        .RDY_getCertified       (),

        .EN_getErrorCode        (1'b1),
        .getErrorCode           (cpu_error_code),
        .RDY_getErrorCode       (),

        .EN_getBianchiAlarm     (1'b1),
        .getBianchiAlarm        (cpu_bianchi),
        .RDY_getBianchiAlarm    (),

        // Unused readback ports — enable but leave output unconnected
        .EN_getWcSame00         (1'b1),  .getWcSame00         (),  .RDY_getWcSame00         (),
        .EN_getWcDiff00         (1'b1),  .getWcDiff00         (),  .RDY_getWcDiff00         (),
        .EN_getWcSame01         (1'b1),  .getWcSame01         (),  .RDY_getWcSame01         (),
        .EN_getWcDiff01         (1'b1),  .getWcDiff01         (),  .RDY_getWcDiff01         (),
        .EN_getWcSame10         (1'b1),  .getWcSame10         (),  .RDY_getWcSame10         (),
        .EN_getWcDiff10         (1'b1),  .getWcDiff10         (),  .RDY_getWcDiff10         (),
        .EN_getWcSame11         (1'b1),  .getWcSame11         (),  .RDY_getWcSame11         (),
        .EN_getWcDiff11         (1'b1),  .getWcDiff11         (),  .RDY_getWcDiff11         (),
        .EN_getPartitionOps     (1'b1),  .getPartitionOps     (),  .RDY_getPartitionOps     (),
        .EN_getMdlOps           (1'b1),  .getMdlOps           (),  .RDY_getMdlOps           (),
        .EN_getInfoGain         (1'b1),  .getInfoGain         (),  .RDY_getInfoGain         (),
        .EN_getMstatus          (1'b1),  .getMstatus          (),  .RDY_getMstatus          (),
        .EN_getMcycleLo         (1'b1),  .getMcycleLo         (),  .RDY_getMcycleLo         (),
        .EN_getMcycleHi         (1'b1),  .getMcycleHi         (),  .RDY_getMcycleHi         (),
        .EN_getMinstretLo       (1'b1),  .getMinstretLo       (),  .RDY_getMinstretLo       (),
        .EN_getMinstretHi       (1'b1),  .getMinstretHi       (),  .RDY_getMinstretHi       (),
        .EN_getLogicAcc         (1'b1),  .getLogicAcc         (),  .RDY_getLogicAcc         (),
        .EN_getLogicReqValid    (1'b1),  .getLogicReqValid    (),  .RDY_getLogicReqValid    (),
        .EN_getLogicReqOpcode   (1'b1),  .getLogicReqOpcode   (),  .RDY_getLogicReqOpcode   (),
        .EN_getLogicReqPayload  (1'b1),  .getLogicReqPayload  (),  .RDY_getLogicReqPayload  (),
        .EN_getMuTensor0        (1'b1),  .getMuTensor0        (),  .RDY_getMuTensor0        (),
        .EN_getMuTensor1        (1'b1),  .getMuTensor1        (),  .RDY_getMuTensor1        (),
        .EN_getMuTensor2        (1'b1),  .getMuTensor2        (),  .RDY_getMuTensor2        (),
        .EN_getMuTensor3        (1'b1),  .getMuTensor3        (),  .RDY_getMuTensor3        (),
        .EN_getPtNextId         (1'b1),  .getPtNextId         (),  .RDY_getPtNextId         (),
        .getPtSize_x_0          (6'd0),
        .EN_getPtSize           (1'b1),  .getPtSize           (),  .RDY_getPtSize           (),

        // Unused input ports — tied off
        .setLogicResp_x_0       (34'd0),
        .EN_setLogicResp        (1'b0),
        .RDY_setLogicResp       (),

        .setActiveModule_x_0    (6'd0),
        .EN_setActiveModule     (1'b0),
        .RDY_setActiveModule    (),

        .setTrapVector_x_0      (32'd0),
        .EN_setTrapVector       (1'b0),
        .RDY_setTrapVector      (),

        .apbReadData_x_0        (32'd0),
        .EN_apbReadData         (1'b0),
        .RDY_apbReadData        (),

        .apbReadErr_x_0         (32'd0),
        .EN_apbReadErr          (1'b0),
        .RDY_apbReadErr         (),

        // APB bus — EN_apbWrite stalls CPU step rule during program loading
        .apbWrite_x_0           (64'd0),
        .EN_apbWrite            (cpu_stall),
        .RDY_apbWrite           ()
    );

    assign LED_HALTED  = cpu_halted;
    assign LED_ERR     = cpu_err;
    assign LED_BIANCHI = cpu_bianchi;

    // ---- Debug Dumper ----
    wire       dump_tx_valid;
    wire [7:0] dump_tx_data;
    wire       tx_busy;

    debug_dumper u_dump (
        .clk            (CLK),
        .rst_n          (RST_N),
        .i_halted       (cpu_halted),
        .i_err          (cpu_err),
        .i_certified    (cpu_certified),
        .i_pc           (cpu_pc),
        .i_mu           (cpu_mu),
        .i_error_code   (cpu_error_code),
        .o_tx_valid     (dump_tx_valid),
        .o_tx_data      (dump_tx_data),
        .i_tx_busy      (tx_busy)
    );

    // ---- UART TX ----
    uart_tx #(.CLKS_PER_BIT(CLKS_PER_BIT)) u_tx (
        .clk     (CLK),
        .rst_n   (RST_N),
        .i_valid (dump_tx_valid),
        .i_data  (dump_tx_data),
        .o_tx    (UART_TX),
        .o_busy  (tx_busy)
    );

endmodule
