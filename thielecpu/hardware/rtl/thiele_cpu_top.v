// thiele_cpu_top.v — Physical top-level wrapper for Thiele Machine CPU
//
// Reduces the wide Kami-generated mkModule1 interface to 5 physical pins:
//   CLK        — 25 MHz system clock
//   RST_N      — active-low reset (button)
//   LED_HALTED — high when CPU has executed HALT
//   LED_ERR    — high when CPU has set error flag
//   LED_BIANCHI — high when Bianchi conservation alarm fires
//
// All readback/monitor ports (getPC, getMu, etc.) are left floating (un-driven
// outputs are safe; we only care about physical LED signals for bringup).
// The instruction memory is pre-loaded at reset via the internal ROM tie-off:
//   loadInstr is pulled low (no external instruction load) — the CPU boots
//   from its internal memory which is initialised through synthesis.
//
// For full deployment, replace this wrapper with one that connects loadInstr
// to a UART or SPI interface and exposes a debug bus.

`define BSV_ASSIGNMENT_DELAY
`define BSV_RESET_VALUE 1'b0
`define BSV_RESET_EDGE  negedge

module thiele_cpu_top (
    input  CLK,
    input  RST_N,
    output LED_HALTED,
    output LED_ERR,
    output LED_BIANCHI
);

    // --- Tie-off constants for unused input ports ---
    wire [39:0] load_instr_data = 40'h0;
    wire        en_load_instr   = 1'b0;

    // EN lines: drive high so readback methods always present valid data.
    // (RDY_* outputs are wired to 'nc_*' and ignored.)
    wire en_getPC          = 1'b1;
    wire en_getMu          = 1'b1;
    wire en_getErr         = 1'b1;
    wire en_getHalted      = 1'b1;
    wire en_getPartOps     = 1'b1;
    wire en_getMdlOps      = 1'b1;
    wire en_getInfoGain    = 1'b1;
    wire en_getErrorCode   = 1'b1;
    wire en_getMuTensor0   = 1'b1;
    wire en_getMuTensor1   = 1'b1;
    wire en_getMuTensor2   = 1'b1;
    wire en_getMuTensor3   = 1'b1;
    wire en_getBianchi     = 1'b1;

    // --- Instantiate CPU core ---
    mkModule1 cpu (
        .CLK                 (CLK),
        .RST_N               (RST_N),

        .loadInstr_x_0       (load_instr_data),
        .EN_loadInstr        (en_load_instr),
        .RDY_loadInstr       (),   // nc

        .EN_getPC            (en_getPC),
        .getPC               (),   // nc
        .RDY_getPC           (),

        .EN_getMu            (en_getMu),
        .getMu               (),
        .RDY_getMu           (),

        .EN_getErr           (en_getErr),
        .getErr              (LED_ERR),
        .RDY_getErr          (),

        .EN_getHalted        (en_getHalted),
        .getHalted           (LED_HALTED),
        .RDY_getHalted       (),

        .EN_getPartitionOps  (en_getPartOps),
        .getPartitionOps     (),
        .RDY_getPartitionOps (),

        .EN_getMdlOps        (en_getMdlOps),
        .getMdlOps           (),
        .RDY_getMdlOps       (),

        .EN_getInfoGain      (en_getInfoGain),
        .getInfoGain         (),
        .RDY_getInfoGain     (),

        .EN_getErrorCode     (en_getErrorCode),
        .getErrorCode        (),
        .RDY_getErrorCode    (),

        .EN_getMuTensor0     (en_getMuTensor0),
        .getMuTensor0        (),
        .RDY_getMuTensor0    (),

        .EN_getMuTensor1     (en_getMuTensor1),
        .getMuTensor1        (),
        .RDY_getMuTensor1    (),

        .EN_getMuTensor2     (en_getMuTensor2),
        .getMuTensor2        (),
        .RDY_getMuTensor2    (),

        .EN_getMuTensor3     (en_getMuTensor3),
        .getMuTensor3        (),
        .RDY_getMuTensor3    (),

        .EN_getBianchiAlarm  (en_getBianchi),
        .getBianchiAlarm     (LED_BIANCHI),
        .RDY_getBianchiAlarm ()
    );

endmodule
