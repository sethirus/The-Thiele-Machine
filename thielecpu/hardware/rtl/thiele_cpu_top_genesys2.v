// thiele_cpu_top_genesys2.v — CI-synthesis wrapper (K480T / ffg901).
//
// File name kept as thiele_cpu_top_genesys2.v to minimise downstream churn
// (synth_xc7.ys, run_synthesis_xc7.sh, the CI workflow all reference this
// wrapper by name). The wrapper itself no longer matches a Genesys 2 board
// layout — that board uses xc7k325t-ffg900 which has only 840 DSPs, too few
// for the ~1131 DSP48E1 slices yosys infers for column_contractive_check_witness
// (~20 integer multiplications per cycle including two 128×128). Targeting
// K480T-ffg901 instead (1920 DSPs, the smallest part that fits in openXC7's
// prjxray-db with a complete parent-dir tilegrid.json — K420T was incomplete).
//
// Clock input is single-ended for CI portability. A real Genesys 2 build with
// the original K325T part still wants the IBUFDS-driven LVDS pair; that wrapper
// can be reinstated as a board-specific variant when an actual K480T-ffg901
// board enters the deploy path.
//
// The wrapper layer sits OUTSIDE the Coq↔OCaml↔Kami↔BSC↔Verilog isomorphism
// chain — it just connects external pins to the canonical CPU top. The CPU
// itself (mkModule1) is unchanged.
module thiele_cpu_top_genesys2 (
    input  sysclk,
    input  cpu_reset_n,
    output LED_HALTED,
    output LED_ERR,
    output LED_BIANCHI
);
    thiele_cpu_top inner (
        .CLK        (sysclk),
        .RST_N      (cpu_reset_n),
        .LED_HALTED (LED_HALTED),
        .LED_ERR    (LED_ERR),
        .LED_BIANCHI(LED_BIANCHI)
    );
endmodule
