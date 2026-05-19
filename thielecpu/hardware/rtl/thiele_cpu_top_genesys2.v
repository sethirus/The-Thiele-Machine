// thiele_cpu_top_genesys2.v — Genesys 2 (xc7k325t-ffg900-2) deployment wrapper.
//
// The canonical top wrapper `thiele_cpu_top` (in thiele_cpu_top_min.v) takes a
// single-ended CLK input. Genesys 2's only on-board clock source is a 200MHz
// LVDS pair on FPGA pins AD12/AD11; this wrapper converts that LVDS pair to
// single-ended via an `IBUFDS` primitive and feeds the inner wrapper.
//
// The wrapper layer is board-specific glue and sits OUTSIDE the Coq↔OCaml↔
// Kami↔BSC↔Verilog isomorphism chain — it just connects external pins to the
// canonical CPU top. The CPU itself (mkModule1) is unchanged.
//
// Why Kintex-7 K325T (not Artix-7 35T): yosys's DSP48E1 inference (enabled
// by removing -nodsp from synth_xc7.ys) maps `column_contractive_check_witness`'s
// ~20 integer multiplications per cycle (including two 128×128) onto ~771 DSP
// slices. The Arty A7-35T only has 90 DSP slices; Kintex-7 K325T has 840, with
// headroom. LUT utilization is ~33K (16% of K325T's 203K) — DSPs are the
// binding constraint, not LUTs.
module thiele_cpu_top_genesys2 (
    input  clk_p,
    input  clk_n,
    input  cpu_reset_n,
    output LED_HALTED,
    output LED_ERR,
    output LED_BIANCHI
);
    wire sysclk;
    IBUFDS #(
        .DIFF_TERM   ("FALSE"),
        .IBUF_LOW_PWR("FALSE"),
        .IOSTANDARD  ("LVDS")
    ) ibufds_sysclk (
        .I (clk_p),
        .IB(clk_n),
        .O (sysclk)
    );

    thiele_cpu_top inner (
        .CLK        (sysclk),
        .RST_N      (cpu_reset_n),
        .LED_HALTED (LED_HALTED),
        .LED_ERR    (LED_ERR),
        .LED_BIANCHI(LED_BIANCHI)
    );
endmodule
