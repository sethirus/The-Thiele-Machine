// thiele_cpu_top_genesys2.v — Genesys 2 (xc7k325t-ffg900-2) deployment wrapper.
//
// The canonical top wrapper `thiele_cpu_top` (in thiele_cpu_top_min.v) takes a
// single-ended CLK input. Genesys 2's only on-board clock source is a 200MHz
// LVDS pair on FPGA pins AD12/AD11. This wrapper converts that pair to
// single-ended via `IBUFDS`, and an MMCM divides it down to the 20MHz clock
// the CPU runs on. The design closes timing above 40MHz, so it can't take
// the 200MHz oscillator directly. The CPU clock buffer is enabled only once
// the MMCM reports lock.
//
// The wrapper layer is board-specific glue and sits OUTSIDE the Coq↔OCaml↔
// Kami↔BSC↔Verilog isomorphism chain — it just connects external pins to the
// canonical CPU top. The CPU itself (mkModule1) is unchanged.
module thiele_cpu_top_genesys2 (
    input  clk_p,
    input  clk_n,
    input  cpu_reset_n,
    output LED_HALTED,
    output LED_ERR,
    output LED_BIANCHI
);
    wire sysclk_200;
    IBUFDS #(
        .DIFF_TERM   ("FALSE"),
        .IBUF_LOW_PWR("FALSE"),
        .IOSTANDARD  ("LVDS")
    ) ibufds_sysclk (
        .I (clk_p),
        .IB(clk_n),
        .O (sysclk_200)
    );

    // 200MHz in, VCO = 200 * 5 / 1 = 1000MHz, CPU clock = 1000 / 50 = 20MHz.
    wire clkfb, clk_20_unbuf, cpu_clk, mmcm_locked;
    MMCME2_BASE #(
        .CLKIN1_PERIOD   (5.000),
        .CLKFBOUT_MULT_F (5.000),
        .DIVCLK_DIVIDE   (1),
        .CLKOUT0_DIVIDE_F(50.000)
    ) mmcm_cpu (
        .CLKIN1  (sysclk_200),
        .CLKFBIN (clkfb),
        .CLKFBOUT(clkfb),
        .CLKOUT0 (clk_20_unbuf),
        .LOCKED  (mmcm_locked),
        .PWRDWN  (1'b0),
        .RST     (1'b0)
    );
    // The clock buffer stays off until the MMCM locks, so the CPU sees no
    // clock edges until the 20MHz clock is stable.
    BUFGCE bufg_cpu (.I(clk_20_unbuf), .CE(mmcm_locked), .O(cpu_clk));

    thiele_cpu_top inner (
        .CLK        (cpu_clk),
        .RST_N      (cpu_reset_n),
        .LED_HALTED (LED_HALTED),
        .LED_ERR    (LED_ERR),
        .LED_BIANCHI(LED_BIANCHI)
    );
endmodule
