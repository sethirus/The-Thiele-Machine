// thiele_cpu_top_genesys2.v: Genesys 2 (xc7k325t-ffg900-2) board wrapper.
//
// Everything the design computes is mkThieleSystem, extracted from the Coq
// model (coq/kami_hw/ThieleSystem.v): the CPU, the serial program loader,
// the status report, and the input synchronizer. This file holds only what
// cannot be extracted because it is a cell of this particular chip:
//
//   IBUFDS       converts the board's 200 MHz LVDS clock pair to one signal.
//   MMCME2_BASE  divides it to the 20 MHz CPU clock (200 * 5 / 50).
//   BUFGCE       passes that clock on only once the MMCM reports lock.
//
// The loader's bit time (ClksPerBit = 174 in ThieleLoader.v) is set for this
// 20 MHz clock: 115200 baud on the board's USB-UART bridge.
module thiele_cpu_top_genesys2 (
    input  clk_p,
    input  clk_n,
    input  cpu_reset_n,
    input  uart_rx,
    output uart_tx,
    output LED_HALTED,
    output LED_ERR,
    output LED_BIANCHI,
    output LED_LOADING
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
    BUFGCE bufg_cpu (.I(clk_20_unbuf), .CE(mmcm_locked), .O(cpu_clk));

    wire [3:0] leds;
    assign LED_HALTED  = leds[0];
    assign LED_ERR     = leds[1];
    assign LED_BIANCHI = leds[2];
    assign LED_LOADING = leds[3];

    mkThieleSystem system (
        .CLK          (cpu_clk),
        .RST_N        (cpu_reset_n),
        .rxSample_x_0 (uart_rx),
        .EN_rxSample  (1'b1),
        .RDY_rxSample (),
        .EN_getTx     (1'b1),
        .getTx        (uart_tx),
        .RDY_getTx    (),
        .EN_getLeds   (1'b1),
        .getLeds      (leds),
        .RDY_getLeds  ()
    );
endmodule
