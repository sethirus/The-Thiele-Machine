// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb__Syms.h"
#include "Vthiele_cpu_kami_tb_thiele_cpu_kami_tb.h"

VL_INLINE_OPT VlCoroutine Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb__Vtiming__1(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+      Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb__Vtiming__1\n"); );
    // Body
    while (1U) {
        co_await vlSymsp->TOP.__VdlySched.delay(0x1388ULL, 
                                                nullptr, 
                                                "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                20);
        vlSelf->__PVT__clk = (1U & (~ (IData)(vlSelf->__PVT__clk)));
    }
}
