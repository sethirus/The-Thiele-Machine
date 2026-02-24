// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb__Syms.h"
#include "Vthiele_cpu_kami_tb___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__act(Vthiele_cpu_kami_tb___024root* vlSelf);
#endif  // VL_DEBUG

void Vthiele_cpu_kami_tb___024root___eval_triggers__act(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__clk) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb__DOT__clk__0))));
    vlSelf->__VactTriggered.set(1U, ((~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__clk)) 
                                     & (IData)(vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb__DOT__clk__0)));
    vlSelf->__VactTriggered.set(2U, vlSelf->__VdlySched.awaitingCurrentTime());
    vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb__DOT__clk__0 
        = vlSelf->thiele_cpu_kami_tb__DOT__clk;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        Vthiele_cpu_kami_tb___024root___dump_triggers__act(vlSelf);
    }
#endif
}
