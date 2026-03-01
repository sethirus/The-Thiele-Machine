// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb__Syms.h"
#include "Vthiele_cpu_kami_tb___024root.h"

VL_ATTR_COLD void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
VlCoroutine Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb__Vtiming__0(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
VlCoroutine Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb__Vtiming__1(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);

void Vthiele_cpu_kami_tb___024root___eval_initial(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_initial\n"); );
    // Body
    Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb((&vlSymsp->TOP__thiele_cpu_kami_tb));
    vlSelf->__Vm_traceActivity[1U] = 1U;
    Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb__Vtiming__0((&vlSymsp->TOP__thiele_cpu_kami_tb));
    Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_initial__TOP__thiele_cpu_kami_tb__Vtiming__1((&vlSymsp->TOP__thiele_cpu_kami_tb));
    vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb____PVT__clk__0 
        = vlSymsp->TOP__thiele_cpu_kami_tb.__PVT__clk;
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__act(Vthiele_cpu_kami_tb___024root* vlSelf);
#endif  // VL_DEBUG

void Vthiele_cpu_kami_tb___024root___eval_triggers__act(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, ((IData)(vlSymsp->TOP__thiele_cpu_kami_tb.__PVT__clk) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb____PVT__clk__0))));
    vlSelf->__VactTriggered.set(1U, ((~ (IData)(vlSymsp->TOP__thiele_cpu_kami_tb.__PVT__clk)) 
                                     & (IData)(vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb____PVT__clk__0)));
    vlSelf->__VactTriggered.set(2U, vlSelf->__VdlySched.awaitingCurrentTime());
    vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb____PVT__clk__0 
        = vlSymsp->TOP__thiele_cpu_kami_tb.__PVT__clk;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        Vthiele_cpu_kami_tb___024root___dump_triggers__act(vlSelf);
    }
#endif
}

void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__0(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__1(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__2(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);

void Vthiele_cpu_kami_tb___024root___eval_act(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_act\n"); );
    // Body
    if ((7ULL & vlSelf->__VactTriggered.word(0U))) {
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__0((&vlSymsp->TOP__thiele_cpu_kami_tb));
        vlSelf->__Vm_traceActivity[2U] = 1U;
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__1((&vlSymsp->TOP__thiele_cpu_kami_tb));
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__2((&vlSymsp->TOP__thiele_cpu_kami_tb));
    }
}

void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___nba_sequent__TOP__thiele_cpu_kami_tb__0(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___nba_comb__TOP__thiele_cpu_kami_tb__0(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);

void Vthiele_cpu_kami_tb___024root___eval_nba(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_nba\n"); );
    // Body
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___nba_sequent__TOP__thiele_cpu_kami_tb__0((&vlSymsp->TOP__thiele_cpu_kami_tb));
        vlSelf->__Vm_traceActivity[3U] = 1U;
    }
    if ((7ULL & vlSelf->__VnbaTriggered.word(0U))) {
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___nba_comb__TOP__thiele_cpu_kami_tb__0((&vlSymsp->TOP__thiele_cpu_kami_tb));
        vlSelf->__Vm_traceActivity[4U] = 1U;
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__1((&vlSymsp->TOP__thiele_cpu_kami_tb));
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__2((&vlSymsp->TOP__thiele_cpu_kami_tb));
    }
}
