// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb__Syms.h"
#include "Vthiele_cpu_kami_tb___024root.h"

VL_ATTR_COLD void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_static__TOP__thiele_cpu_kami_tb(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_static(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_static\n"); );
    // Body
    Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___eval_static__TOP__thiele_cpu_kami_tb((&vlSymsp->TOP__thiele_cpu_kami_tb));
    vlSelf->__Vm_traceActivity[6U] = 1U;
    vlSelf->__Vm_traceActivity[5U] = 1U;
    vlSelf->__Vm_traceActivity[4U] = 1U;
    vlSelf->__Vm_traceActivity[3U] = 1U;
    vlSelf->__Vm_traceActivity[2U] = 1U;
    vlSelf->__Vm_traceActivity[1U] = 1U;
    vlSelf->__Vm_traceActivity[0U] = 1U;
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__stl(Vthiele_cpu_kami_tb___024root* vlSelf);
#endif  // VL_DEBUG

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_triggers__stl(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_triggers__stl\n"); );
    // Body
    vlSelf->__VstlTriggered.set(0U, (IData)(vlSelf->__VstlFirstIteration));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        Vthiele_cpu_kami_tb___024root___dump_triggers__stl(vlSelf);
    }
#endif
}

VL_ATTR_COLD void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___stl_sequent__TOP__thiele_cpu_kami_tb__0(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
VL_ATTR_COLD void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___stl_sequent__TOP__thiele_cpu_kami_tb__1(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);
void Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__2(Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* vlSelf);

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_stl(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___stl_sequent__TOP__thiele_cpu_kami_tb__0((&vlSymsp->TOP__thiele_cpu_kami_tb));
        vlSelf->__Vm_traceActivity[6U] = 1U;
        vlSelf->__Vm_traceActivity[5U] = 1U;
        vlSelf->__Vm_traceActivity[4U] = 1U;
        vlSelf->__Vm_traceActivity[3U] = 1U;
        vlSelf->__Vm_traceActivity[2U] = 1U;
        vlSelf->__Vm_traceActivity[1U] = 1U;
        vlSelf->__Vm_traceActivity[0U] = 1U;
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___stl_sequent__TOP__thiele_cpu_kami_tb__1((&vlSymsp->TOP__thiele_cpu_kami_tb));
        Vthiele_cpu_kami_tb_thiele_cpu_kami_tb___act_comb__TOP__thiele_cpu_kami_tb__2((&vlSymsp->TOP__thiele_cpu_kami_tb));
    }
}
