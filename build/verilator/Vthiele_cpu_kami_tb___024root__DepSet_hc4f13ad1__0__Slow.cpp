// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb___024root.h"

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_static__TOP(Vthiele_cpu_kami_tb___024root* vlSelf);

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_static(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_static\n"); );
    // Body
    Vthiele_cpu_kami_tb___024root___eval_static__TOP(vlSelf);
}

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_static__TOP(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_static__TOP\n"); );
    // Body
    vlSelf->thiele_cpu_kami_tb__DOT__clk = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__rst_n = 0U;
}

extern const VlWide<256>/*8191:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h159503b3_0;
extern const VlWide<16>/*511:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0;
extern const VlWide<32>/*1023:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0;
extern const VlWide<32>/*1023:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0;
extern const VlWide<256>/*8191:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h4ae14f6a_0;
extern const VlWide<16>/*511:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0;

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_initial__TOP(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_initial__TOP\n"); );
    // Body
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code = 0xaaaaaaaaU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted = 0U;
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem, Vthiele_cpu_kami_tb__ConstPool__CONST_h159503b3_0);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain = 0xaaaaaaaaU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops = 0xaaaaaaaaU;
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem, Vthiele_cpu_kami_tb__ConstPool__CONST_h159503b3_0);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu = 0xaaaaaaaaU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h13805816_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops = 0xaaaaaaaaU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc = 0xaaaaaaaaU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x10U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x10U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x11U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x11U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x12U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x12U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x13U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x13U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x14U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x14U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x15U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x15U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x16U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x16U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x17U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x17U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x18U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x18U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x19U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x19U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1aU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x1aU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1bU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x1bU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1cU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x1cU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1dU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x1dU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1eU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x1eU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1fU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h74ec5c45_0[0x1fU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x10U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x10U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x11U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x11U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x12U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x12U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x13U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x13U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x14U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x14U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x15U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x15U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x16U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x16U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x17U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x17U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x18U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x18U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x19U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x19U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1aU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1aU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1bU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1bU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1cU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1cU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1dU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1dU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1eU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1eU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1fU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1fU];
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn, Vthiele_cpu_kami_tb__ConstPool__CONST_h4ae14f6a_0);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xfU];
}

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_final(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_final\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__stl(Vthiele_cpu_kami_tb___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD bool Vthiele_cpu_kami_tb___024root___eval_phase__stl(Vthiele_cpu_kami_tb___024root* vlSelf);

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_settle(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_settle\n"); );
    // Init
    IData/*31:0*/ __VstlIterCount;
    CData/*0:0*/ __VstlContinue;
    // Body
    __VstlIterCount = 0U;
    vlSelf->__VstlFirstIteration = 1U;
    __VstlContinue = 1U;
    while (__VstlContinue) {
        if (VL_UNLIKELY((0x64U < __VstlIterCount))) {
#ifdef VL_DEBUG
            Vthiele_cpu_kami_tb___024root___dump_triggers__stl(vlSelf);
#endif
            VL_FATAL_MT("/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 12, "", "Settle region did not converge.");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        __VstlContinue = 0U;
        if (Vthiele_cpu_kami_tb___024root___eval_phase__stl(vlSelf)) {
            __VstlContinue = 1U;
        }
        vlSelf->__VstlFirstIteration = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__stl(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

void Vthiele_cpu_kami_tb___024root___act_comb__TOP__0(Vthiele_cpu_kami_tb___024root* vlSelf);
void Vthiele_cpu_kami_tb___024root___act_comb__TOP__1(Vthiele_cpu_kami_tb___024root* vlSelf);

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_stl(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        Vthiele_cpu_kami_tb___024root___act_comb__TOP__0(vlSelf);
        Vthiele_cpu_kami_tb___024root___act_comb__TOP__1(vlSelf);
    }
}

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_triggers__stl(Vthiele_cpu_kami_tb___024root* vlSelf);

VL_ATTR_COLD bool Vthiele_cpu_kami_tb___024root___eval_phase__stl(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_phase__stl\n"); );
    // Init
    CData/*0:0*/ __VstlExecute;
    // Body
    Vthiele_cpu_kami_tb___024root___eval_triggers__stl(vlSelf);
    __VstlExecute = vlSelf->__VstlTriggered.any();
    if (__VstlExecute) {
        Vthiele_cpu_kami_tb___024root___eval_stl(vlSelf);
    }
    return (__VstlExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__act(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VactTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 0 is active: @(posedge thiele_cpu_kami_tb.clk)\n");
    }
    if ((2ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 1 is active: @(negedge thiele_cpu_kami_tb.clk)\n");
    }
    if ((4ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 2 is active: @([true] __VdlySched.awaitingCurrentTime())\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___dump_triggers__nba(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge thiele_cpu_kami_tb.clk)\n");
    }
    if ((2ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 1 is active: @(negedge thiele_cpu_kami_tb.clk)\n");
    }
    if ((4ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 2 is active: @([true] __VdlySched.awaitingCurrentTime())\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___ctor_var_reset(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->thiele_cpu_kami_tb__DOT__clk = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__rst_n = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__load_data = VL_RAND_RESET_Q(40);
    vlSelf->thiele_cpu_kami_tb__DOT__load_en = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__pc_out = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__mu_out = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__partition_ops_out = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__mdl_ops_out = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__info_gain_out = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__error_code_out = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_0 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_1 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_2 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_3 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__err_out = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__halted_out = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 256; ++__Vi0) {
        vlSelf->thiele_cpu_kami_tb__DOT__instr_memory[__Vi0] = VL_RAND_RESET_I(32);
    }
    for (int __Vi0 = 0; __Vi0 < 256; ++__Vi0) {
        vlSelf->thiele_cpu_kami_tb__DOT__data_memory[__Vi0] = VL_RAND_RESET_I(32);
    }
    vlSelf->thiele_cpu_kami_tb__DOT__num_instrs = VL_RAND_RESET_I(32);
    for (int __Vi0 = 0; __Vi0 < 64; ++__Vi0) {
        vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[__Vi0] = VL_RAND_RESET_Q(64);
    }
    vlSelf->thiele_cpu_kami_tb__DOT__exec_op_i = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__sh_m = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__sh_left = VL_RAND_RESET_Q(64);
    vlSelf->thiele_cpu_kami_tb__DOT__sh_right = VL_RAND_RESET_Q(64);
    vlSelf->thiele_cpu_kami_tb__DOT__shadow_new_mask = VL_RAND_RESET_Q(64);
    vlSelf->thiele_cpu_kami_tb__DOT__first_bit = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__program_hex_path);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__data_hex_path);
    vlSelf->thiele_cpu_kami_tb__DOT__current_instr = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceVal = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__024D_IN = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__024EN = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceRd = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceVal = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceVal = VL_RAND_RESET_I(1);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__024D_IN = VL_RAND_RESET_I(1);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem__024D_IN);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceVal = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__024D_IN = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceVal = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__024D_IN = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceVal);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceVal = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__024D_IN = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(512, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor);
    VL_RAND_RESET_W(512, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd);
    VL_RAND_RESET_W(512, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn);
    VL_RAND_RESET_W(512, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal);
    VL_RAND_RESET_W(512, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__024D_IN);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceVal = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__024D_IN = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceVal = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq3);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d1233);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq2 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq4 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_47___05Fh66776 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_61___05Fh66790 = VL_RAND_RESET_I(32);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d1876);
    VL_RAND_RESET_W(8192, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_regs_68_BITS_999_TO_992_877_EQ_255_878_THEN_ETC___05F_d2517);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702);
    VL_RAND_RESET_W(1024, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d614 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_62___05Fh66791 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_63___05Fh66792 = VL_RAND_RESET_I(32);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_90___05Fh66811 = VL_RAND_RESET_I(32);
    vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb__DOT__clk__0 = VL_RAND_RESET_I(1);
}
