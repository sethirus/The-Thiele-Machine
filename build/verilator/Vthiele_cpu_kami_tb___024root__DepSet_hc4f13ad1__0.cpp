// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb___024root.h"

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root___eval_initial__TOP(Vthiele_cpu_kami_tb___024root* vlSelf);
VlCoroutine Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__0(Vthiele_cpu_kami_tb___024root* vlSelf);
VlCoroutine Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__1(Vthiele_cpu_kami_tb___024root* vlSelf);

void Vthiele_cpu_kami_tb___024root___eval_initial(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_initial\n"); );
    // Body
    Vthiele_cpu_kami_tb___024root___eval_initial__TOP(vlSelf);
    Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__0(vlSelf);
    Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__1(vlSelf);
    vlSelf->__Vtrigprevexpr___TOP__thiele_cpu_kami_tb__DOT__clk__0 
        = vlSelf->thiele_cpu_kami_tb__DOT__clk;
}

extern const VlWide<256>/*8191:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h4ae14f6a_0;
extern const VlWide<32>/*1023:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0;
extern const VlWide<32>/*1023:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0;
extern const VlWide<256>/*8191:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h48f27eb7_0;
extern const VlWide<16>/*511:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0;
extern const VlWide<16>/*511:0*/ Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0;

VL_INLINE_OPT VlCoroutine Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__0(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__0\n"); );
    // Init
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__i;
    thiele_cpu_kami_tb__DOT__i = 0;
    IData/*31:0*/ __Vilp;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__cycle_count;
    thiele_cpu_kami_tb__DOT__cycle_count = 0;
    VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__mem_init_val;
    VL_ZERO_W(8192, thiele_cpu_kami_tb__DOT__mem_init_val);
    CData/*7:0*/ thiele_cpu_kami_tb__DOT__shadow_next_mid;
    thiele_cpu_kami_tb__DOT__shadow_next_mid = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__exec_word;
    thiele_cpu_kami_tb__DOT__exec_word = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__shadow_found_dup;
    thiele_cpu_kami_tb__DOT__shadow_found_dup = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__mod_j;
    thiele_cpu_kami_tb__DOT__mod_j = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__first_mod;
    thiele_cpu_kami_tb__DOT__first_mod = 0;
    CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd = 0;
    CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd = 0;
    VlWide<3>/*95:0*/ __Vtemp_2;
    VlWide<3>/*95:0*/ __Vtemp_3;
    VlWide<32>/*1023:0*/ __Vtemp_10;
    VlWide<256>/*8191:0*/ __Vtemp_14;
    VlWide<256>/*8191:0*/ __Vtemp_15;
    VlWide<256>/*8191:0*/ __Vtemp_16;
    VlWide<256>/*8191:0*/ __Vtemp_17;
    VlWide<16>/*511:0*/ __Vtemp_22;
    // Body
    thiele_cpu_kami_tb__DOT__i = 0U;
    while (VL_GTS_III(32, 0x100U, thiele_cpu_kami_tb__DOT__i)) {
        vlSelf->thiele_cpu_kami_tb__DOT__instr_memory[(0xffU 
                                                       & thiele_cpu_kami_tb__DOT__i)] = 0U;
        vlSelf->thiele_cpu_kami_tb__DOT__data_memory[(0xffU 
                                                      & thiele_cpu_kami_tb__DOT__i)] = 0U;
        thiele_cpu_kami_tb__DOT__i = ((IData)(1U) + thiele_cpu_kami_tb__DOT__i);
    }
    __Vilp = 0U;
    while ((__Vilp <= 0x3fU)) {
        vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[__Vilp] = 0ULL;
        __Vilp = ((IData)(1U) + __Vilp);
    }
    thiele_cpu_kami_tb__DOT__i = 0x40U;
    thiele_cpu_kami_tb__DOT__shadow_next_mid = 1U;
    thiele_cpu_kami_tb__DOT__exec_word = 0U;
    thiele_cpu_kami_tb__DOT__shadow_found_dup = 0U;
    __Vtemp_2[0U] = 0x4d3d2573U;
    __Vtemp_2[1U] = 0x4f475241U;
    __Vtemp_2[2U] = 0x5052U;
    if (VL_UNLIKELY(VL_VALUEPLUSARGS_INW(1024, VL_CVT_PACK_STR_NW(3, __Vtemp_2), 
                                         vlSelf->thiele_cpu_kami_tb__DOT__program_hex_path))) {
        VL_READMEM_N(true, 32, 256, 0, VL_CVT_PACK_STR_NW(32, vlSelf->thiele_cpu_kami_tb__DOT__program_hex_path)
                     ,  &(vlSelf->thiele_cpu_kami_tb__DOT__instr_memory)
                     , 0, ~0ULL);
    } else {
        vlSelf->thiele_cpu_kami_tb__DOT__instr_memory[0U] = 0xff000000U;
    }
    if (VL_UNLIKELY(VL_VALUEPLUSARGS_INW(1024, std::string{"DATA=%s"}, 
                                         vlSelf->thiele_cpu_kami_tb__DOT__data_hex_path))) {
        VL_READMEM_N(true, 32, 256, 0, VL_CVT_PACK_STR_NW(32, vlSelf->thiele_cpu_kami_tb__DOT__data_hex_path)
                     ,  &(vlSelf->thiele_cpu_kami_tb__DOT__data_memory)
                     , 0, ~0ULL);
    }
    __Vtemp_3[0U] = 0x533d2564U;
    __Vtemp_3[1U] = 0x4e535452U;
    __Vtemp_3[2U] = 0x4e5f49U;
    if ((! VL_VALUEPLUSARGS_INI(32, VL_CVT_PACK_STR_NW(3, __Vtemp_3), 
                                vlSelf->thiele_cpu_kami_tb__DOT__num_instrs))) {
        vlSelf->thiele_cpu_kami_tb__DOT__num_instrs = 0x100U;
    }
    vlSelf->thiele_cpu_kami_tb__DOT__rst_n = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__load_en = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__load_data = 0ULL;
    co_await vlSelf->__VtrigSched_he0995f9e__0.trigger(0U, 
                                                       nullptr, 
                                                       "@(posedge thiele_cpu_kami_tb.clk)", 
                                                       "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                       169);
    co_await vlSelf->__VtrigSched_he0995f9e__0.trigger(0U, 
                                                       nullptr, 
                                                       "@(posedge thiele_cpu_kami_tb.clk)", 
                                                       "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                       170);
    vlSelf->thiele_cpu_kami_tb__DOT__rst_n = 1U;
    thiele_cpu_kami_tb__DOT__i = 0U;
    while (VL_LTS_III(32, thiele_cpu_kami_tb__DOT__i, vlSelf->thiele_cpu_kami_tb__DOT__num_instrs)) {
        vlSelf->thiele_cpu_kami_tb__DOT__load_data 
            = (((QData)((IData)((0xffU & thiele_cpu_kami_tb__DOT__i))) 
                << 0x20U) | (QData)((IData)(vlSelf->thiele_cpu_kami_tb__DOT__instr_memory
                                            [(0xffU 
                                              & thiele_cpu_kami_tb__DOT__i)])));
        vlSelf->thiele_cpu_kami_tb__DOT__load_en = 1U;
        co_await vlSelf->__VtrigSched_he0995f9e__0.trigger(0U, 
                                                           nullptr, 
                                                           "@(posedge thiele_cpu_kami_tb.clk)", 
                                                           "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                           177);
        thiele_cpu_kami_tb__DOT__i = ((IData)(1U) + thiele_cpu_kami_tb__DOT__i);
    }
    vlSelf->thiele_cpu_kami_tb__DOT__load_en = 0U;
    VL_ASSIGN_W(8192,thiele_cpu_kami_tb__DOT__mem_init_val, Vthiele_cpu_kami_tb__ConstPool__CONST_h4ae14f6a_0);
    thiele_cpu_kami_tb__DOT__i = 0U;
    while (VL_GTS_III(32, 0x100U, thiele_cpu_kami_tb__DOT__i)) {
        VL_ASSIGNSEL_WI(8192,32,(0x1fffU & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i)), thiele_cpu_kami_tb__DOT__mem_init_val, 
                        vlSelf->thiele_cpu_kami_tb__DOT__data_memory
                        [(0xffU & thiele_cpu_kami_tb__DOT__i)]);
        thiele_cpu_kami_tb__DOT__i = ((IData)(1U) + thiele_cpu_kami_tb__DOT__i);
    }
    co_await vlSelf->__VtrigSched_he099605b__0.trigger(0U, 
                                                       nullptr, 
                                                       "@(negedge thiele_cpu_kami_tb.clk)", 
                                                       "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                       192);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn = 0xffffffffU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceVal = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn = 0xffffffffU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceVal = 0U;
    thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn = 1U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceVal = 0U;
    thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn = 1U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceVal = 0U;
    thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x10U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x10U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x11U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x11U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x12U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x12U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x13U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x13U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x14U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x14U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x15U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x15U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x16U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x16U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x17U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x17U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x18U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x18U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x19U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x19U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1aU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x1aU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1bU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x1bU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1cU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x1cU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1dU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x1dU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1eU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x1eU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1fU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_ha6258237_0[0x1fU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x10U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x10U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x11U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x11U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x12U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x12U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x13U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x13U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x14U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x14U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x15U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x15U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x16U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x16U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x17U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x17U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x18U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x18U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x19U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x19U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1aU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1aU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1bU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1bU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1cU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1cU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1dU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1dU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1eU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1eU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1fU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1fU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x10U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x11U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x12U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x13U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x14U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x15U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x16U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x17U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x18U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x19U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1aU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1bU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1cU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1dU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1eU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_hd6b7ba52_0[0x1fU];
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn, Vthiele_cpu_kami_tb__ConstPool__CONST_h48f27eb7_0);
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceVal, thiele_cpu_kami_tb__DOT__mem_init_val);
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd, thiele_cpu_kami_tb__DOT__mem_init_val);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn = 0xffffffffU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceVal = 0U;
    thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn = 0xffffffffU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceVal = 0U;
    thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn = 0xffffffffU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceVal = 0U;
    thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn = 0xffffffffU;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceVal = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceRd = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h8b2d9f06_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[1U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[2U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[3U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[4U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[5U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[6U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[7U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[8U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[9U] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xaU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xbU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xcU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xdU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xeU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xfU] 
        = Vthiele_cpu_kami_tb__ConstPool__CONST_h93e1b771_0[0xfU];
    co_await vlSelf->__VtrigSched_he0995f9e__0.trigger(0U, 
                                                       nullptr, 
                                                       "@(posedge thiele_cpu_kami_tb.clk)", 
                                                       "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                       204);
    co_await vlSelf->__VtrigSched_he099605b__0.trigger(0U, 
                                                       nullptr, 
                                                       "@(negedge thiele_cpu_kami_tb.clk)", 
                                                       "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                       205);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc = 
        ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn 
          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceVal) 
         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn) 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu = 
        ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn 
          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceVal) 
         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn) 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err 
        = ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn)
            ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceVal)
            : (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted 
        = ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn)
            ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceVal)
            : (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn = 0U;
    __Vtemp_10[1U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[1U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[1U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[1U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[1U]));
    __Vtemp_10[2U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[2U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[2U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[2U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[2U]));
    __Vtemp_10[3U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[3U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[3U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[3U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[3U]));
    __Vtemp_10[4U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[4U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[4U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[4U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[4U]));
    __Vtemp_10[5U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[5U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[5U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[5U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[5U]));
    __Vtemp_10[6U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[6U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[6U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[6U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[6U]));
    __Vtemp_10[7U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[7U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[7U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[7U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[7U]));
    __Vtemp_10[8U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[8U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[8U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[8U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[8U]));
    __Vtemp_10[9U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[9U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[9U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[9U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[9U]));
    __Vtemp_10[0xaU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xaU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xaU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xaU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xaU]));
    __Vtemp_10[0xbU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xbU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xbU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xbU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xbU]));
    __Vtemp_10[0xcU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xcU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xcU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xcU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xcU]));
    __Vtemp_10[0xdU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xdU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xdU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xdU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xdU]));
    __Vtemp_10[0xeU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xeU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xeU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xeU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xeU]));
    __Vtemp_10[0xfU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xfU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xfU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xfU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xfU]));
    __Vtemp_10[0x10U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x10U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x10U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x10U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x10U]));
    __Vtemp_10[0x11U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x11U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x11U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x11U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x11U]));
    __Vtemp_10[0x12U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x12U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x12U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x12U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x12U]));
    __Vtemp_10[0x13U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x13U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x13U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x13U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x13U]));
    __Vtemp_10[0x14U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x14U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x14U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x14U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x14U]));
    __Vtemp_10[0x15U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x15U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x15U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x15U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x15U]));
    __Vtemp_10[0x16U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x16U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x16U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x16U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x16U]));
    __Vtemp_10[0x17U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x17U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x17U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x17U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x17U]));
    __Vtemp_10[0x18U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x18U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x18U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x18U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x18U]));
    __Vtemp_10[0x19U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x19U] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x19U]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x19U]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x19U]));
    __Vtemp_10[0x1aU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1aU] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1aU]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1aU]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1aU]));
    __Vtemp_10[0x1bU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1bU] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1bU]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1bU]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1bU]));
    __Vtemp_10[0x1cU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1cU] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1cU]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1cU]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1cU]));
    __Vtemp_10[0x1dU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1dU] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1dU]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1dU]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1dU]));
    __Vtemp_10[0x1eU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1eU] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1eU]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1eU]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1eU]));
    __Vtemp_10[0x1fU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1fU] 
                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1fU]) 
                         | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1fU]) 
                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1fU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[1U] 
        = __Vtemp_10[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[2U] 
        = __Vtemp_10[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[3U] 
        = __Vtemp_10[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[4U] 
        = __Vtemp_10[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[5U] 
        = __Vtemp_10[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[6U] 
        = __Vtemp_10[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[7U] 
        = __Vtemp_10[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[8U] 
        = __Vtemp_10[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[9U] 
        = __Vtemp_10[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xaU] 
        = __Vtemp_10[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xbU] 
        = __Vtemp_10[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xcU] 
        = __Vtemp_10[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xdU] 
        = __Vtemp_10[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xeU] 
        = __Vtemp_10[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xfU] 
        = __Vtemp_10[0xfU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x10U] 
        = __Vtemp_10[0x10U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x11U] 
        = __Vtemp_10[0x11U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x12U] 
        = __Vtemp_10[0x12U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x13U] 
        = __Vtemp_10[0x13U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x14U] 
        = __Vtemp_10[0x14U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x15U] 
        = __Vtemp_10[0x15U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x16U] 
        = __Vtemp_10[0x16U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x17U] 
        = __Vtemp_10[0x17U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x18U] 
        = __Vtemp_10[0x18U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x19U] 
        = __Vtemp_10[0x19U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1aU] 
        = __Vtemp_10[0x1aU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1bU] 
        = __Vtemp_10[0x1bU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1cU] 
        = __Vtemp_10[0x1cU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1dU] 
        = __Vtemp_10[0x1dU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1eU] 
        = __Vtemp_10[0x1eU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1fU] 
        = __Vtemp_10[0x1fU];
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
    VL_AND_W(256, __Vtemp_15, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceVal);
    VL_NOT_W(256, __Vtemp_16, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn);
    VL_AND_W(256, __Vtemp_17, __Vtemp_16, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem);
    VL_OR_W(256, __Vtemp_14, __Vtemp_15, __Vtemp_17);
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem, __Vtemp_14);
    VL_ASSIGN_W(8192,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn, Vthiele_cpu_kami_tb__ConstPool__CONST_h4ae14f6a_0);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn = 0U;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn = 0U;
    __Vtemp_22[1U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[1U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[1U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[1U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[1U]));
    __Vtemp_22[2U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[2U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[2U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[2U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[2U]));
    __Vtemp_22[3U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[3U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[3U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[3U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[3U]));
    __Vtemp_22[4U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[4U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[4U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[4U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[4U]));
    __Vtemp_22[5U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[5U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[5U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[5U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[5U]));
    __Vtemp_22[6U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[6U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[6U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[6U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[6U]));
    __Vtemp_22[7U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[7U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[7U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[7U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[7U]));
    __Vtemp_22[8U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[8U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[8U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[8U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[8U]));
    __Vtemp_22[9U] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[9U] 
                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[9U]) 
                      | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[9U]) 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[9U]));
    __Vtemp_22[0xaU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xaU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xaU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xaU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xaU]));
    __Vtemp_22[0xbU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xbU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xbU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xbU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xbU]));
    __Vtemp_22[0xcU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xcU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xcU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xcU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xcU]));
    __Vtemp_22[0xdU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xdU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xdU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xdU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xdU]));
    __Vtemp_22[0xeU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xeU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xeU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xeU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xeU]));
    __Vtemp_22[0xfU] = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xfU] 
                         & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xfU]) 
                        | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xfU]) 
                           & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xfU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[1U] 
        = __Vtemp_22[1U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[2U] 
        = __Vtemp_22[2U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[3U] 
        = __Vtemp_22[3U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[4U] 
        = __Vtemp_22[4U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[5U] 
        = __Vtemp_22[5U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[6U] 
        = __Vtemp_22[6U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[7U] 
        = __Vtemp_22[7U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[8U] 
        = __Vtemp_22[8U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[9U] 
        = __Vtemp_22[9U];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xaU] 
        = __Vtemp_22[0xaU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xbU] 
        = __Vtemp_22[0xbU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xcU] 
        = __Vtemp_22[0xcU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xdU] 
        = __Vtemp_22[0xdU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xeU] 
        = __Vtemp_22[0xeU];
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xfU] 
        = __Vtemp_22[0xfU];
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
    thiele_cpu_kami_tb__DOT__cycle_count = 0U;
    while ((((~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__halted_out)) 
             & (~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__err_out))) 
            & VL_GTS_III(32, 0x2710U, thiele_cpu_kami_tb__DOT__cycle_count))) {
        thiele_cpu_kami_tb__DOT__exec_word = (((0U 
                                                == 
                                                (0x1fU 
                                                 & VL_SHIFTL_III(13,32,32, 
                                                                 (0xffU 
                                                                  & vlSelf->thiele_cpu_kami_tb__DOT__pc_out), 5U)))
                                                ? 0U
                                                : (
                                                   vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[
                                                   (((IData)(0x1fU) 
                                                     + 
                                                     (0x1fffU 
                                                      & VL_SHIFTL_III(13,32,32, 
                                                                      (0xffU 
                                                                       & vlSelf->thiele_cpu_kami_tb__DOT__pc_out), 5U))) 
                                                    >> 5U)] 
                                                   << 
                                                   ((IData)(0x20U) 
                                                    - 
                                                    (0x1fU 
                                                     & VL_SHIFTL_III(13,32,32, 
                                                                     (0xffU 
                                                                      & vlSelf->thiele_cpu_kami_tb__DOT__pc_out), 5U))))) 
                                              | (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[
                                                 (0xffU 
                                                  & (VL_SHIFTL_III(13,32,32, 
                                                                   (0xffU 
                                                                    & vlSelf->thiele_cpu_kami_tb__DOT__pc_out), 5U) 
                                                     >> 5U))] 
                                                 >> 
                                                 (0x1fU 
                                                  & VL_SHIFTL_III(13,32,32, 
                                                                  (0xffU 
                                                                   & vlSelf->thiele_cpu_kami_tb__DOT__pc_out), 5U))));
        co_await vlSelf->__VtrigSched_he0995f9e__0.trigger(0U, 
                                                           nullptr, 
                                                           "@(posedge thiele_cpu_kami_tb.clk)", 
                                                           "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                                           225);
        thiele_cpu_kami_tb__DOT__cycle_count = ((IData)(1U) 
                                                + thiele_cpu_kami_tb__DOT__cycle_count);
        vlSelf->thiele_cpu_kami_tb__DOT__exec_op_i 
            = (thiele_cpu_kami_tb__DOT__exec_word >> 0x18U);
        vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i = 
            (0xffU & (thiele_cpu_kami_tb__DOT__exec_word 
                      >> 0x10U));
        vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i = 
            (0xffU & (thiele_cpu_kami_tb__DOT__exec_word 
                      >> 8U));
        if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__exec_op_i)) {
            vlSelf->thiele_cpu_kami_tb__DOT__shadow_new_mask 
                = VL_SHIFTL_QQI(64,64,32, 1ULL, (0x3fU 
                                                 & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i));
            thiele_cpu_kami_tb__DOT__shadow_found_dup = 0U;
            vlSelf->thiele_cpu_kami_tb__DOT__sh_m = 1U;
            while ((vlSelf->thiele_cpu_kami_tb__DOT__sh_m 
                    < (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))) {
                if ((vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                     [(0x3fU & vlSelf->thiele_cpu_kami_tb__DOT__sh_m)] 
                     == vlSelf->thiele_cpu_kami_tb__DOT__shadow_new_mask)) {
                    thiele_cpu_kami_tb__DOT__shadow_found_dup = 1U;
                }
                vlSelf->thiele_cpu_kami_tb__DOT__sh_m 
                    = ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__sh_m);
            }
            if (((~ (IData)((0U != thiele_cpu_kami_tb__DOT__shadow_found_dup))) 
                 & (0x40U > (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)))) {
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))] 
                    = vlSelf->thiele_cpu_kami_tb__DOT__shadow_new_mask;
                thiele_cpu_kami_tb__DOT__shadow_next_mid 
                    = (0xffU & ((IData)(1U) + (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)));
            }
        } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__exec_op_i)) {
            if ((((vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i 
                   < (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)) 
                  & (vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i 
                     < (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))) 
                 & (0x40U > (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)))) {
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))] 
                    = (vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                       [(0x3fU & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)] 
                       | vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                       [(0x3fU & vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i)]);
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)] = 0ULL;
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i)] = 0ULL;
                thiele_cpu_kami_tb__DOT__shadow_next_mid 
                    = (0xffU & ((IData)(1U) + (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)));
            }
        } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__exec_op_i)) {
            if (((vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i 
                  < (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)) 
                 & (0x40U > ((IData)(1U) + (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))))) {
                vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i 
                    = (3U & VL_SHIFTR_III(32,32,32, vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i, 6U));
                vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i 
                    = (0x3fU & vlSelf->thiele_cpu_kami_tb__DOT__exec_b_i);
                vlSelf->thiele_cpu_kami_tb__DOT__sh_left = 0ULL;
                vlSelf->thiele_cpu_kami_tb__DOT__sh_right = 0ULL;
                if ((0U != (1ULL & vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                            [(0x3fU & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)]))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (1ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (1ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (1ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (1ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)
                                ? (1ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right)
                                : (1ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right));
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 1U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 1U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 1U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (2ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 2U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 2U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 2U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (4ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 3U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 3U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 3U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (8ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 4U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 4U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 4U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x10ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 5U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 5U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 5U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x20ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 6U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 6U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 6U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x40ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 7U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 7U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 7U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x80ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 8U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 8U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 8U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x100ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 9U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 9U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 9U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x200ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0xaU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0xaU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0xaU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x400ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0xbU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0xbU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0xbU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x800ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0xcU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0xcU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0xcU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x1000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0xdU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0xdU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0xdU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x2000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0xeU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0xeU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0xeU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x4000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0xfU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0xfU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0xfU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x8000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x10U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x10U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x10U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x10000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x11U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x11U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x11U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x20000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x12U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x12U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x12U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x40000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x13U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x13U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x13U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x80000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x14U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x14U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x14U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x100000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x15U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x15U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x15U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x200000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x16U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x16U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x16U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x400000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x17U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x17U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x17U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x800000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x18U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x18U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x18U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x1000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x19U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x19U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x19U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x2000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x1aU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x1aU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x1aU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x4000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x1bU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x1bU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x1bU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x8000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x1cU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x1cU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x1cU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x10000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x1dU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x1dU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x1dU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x20000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x1eU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x1eU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x1eU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x40000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x1fU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x1fU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x1fU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x80000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x20U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x20U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x20U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x100000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x21U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x21U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x21U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x200000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x22U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x22U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x22U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x400000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x23U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x23U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x23U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x800000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x24U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x24U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x24U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x1000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x25U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x25U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x25U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x2000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x26U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x26U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x26U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x4000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x27U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x27U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x27U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x8000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x28U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x28U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x28U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x10000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x29U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x29U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x29U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x20000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x2aU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x2aU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x2aU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x40000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x2bU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x2bU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x2bU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x80000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x2cU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x2cU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x2cU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x100000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x2dU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x2dU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x2dU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x200000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x2eU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x2eU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x2eU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x400000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x2fU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x2fU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x2fU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x800000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x30U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x30U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x30U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x1000000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x31U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x31U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x31U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x2000000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x32U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x32U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x32U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x4000000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x33U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x33U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x33U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x8000000000000ULL | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x34U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x34U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x34U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x10000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x10000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x10000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x35U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x35U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x35U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x20000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x20000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x20000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x36U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x36U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x36U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x40000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x40000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x40000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x37U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x37U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x37U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x80000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x80000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x80000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x38U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x38U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x38U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x100000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x100000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x100000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x39U)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x39U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x39U, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x200000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x200000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x200000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x3aU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x3aU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x3aU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x400000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x400000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x400000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x3bU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x3bU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x3bU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x800000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x800000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x800000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x3cU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x3cU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x3cU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x1000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x1000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x1000000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x3dU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x3dU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x3dU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x2000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x2000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x2000000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x3eU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x3eU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x3eU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x4000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x4000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x4000000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                if ((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                 [(0x3fU 
                                                   & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)], 0x3fU)))) {
                    if ((0U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((1U == (1U & vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((1U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if (VL_GTES_III(32, 0x3fU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else if ((2U == vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_mode_i)) {
                        if ((0U != (1U & VL_SHIFTR_III(32,32,32, 0x3fU, vlSelf->thiele_cpu_kami_tb__DOT__sh_pred_param_i)))) {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_left 
                                = (0x8000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_left);
                        } else {
                            vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                                = (0x8000000000000000ULL 
                                   | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                        }
                    } else {
                        vlSelf->thiele_cpu_kami_tb__DOT__sh_right 
                            = (0x8000000000000000ULL 
                               | vlSelf->thiele_cpu_kami_tb__DOT__sh_right);
                    }
                }
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))] 
                    = vlSelf->thiele_cpu_kami_tb__DOT__sh_left;
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & ((IData)(1U) 
                                                                  + (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)))] 
                    = vlSelf->thiele_cpu_kami_tb__DOT__sh_right;
                vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks[(0x3fU 
                                                               & vlSelf->thiele_cpu_kami_tb__DOT__exec_a_i)] = 0ULL;
                thiele_cpu_kami_tb__DOT__shadow_next_mid 
                    = (0xffU & ((IData)(2U) + (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid)));
            }
        }
        if (VL_UNLIKELY((9U == (vlSelf->thiele_cpu_kami_tb__DOT__current_instr 
                                >> 0x18U)))) {
            VL_WRITEF("CHSH_TRIAL %0# %0# %0# %0#\n",
                      1,(1U & (vlSelf->thiele_cpu_kami_tb__DOT__current_instr 
                               >> 0x11U)),1,(1U & (vlSelf->thiele_cpu_kami_tb__DOT__current_instr 
                                                   >> 0x10U)),
                      1,(1U & (vlSelf->thiele_cpu_kami_tb__DOT__current_instr 
                               >> 9U)),1,(1U & (vlSelf->thiele_cpu_kami_tb__DOT__current_instr 
                                                >> 8U)));
        }
    }
    co_await vlSelf->__VdlySched.delay(0x3e8ULL, nullptr, 
                                       "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                       306);
    VL_WRITEF("{\n  \"status\": %0#,\n  \"error_code\": %0#,\n  \"partition_ops\": %0#,\n  \"mdl_ops\": %0#,\n  \"info_gain\": %0#,\n  \"mu\": %0#,\n  \"mu_tensor_0\": %0#,\n  \"mu_tensor_1\": %0#,\n  \"mu_tensor_2\": %0#,\n  \"mu_tensor_3\": %0#,\n  \"bianchi_alarm\": %0#,\n  \"cycles\": %0d,\n  \"pc\": %0#,\n  \"err\": %0#,\n  \"regs\": [\n    %0#,\n",
              32,((IData)(vlSelf->thiele_cpu_kami_tb__DOT__halted_out)
                   ? 2U : ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__err_out)
                            ? 3U : 0U)),32,vlSelf->thiele_cpu_kami_tb__DOT__error_code_out,
              32,vlSelf->thiele_cpu_kami_tb__DOT__partition_ops_out,
              32,vlSelf->thiele_cpu_kami_tb__DOT__mdl_ops_out,
              32,vlSelf->thiele_cpu_kami_tb__DOT__info_gain_out,
              32,vlSelf->thiele_cpu_kami_tb__DOT__mu_out,
              32,vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_0,
              32,vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_1,
              32,vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_2,
              32,vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_3,
              1,(IData)(vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out),
              32,thiele_cpu_kami_tb__DOT__cycle_count,
              32,vlSelf->thiele_cpu_kami_tb__DOT__pc_out,
              1,(IData)(vlSelf->thiele_cpu_kami_tb__DOT__err_out),
              32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U]);
    thiele_cpu_kami_tb__DOT__i = 1U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]);
    thiele_cpu_kami_tb__DOT__i = 2U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U]);
    thiele_cpu_kami_tb__DOT__i = 3U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]);
    thiele_cpu_kami_tb__DOT__i = 4U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]);
    thiele_cpu_kami_tb__DOT__i = 5U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]);
    thiele_cpu_kami_tb__DOT__i = 6U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U]);
    thiele_cpu_kami_tb__DOT__i = 7U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]);
    thiele_cpu_kami_tb__DOT__i = 8U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U]);
    thiele_cpu_kami_tb__DOT__i = 9U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]);
    thiele_cpu_kami_tb__DOT__i = 0xaU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU]);
    thiele_cpu_kami_tb__DOT__i = 0xbU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]);
    thiele_cpu_kami_tb__DOT__i = 0xcU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]);
    thiele_cpu_kami_tb__DOT__i = 0xdU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]);
    thiele_cpu_kami_tb__DOT__i = 0xeU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU]);
    thiele_cpu_kami_tb__DOT__i = 0xfU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]);
    thiele_cpu_kami_tb__DOT__i = 0x10U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U]);
    thiele_cpu_kami_tb__DOT__i = 0x11U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U]);
    thiele_cpu_kami_tb__DOT__i = 0x12U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U]);
    thiele_cpu_kami_tb__DOT__i = 0x13U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U]);
    thiele_cpu_kami_tb__DOT__i = 0x14U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U]);
    thiele_cpu_kami_tb__DOT__i = 0x15U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U]);
    thiele_cpu_kami_tb__DOT__i = 0x16U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U]);
    thiele_cpu_kami_tb__DOT__i = 0x17U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U]);
    thiele_cpu_kami_tb__DOT__i = 0x18U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U]);
    thiele_cpu_kami_tb__DOT__i = 0x19U;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U]);
    thiele_cpu_kami_tb__DOT__i = 0x1aU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU]);
    thiele_cpu_kami_tb__DOT__i = 0x1bU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU]);
    thiele_cpu_kami_tb__DOT__i = 0x1cU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU]);
    thiele_cpu_kami_tb__DOT__i = 0x1dU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU]);
    thiele_cpu_kami_tb__DOT__i = 0x1eU;
    VL_WRITEF("    %0#,\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU]);
    thiele_cpu_kami_tb__DOT__i = 0x1fU;
    VL_WRITEF("    %0#\n",32,vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]);
    thiele_cpu_kami_tb__DOT__i = 0x20U;
    VL_WRITEF("  ],\n  \"mem\": [\n");
    thiele_cpu_kami_tb__DOT__i = 0U;
    while (VL_GTS_III(32, 0x100U, thiele_cpu_kami_tb__DOT__i)) {
        if (VL_GTS_III(32, 0xffU, thiele_cpu_kami_tb__DOT__i)) {
            VL_WRITEF("    %0#,\n",32,(((0U == (0x1fU 
                                                & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i)))
                                         ? 0U : (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[
                                                 (((IData)(0x1fU) 
                                                   + 
                                                   (0x1fffU 
                                                    & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i))) 
                                                  >> 5U)] 
                                                 << 
                                                 ((IData)(0x20U) 
                                                  - 
                                                  (0x1fU 
                                                   & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i))))) 
                                       | (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[
                                          (0xffU & 
                                           (VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i) 
                                            >> 5U))] 
                                          >> (0x1fU 
                                              & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i)))));
        } else {
            VL_WRITEF("    %0#\n",32,(((0U == (0x1fU 
                                               & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i)))
                                        ? 0U : (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[
                                                (((IData)(0x1fU) 
                                                  + 
                                                  (0x1fffU 
                                                   & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i))) 
                                                 >> 5U)] 
                                                << 
                                                ((IData)(0x20U) 
                                                 - 
                                                 (0x1fU 
                                                  & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i))))) 
                                      | (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[
                                         (0xffU & (
                                                   VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i) 
                                                   >> 5U))] 
                                         >> (0x1fU 
                                             & VL_MULS_III(32, (IData)(0x20U), thiele_cpu_kami_tb__DOT__i)))));
        }
        thiele_cpu_kami_tb__DOT__i = ((IData)(1U) + thiele_cpu_kami_tb__DOT__i);
    }
    VL_WRITEF("  ],\n  \"modules\": [");
    thiele_cpu_kami_tb__DOT__first_mod = 1U;
    thiele_cpu_kami_tb__DOT__mod_j = 1U;
    while ((thiele_cpu_kami_tb__DOT__mod_j < (IData)(thiele_cpu_kami_tb__DOT__shadow_next_mid))) {
        if (VL_UNLIKELY((0ULL != vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                         [(0x3fU & thiele_cpu_kami_tb__DOT__mod_j)]))) {
            if (VL_UNLIKELY((1U & (~ (IData)((0U != thiele_cpu_kami_tb__DOT__first_mod)))))) {
                VL_WRITEF(", ");
            }
            VL_WRITEF("{\"id\": %0d, \"region\": [",
                      32,thiele_cpu_kami_tb__DOT__mod_j);
            vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 1U;
            if (VL_UNLIKELY((0U != (1ULL & vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                    [(0x3fU & thiele_cpu_kami_tb__DOT__mod_j)])))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("0");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 1U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("1");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 2U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("2");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 3U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("3");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 4U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("4");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 5U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("5");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 6U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("6");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 7U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("7");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 8U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("8");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 9U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("9");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0xaU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("10");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0xbU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("11");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0xcU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("12");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0xdU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("13");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0xeU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("14");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0xfU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("15");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x10U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("16");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x11U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("17");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x12U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("18");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x13U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("19");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x14U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("20");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x15U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("21");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x16U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("22");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x17U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("23");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x18U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("24");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x19U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("25");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x1aU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("26");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x1bU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("27");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x1cU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("28");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x1dU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("29");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x1eU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("30");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x1fU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("31");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x20U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("32");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x21U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("33");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x22U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("34");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x23U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("35");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x24U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("36");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x25U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("37");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x26U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("38");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x27U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("39");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x28U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("40");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x29U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("41");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x2aU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("42");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x2bU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("43");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x2cU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("44");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x2dU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("45");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x2eU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("46");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x2fU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("47");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x30U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("48");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x31U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("49");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x32U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("50");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x33U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("51");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x34U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("52");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x35U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("53");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x36U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("54");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x37U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("55");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x38U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("56");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x39U))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("57");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x3aU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("58");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x3bU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("59");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x3cU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("60");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x3dU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("61");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x3eU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("62");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            if (VL_UNLIKELY((0U != (1ULL & VL_SHIFTR_QQI(64,64,32, 
                                                         vlSelf->thiele_cpu_kami_tb__DOT__shadow_masks
                                                         [
                                                         (0x3fU 
                                                          & thiele_cpu_kami_tb__DOT__mod_j)], 0x3fU))))) {
                if (VL_UNLIKELY((1U & (~ (IData)((0U 
                                                  != vlSelf->thiele_cpu_kami_tb__DOT__first_bit)))))) {
                    VL_WRITEF(", ");
                }
                VL_WRITEF("63");
                vlSelf->thiele_cpu_kami_tb__DOT__first_bit = 0U;
            }
            VL_WRITEF("]}");
            thiele_cpu_kami_tb__DOT__first_mod = 0U;
        }
        thiele_cpu_kami_tb__DOT__mod_j = ((IData)(1U) 
                                          + thiele_cpu_kami_tb__DOT__mod_j);
    }
    VL_WRITEF("]\n}\n");
    VL_FINISH_MT("/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 368, "");
}

VL_INLINE_OPT VlCoroutine Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__1(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___eval_initial__TOP__Vtiming__1\n"); );
    // Body
    while (1U) {
        co_await vlSelf->__VdlySched.delay(0x1388ULL, 
                                           nullptr, 
                                           "/workspaces/The-Thiele-Machine/thielecpu/hardware/testbench/thiele_cpu_kami_tb.v", 
                                           20);
        vlSelf->thiele_cpu_kami_tb__DOT__clk = (1U 
                                                & (~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__clk)));
    }
}

VL_INLINE_OPT void Vthiele_cpu_kami_tb___024root___act_comb__TOP__0(Vthiele_cpu_kami_tb___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vthiele_cpu_kami_tb___024root___act_comb__TOP__0\n"); );
    // Init
    CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd = 0;
    CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd;
    thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_45___05Fh66774;
    thiele_cpu_kami_tb__DOT__dut__DOT__x_45___05Fh66774 = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_46___05Fh66775;
    thiele_cpu_kami_tb__DOT__dut__DOT__x_46___05Fh66775 = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781;
    thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781 = 0;
    IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_89___05Fh66810;
    thiele_cpu_kami_tb__DOT__dut__DOT__x_89___05Fh66810 = 0;
    VlWide<64>/*2047:0*/ __Vtemp_62;
    VlWide<65>/*2079:0*/ __Vtemp_63;
    VlWide<66>/*2111:0*/ __Vtemp_64;
    VlWide<67>/*2143:0*/ __Vtemp_65;
    VlWide<68>/*2175:0*/ __Vtemp_66;
    VlWide<69>/*2207:0*/ __Vtemp_67;
    VlWide<70>/*2239:0*/ __Vtemp_68;
    VlWide<71>/*2271:0*/ __Vtemp_69;
    VlWide<72>/*2303:0*/ __Vtemp_70;
    VlWide<73>/*2335:0*/ __Vtemp_71;
    VlWide<74>/*2367:0*/ __Vtemp_72;
    VlWide<75>/*2399:0*/ __Vtemp_73;
    VlWide<76>/*2431:0*/ __Vtemp_74;
    VlWide<77>/*2463:0*/ __Vtemp_75;
    VlWide<78>/*2495:0*/ __Vtemp_76;
    VlWide<79>/*2527:0*/ __Vtemp_77;
    VlWide<80>/*2559:0*/ __Vtemp_78;
    VlWide<81>/*2591:0*/ __Vtemp_79;
    VlWide<82>/*2623:0*/ __Vtemp_80;
    VlWide<83>/*2655:0*/ __Vtemp_81;
    VlWide<84>/*2687:0*/ __Vtemp_82;
    VlWide<85>/*2719:0*/ __Vtemp_83;
    VlWide<86>/*2751:0*/ __Vtemp_84;
    VlWide<87>/*2783:0*/ __Vtemp_85;
    VlWide<88>/*2815:0*/ __Vtemp_86;
    VlWide<89>/*2847:0*/ __Vtemp_87;
    VlWide<90>/*2879:0*/ __Vtemp_88;
    VlWide<91>/*2911:0*/ __Vtemp_89;
    VlWide<92>/*2943:0*/ __Vtemp_90;
    VlWide<93>/*2975:0*/ __Vtemp_91;
    VlWide<94>/*3007:0*/ __Vtemp_92;
    VlWide<95>/*3039:0*/ __Vtemp_93;
    VlWide<96>/*3071:0*/ __Vtemp_94;
    VlWide<97>/*3103:0*/ __Vtemp_95;
    VlWide<98>/*3135:0*/ __Vtemp_96;
    VlWide<99>/*3167:0*/ __Vtemp_97;
    VlWide<100>/*3199:0*/ __Vtemp_98;
    VlWide<101>/*3231:0*/ __Vtemp_99;
    VlWide<102>/*3263:0*/ __Vtemp_100;
    VlWide<103>/*3295:0*/ __Vtemp_101;
    VlWide<104>/*3327:0*/ __Vtemp_102;
    VlWide<105>/*3359:0*/ __Vtemp_103;
    VlWide<106>/*3391:0*/ __Vtemp_104;
    VlWide<107>/*3423:0*/ __Vtemp_105;
    VlWide<108>/*3455:0*/ __Vtemp_106;
    VlWide<109>/*3487:0*/ __Vtemp_107;
    VlWide<110>/*3519:0*/ __Vtemp_108;
    VlWide<111>/*3551:0*/ __Vtemp_109;
    VlWide<112>/*3583:0*/ __Vtemp_110;
    VlWide<113>/*3615:0*/ __Vtemp_111;
    VlWide<114>/*3647:0*/ __Vtemp_112;
    VlWide<115>/*3679:0*/ __Vtemp_113;
    VlWide<116>/*3711:0*/ __Vtemp_114;
    VlWide<117>/*3743:0*/ __Vtemp_115;
    VlWide<118>/*3775:0*/ __Vtemp_116;
    VlWide<119>/*3807:0*/ __Vtemp_117;
    VlWide<120>/*3839:0*/ __Vtemp_118;
    VlWide<121>/*3871:0*/ __Vtemp_119;
    VlWide<122>/*3903:0*/ __Vtemp_120;
    VlWide<123>/*3935:0*/ __Vtemp_121;
    VlWide<124>/*3967:0*/ __Vtemp_122;
    VlWide<125>/*3999:0*/ __Vtemp_123;
    VlWide<126>/*4031:0*/ __Vtemp_124;
    VlWide<127>/*4063:0*/ __Vtemp_125;
    VlWide<128>/*4095:0*/ __Vtemp_126;
    VlWide<129>/*4127:0*/ __Vtemp_127;
    VlWide<130>/*4159:0*/ __Vtemp_128;
    VlWide<131>/*4191:0*/ __Vtemp_129;
    VlWide<132>/*4223:0*/ __Vtemp_130;
    VlWide<133>/*4255:0*/ __Vtemp_131;
    VlWide<134>/*4287:0*/ __Vtemp_132;
    VlWide<135>/*4319:0*/ __Vtemp_133;
    VlWide<136>/*4351:0*/ __Vtemp_134;
    VlWide<137>/*4383:0*/ __Vtemp_135;
    VlWide<138>/*4415:0*/ __Vtemp_136;
    VlWide<139>/*4447:0*/ __Vtemp_137;
    VlWide<140>/*4479:0*/ __Vtemp_138;
    VlWide<141>/*4511:0*/ __Vtemp_139;
    VlWide<142>/*4543:0*/ __Vtemp_140;
    VlWide<143>/*4575:0*/ __Vtemp_141;
    VlWide<144>/*4607:0*/ __Vtemp_142;
    VlWide<145>/*4639:0*/ __Vtemp_143;
    VlWide<146>/*4671:0*/ __Vtemp_144;
    VlWide<147>/*4703:0*/ __Vtemp_145;
    VlWide<148>/*4735:0*/ __Vtemp_146;
    VlWide<149>/*4767:0*/ __Vtemp_147;
    VlWide<150>/*4799:0*/ __Vtemp_148;
    VlWide<151>/*4831:0*/ __Vtemp_149;
    VlWide<152>/*4863:0*/ __Vtemp_150;
    VlWide<153>/*4895:0*/ __Vtemp_151;
    VlWide<154>/*4927:0*/ __Vtemp_152;
    VlWide<155>/*4959:0*/ __Vtemp_153;
    VlWide<156>/*4991:0*/ __Vtemp_154;
    VlWide<157>/*5023:0*/ __Vtemp_155;
    VlWide<158>/*5055:0*/ __Vtemp_156;
    VlWide<159>/*5087:0*/ __Vtemp_157;
    VlWide<160>/*5119:0*/ __Vtemp_158;
    VlWide<161>/*5151:0*/ __Vtemp_159;
    VlWide<162>/*5183:0*/ __Vtemp_160;
    VlWide<163>/*5215:0*/ __Vtemp_161;
    VlWide<164>/*5247:0*/ __Vtemp_162;
    VlWide<165>/*5279:0*/ __Vtemp_163;
    VlWide<166>/*5311:0*/ __Vtemp_164;
    VlWide<167>/*5343:0*/ __Vtemp_165;
    VlWide<168>/*5375:0*/ __Vtemp_166;
    VlWide<169>/*5407:0*/ __Vtemp_167;
    VlWide<170>/*5439:0*/ __Vtemp_168;
    VlWide<171>/*5471:0*/ __Vtemp_169;
    VlWide<172>/*5503:0*/ __Vtemp_170;
    VlWide<173>/*5535:0*/ __Vtemp_171;
    VlWide<174>/*5567:0*/ __Vtemp_172;
    VlWide<175>/*5599:0*/ __Vtemp_173;
    VlWide<176>/*5631:0*/ __Vtemp_174;
    VlWide<177>/*5663:0*/ __Vtemp_175;
    VlWide<178>/*5695:0*/ __Vtemp_176;
    VlWide<179>/*5727:0*/ __Vtemp_177;
    VlWide<180>/*5759:0*/ __Vtemp_178;
    VlWide<181>/*5791:0*/ __Vtemp_179;
    VlWide<182>/*5823:0*/ __Vtemp_180;
    VlWide<183>/*5855:0*/ __Vtemp_181;
    VlWide<184>/*5887:0*/ __Vtemp_182;
    VlWide<185>/*5919:0*/ __Vtemp_183;
    VlWide<186>/*5951:0*/ __Vtemp_184;
    VlWide<187>/*5983:0*/ __Vtemp_185;
    VlWide<188>/*6015:0*/ __Vtemp_186;
    VlWide<189>/*6047:0*/ __Vtemp_187;
    VlWide<190>/*6079:0*/ __Vtemp_188;
    VlWide<191>/*6111:0*/ __Vtemp_189;
    VlWide<192>/*6143:0*/ __Vtemp_190;
    VlWide<193>/*6175:0*/ __Vtemp_191;
    VlWide<194>/*6207:0*/ __Vtemp_192;
    VlWide<195>/*6239:0*/ __Vtemp_193;
    VlWide<196>/*6271:0*/ __Vtemp_194;
    VlWide<197>/*6303:0*/ __Vtemp_195;
    VlWide<198>/*6335:0*/ __Vtemp_196;
    VlWide<199>/*6367:0*/ __Vtemp_197;
    VlWide<200>/*6399:0*/ __Vtemp_198;
    VlWide<201>/*6431:0*/ __Vtemp_199;
    VlWide<202>/*6463:0*/ __Vtemp_200;
    VlWide<203>/*6495:0*/ __Vtemp_201;
    VlWide<204>/*6527:0*/ __Vtemp_202;
    VlWide<205>/*6559:0*/ __Vtemp_203;
    VlWide<206>/*6591:0*/ __Vtemp_204;
    VlWide<207>/*6623:0*/ __Vtemp_205;
    VlWide<208>/*6655:0*/ __Vtemp_206;
    VlWide<209>/*6687:0*/ __Vtemp_207;
    VlWide<210>/*6719:0*/ __Vtemp_208;
    VlWide<211>/*6751:0*/ __Vtemp_209;
    VlWide<212>/*6783:0*/ __Vtemp_210;
    VlWide<213>/*6815:0*/ __Vtemp_211;
    VlWide<214>/*6847:0*/ __Vtemp_212;
    VlWide<215>/*6879:0*/ __Vtemp_213;
    VlWide<216>/*6911:0*/ __Vtemp_214;
    VlWide<217>/*6943:0*/ __Vtemp_215;
    VlWide<218>/*6975:0*/ __Vtemp_216;
    VlWide<219>/*7007:0*/ __Vtemp_217;
    VlWide<220>/*7039:0*/ __Vtemp_218;
    VlWide<221>/*7071:0*/ __Vtemp_219;
    VlWide<222>/*7103:0*/ __Vtemp_220;
    VlWide<223>/*7135:0*/ __Vtemp_221;
    VlWide<224>/*7167:0*/ __Vtemp_222;
    VlWide<225>/*7199:0*/ __Vtemp_223;
    VlWide<226>/*7231:0*/ __Vtemp_224;
    VlWide<227>/*7263:0*/ __Vtemp_225;
    VlWide<228>/*7295:0*/ __Vtemp_226;
    VlWide<229>/*7327:0*/ __Vtemp_227;
    VlWide<230>/*7359:0*/ __Vtemp_228;
    VlWide<231>/*7391:0*/ __Vtemp_229;
    VlWide<232>/*7423:0*/ __Vtemp_230;
    VlWide<233>/*7455:0*/ __Vtemp_231;
    VlWide<234>/*7487:0*/ __Vtemp_232;
    VlWide<235>/*7519:0*/ __Vtemp_233;
    VlWide<236>/*7551:0*/ __Vtemp_234;
    VlWide<237>/*7583:0*/ __Vtemp_235;
    VlWide<238>/*7615:0*/ __Vtemp_236;
    VlWide<239>/*7647:0*/ __Vtemp_237;
    VlWide<240>/*7679:0*/ __Vtemp_238;
    VlWide<241>/*7711:0*/ __Vtemp_239;
    VlWide<242>/*7743:0*/ __Vtemp_240;
    VlWide<243>/*7775:0*/ __Vtemp_241;
    VlWide<244>/*7807:0*/ __Vtemp_242;
    VlWide<245>/*7839:0*/ __Vtemp_243;
    VlWide<246>/*7871:0*/ __Vtemp_244;
    VlWide<247>/*7903:0*/ __Vtemp_245;
    VlWide<248>/*7935:0*/ __Vtemp_246;
    VlWide<249>/*7967:0*/ __Vtemp_247;
    VlWide<250>/*7999:0*/ __Vtemp_248;
    VlWide<251>/*8031:0*/ __Vtemp_249;
    VlWide<252>/*8063:0*/ __Vtemp_250;
    VlWide<253>/*8095:0*/ __Vtemp_251;
    VlWide<254>/*8127:0*/ __Vtemp_252;
    VlWide<255>/*8159:0*/ __Vtemp_253;
    VlWide<256>/*8191:0*/ __Vtemp_257;
    VlWide<256>/*8191:0*/ __Vtemp_258;
    VlWide<256>/*8191:0*/ __Vtemp_259;
    VlWide<64>/*2047:0*/ __Vtemp_324;
    VlWide<65>/*2079:0*/ __Vtemp_325;
    VlWide<66>/*2111:0*/ __Vtemp_326;
    VlWide<67>/*2143:0*/ __Vtemp_327;
    VlWide<68>/*2175:0*/ __Vtemp_328;
    VlWide<69>/*2207:0*/ __Vtemp_329;
    VlWide<70>/*2239:0*/ __Vtemp_330;
    VlWide<71>/*2271:0*/ __Vtemp_331;
    VlWide<72>/*2303:0*/ __Vtemp_332;
    VlWide<73>/*2335:0*/ __Vtemp_333;
    VlWide<74>/*2367:0*/ __Vtemp_334;
    VlWide<75>/*2399:0*/ __Vtemp_335;
    VlWide<76>/*2431:0*/ __Vtemp_336;
    VlWide<77>/*2463:0*/ __Vtemp_337;
    VlWide<78>/*2495:0*/ __Vtemp_338;
    VlWide<79>/*2527:0*/ __Vtemp_339;
    VlWide<80>/*2559:0*/ __Vtemp_340;
    VlWide<81>/*2591:0*/ __Vtemp_341;
    VlWide<82>/*2623:0*/ __Vtemp_342;
    VlWide<83>/*2655:0*/ __Vtemp_343;
    VlWide<84>/*2687:0*/ __Vtemp_344;
    VlWide<85>/*2719:0*/ __Vtemp_345;
    VlWide<86>/*2751:0*/ __Vtemp_346;
    VlWide<87>/*2783:0*/ __Vtemp_347;
    VlWide<88>/*2815:0*/ __Vtemp_348;
    VlWide<89>/*2847:0*/ __Vtemp_349;
    VlWide<90>/*2879:0*/ __Vtemp_350;
    VlWide<91>/*2911:0*/ __Vtemp_351;
    VlWide<92>/*2943:0*/ __Vtemp_352;
    VlWide<93>/*2975:0*/ __Vtemp_353;
    VlWide<94>/*3007:0*/ __Vtemp_354;
    VlWide<95>/*3039:0*/ __Vtemp_355;
    VlWide<96>/*3071:0*/ __Vtemp_356;
    VlWide<97>/*3103:0*/ __Vtemp_357;
    VlWide<98>/*3135:0*/ __Vtemp_358;
    VlWide<99>/*3167:0*/ __Vtemp_359;
    VlWide<100>/*3199:0*/ __Vtemp_360;
    VlWide<101>/*3231:0*/ __Vtemp_361;
    VlWide<102>/*3263:0*/ __Vtemp_362;
    VlWide<103>/*3295:0*/ __Vtemp_363;
    VlWide<104>/*3327:0*/ __Vtemp_364;
    VlWide<105>/*3359:0*/ __Vtemp_365;
    VlWide<106>/*3391:0*/ __Vtemp_366;
    VlWide<107>/*3423:0*/ __Vtemp_367;
    VlWide<108>/*3455:0*/ __Vtemp_368;
    VlWide<109>/*3487:0*/ __Vtemp_369;
    VlWide<110>/*3519:0*/ __Vtemp_370;
    VlWide<111>/*3551:0*/ __Vtemp_371;
    VlWide<112>/*3583:0*/ __Vtemp_372;
    VlWide<113>/*3615:0*/ __Vtemp_373;
    VlWide<114>/*3647:0*/ __Vtemp_374;
    VlWide<115>/*3679:0*/ __Vtemp_375;
    VlWide<116>/*3711:0*/ __Vtemp_376;
    VlWide<117>/*3743:0*/ __Vtemp_377;
    VlWide<118>/*3775:0*/ __Vtemp_378;
    VlWide<119>/*3807:0*/ __Vtemp_379;
    VlWide<120>/*3839:0*/ __Vtemp_380;
    VlWide<121>/*3871:0*/ __Vtemp_381;
    VlWide<122>/*3903:0*/ __Vtemp_382;
    VlWide<123>/*3935:0*/ __Vtemp_383;
    VlWide<124>/*3967:0*/ __Vtemp_384;
    VlWide<125>/*3999:0*/ __Vtemp_385;
    VlWide<126>/*4031:0*/ __Vtemp_386;
    VlWide<127>/*4063:0*/ __Vtemp_387;
    VlWide<128>/*4095:0*/ __Vtemp_388;
    VlWide<129>/*4127:0*/ __Vtemp_389;
    VlWide<130>/*4159:0*/ __Vtemp_390;
    VlWide<131>/*4191:0*/ __Vtemp_391;
    VlWide<132>/*4223:0*/ __Vtemp_392;
    VlWide<133>/*4255:0*/ __Vtemp_393;
    VlWide<134>/*4287:0*/ __Vtemp_394;
    VlWide<135>/*4319:0*/ __Vtemp_395;
    VlWide<136>/*4351:0*/ __Vtemp_396;
    VlWide<137>/*4383:0*/ __Vtemp_397;
    VlWide<138>/*4415:0*/ __Vtemp_398;
    VlWide<139>/*4447:0*/ __Vtemp_399;
    VlWide<140>/*4479:0*/ __Vtemp_400;
    VlWide<141>/*4511:0*/ __Vtemp_401;
    VlWide<142>/*4543:0*/ __Vtemp_402;
    VlWide<143>/*4575:0*/ __Vtemp_403;
    VlWide<144>/*4607:0*/ __Vtemp_404;
    VlWide<145>/*4639:0*/ __Vtemp_405;
    VlWide<146>/*4671:0*/ __Vtemp_406;
    VlWide<147>/*4703:0*/ __Vtemp_407;
    VlWide<148>/*4735:0*/ __Vtemp_408;
    VlWide<149>/*4767:0*/ __Vtemp_409;
    VlWide<150>/*4799:0*/ __Vtemp_410;
    VlWide<151>/*4831:0*/ __Vtemp_411;
    VlWide<152>/*4863:0*/ __Vtemp_412;
    VlWide<153>/*4895:0*/ __Vtemp_413;
    VlWide<154>/*4927:0*/ __Vtemp_414;
    VlWide<155>/*4959:0*/ __Vtemp_415;
    VlWide<156>/*4991:0*/ __Vtemp_416;
    VlWide<157>/*5023:0*/ __Vtemp_417;
    VlWide<158>/*5055:0*/ __Vtemp_418;
    VlWide<159>/*5087:0*/ __Vtemp_419;
    VlWide<160>/*5119:0*/ __Vtemp_420;
    VlWide<161>/*5151:0*/ __Vtemp_421;
    VlWide<162>/*5183:0*/ __Vtemp_422;
    VlWide<163>/*5215:0*/ __Vtemp_423;
    VlWide<164>/*5247:0*/ __Vtemp_424;
    VlWide<165>/*5279:0*/ __Vtemp_425;
    VlWide<166>/*5311:0*/ __Vtemp_426;
    VlWide<167>/*5343:0*/ __Vtemp_427;
    VlWide<168>/*5375:0*/ __Vtemp_428;
    VlWide<169>/*5407:0*/ __Vtemp_429;
    VlWide<170>/*5439:0*/ __Vtemp_430;
    VlWide<171>/*5471:0*/ __Vtemp_431;
    VlWide<172>/*5503:0*/ __Vtemp_432;
    VlWide<173>/*5535:0*/ __Vtemp_433;
    VlWide<174>/*5567:0*/ __Vtemp_434;
    VlWide<175>/*5599:0*/ __Vtemp_435;
    VlWide<176>/*5631:0*/ __Vtemp_436;
    VlWide<177>/*5663:0*/ __Vtemp_437;
    VlWide<178>/*5695:0*/ __Vtemp_438;
    VlWide<179>/*5727:0*/ __Vtemp_439;
    VlWide<180>/*5759:0*/ __Vtemp_440;
    VlWide<181>/*5791:0*/ __Vtemp_441;
    VlWide<182>/*5823:0*/ __Vtemp_442;
    VlWide<183>/*5855:0*/ __Vtemp_443;
    VlWide<184>/*5887:0*/ __Vtemp_444;
    VlWide<185>/*5919:0*/ __Vtemp_445;
    VlWide<186>/*5951:0*/ __Vtemp_446;
    VlWide<187>/*5983:0*/ __Vtemp_447;
    VlWide<188>/*6015:0*/ __Vtemp_448;
    VlWide<189>/*6047:0*/ __Vtemp_449;
    VlWide<190>/*6079:0*/ __Vtemp_450;
    VlWide<191>/*6111:0*/ __Vtemp_451;
    VlWide<192>/*6143:0*/ __Vtemp_452;
    VlWide<193>/*6175:0*/ __Vtemp_453;
    VlWide<194>/*6207:0*/ __Vtemp_454;
    VlWide<195>/*6239:0*/ __Vtemp_455;
    VlWide<196>/*6271:0*/ __Vtemp_456;
    VlWide<197>/*6303:0*/ __Vtemp_457;
    VlWide<198>/*6335:0*/ __Vtemp_458;
    VlWide<199>/*6367:0*/ __Vtemp_459;
    VlWide<200>/*6399:0*/ __Vtemp_460;
    VlWide<201>/*6431:0*/ __Vtemp_461;
    VlWide<202>/*6463:0*/ __Vtemp_462;
    VlWide<203>/*6495:0*/ __Vtemp_463;
    VlWide<204>/*6527:0*/ __Vtemp_464;
    VlWide<205>/*6559:0*/ __Vtemp_465;
    VlWide<206>/*6591:0*/ __Vtemp_466;
    VlWide<207>/*6623:0*/ __Vtemp_467;
    VlWide<208>/*6655:0*/ __Vtemp_468;
    VlWide<209>/*6687:0*/ __Vtemp_469;
    VlWide<210>/*6719:0*/ __Vtemp_470;
    VlWide<211>/*6751:0*/ __Vtemp_471;
    VlWide<212>/*6783:0*/ __Vtemp_472;
    VlWide<213>/*6815:0*/ __Vtemp_473;
    VlWide<214>/*6847:0*/ __Vtemp_474;
    VlWide<215>/*6879:0*/ __Vtemp_475;
    VlWide<216>/*6911:0*/ __Vtemp_476;
    VlWide<217>/*6943:0*/ __Vtemp_477;
    VlWide<218>/*6975:0*/ __Vtemp_478;
    VlWide<219>/*7007:0*/ __Vtemp_479;
    VlWide<220>/*7039:0*/ __Vtemp_480;
    VlWide<221>/*7071:0*/ __Vtemp_481;
    VlWide<222>/*7103:0*/ __Vtemp_482;
    VlWide<223>/*7135:0*/ __Vtemp_483;
    VlWide<224>/*7167:0*/ __Vtemp_484;
    VlWide<225>/*7199:0*/ __Vtemp_485;
    VlWide<226>/*7231:0*/ __Vtemp_486;
    VlWide<227>/*7263:0*/ __Vtemp_487;
    VlWide<228>/*7295:0*/ __Vtemp_488;
    VlWide<229>/*7327:0*/ __Vtemp_489;
    VlWide<230>/*7359:0*/ __Vtemp_490;
    VlWide<231>/*7391:0*/ __Vtemp_491;
    VlWide<232>/*7423:0*/ __Vtemp_492;
    VlWide<233>/*7455:0*/ __Vtemp_493;
    VlWide<234>/*7487:0*/ __Vtemp_494;
    VlWide<235>/*7519:0*/ __Vtemp_495;
    VlWide<236>/*7551:0*/ __Vtemp_496;
    VlWide<237>/*7583:0*/ __Vtemp_497;
    VlWide<238>/*7615:0*/ __Vtemp_498;
    VlWide<239>/*7647:0*/ __Vtemp_499;
    VlWide<240>/*7679:0*/ __Vtemp_500;
    VlWide<241>/*7711:0*/ __Vtemp_501;
    VlWide<242>/*7743:0*/ __Vtemp_502;
    VlWide<243>/*7775:0*/ __Vtemp_503;
    VlWide<244>/*7807:0*/ __Vtemp_504;
    VlWide<245>/*7839:0*/ __Vtemp_505;
    VlWide<246>/*7871:0*/ __Vtemp_506;
    VlWide<247>/*7903:0*/ __Vtemp_507;
    VlWide<248>/*7935:0*/ __Vtemp_508;
    VlWide<249>/*7967:0*/ __Vtemp_509;
    VlWide<250>/*7999:0*/ __Vtemp_510;
    VlWide<251>/*8031:0*/ __Vtemp_511;
    VlWide<252>/*8063:0*/ __Vtemp_512;
    VlWide<253>/*8095:0*/ __Vtemp_513;
    VlWide<254>/*8127:0*/ __Vtemp_514;
    VlWide<255>/*8159:0*/ __Vtemp_515;
    VlWide<64>/*2047:0*/ __Vtemp_635;
    VlWide<65>/*2079:0*/ __Vtemp_636;
    VlWide<66>/*2111:0*/ __Vtemp_637;
    VlWide<67>/*2143:0*/ __Vtemp_638;
    VlWide<68>/*2175:0*/ __Vtemp_639;
    VlWide<69>/*2207:0*/ __Vtemp_640;
    VlWide<70>/*2239:0*/ __Vtemp_641;
    VlWide<71>/*2271:0*/ __Vtemp_642;
    VlWide<72>/*2303:0*/ __Vtemp_643;
    VlWide<73>/*2335:0*/ __Vtemp_644;
    VlWide<74>/*2367:0*/ __Vtemp_645;
    VlWide<75>/*2399:0*/ __Vtemp_646;
    VlWide<76>/*2431:0*/ __Vtemp_647;
    VlWide<77>/*2463:0*/ __Vtemp_648;
    VlWide<78>/*2495:0*/ __Vtemp_649;
    VlWide<79>/*2527:0*/ __Vtemp_650;
    VlWide<80>/*2559:0*/ __Vtemp_651;
    VlWide<81>/*2591:0*/ __Vtemp_652;
    VlWide<82>/*2623:0*/ __Vtemp_653;
    VlWide<83>/*2655:0*/ __Vtemp_654;
    VlWide<84>/*2687:0*/ __Vtemp_655;
    VlWide<85>/*2719:0*/ __Vtemp_656;
    VlWide<86>/*2751:0*/ __Vtemp_657;
    VlWide<87>/*2783:0*/ __Vtemp_658;
    VlWide<88>/*2815:0*/ __Vtemp_659;
    VlWide<89>/*2847:0*/ __Vtemp_660;
    VlWide<90>/*2879:0*/ __Vtemp_661;
    VlWide<91>/*2911:0*/ __Vtemp_662;
    VlWide<92>/*2943:0*/ __Vtemp_663;
    VlWide<93>/*2975:0*/ __Vtemp_664;
    VlWide<94>/*3007:0*/ __Vtemp_665;
    VlWide<95>/*3039:0*/ __Vtemp_666;
    VlWide<96>/*3071:0*/ __Vtemp_667;
    VlWide<97>/*3103:0*/ __Vtemp_668;
    VlWide<98>/*3135:0*/ __Vtemp_669;
    VlWide<99>/*3167:0*/ __Vtemp_670;
    VlWide<100>/*3199:0*/ __Vtemp_671;
    VlWide<101>/*3231:0*/ __Vtemp_672;
    VlWide<102>/*3263:0*/ __Vtemp_673;
    VlWide<103>/*3295:0*/ __Vtemp_674;
    VlWide<104>/*3327:0*/ __Vtemp_675;
    VlWide<105>/*3359:0*/ __Vtemp_676;
    VlWide<106>/*3391:0*/ __Vtemp_677;
    VlWide<107>/*3423:0*/ __Vtemp_678;
    VlWide<108>/*3455:0*/ __Vtemp_679;
    VlWide<109>/*3487:0*/ __Vtemp_680;
    VlWide<110>/*3519:0*/ __Vtemp_681;
    VlWide<111>/*3551:0*/ __Vtemp_682;
    VlWide<112>/*3583:0*/ __Vtemp_683;
    VlWide<113>/*3615:0*/ __Vtemp_684;
    VlWide<114>/*3647:0*/ __Vtemp_685;
    VlWide<115>/*3679:0*/ __Vtemp_686;
    VlWide<116>/*3711:0*/ __Vtemp_687;
    VlWide<117>/*3743:0*/ __Vtemp_688;
    VlWide<118>/*3775:0*/ __Vtemp_689;
    VlWide<119>/*3807:0*/ __Vtemp_690;
    VlWide<120>/*3839:0*/ __Vtemp_691;
    VlWide<121>/*3871:0*/ __Vtemp_692;
    VlWide<122>/*3903:0*/ __Vtemp_693;
    VlWide<123>/*3935:0*/ __Vtemp_694;
    VlWide<124>/*3967:0*/ __Vtemp_695;
    VlWide<125>/*3999:0*/ __Vtemp_696;
    VlWide<126>/*4031:0*/ __Vtemp_697;
    VlWide<127>/*4063:0*/ __Vtemp_698;
    VlWide<128>/*4095:0*/ __Vtemp_699;
    VlWide<129>/*4127:0*/ __Vtemp_700;
    VlWide<130>/*4159:0*/ __Vtemp_701;
    VlWide<131>/*4191:0*/ __Vtemp_702;
    VlWide<132>/*4223:0*/ __Vtemp_703;
    VlWide<133>/*4255:0*/ __Vtemp_704;
    VlWide<134>/*4287:0*/ __Vtemp_705;
    VlWide<135>/*4319:0*/ __Vtemp_706;
    VlWide<136>/*4351:0*/ __Vtemp_707;
    VlWide<137>/*4383:0*/ __Vtemp_708;
    VlWide<138>/*4415:0*/ __Vtemp_709;
    VlWide<139>/*4447:0*/ __Vtemp_710;
    VlWide<140>/*4479:0*/ __Vtemp_711;
    VlWide<141>/*4511:0*/ __Vtemp_712;
    VlWide<142>/*4543:0*/ __Vtemp_713;
    VlWide<143>/*4575:0*/ __Vtemp_714;
    VlWide<144>/*4607:0*/ __Vtemp_715;
    VlWide<145>/*4639:0*/ __Vtemp_716;
    VlWide<146>/*4671:0*/ __Vtemp_717;
    VlWide<147>/*4703:0*/ __Vtemp_718;
    VlWide<148>/*4735:0*/ __Vtemp_719;
    VlWide<149>/*4767:0*/ __Vtemp_720;
    VlWide<150>/*4799:0*/ __Vtemp_721;
    VlWide<151>/*4831:0*/ __Vtemp_722;
    VlWide<152>/*4863:0*/ __Vtemp_723;
    VlWide<153>/*4895:0*/ __Vtemp_724;
    VlWide<154>/*4927:0*/ __Vtemp_725;
    VlWide<155>/*4959:0*/ __Vtemp_726;
    VlWide<156>/*4991:0*/ __Vtemp_727;
    VlWide<157>/*5023:0*/ __Vtemp_728;
    VlWide<158>/*5055:0*/ __Vtemp_729;
    VlWide<159>/*5087:0*/ __Vtemp_730;
    VlWide<160>/*5119:0*/ __Vtemp_731;
    VlWide<161>/*5151:0*/ __Vtemp_732;
    VlWide<162>/*5183:0*/ __Vtemp_733;
    VlWide<163>/*5215:0*/ __Vtemp_734;
    VlWide<164>/*5247:0*/ __Vtemp_735;
    VlWide<165>/*5279:0*/ __Vtemp_736;
    VlWide<166>/*5311:0*/ __Vtemp_737;
    VlWide<167>/*5343:0*/ __Vtemp_738;
    VlWide<168>/*5375:0*/ __Vtemp_739;
    VlWide<169>/*5407:0*/ __Vtemp_740;
    VlWide<170>/*5439:0*/ __Vtemp_741;
    VlWide<171>/*5471:0*/ __Vtemp_742;
    VlWide<172>/*5503:0*/ __Vtemp_743;
    VlWide<173>/*5535:0*/ __Vtemp_744;
    VlWide<174>/*5567:0*/ __Vtemp_745;
    VlWide<175>/*5599:0*/ __Vtemp_746;
    VlWide<176>/*5631:0*/ __Vtemp_747;
    VlWide<177>/*5663:0*/ __Vtemp_748;
    VlWide<178>/*5695:0*/ __Vtemp_749;
    VlWide<179>/*5727:0*/ __Vtemp_750;
    VlWide<180>/*5759:0*/ __Vtemp_751;
    VlWide<181>/*5791:0*/ __Vtemp_752;
    VlWide<182>/*5823:0*/ __Vtemp_753;
    VlWide<183>/*5855:0*/ __Vtemp_754;
    VlWide<184>/*5887:0*/ __Vtemp_755;
    VlWide<185>/*5919:0*/ __Vtemp_756;
    VlWide<186>/*5951:0*/ __Vtemp_757;
    VlWide<187>/*5983:0*/ __Vtemp_758;
    VlWide<188>/*6015:0*/ __Vtemp_759;
    VlWide<189>/*6047:0*/ __Vtemp_760;
    VlWide<190>/*6079:0*/ __Vtemp_761;
    VlWide<191>/*6111:0*/ __Vtemp_762;
    VlWide<192>/*6143:0*/ __Vtemp_763;
    VlWide<193>/*6175:0*/ __Vtemp_764;
    VlWide<194>/*6207:0*/ __Vtemp_765;
    VlWide<195>/*6239:0*/ __Vtemp_766;
    VlWide<196>/*6271:0*/ __Vtemp_767;
    VlWide<197>/*6303:0*/ __Vtemp_768;
    VlWide<198>/*6335:0*/ __Vtemp_769;
    VlWide<199>/*6367:0*/ __Vtemp_770;
    VlWide<200>/*6399:0*/ __Vtemp_771;
    VlWide<201>/*6431:0*/ __Vtemp_772;
    VlWide<202>/*6463:0*/ __Vtemp_773;
    VlWide<203>/*6495:0*/ __Vtemp_774;
    VlWide<204>/*6527:0*/ __Vtemp_775;
    VlWide<205>/*6559:0*/ __Vtemp_776;
    VlWide<206>/*6591:0*/ __Vtemp_777;
    VlWide<207>/*6623:0*/ __Vtemp_778;
    VlWide<208>/*6655:0*/ __Vtemp_779;
    VlWide<209>/*6687:0*/ __Vtemp_780;
    VlWide<210>/*6719:0*/ __Vtemp_781;
    VlWide<211>/*6751:0*/ __Vtemp_782;
    VlWide<212>/*6783:0*/ __Vtemp_783;
    VlWide<213>/*6815:0*/ __Vtemp_784;
    VlWide<214>/*6847:0*/ __Vtemp_785;
    VlWide<215>/*6879:0*/ __Vtemp_786;
    VlWide<216>/*6911:0*/ __Vtemp_787;
    VlWide<217>/*6943:0*/ __Vtemp_788;
    VlWide<218>/*6975:0*/ __Vtemp_789;
    VlWide<219>/*7007:0*/ __Vtemp_790;
    VlWide<220>/*7039:0*/ __Vtemp_791;
    VlWide<221>/*7071:0*/ __Vtemp_792;
    VlWide<222>/*7103:0*/ __Vtemp_793;
    VlWide<223>/*7135:0*/ __Vtemp_794;
    VlWide<224>/*7167:0*/ __Vtemp_795;
    VlWide<225>/*7199:0*/ __Vtemp_796;
    VlWide<226>/*7231:0*/ __Vtemp_797;
    VlWide<227>/*7263:0*/ __Vtemp_798;
    VlWide<228>/*7295:0*/ __Vtemp_799;
    VlWide<229>/*7327:0*/ __Vtemp_800;
    VlWide<230>/*7359:0*/ __Vtemp_801;
    VlWide<231>/*7391:0*/ __Vtemp_802;
    VlWide<232>/*7423:0*/ __Vtemp_803;
    VlWide<233>/*7455:0*/ __Vtemp_804;
    VlWide<234>/*7487:0*/ __Vtemp_805;
    VlWide<235>/*7519:0*/ __Vtemp_806;
    VlWide<236>/*7551:0*/ __Vtemp_807;
    VlWide<237>/*7583:0*/ __Vtemp_808;
    VlWide<238>/*7615:0*/ __Vtemp_809;
    VlWide<239>/*7647:0*/ __Vtemp_810;
    VlWide<240>/*7679:0*/ __Vtemp_811;
    VlWide<241>/*7711:0*/ __Vtemp_812;
    VlWide<242>/*7743:0*/ __Vtemp_813;
    VlWide<243>/*7775:0*/ __Vtemp_814;
    VlWide<244>/*7807:0*/ __Vtemp_815;
    VlWide<245>/*7839:0*/ __Vtemp_816;
    VlWide<246>/*7871:0*/ __Vtemp_817;
    VlWide<247>/*7903:0*/ __Vtemp_818;
    VlWide<248>/*7935:0*/ __Vtemp_819;
    VlWide<249>/*7967:0*/ __Vtemp_820;
    VlWide<250>/*7999:0*/ __Vtemp_821;
    VlWide<251>/*8031:0*/ __Vtemp_822;
    VlWide<252>/*8063:0*/ __Vtemp_823;
    VlWide<253>/*8095:0*/ __Vtemp_824;
    VlWide<254>/*8127:0*/ __Vtemp_825;
    VlWide<255>/*8159:0*/ __Vtemp_826;
    // Body
    __Vtemp_62[0U] = ((0xc0U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc0U]);
    __Vtemp_62[1U] = ((0xc1U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc1U]);
    __Vtemp_62[2U] = ((0xc2U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc2U]);
    __Vtemp_62[3U] = ((0xc3U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc3U]);
    __Vtemp_62[4U] = ((0xc4U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc4U]);
    __Vtemp_62[5U] = ((0xc5U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc5U]);
    __Vtemp_62[6U] = ((0xc6U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc6U]);
    __Vtemp_62[7U] = ((0xc7U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc7U]);
    __Vtemp_62[8U] = ((0xc8U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc8U]);
    __Vtemp_62[9U] = ((0xc9U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                  >> 0x20U))))
                       ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc9U]);
    __Vtemp_62[0xaU] = ((0xcaU == (0xffU & (IData)(
                                                   (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                    >> 0x20U))))
                         ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                         : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcaU]);
    __Vtemp_62[0xbU] = ((0xcbU == (0xffU & (IData)(
                                                   (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                    >> 0x20U))))
                         ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                         : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcbU]);
    __Vtemp_62[0xcU] = ((0xccU == (0xffU & (IData)(
                                                   (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                    >> 0x20U))))
                         ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                         : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xccU]);
    __Vtemp_62[0xdU] = ((0xcdU == (0xffU & (IData)(
                                                   (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                    >> 0x20U))))
                         ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                         : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcdU]);
    __Vtemp_62[0xeU] = ((0xceU == (0xffU & (IData)(
                                                   (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                    >> 0x20U))))
                         ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                         : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xceU]);
    __Vtemp_62[0xfU] = ((0xcfU == (0xffU & (IData)(
                                                   (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                    >> 0x20U))))
                         ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                         : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcfU]);
    __Vtemp_62[0x10U] = ((0xd0U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd0U]);
    __Vtemp_62[0x11U] = ((0xd1U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd1U]);
    __Vtemp_62[0x12U] = ((0xd2U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd2U]);
    __Vtemp_62[0x13U] = ((0xd3U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd3U]);
    __Vtemp_62[0x14U] = ((0xd4U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd4U]);
    __Vtemp_62[0x15U] = ((0xd5U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd5U]);
    __Vtemp_62[0x16U] = ((0xd6U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd6U]);
    __Vtemp_62[0x17U] = ((0xd7U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd7U]);
    __Vtemp_62[0x18U] = ((0xd8U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd8U]);
    __Vtemp_62[0x19U] = ((0xd9U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd9U]);
    __Vtemp_62[0x1aU] = ((0xdaU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdaU]);
    __Vtemp_62[0x1bU] = ((0xdbU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdbU]);
    __Vtemp_62[0x1cU] = ((0xdcU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdcU]);
    __Vtemp_62[0x1dU] = ((0xddU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xddU]);
    __Vtemp_62[0x1eU] = ((0xdeU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdeU]);
    __Vtemp_62[0x1fU] = ((0xdfU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdfU]);
    __Vtemp_62[0x20U] = ((0xe0U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe0U]);
    __Vtemp_62[0x21U] = ((0xe1U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe1U]);
    __Vtemp_62[0x22U] = ((0xe2U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe2U]);
    __Vtemp_62[0x23U] = ((0xe3U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe3U]);
    __Vtemp_62[0x24U] = ((0xe4U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe4U]);
    __Vtemp_62[0x25U] = ((0xe5U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe5U]);
    __Vtemp_62[0x26U] = ((0xe6U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe6U]);
    __Vtemp_62[0x27U] = ((0xe7U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe7U]);
    __Vtemp_62[0x28U] = ((0xe8U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe8U]);
    __Vtemp_62[0x29U] = ((0xe9U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe9U]);
    __Vtemp_62[0x2aU] = ((0xeaU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xeaU]);
    __Vtemp_62[0x2bU] = ((0xebU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xebU]);
    __Vtemp_62[0x2cU] = ((0xecU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xecU]);
    __Vtemp_62[0x2dU] = ((0xedU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xedU]);
    __Vtemp_62[0x2eU] = ((0xeeU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xeeU]);
    __Vtemp_62[0x2fU] = ((0xefU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xefU]);
    __Vtemp_62[0x30U] = ((0xf0U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf0U]);
    __Vtemp_62[0x31U] = ((0xf1U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf1U]);
    __Vtemp_62[0x32U] = ((0xf2U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf2U]);
    __Vtemp_62[0x33U] = ((0xf3U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf3U]);
    __Vtemp_62[0x34U] = ((0xf4U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf4U]);
    __Vtemp_62[0x35U] = ((0xf5U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf5U]);
    __Vtemp_62[0x36U] = ((0xf6U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf6U]);
    __Vtemp_62[0x37U] = ((0xf7U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf7U]);
    __Vtemp_62[0x38U] = ((0xf8U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf8U]);
    __Vtemp_62[0x39U] = ((0xf9U == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf9U]);
    __Vtemp_62[0x3aU] = ((0xfaU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfaU]);
    __Vtemp_62[0x3bU] = ((0xfbU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfbU]);
    __Vtemp_62[0x3cU] = ((0xfcU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfcU]);
    __Vtemp_62[0x3dU] = ((0xfdU == (0xffU & (IData)(
                                                    (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                     >> 0x20U))))
                          ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfdU]);
    __Vtemp_62[0x3eU] = (IData)((((QData)((IData)((
                                                   (0xffU 
                                                    == 
                                                    (0xffU 
                                                     & (IData)(
                                                               (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                                >> 0x20U))))
                                                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                                                    : 
                                                   vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xffU]))) 
                                  << 0x20U) | (QData)((IData)(
                                                              ((0xfeU 
                                                                == 
                                                                (0xffU 
                                                                 & (IData)(
                                                                           (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                                            >> 0x20U))))
                                                                ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                                                                : 
                                                               vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfeU])))));
    __Vtemp_62[0x3fU] = (IData)(((((QData)((IData)(
                                                   ((0xffU 
                                                     == 
                                                     (0xffU 
                                                      & (IData)(
                                                                (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                                 >> 0x20U))))
                                                     ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xffU]))) 
                                   << 0x20U) | (QData)((IData)(
                                                               ((0xfeU 
                                                                 == 
                                                                 (0xffU 
                                                                  & (IData)(
                                                                            (vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                                                             >> 0x20U))))
                                                                 ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                                                                 : 
                                                                vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfeU])))) 
                                 >> 0x20U));
    VL_CONCAT_WWI(2080,2048,32, __Vtemp_63, __Vtemp_62, 
                  ((0xbfU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbfU]));
    VL_CONCAT_WWI(2112,2080,32, __Vtemp_64, __Vtemp_63, 
                  ((0xbeU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbeU]));
    VL_CONCAT_WWI(2144,2112,32, __Vtemp_65, __Vtemp_64, 
                  ((0xbdU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbdU]));
    VL_CONCAT_WWI(2176,2144,32, __Vtemp_66, __Vtemp_65, 
                  ((0xbcU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbcU]));
    VL_CONCAT_WWI(2208,2176,32, __Vtemp_67, __Vtemp_66, 
                  ((0xbbU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbbU]));
    VL_CONCAT_WWI(2240,2208,32, __Vtemp_68, __Vtemp_67, 
                  ((0xbaU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbaU]));
    VL_CONCAT_WWI(2272,2240,32, __Vtemp_69, __Vtemp_68, 
                  ((0xb9U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb9U]));
    VL_CONCAT_WWI(2304,2272,32, __Vtemp_70, __Vtemp_69, 
                  ((0xb8U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb8U]));
    VL_CONCAT_WWI(2336,2304,32, __Vtemp_71, __Vtemp_70, 
                  ((0xb7U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb7U]));
    VL_CONCAT_WWI(2368,2336,32, __Vtemp_72, __Vtemp_71, 
                  ((0xb6U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb6U]));
    VL_CONCAT_WWI(2400,2368,32, __Vtemp_73, __Vtemp_72, 
                  ((0xb5U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb5U]));
    VL_CONCAT_WWI(2432,2400,32, __Vtemp_74, __Vtemp_73, 
                  ((0xb4U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb4U]));
    VL_CONCAT_WWI(2464,2432,32, __Vtemp_75, __Vtemp_74, 
                  ((0xb3U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb3U]));
    VL_CONCAT_WWI(2496,2464,32, __Vtemp_76, __Vtemp_75, 
                  ((0xb2U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb2U]));
    VL_CONCAT_WWI(2528,2496,32, __Vtemp_77, __Vtemp_76, 
                  ((0xb1U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb1U]));
    VL_CONCAT_WWI(2560,2528,32, __Vtemp_78, __Vtemp_77, 
                  ((0xb0U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb0U]));
    VL_CONCAT_WWI(2592,2560,32, __Vtemp_79, __Vtemp_78, 
                  ((0xafU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xafU]));
    VL_CONCAT_WWI(2624,2592,32, __Vtemp_80, __Vtemp_79, 
                  ((0xaeU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xaeU]));
    VL_CONCAT_WWI(2656,2624,32, __Vtemp_81, __Vtemp_80, 
                  ((0xadU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xadU]));
    VL_CONCAT_WWI(2688,2656,32, __Vtemp_82, __Vtemp_81, 
                  ((0xacU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xacU]));
    VL_CONCAT_WWI(2720,2688,32, __Vtemp_83, __Vtemp_82, 
                  ((0xabU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xabU]));
    VL_CONCAT_WWI(2752,2720,32, __Vtemp_84, __Vtemp_83, 
                  ((0xaaU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xaaU]));
    VL_CONCAT_WWI(2784,2752,32, __Vtemp_85, __Vtemp_84, 
                  ((0xa9U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa9U]));
    VL_CONCAT_WWI(2816,2784,32, __Vtemp_86, __Vtemp_85, 
                  ((0xa8U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa8U]));
    VL_CONCAT_WWI(2848,2816,32, __Vtemp_87, __Vtemp_86, 
                  ((0xa7U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa7U]));
    VL_CONCAT_WWI(2880,2848,32, __Vtemp_88, __Vtemp_87, 
                  ((0xa6U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa6U]));
    VL_CONCAT_WWI(2912,2880,32, __Vtemp_89, __Vtemp_88, 
                  ((0xa5U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa5U]));
    VL_CONCAT_WWI(2944,2912,32, __Vtemp_90, __Vtemp_89, 
                  ((0xa4U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa4U]));
    VL_CONCAT_WWI(2976,2944,32, __Vtemp_91, __Vtemp_90, 
                  ((0xa3U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa3U]));
    VL_CONCAT_WWI(3008,2976,32, __Vtemp_92, __Vtemp_91, 
                  ((0xa2U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa2U]));
    VL_CONCAT_WWI(3040,3008,32, __Vtemp_93, __Vtemp_92, 
                  ((0xa1U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa1U]));
    VL_CONCAT_WWI(3072,3040,32, __Vtemp_94, __Vtemp_93, 
                  ((0xa0U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa0U]));
    VL_CONCAT_WWI(3104,3072,32, __Vtemp_95, __Vtemp_94, 
                  ((0x9fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9fU]));
    VL_CONCAT_WWI(3136,3104,32, __Vtemp_96, __Vtemp_95, 
                  ((0x9eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9eU]));
    VL_CONCAT_WWI(3168,3136,32, __Vtemp_97, __Vtemp_96, 
                  ((0x9dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9dU]));
    VL_CONCAT_WWI(3200,3168,32, __Vtemp_98, __Vtemp_97, 
                  ((0x9cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9cU]));
    VL_CONCAT_WWI(3232,3200,32, __Vtemp_99, __Vtemp_98, 
                  ((0x9bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9bU]));
    VL_CONCAT_WWI(3264,3232,32, __Vtemp_100, __Vtemp_99, 
                  ((0x9aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9aU]));
    VL_CONCAT_WWI(3296,3264,32, __Vtemp_101, __Vtemp_100, 
                  ((0x99U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x99U]));
    VL_CONCAT_WWI(3328,3296,32, __Vtemp_102, __Vtemp_101, 
                  ((0x98U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x98U]));
    VL_CONCAT_WWI(3360,3328,32, __Vtemp_103, __Vtemp_102, 
                  ((0x97U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x97U]));
    VL_CONCAT_WWI(3392,3360,32, __Vtemp_104, __Vtemp_103, 
                  ((0x96U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x96U]));
    VL_CONCAT_WWI(3424,3392,32, __Vtemp_105, __Vtemp_104, 
                  ((0x95U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x95U]));
    VL_CONCAT_WWI(3456,3424,32, __Vtemp_106, __Vtemp_105, 
                  ((0x94U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x94U]));
    VL_CONCAT_WWI(3488,3456,32, __Vtemp_107, __Vtemp_106, 
                  ((0x93U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x93U]));
    VL_CONCAT_WWI(3520,3488,32, __Vtemp_108, __Vtemp_107, 
                  ((0x92U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x92U]));
    VL_CONCAT_WWI(3552,3520,32, __Vtemp_109, __Vtemp_108, 
                  ((0x91U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x91U]));
    VL_CONCAT_WWI(3584,3552,32, __Vtemp_110, __Vtemp_109, 
                  ((0x90U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x90U]));
    VL_CONCAT_WWI(3616,3584,32, __Vtemp_111, __Vtemp_110, 
                  ((0x8fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8fU]));
    VL_CONCAT_WWI(3648,3616,32, __Vtemp_112, __Vtemp_111, 
                  ((0x8eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8eU]));
    VL_CONCAT_WWI(3680,3648,32, __Vtemp_113, __Vtemp_112, 
                  ((0x8dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8dU]));
    VL_CONCAT_WWI(3712,3680,32, __Vtemp_114, __Vtemp_113, 
                  ((0x8cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8cU]));
    VL_CONCAT_WWI(3744,3712,32, __Vtemp_115, __Vtemp_114, 
                  ((0x8bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8bU]));
    VL_CONCAT_WWI(3776,3744,32, __Vtemp_116, __Vtemp_115, 
                  ((0x8aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8aU]));
    VL_CONCAT_WWI(3808,3776,32, __Vtemp_117, __Vtemp_116, 
                  ((0x89U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x89U]));
    VL_CONCAT_WWI(3840,3808,32, __Vtemp_118, __Vtemp_117, 
                  ((0x88U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x88U]));
    VL_CONCAT_WWI(3872,3840,32, __Vtemp_119, __Vtemp_118, 
                  ((0x87U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x87U]));
    VL_CONCAT_WWI(3904,3872,32, __Vtemp_120, __Vtemp_119, 
                  ((0x86U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x86U]));
    VL_CONCAT_WWI(3936,3904,32, __Vtemp_121, __Vtemp_120, 
                  ((0x85U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x85U]));
    VL_CONCAT_WWI(3968,3936,32, __Vtemp_122, __Vtemp_121, 
                  ((0x84U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x84U]));
    VL_CONCAT_WWI(4000,3968,32, __Vtemp_123, __Vtemp_122, 
                  ((0x83U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x83U]));
    VL_CONCAT_WWI(4032,4000,32, __Vtemp_124, __Vtemp_123, 
                  ((0x82U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x82U]));
    VL_CONCAT_WWI(4064,4032,32, __Vtemp_125, __Vtemp_124, 
                  ((0x81U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x81U]));
    VL_CONCAT_WWI(4096,4064,32, __Vtemp_126, __Vtemp_125, 
                  ((0x80U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x80U]));
    VL_CONCAT_WWI(4128,4096,32, __Vtemp_127, __Vtemp_126, 
                  ((0x7fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7fU]));
    VL_CONCAT_WWI(4160,4128,32, __Vtemp_128, __Vtemp_127, 
                  ((0x7eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7eU]));
    VL_CONCAT_WWI(4192,4160,32, __Vtemp_129, __Vtemp_128, 
                  ((0x7dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7dU]));
    VL_CONCAT_WWI(4224,4192,32, __Vtemp_130, __Vtemp_129, 
                  ((0x7cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7cU]));
    VL_CONCAT_WWI(4256,4224,32, __Vtemp_131, __Vtemp_130, 
                  ((0x7bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7bU]));
    VL_CONCAT_WWI(4288,4256,32, __Vtemp_132, __Vtemp_131, 
                  ((0x7aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7aU]));
    VL_CONCAT_WWI(4320,4288,32, __Vtemp_133, __Vtemp_132, 
                  ((0x79U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x79U]));
    VL_CONCAT_WWI(4352,4320,32, __Vtemp_134, __Vtemp_133, 
                  ((0x78U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x78U]));
    VL_CONCAT_WWI(4384,4352,32, __Vtemp_135, __Vtemp_134, 
                  ((0x77U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x77U]));
    VL_CONCAT_WWI(4416,4384,32, __Vtemp_136, __Vtemp_135, 
                  ((0x76U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x76U]));
    VL_CONCAT_WWI(4448,4416,32, __Vtemp_137, __Vtemp_136, 
                  ((0x75U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x75U]));
    VL_CONCAT_WWI(4480,4448,32, __Vtemp_138, __Vtemp_137, 
                  ((0x74U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x74U]));
    VL_CONCAT_WWI(4512,4480,32, __Vtemp_139, __Vtemp_138, 
                  ((0x73U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x73U]));
    VL_CONCAT_WWI(4544,4512,32, __Vtemp_140, __Vtemp_139, 
                  ((0x72U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x72U]));
    VL_CONCAT_WWI(4576,4544,32, __Vtemp_141, __Vtemp_140, 
                  ((0x71U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x71U]));
    VL_CONCAT_WWI(4608,4576,32, __Vtemp_142, __Vtemp_141, 
                  ((0x70U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x70U]));
    VL_CONCAT_WWI(4640,4608,32, __Vtemp_143, __Vtemp_142, 
                  ((0x6fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6fU]));
    VL_CONCAT_WWI(4672,4640,32, __Vtemp_144, __Vtemp_143, 
                  ((0x6eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6eU]));
    VL_CONCAT_WWI(4704,4672,32, __Vtemp_145, __Vtemp_144, 
                  ((0x6dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6dU]));
    VL_CONCAT_WWI(4736,4704,32, __Vtemp_146, __Vtemp_145, 
                  ((0x6cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6cU]));
    VL_CONCAT_WWI(4768,4736,32, __Vtemp_147, __Vtemp_146, 
                  ((0x6bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6bU]));
    VL_CONCAT_WWI(4800,4768,32, __Vtemp_148, __Vtemp_147, 
                  ((0x6aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6aU]));
    VL_CONCAT_WWI(4832,4800,32, __Vtemp_149, __Vtemp_148, 
                  ((0x69U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x69U]));
    VL_CONCAT_WWI(4864,4832,32, __Vtemp_150, __Vtemp_149, 
                  ((0x68U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x68U]));
    VL_CONCAT_WWI(4896,4864,32, __Vtemp_151, __Vtemp_150, 
                  ((0x67U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x67U]));
    VL_CONCAT_WWI(4928,4896,32, __Vtemp_152, __Vtemp_151, 
                  ((0x66U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x66U]));
    VL_CONCAT_WWI(4960,4928,32, __Vtemp_153, __Vtemp_152, 
                  ((0x65U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x65U]));
    VL_CONCAT_WWI(4992,4960,32, __Vtemp_154, __Vtemp_153, 
                  ((0x64U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x64U]));
    VL_CONCAT_WWI(5024,4992,32, __Vtemp_155, __Vtemp_154, 
                  ((0x63U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x63U]));
    VL_CONCAT_WWI(5056,5024,32, __Vtemp_156, __Vtemp_155, 
                  ((0x62U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x62U]));
    VL_CONCAT_WWI(5088,5056,32, __Vtemp_157, __Vtemp_156, 
                  ((0x61U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x61U]));
    VL_CONCAT_WWI(5120,5088,32, __Vtemp_158, __Vtemp_157, 
                  ((0x60U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x60U]));
    VL_CONCAT_WWI(5152,5120,32, __Vtemp_159, __Vtemp_158, 
                  ((0x5fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5fU]));
    VL_CONCAT_WWI(5184,5152,32, __Vtemp_160, __Vtemp_159, 
                  ((0x5eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5eU]));
    VL_CONCAT_WWI(5216,5184,32, __Vtemp_161, __Vtemp_160, 
                  ((0x5dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5dU]));
    VL_CONCAT_WWI(5248,5216,32, __Vtemp_162, __Vtemp_161, 
                  ((0x5cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5cU]));
    VL_CONCAT_WWI(5280,5248,32, __Vtemp_163, __Vtemp_162, 
                  ((0x5bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5bU]));
    VL_CONCAT_WWI(5312,5280,32, __Vtemp_164, __Vtemp_163, 
                  ((0x5aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5aU]));
    VL_CONCAT_WWI(5344,5312,32, __Vtemp_165, __Vtemp_164, 
                  ((0x59U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x59U]));
    VL_CONCAT_WWI(5376,5344,32, __Vtemp_166, __Vtemp_165, 
                  ((0x58U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x58U]));
    VL_CONCAT_WWI(5408,5376,32, __Vtemp_167, __Vtemp_166, 
                  ((0x57U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x57U]));
    VL_CONCAT_WWI(5440,5408,32, __Vtemp_168, __Vtemp_167, 
                  ((0x56U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x56U]));
    VL_CONCAT_WWI(5472,5440,32, __Vtemp_169, __Vtemp_168, 
                  ((0x55U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x55U]));
    VL_CONCAT_WWI(5504,5472,32, __Vtemp_170, __Vtemp_169, 
                  ((0x54U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x54U]));
    VL_CONCAT_WWI(5536,5504,32, __Vtemp_171, __Vtemp_170, 
                  ((0x53U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x53U]));
    VL_CONCAT_WWI(5568,5536,32, __Vtemp_172, __Vtemp_171, 
                  ((0x52U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x52U]));
    VL_CONCAT_WWI(5600,5568,32, __Vtemp_173, __Vtemp_172, 
                  ((0x51U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x51U]));
    VL_CONCAT_WWI(5632,5600,32, __Vtemp_174, __Vtemp_173, 
                  ((0x50U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x50U]));
    VL_CONCAT_WWI(5664,5632,32, __Vtemp_175, __Vtemp_174, 
                  ((0x4fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4fU]));
    VL_CONCAT_WWI(5696,5664,32, __Vtemp_176, __Vtemp_175, 
                  ((0x4eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4eU]));
    VL_CONCAT_WWI(5728,5696,32, __Vtemp_177, __Vtemp_176, 
                  ((0x4dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4dU]));
    VL_CONCAT_WWI(5760,5728,32, __Vtemp_178, __Vtemp_177, 
                  ((0x4cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4cU]));
    VL_CONCAT_WWI(5792,5760,32, __Vtemp_179, __Vtemp_178, 
                  ((0x4bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4bU]));
    VL_CONCAT_WWI(5824,5792,32, __Vtemp_180, __Vtemp_179, 
                  ((0x4aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4aU]));
    VL_CONCAT_WWI(5856,5824,32, __Vtemp_181, __Vtemp_180, 
                  ((0x49U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x49U]));
    VL_CONCAT_WWI(5888,5856,32, __Vtemp_182, __Vtemp_181, 
                  ((0x48U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x48U]));
    VL_CONCAT_WWI(5920,5888,32, __Vtemp_183, __Vtemp_182, 
                  ((0x47U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x47U]));
    VL_CONCAT_WWI(5952,5920,32, __Vtemp_184, __Vtemp_183, 
                  ((0x46U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x46U]));
    VL_CONCAT_WWI(5984,5952,32, __Vtemp_185, __Vtemp_184, 
                  ((0x45U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x45U]));
    VL_CONCAT_WWI(6016,5984,32, __Vtemp_186, __Vtemp_185, 
                  ((0x44U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x44U]));
    VL_CONCAT_WWI(6048,6016,32, __Vtemp_187, __Vtemp_186, 
                  ((0x43U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x43U]));
    VL_CONCAT_WWI(6080,6048,32, __Vtemp_188, __Vtemp_187, 
                  ((0x42U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x42U]));
    VL_CONCAT_WWI(6112,6080,32, __Vtemp_189, __Vtemp_188, 
                  ((0x41U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x41U]));
    VL_CONCAT_WWI(6144,6112,32, __Vtemp_190, __Vtemp_189, 
                  ((0x40U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x40U]));
    VL_CONCAT_WWI(6176,6144,32, __Vtemp_191, __Vtemp_190, 
                  ((0x3fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3fU]));
    VL_CONCAT_WWI(6208,6176,32, __Vtemp_192, __Vtemp_191, 
                  ((0x3eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3eU]));
    VL_CONCAT_WWI(6240,6208,32, __Vtemp_193, __Vtemp_192, 
                  ((0x3dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3dU]));
    VL_CONCAT_WWI(6272,6240,32, __Vtemp_194, __Vtemp_193, 
                  ((0x3cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3cU]));
    VL_CONCAT_WWI(6304,6272,32, __Vtemp_195, __Vtemp_194, 
                  ((0x3bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3bU]));
    VL_CONCAT_WWI(6336,6304,32, __Vtemp_196, __Vtemp_195, 
                  ((0x3aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3aU]));
    VL_CONCAT_WWI(6368,6336,32, __Vtemp_197, __Vtemp_196, 
                  ((0x39U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x39U]));
    VL_CONCAT_WWI(6400,6368,32, __Vtemp_198, __Vtemp_197, 
                  ((0x38U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x38U]));
    VL_CONCAT_WWI(6432,6400,32, __Vtemp_199, __Vtemp_198, 
                  ((0x37U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x37U]));
    VL_CONCAT_WWI(6464,6432,32, __Vtemp_200, __Vtemp_199, 
                  ((0x36U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x36U]));
    VL_CONCAT_WWI(6496,6464,32, __Vtemp_201, __Vtemp_200, 
                  ((0x35U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x35U]));
    VL_CONCAT_WWI(6528,6496,32, __Vtemp_202, __Vtemp_201, 
                  ((0x34U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x34U]));
    VL_CONCAT_WWI(6560,6528,32, __Vtemp_203, __Vtemp_202, 
                  ((0x33U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x33U]));
    VL_CONCAT_WWI(6592,6560,32, __Vtemp_204, __Vtemp_203, 
                  ((0x32U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x32U]));
    VL_CONCAT_WWI(6624,6592,32, __Vtemp_205, __Vtemp_204, 
                  ((0x31U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x31U]));
    VL_CONCAT_WWI(6656,6624,32, __Vtemp_206, __Vtemp_205, 
                  ((0x30U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x30U]));
    VL_CONCAT_WWI(6688,6656,32, __Vtemp_207, __Vtemp_206, 
                  ((0x2fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2fU]));
    VL_CONCAT_WWI(6720,6688,32, __Vtemp_208, __Vtemp_207, 
                  ((0x2eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2eU]));
    VL_CONCAT_WWI(6752,6720,32, __Vtemp_209, __Vtemp_208, 
                  ((0x2dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2dU]));
    VL_CONCAT_WWI(6784,6752,32, __Vtemp_210, __Vtemp_209, 
                  ((0x2cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2cU]));
    VL_CONCAT_WWI(6816,6784,32, __Vtemp_211, __Vtemp_210, 
                  ((0x2bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2bU]));
    VL_CONCAT_WWI(6848,6816,32, __Vtemp_212, __Vtemp_211, 
                  ((0x2aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2aU]));
    VL_CONCAT_WWI(6880,6848,32, __Vtemp_213, __Vtemp_212, 
                  ((0x29U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x29U]));
    VL_CONCAT_WWI(6912,6880,32, __Vtemp_214, __Vtemp_213, 
                  ((0x28U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x28U]));
    VL_CONCAT_WWI(6944,6912,32, __Vtemp_215, __Vtemp_214, 
                  ((0x27U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x27U]));
    VL_CONCAT_WWI(6976,6944,32, __Vtemp_216, __Vtemp_215, 
                  ((0x26U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x26U]));
    VL_CONCAT_WWI(7008,6976,32, __Vtemp_217, __Vtemp_216, 
                  ((0x25U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x25U]));
    VL_CONCAT_WWI(7040,7008,32, __Vtemp_218, __Vtemp_217, 
                  ((0x24U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x24U]));
    VL_CONCAT_WWI(7072,7040,32, __Vtemp_219, __Vtemp_218, 
                  ((0x23U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x23U]));
    VL_CONCAT_WWI(7104,7072,32, __Vtemp_220, __Vtemp_219, 
                  ((0x22U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x22U]));
    VL_CONCAT_WWI(7136,7104,32, __Vtemp_221, __Vtemp_220, 
                  ((0x21U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x21U]));
    VL_CONCAT_WWI(7168,7136,32, __Vtemp_222, __Vtemp_221, 
                  ((0x20U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x20U]));
    VL_CONCAT_WWI(7200,7168,32, __Vtemp_223, __Vtemp_222, 
                  ((0x1fU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1fU]));
    VL_CONCAT_WWI(7232,7200,32, __Vtemp_224, __Vtemp_223, 
                  ((0x1eU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1eU]));
    VL_CONCAT_WWI(7264,7232,32, __Vtemp_225, __Vtemp_224, 
                  ((0x1dU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1dU]));
    VL_CONCAT_WWI(7296,7264,32, __Vtemp_226, __Vtemp_225, 
                  ((0x1cU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1cU]));
    VL_CONCAT_WWI(7328,7296,32, __Vtemp_227, __Vtemp_226, 
                  ((0x1bU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1bU]));
    VL_CONCAT_WWI(7360,7328,32, __Vtemp_228, __Vtemp_227, 
                  ((0x1aU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1aU]));
    VL_CONCAT_WWI(7392,7360,32, __Vtemp_229, __Vtemp_228, 
                  ((0x19U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x19U]));
    VL_CONCAT_WWI(7424,7392,32, __Vtemp_230, __Vtemp_229, 
                  ((0x18U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x18U]));
    VL_CONCAT_WWI(7456,7424,32, __Vtemp_231, __Vtemp_230, 
                  ((0x17U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x17U]));
    VL_CONCAT_WWI(7488,7456,32, __Vtemp_232, __Vtemp_231, 
                  ((0x16U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x16U]));
    VL_CONCAT_WWI(7520,7488,32, __Vtemp_233, __Vtemp_232, 
                  ((0x15U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x15U]));
    VL_CONCAT_WWI(7552,7520,32, __Vtemp_234, __Vtemp_233, 
                  ((0x14U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x14U]));
    VL_CONCAT_WWI(7584,7552,32, __Vtemp_235, __Vtemp_234, 
                  ((0x13U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x13U]));
    VL_CONCAT_WWI(7616,7584,32, __Vtemp_236, __Vtemp_235, 
                  ((0x12U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x12U]));
    VL_CONCAT_WWI(7648,7616,32, __Vtemp_237, __Vtemp_236, 
                  ((0x11U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x11U]));
    VL_CONCAT_WWI(7680,7648,32, __Vtemp_238, __Vtemp_237, 
                  ((0x10U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                               >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x10U]));
    VL_CONCAT_WWI(7712,7680,32, __Vtemp_239, __Vtemp_238, 
                  ((0xfU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                              >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfU]));
    VL_CONCAT_WWI(7744,7712,32, __Vtemp_240, __Vtemp_239, 
                  ((0xeU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                              >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xeU]));
    VL_CONCAT_WWI(7776,7744,32, __Vtemp_241, __Vtemp_240, 
                  ((0xdU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                              >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdU]));
    VL_CONCAT_WWI(7808,7776,32, __Vtemp_242, __Vtemp_241, 
                  ((0xcU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                              >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcU]));
    VL_CONCAT_WWI(7840,7808,32, __Vtemp_243, __Vtemp_242, 
                  ((0xbU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                              >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbU]));
    VL_CONCAT_WWI(7872,7840,32, __Vtemp_244, __Vtemp_243, 
                  ((0xaU == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                              >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xaU]));
    VL_CONCAT_WWI(7904,7872,32, __Vtemp_245, __Vtemp_244, 
                  ((9U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[9U]));
    VL_CONCAT_WWI(7936,7904,32, __Vtemp_246, __Vtemp_245, 
                  ((8U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[8U]));
    VL_CONCAT_WWI(7968,7936,32, __Vtemp_247, __Vtemp_246, 
                  ((7U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[7U]));
    VL_CONCAT_WWI(8000,7968,32, __Vtemp_248, __Vtemp_247, 
                  ((6U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[6U]));
    VL_CONCAT_WWI(8032,8000,32, __Vtemp_249, __Vtemp_248, 
                  ((5U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[5U]));
    VL_CONCAT_WWI(8064,8032,32, __Vtemp_250, __Vtemp_249, 
                  ((4U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[4U]));
    VL_CONCAT_WWI(8096,8064,32, __Vtemp_251, __Vtemp_250, 
                  ((3U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[3U]));
    VL_CONCAT_WWI(8128,8096,32, __Vtemp_252, __Vtemp_251, 
                  ((2U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[2U]));
    VL_CONCAT_WWI(8160,8128,32, __Vtemp_253, __Vtemp_252, 
                  ((1U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[1U]));
    VL_CONCAT_WWI(8192,8160,32, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem__024D_IN, __Vtemp_253, 
                  ((0U == (0xffU & (IData)((vlSelf->thiele_cpu_kami_tb__DOT__load_data 
                                            >> 0x20U))))
                    ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__load_data)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceRd 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code));
    thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd 
        = ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn)
            ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceVal)
            : (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err));
    thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd 
        = ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn)
            ? (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceVal)
            : (IData)(vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted));
    thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops));
    thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops));
    thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain));
    thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[1U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[1U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[1U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[1U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[1U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[2U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[2U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[2U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[2U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[2U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[3U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[3U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[3U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[3U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[3U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[4U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[4U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[4U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[4U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[4U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[5U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[5U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[5U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[5U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[5U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[6U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[6U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[6U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[6U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[6U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[7U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[7U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[7U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[7U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[7U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[8U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[8U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[8U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[8U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[8U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[9U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[9U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[9U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[9U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[9U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xaU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xaU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xaU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xaU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xaU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xbU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xbU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xbU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xbU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xbU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xcU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xcU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xcU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xcU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xcU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xdU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xdU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xdU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xdU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xdU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xeU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xeU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xeU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xeU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xeU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xfU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xfU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal[0xfU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn[0xfU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor[0xfU]));
    VL_AND_W(256, __Vtemp_257, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceVal);
    VL_NOT_W(256, __Vtemp_258, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn);
    VL_AND_W(256, __Vtemp_259, __Vtemp_258, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem);
    VL_OR_W(256, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd, __Vtemp_257, __Vtemp_259);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[1U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[1U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[1U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[1U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[2U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[2U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[2U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[2U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[3U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[3U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[3U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[3U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[4U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[4U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[4U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[4U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[5U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[5U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[5U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[5U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[6U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[6U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[6U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[6U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[7U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[7U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[7U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[7U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[8U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[8U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[8U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[8U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[9U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[9U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[9U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[9U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xaU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xaU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xaU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xaU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xbU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xbU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xbU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xbU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xcU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xcU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xcU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xcU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xdU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xdU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xdU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xdU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xeU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xeU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xeU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xeU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xfU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0xfU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0xfU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0xfU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x10U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x10U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x10U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x10U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x11U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x11U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x11U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x11U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x12U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x12U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x12U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x12U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x13U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x13U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x13U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x13U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x14U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x14U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x14U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x14U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x15U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x15U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x15U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x15U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x16U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x16U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x16U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x16U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x17U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x17U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x17U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x17U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x18U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x18U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x18U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x18U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x19U] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x19U]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x19U]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x19U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1aU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1aU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1aU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1aU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1bU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1bU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1bU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1bU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1cU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1cU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1cU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1cU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1dU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1dU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1dU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1dU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1eU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1eU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1eU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1eU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1fU] 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal[0x1fU]) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn[0x1fU]) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs[0x1fU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd 
        = ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn 
            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceVal) 
           | ((~ vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn) 
              & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc));
    vlSelf->thiele_cpu_kami_tb__DOT__error_code_out 
        = vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__err_out = thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__halted_out = thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__024EN 
        = (1U & (~ ((IData)(thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceRd) 
                    | (IData)(thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceRd))));
    vlSelf->thiele_cpu_kami_tb__DOT__partition_ops_out 
        = thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__mdl_ops_out = thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__info_gain_out 
        = thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__mu_out = thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_0 = 
        (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0U] 
         + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[1U] 
            + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[2U] 
               + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[3U])));
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_1 = 
        (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[4U] 
         + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[5U] 
            + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[6U] 
               + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[7U])));
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_2 = 
        (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[8U] 
         + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[9U] 
            + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xaU] 
               + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xbU])));
    vlSelf->thiele_cpu_kami_tb__DOT__mu_tensor_3 = 
        (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xcU] 
         + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xdU] 
            + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xeU] 
               + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xfU])));
    vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out 
        = (thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd 
           < ((vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0U] 
               + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[1U] 
                  + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[2U] 
                     + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[3U]))) 
              + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[4U] 
                 + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[5U] 
                    + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[6U] 
                       + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[7U] 
                          + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[8U] 
                             + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[9U] 
                                + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xaU] 
                                   + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xbU] 
                                      + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xcU] 
                                         + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xdU] 
                                            + (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xeU] 
                                               + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xfU])))))))))))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_61___05Fh66790 
        = ((0x80U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                     - (IData)(1U))) ? ((0x40U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                  - (IData)(1U)))
                                         ? ((0x20U 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                - (IData)(1U)))
                                             ? ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xffU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfeU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfdU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfcU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfbU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfaU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf9U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf8U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf7U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf6U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf5U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf4U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf3U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf2U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf1U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf0U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xefU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeeU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xedU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xecU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xebU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeaU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe9U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe8U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe7U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe6U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe5U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe4U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe3U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe2U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe1U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe0U])))))
                                             : ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdfU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdeU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xddU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdcU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdbU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdaU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd9U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd8U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd7U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd6U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd5U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd4U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd3U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd2U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd1U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd0U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcfU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xceU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcdU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xccU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcbU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcaU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc9U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc8U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc7U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc6U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc5U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc4U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc3U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc2U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc1U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc0U]))))))
                                         : ((0x20U 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                - (IData)(1U)))
                                             ? ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbfU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbeU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbdU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbcU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbbU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbaU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb9U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb8U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb7U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb6U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb5U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb4U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb3U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb2U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb1U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb0U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xafU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaeU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xadU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xacU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xabU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaaU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa9U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa8U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa7U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa6U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa5U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa4U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa3U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa2U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa1U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa0U])))))
                                             : ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x99U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x98U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x97U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x96U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x95U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x94U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x93U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x92U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x91U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x90U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x89U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x88U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x87U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x86U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x85U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x84U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x83U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x82U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x81U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x80U])))))))
            : ((0x40U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                         - (IData)(1U))) ? ((0x20U 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                - (IData)(1U)))
                                             ? ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x79U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x78U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x77U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x76U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x75U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x74U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x73U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x72U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x71U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x70U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x69U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x68U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x67U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x66U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x65U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x64U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x63U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x62U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x61U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x60U])))))
                                             : ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x59U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x58U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x57U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x56U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x55U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x54U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x53U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x52U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x51U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x50U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x49U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x48U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x47U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x46U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x45U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x44U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x43U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x42U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x41U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x40U]))))))
                : ((0x20U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                             - (IData)(1U))) ? ((0x10U 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                    - (IData)(1U)))
                                                 ? 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x39U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x38U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x37U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x36U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x35U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x34U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x33U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x32U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x31U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x30U]))))
                                                 : 
                                                ((8U 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                     - (IData)(1U)))
                                                  ? 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x29U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x28U])))
                                                  : 
                                                 ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x27U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x26U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x25U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x24U]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x23U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x22U])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x21U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x20U])))))
                    : ((0x10U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                 - (IData)(1U))) ? 
                       ((8U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                               - (IData)(1U))) ? ((4U 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                      - (IData)(1U)))
                                                   ? 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1fU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1eU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1dU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1cU]))
                                                   : 
                                                  ((2U 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                       - (IData)(1U)))
                                                    ? 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1bU]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1aU])
                                                    : 
                                                   ((1U 
                                                     & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                                        - (IData)(1U)))
                                                     ? 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x19U]
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x18U])))
                         : ((4U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                   - (IData)(1U))) ? 
                            ((2U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                    - (IData)(1U)))
                              ? ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                        - (IData)(1U)))
                                  ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x17U]
                                  : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x16U])
                              : ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                        - (IData)(1U)))
                                  ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x15U]
                                  : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x14U]))
                             : ((2U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                       - (IData)(1U)))
                                 ? ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                           - (IData)(1U)))
                                     ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x13U]
                                     : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x12U])
                                 : ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                           - (IData)(1U)))
                                     ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x11U]
                                     : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x10U]))))
                        : ((8U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                  - (IData)(1U))) ? 
                           ((4U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                   - (IData)(1U))) ? 
                            ((2U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                    - (IData)(1U)))
                              ? ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                        - (IData)(1U)))
                                  ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfU]
                                  : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeU])
                              : ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                        - (IData)(1U)))
                                  ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdU]
                                  : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcU]))
                             : ((2U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                       - (IData)(1U)))
                                 ? ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                           - (IData)(1U)))
                                     ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbU]
                                     : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaU])
                                 : ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                           - (IData)(1U)))
                                     ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[9U]
                                     : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[8U])))
                            : ((4U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                      - (IData)(1U)))
                                ? ((2U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                          - (IData)(1U)))
                                    ? ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                              - (IData)(1U)))
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[6U])
                                    : ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                              - (IData)(1U)))
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[4U]))
                                : ((2U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                          - (IData)(1U)))
                                    ? ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                              - (IData)(1U)))
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[2U])
                                    : ((1U & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                              - (IData)(1U)))
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0U]))))))));
    vlSelf->thiele_cpu_kami_tb__DOT__pc_out = vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd;
    vlSelf->thiele_cpu_kami_tb__DOT__current_instr 
        = (((0U == (0x1fU & VL_SHIFTL_III(13,32,32, 
                                          (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd), 5U)))
             ? 0U : (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[
                     (((IData)(0x1fU) + (0x1fffU & 
                                         VL_SHIFTL_III(13,32,32, 
                                                       (0xffU 
                                                        & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd), 5U))) 
                      >> 5U)] << ((IData)(0x20U) - 
                                  (0x1fU & VL_SHIFTL_III(13,32,32, 
                                                         (0xffU 
                                                          & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd), 5U))))) 
           | (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[
              (0xffU & (VL_SHIFTL_III(13,32,32, (0xffU 
                                                 & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd), 5U) 
                        >> 5U))] >> (0x1fU & VL_SHIFTL_III(13,32,32, 
                                                           (0xffU 
                                                            & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd), 5U))));
    __Vtemp_324[0U] = ((0xc0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc0U]);
    __Vtemp_324[1U] = ((0xc1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc1U]);
    __Vtemp_324[2U] = ((0xc2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc2U]);
    __Vtemp_324[3U] = ((0xc3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc3U]);
    __Vtemp_324[4U] = ((0xc4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc4U]);
    __Vtemp_324[5U] = ((0xc5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc5U]);
    __Vtemp_324[6U] = ((0xc6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc6U]);
    __Vtemp_324[7U] = ((0xc7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc7U]);
    __Vtemp_324[8U] = ((0xc8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc8U]);
    __Vtemp_324[9U] = ((0xc9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                        ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc9U]);
    __Vtemp_324[0xaU] = ((0xcaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                          ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcaU]);
    __Vtemp_324[0xbU] = ((0xcbU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                          ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcbU]);
    __Vtemp_324[0xcU] = ((0xccU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                          ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xccU]);
    __Vtemp_324[0xdU] = ((0xcdU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                          ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcdU]);
    __Vtemp_324[0xeU] = ((0xceU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                          ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xceU]);
    __Vtemp_324[0xfU] = ((0xcfU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                          ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcfU]);
    __Vtemp_324[0x10U] = ((0xd0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd0U]);
    __Vtemp_324[0x11U] = ((0xd1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd1U]);
    __Vtemp_324[0x12U] = ((0xd2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd2U]);
    __Vtemp_324[0x13U] = ((0xd3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd3U]);
    __Vtemp_324[0x14U] = ((0xd4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd4U]);
    __Vtemp_324[0x15U] = ((0xd5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd5U]);
    __Vtemp_324[0x16U] = ((0xd6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd6U]);
    __Vtemp_324[0x17U] = ((0xd7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd7U]);
    __Vtemp_324[0x18U] = ((0xd8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd8U]);
    __Vtemp_324[0x19U] = ((0xd9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd9U]);
    __Vtemp_324[0x1aU] = ((0xdaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdaU]);
    __Vtemp_324[0x1bU] = ((0xdbU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdbU]);
    __Vtemp_324[0x1cU] = ((0xdcU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdcU]);
    __Vtemp_324[0x1dU] = ((0xddU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xddU]);
    __Vtemp_324[0x1eU] = ((0xdeU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdeU]);
    __Vtemp_324[0x1fU] = ((0xdfU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdfU]);
    __Vtemp_324[0x20U] = ((0xe0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe0U]);
    __Vtemp_324[0x21U] = ((0xe1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe1U]);
    __Vtemp_324[0x22U] = ((0xe2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe2U]);
    __Vtemp_324[0x23U] = ((0xe3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe3U]);
    __Vtemp_324[0x24U] = ((0xe4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe4U]);
    __Vtemp_324[0x25U] = ((0xe5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe5U]);
    __Vtemp_324[0x26U] = ((0xe6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe6U]);
    __Vtemp_324[0x27U] = ((0xe7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe7U]);
    __Vtemp_324[0x28U] = ((0xe8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe8U]);
    __Vtemp_324[0x29U] = ((0xe9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe9U]);
    __Vtemp_324[0x2aU] = ((0xeaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeaU]);
    __Vtemp_324[0x2bU] = ((0xebU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xebU]);
    __Vtemp_324[0x2cU] = ((0xecU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xecU]);
    __Vtemp_324[0x2dU] = ((0xedU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xedU]);
    __Vtemp_324[0x2eU] = ((0xeeU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeeU]);
    __Vtemp_324[0x2fU] = ((0xefU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xefU]);
    __Vtemp_324[0x30U] = ((0xf0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf0U]);
    __Vtemp_324[0x31U] = ((0xf1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf1U]);
    __Vtemp_324[0x32U] = ((0xf2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf2U]);
    __Vtemp_324[0x33U] = ((0xf3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf3U]);
    __Vtemp_324[0x34U] = ((0xf4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf4U]);
    __Vtemp_324[0x35U] = ((0xf5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf5U]);
    __Vtemp_324[0x36U] = ((0xf6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf6U]);
    __Vtemp_324[0x37U] = ((0xf7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf7U]);
    __Vtemp_324[0x38U] = ((0xf8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf8U]);
    __Vtemp_324[0x39U] = ((0xf9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf9U]);
    __Vtemp_324[0x3aU] = ((0xfaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfaU]);
    __Vtemp_324[0x3bU] = ((0xfbU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfbU]);
    __Vtemp_324[0x3cU] = ((0xfcU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfcU]);
    __Vtemp_324[0x3dU] = ((0xfdU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                           ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfdU]);
    __Vtemp_324[0x3eU] = (IData)((((QData)((IData)(
                                                   ((0xffU 
                                                     == 
                                                     (0xffU 
                                                      & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                                                     ? 
                                                    ((IData)(1U) 
                                                     + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xffU]))) 
                                   << 0x20U) | (QData)((IData)(
                                                               ((0xfeU 
                                                                 == 
                                                                 (0xffU 
                                                                  & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                                                                 ? 
                                                                ((IData)(1U) 
                                                                 + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                                                 : 
                                                                vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfeU])))));
    __Vtemp_324[0x3fU] = (IData)(((((QData)((IData)(
                                                    ((0xffU 
                                                      == 
                                                      (0xffU 
                                                       & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                                                      ? 
                                                     ((IData)(1U) 
                                                      + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                                      : 
                                                     vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xffU]))) 
                                    << 0x20U) | (QData)((IData)(
                                                                ((0xfeU 
                                                                  == 
                                                                  (0xffU 
                                                                   & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                                                                  ? 
                                                                 ((IData)(1U) 
                                                                  + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                                                  : 
                                                                 vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfeU])))) 
                                  >> 0x20U));
    VL_CONCAT_WWI(2080,2048,32, __Vtemp_325, __Vtemp_324, 
                  ((0xbfU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbfU]));
    VL_CONCAT_WWI(2112,2080,32, __Vtemp_326, __Vtemp_325, 
                  ((0xbeU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbeU]));
    VL_CONCAT_WWI(2144,2112,32, __Vtemp_327, __Vtemp_326, 
                  ((0xbdU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbdU]));
    VL_CONCAT_WWI(2176,2144,32, __Vtemp_328, __Vtemp_327, 
                  ((0xbcU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbcU]));
    VL_CONCAT_WWI(2208,2176,32, __Vtemp_329, __Vtemp_328, 
                  ((0xbbU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbbU]));
    VL_CONCAT_WWI(2240,2208,32, __Vtemp_330, __Vtemp_329, 
                  ((0xbaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbaU]));
    VL_CONCAT_WWI(2272,2240,32, __Vtemp_331, __Vtemp_330, 
                  ((0xb9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb9U]));
    VL_CONCAT_WWI(2304,2272,32, __Vtemp_332, __Vtemp_331, 
                  ((0xb8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb8U]));
    VL_CONCAT_WWI(2336,2304,32, __Vtemp_333, __Vtemp_332, 
                  ((0xb7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb7U]));
    VL_CONCAT_WWI(2368,2336,32, __Vtemp_334, __Vtemp_333, 
                  ((0xb6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb6U]));
    VL_CONCAT_WWI(2400,2368,32, __Vtemp_335, __Vtemp_334, 
                  ((0xb5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb5U]));
    VL_CONCAT_WWI(2432,2400,32, __Vtemp_336, __Vtemp_335, 
                  ((0xb4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb4U]));
    VL_CONCAT_WWI(2464,2432,32, __Vtemp_337, __Vtemp_336, 
                  ((0xb3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb3U]));
    VL_CONCAT_WWI(2496,2464,32, __Vtemp_338, __Vtemp_337, 
                  ((0xb2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb2U]));
    VL_CONCAT_WWI(2528,2496,32, __Vtemp_339, __Vtemp_338, 
                  ((0xb1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb1U]));
    VL_CONCAT_WWI(2560,2528,32, __Vtemp_340, __Vtemp_339, 
                  ((0xb0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb0U]));
    VL_CONCAT_WWI(2592,2560,32, __Vtemp_341, __Vtemp_340, 
                  ((0xafU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xafU]));
    VL_CONCAT_WWI(2624,2592,32, __Vtemp_342, __Vtemp_341, 
                  ((0xaeU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaeU]));
    VL_CONCAT_WWI(2656,2624,32, __Vtemp_343, __Vtemp_342, 
                  ((0xadU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xadU]));
    VL_CONCAT_WWI(2688,2656,32, __Vtemp_344, __Vtemp_343, 
                  ((0xacU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xacU]));
    VL_CONCAT_WWI(2720,2688,32, __Vtemp_345, __Vtemp_344, 
                  ((0xabU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xabU]));
    VL_CONCAT_WWI(2752,2720,32, __Vtemp_346, __Vtemp_345, 
                  ((0xaaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaaU]));
    VL_CONCAT_WWI(2784,2752,32, __Vtemp_347, __Vtemp_346, 
                  ((0xa9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa9U]));
    VL_CONCAT_WWI(2816,2784,32, __Vtemp_348, __Vtemp_347, 
                  ((0xa8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa8U]));
    VL_CONCAT_WWI(2848,2816,32, __Vtemp_349, __Vtemp_348, 
                  ((0xa7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa7U]));
    VL_CONCAT_WWI(2880,2848,32, __Vtemp_350, __Vtemp_349, 
                  ((0xa6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa6U]));
    VL_CONCAT_WWI(2912,2880,32, __Vtemp_351, __Vtemp_350, 
                  ((0xa5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa5U]));
    VL_CONCAT_WWI(2944,2912,32, __Vtemp_352, __Vtemp_351, 
                  ((0xa4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa4U]));
    VL_CONCAT_WWI(2976,2944,32, __Vtemp_353, __Vtemp_352, 
                  ((0xa3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa3U]));
    VL_CONCAT_WWI(3008,2976,32, __Vtemp_354, __Vtemp_353, 
                  ((0xa2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa2U]));
    VL_CONCAT_WWI(3040,3008,32, __Vtemp_355, __Vtemp_354, 
                  ((0xa1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa1U]));
    VL_CONCAT_WWI(3072,3040,32, __Vtemp_356, __Vtemp_355, 
                  ((0xa0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa0U]));
    VL_CONCAT_WWI(3104,3072,32, __Vtemp_357, __Vtemp_356, 
                  ((0x9fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9fU]));
    VL_CONCAT_WWI(3136,3104,32, __Vtemp_358, __Vtemp_357, 
                  ((0x9eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9eU]));
    VL_CONCAT_WWI(3168,3136,32, __Vtemp_359, __Vtemp_358, 
                  ((0x9dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9dU]));
    VL_CONCAT_WWI(3200,3168,32, __Vtemp_360, __Vtemp_359, 
                  ((0x9cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9cU]));
    VL_CONCAT_WWI(3232,3200,32, __Vtemp_361, __Vtemp_360, 
                  ((0x9bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9bU]));
    VL_CONCAT_WWI(3264,3232,32, __Vtemp_362, __Vtemp_361, 
                  ((0x9aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9aU]));
    VL_CONCAT_WWI(3296,3264,32, __Vtemp_363, __Vtemp_362, 
                  ((0x99U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x99U]));
    VL_CONCAT_WWI(3328,3296,32, __Vtemp_364, __Vtemp_363, 
                  ((0x98U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x98U]));
    VL_CONCAT_WWI(3360,3328,32, __Vtemp_365, __Vtemp_364, 
                  ((0x97U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x97U]));
    VL_CONCAT_WWI(3392,3360,32, __Vtemp_366, __Vtemp_365, 
                  ((0x96U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x96U]));
    VL_CONCAT_WWI(3424,3392,32, __Vtemp_367, __Vtemp_366, 
                  ((0x95U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x95U]));
    VL_CONCAT_WWI(3456,3424,32, __Vtemp_368, __Vtemp_367, 
                  ((0x94U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x94U]));
    VL_CONCAT_WWI(3488,3456,32, __Vtemp_369, __Vtemp_368, 
                  ((0x93U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x93U]));
    VL_CONCAT_WWI(3520,3488,32, __Vtemp_370, __Vtemp_369, 
                  ((0x92U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x92U]));
    VL_CONCAT_WWI(3552,3520,32, __Vtemp_371, __Vtemp_370, 
                  ((0x91U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x91U]));
    VL_CONCAT_WWI(3584,3552,32, __Vtemp_372, __Vtemp_371, 
                  ((0x90U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x90U]));
    VL_CONCAT_WWI(3616,3584,32, __Vtemp_373, __Vtemp_372, 
                  ((0x8fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8fU]));
    VL_CONCAT_WWI(3648,3616,32, __Vtemp_374, __Vtemp_373, 
                  ((0x8eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8eU]));
    VL_CONCAT_WWI(3680,3648,32, __Vtemp_375, __Vtemp_374, 
                  ((0x8dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8dU]));
    VL_CONCAT_WWI(3712,3680,32, __Vtemp_376, __Vtemp_375, 
                  ((0x8cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8cU]));
    VL_CONCAT_WWI(3744,3712,32, __Vtemp_377, __Vtemp_376, 
                  ((0x8bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8bU]));
    VL_CONCAT_WWI(3776,3744,32, __Vtemp_378, __Vtemp_377, 
                  ((0x8aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8aU]));
    VL_CONCAT_WWI(3808,3776,32, __Vtemp_379, __Vtemp_378, 
                  ((0x89U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x89U]));
    VL_CONCAT_WWI(3840,3808,32, __Vtemp_380, __Vtemp_379, 
                  ((0x88U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x88U]));
    VL_CONCAT_WWI(3872,3840,32, __Vtemp_381, __Vtemp_380, 
                  ((0x87U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x87U]));
    VL_CONCAT_WWI(3904,3872,32, __Vtemp_382, __Vtemp_381, 
                  ((0x86U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x86U]));
    VL_CONCAT_WWI(3936,3904,32, __Vtemp_383, __Vtemp_382, 
                  ((0x85U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x85U]));
    VL_CONCAT_WWI(3968,3936,32, __Vtemp_384, __Vtemp_383, 
                  ((0x84U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x84U]));
    VL_CONCAT_WWI(4000,3968,32, __Vtemp_385, __Vtemp_384, 
                  ((0x83U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x83U]));
    VL_CONCAT_WWI(4032,4000,32, __Vtemp_386, __Vtemp_385, 
                  ((0x82U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x82U]));
    VL_CONCAT_WWI(4064,4032,32, __Vtemp_387, __Vtemp_386, 
                  ((0x81U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x81U]));
    VL_CONCAT_WWI(4096,4064,32, __Vtemp_388, __Vtemp_387, 
                  ((0x80U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x80U]));
    VL_CONCAT_WWI(4128,4096,32, __Vtemp_389, __Vtemp_388, 
                  ((0x7fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7fU]));
    VL_CONCAT_WWI(4160,4128,32, __Vtemp_390, __Vtemp_389, 
                  ((0x7eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7eU]));
    VL_CONCAT_WWI(4192,4160,32, __Vtemp_391, __Vtemp_390, 
                  ((0x7dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7dU]));
    VL_CONCAT_WWI(4224,4192,32, __Vtemp_392, __Vtemp_391, 
                  ((0x7cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7cU]));
    VL_CONCAT_WWI(4256,4224,32, __Vtemp_393, __Vtemp_392, 
                  ((0x7bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7bU]));
    VL_CONCAT_WWI(4288,4256,32, __Vtemp_394, __Vtemp_393, 
                  ((0x7aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7aU]));
    VL_CONCAT_WWI(4320,4288,32, __Vtemp_395, __Vtemp_394, 
                  ((0x79U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x79U]));
    VL_CONCAT_WWI(4352,4320,32, __Vtemp_396, __Vtemp_395, 
                  ((0x78U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x78U]));
    VL_CONCAT_WWI(4384,4352,32, __Vtemp_397, __Vtemp_396, 
                  ((0x77U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x77U]));
    VL_CONCAT_WWI(4416,4384,32, __Vtemp_398, __Vtemp_397, 
                  ((0x76U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x76U]));
    VL_CONCAT_WWI(4448,4416,32, __Vtemp_399, __Vtemp_398, 
                  ((0x75U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x75U]));
    VL_CONCAT_WWI(4480,4448,32, __Vtemp_400, __Vtemp_399, 
                  ((0x74U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x74U]));
    VL_CONCAT_WWI(4512,4480,32, __Vtemp_401, __Vtemp_400, 
                  ((0x73U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x73U]));
    VL_CONCAT_WWI(4544,4512,32, __Vtemp_402, __Vtemp_401, 
                  ((0x72U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x72U]));
    VL_CONCAT_WWI(4576,4544,32, __Vtemp_403, __Vtemp_402, 
                  ((0x71U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x71U]));
    VL_CONCAT_WWI(4608,4576,32, __Vtemp_404, __Vtemp_403, 
                  ((0x70U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x70U]));
    VL_CONCAT_WWI(4640,4608,32, __Vtemp_405, __Vtemp_404, 
                  ((0x6fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6fU]));
    VL_CONCAT_WWI(4672,4640,32, __Vtemp_406, __Vtemp_405, 
                  ((0x6eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6eU]));
    VL_CONCAT_WWI(4704,4672,32, __Vtemp_407, __Vtemp_406, 
                  ((0x6dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6dU]));
    VL_CONCAT_WWI(4736,4704,32, __Vtemp_408, __Vtemp_407, 
                  ((0x6cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6cU]));
    VL_CONCAT_WWI(4768,4736,32, __Vtemp_409, __Vtemp_408, 
                  ((0x6bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6bU]));
    VL_CONCAT_WWI(4800,4768,32, __Vtemp_410, __Vtemp_409, 
                  ((0x6aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6aU]));
    VL_CONCAT_WWI(4832,4800,32, __Vtemp_411, __Vtemp_410, 
                  ((0x69U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x69U]));
    VL_CONCAT_WWI(4864,4832,32, __Vtemp_412, __Vtemp_411, 
                  ((0x68U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x68U]));
    VL_CONCAT_WWI(4896,4864,32, __Vtemp_413, __Vtemp_412, 
                  ((0x67U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x67U]));
    VL_CONCAT_WWI(4928,4896,32, __Vtemp_414, __Vtemp_413, 
                  ((0x66U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x66U]));
    VL_CONCAT_WWI(4960,4928,32, __Vtemp_415, __Vtemp_414, 
                  ((0x65U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x65U]));
    VL_CONCAT_WWI(4992,4960,32, __Vtemp_416, __Vtemp_415, 
                  ((0x64U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x64U]));
    VL_CONCAT_WWI(5024,4992,32, __Vtemp_417, __Vtemp_416, 
                  ((0x63U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x63U]));
    VL_CONCAT_WWI(5056,5024,32, __Vtemp_418, __Vtemp_417, 
                  ((0x62U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x62U]));
    VL_CONCAT_WWI(5088,5056,32, __Vtemp_419, __Vtemp_418, 
                  ((0x61U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x61U]));
    VL_CONCAT_WWI(5120,5088,32, __Vtemp_420, __Vtemp_419, 
                  ((0x60U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x60U]));
    VL_CONCAT_WWI(5152,5120,32, __Vtemp_421, __Vtemp_420, 
                  ((0x5fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5fU]));
    VL_CONCAT_WWI(5184,5152,32, __Vtemp_422, __Vtemp_421, 
                  ((0x5eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5eU]));
    VL_CONCAT_WWI(5216,5184,32, __Vtemp_423, __Vtemp_422, 
                  ((0x5dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5dU]));
    VL_CONCAT_WWI(5248,5216,32, __Vtemp_424, __Vtemp_423, 
                  ((0x5cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5cU]));
    VL_CONCAT_WWI(5280,5248,32, __Vtemp_425, __Vtemp_424, 
                  ((0x5bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5bU]));
    VL_CONCAT_WWI(5312,5280,32, __Vtemp_426, __Vtemp_425, 
                  ((0x5aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5aU]));
    VL_CONCAT_WWI(5344,5312,32, __Vtemp_427, __Vtemp_426, 
                  ((0x59U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x59U]));
    VL_CONCAT_WWI(5376,5344,32, __Vtemp_428, __Vtemp_427, 
                  ((0x58U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x58U]));
    VL_CONCAT_WWI(5408,5376,32, __Vtemp_429, __Vtemp_428, 
                  ((0x57U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x57U]));
    VL_CONCAT_WWI(5440,5408,32, __Vtemp_430, __Vtemp_429, 
                  ((0x56U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x56U]));
    VL_CONCAT_WWI(5472,5440,32, __Vtemp_431, __Vtemp_430, 
                  ((0x55U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x55U]));
    VL_CONCAT_WWI(5504,5472,32, __Vtemp_432, __Vtemp_431, 
                  ((0x54U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x54U]));
    VL_CONCAT_WWI(5536,5504,32, __Vtemp_433, __Vtemp_432, 
                  ((0x53U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x53U]));
    VL_CONCAT_WWI(5568,5536,32, __Vtemp_434, __Vtemp_433, 
                  ((0x52U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x52U]));
    VL_CONCAT_WWI(5600,5568,32, __Vtemp_435, __Vtemp_434, 
                  ((0x51U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x51U]));
    VL_CONCAT_WWI(5632,5600,32, __Vtemp_436, __Vtemp_435, 
                  ((0x50U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x50U]));
    VL_CONCAT_WWI(5664,5632,32, __Vtemp_437, __Vtemp_436, 
                  ((0x4fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4fU]));
    VL_CONCAT_WWI(5696,5664,32, __Vtemp_438, __Vtemp_437, 
                  ((0x4eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4eU]));
    VL_CONCAT_WWI(5728,5696,32, __Vtemp_439, __Vtemp_438, 
                  ((0x4dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4dU]));
    VL_CONCAT_WWI(5760,5728,32, __Vtemp_440, __Vtemp_439, 
                  ((0x4cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4cU]));
    VL_CONCAT_WWI(5792,5760,32, __Vtemp_441, __Vtemp_440, 
                  ((0x4bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4bU]));
    VL_CONCAT_WWI(5824,5792,32, __Vtemp_442, __Vtemp_441, 
                  ((0x4aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4aU]));
    VL_CONCAT_WWI(5856,5824,32, __Vtemp_443, __Vtemp_442, 
                  ((0x49U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x49U]));
    VL_CONCAT_WWI(5888,5856,32, __Vtemp_444, __Vtemp_443, 
                  ((0x48U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x48U]));
    VL_CONCAT_WWI(5920,5888,32, __Vtemp_445, __Vtemp_444, 
                  ((0x47U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x47U]));
    VL_CONCAT_WWI(5952,5920,32, __Vtemp_446, __Vtemp_445, 
                  ((0x46U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x46U]));
    VL_CONCAT_WWI(5984,5952,32, __Vtemp_447, __Vtemp_446, 
                  ((0x45U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x45U]));
    VL_CONCAT_WWI(6016,5984,32, __Vtemp_448, __Vtemp_447, 
                  ((0x44U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x44U]));
    VL_CONCAT_WWI(6048,6016,32, __Vtemp_449, __Vtemp_448, 
                  ((0x43U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x43U]));
    VL_CONCAT_WWI(6080,6048,32, __Vtemp_450, __Vtemp_449, 
                  ((0x42U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x42U]));
    VL_CONCAT_WWI(6112,6080,32, __Vtemp_451, __Vtemp_450, 
                  ((0x41U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x41U]));
    VL_CONCAT_WWI(6144,6112,32, __Vtemp_452, __Vtemp_451, 
                  ((0x40U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x40U]));
    VL_CONCAT_WWI(6176,6144,32, __Vtemp_453, __Vtemp_452, 
                  ((0x3fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3fU]));
    VL_CONCAT_WWI(6208,6176,32, __Vtemp_454, __Vtemp_453, 
                  ((0x3eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3eU]));
    VL_CONCAT_WWI(6240,6208,32, __Vtemp_455, __Vtemp_454, 
                  ((0x3dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3dU]));
    VL_CONCAT_WWI(6272,6240,32, __Vtemp_456, __Vtemp_455, 
                  ((0x3cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3cU]));
    VL_CONCAT_WWI(6304,6272,32, __Vtemp_457, __Vtemp_456, 
                  ((0x3bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3bU]));
    VL_CONCAT_WWI(6336,6304,32, __Vtemp_458, __Vtemp_457, 
                  ((0x3aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3aU]));
    VL_CONCAT_WWI(6368,6336,32, __Vtemp_459, __Vtemp_458, 
                  ((0x39U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x39U]));
    VL_CONCAT_WWI(6400,6368,32, __Vtemp_460, __Vtemp_459, 
                  ((0x38U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x38U]));
    VL_CONCAT_WWI(6432,6400,32, __Vtemp_461, __Vtemp_460, 
                  ((0x37U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x37U]));
    VL_CONCAT_WWI(6464,6432,32, __Vtemp_462, __Vtemp_461, 
                  ((0x36U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x36U]));
    VL_CONCAT_WWI(6496,6464,32, __Vtemp_463, __Vtemp_462, 
                  ((0x35U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x35U]));
    VL_CONCAT_WWI(6528,6496,32, __Vtemp_464, __Vtemp_463, 
                  ((0x34U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x34U]));
    VL_CONCAT_WWI(6560,6528,32, __Vtemp_465, __Vtemp_464, 
                  ((0x33U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x33U]));
    VL_CONCAT_WWI(6592,6560,32, __Vtemp_466, __Vtemp_465, 
                  ((0x32U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x32U]));
    VL_CONCAT_WWI(6624,6592,32, __Vtemp_467, __Vtemp_466, 
                  ((0x31U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x31U]));
    VL_CONCAT_WWI(6656,6624,32, __Vtemp_468, __Vtemp_467, 
                  ((0x30U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x30U]));
    VL_CONCAT_WWI(6688,6656,32, __Vtemp_469, __Vtemp_468, 
                  ((0x2fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2fU]));
    VL_CONCAT_WWI(6720,6688,32, __Vtemp_470, __Vtemp_469, 
                  ((0x2eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2eU]));
    VL_CONCAT_WWI(6752,6720,32, __Vtemp_471, __Vtemp_470, 
                  ((0x2dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2dU]));
    VL_CONCAT_WWI(6784,6752,32, __Vtemp_472, __Vtemp_471, 
                  ((0x2cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2cU]));
    VL_CONCAT_WWI(6816,6784,32, __Vtemp_473, __Vtemp_472, 
                  ((0x2bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2bU]));
    VL_CONCAT_WWI(6848,6816,32, __Vtemp_474, __Vtemp_473, 
                  ((0x2aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2aU]));
    VL_CONCAT_WWI(6880,6848,32, __Vtemp_475, __Vtemp_474, 
                  ((0x29U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x29U]));
    VL_CONCAT_WWI(6912,6880,32, __Vtemp_476, __Vtemp_475, 
                  ((0x28U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x28U]));
    VL_CONCAT_WWI(6944,6912,32, __Vtemp_477, __Vtemp_476, 
                  ((0x27U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x27U]));
    VL_CONCAT_WWI(6976,6944,32, __Vtemp_478, __Vtemp_477, 
                  ((0x26U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x26U]));
    VL_CONCAT_WWI(7008,6976,32, __Vtemp_479, __Vtemp_478, 
                  ((0x25U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x25U]));
    VL_CONCAT_WWI(7040,7008,32, __Vtemp_480, __Vtemp_479, 
                  ((0x24U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x24U]));
    VL_CONCAT_WWI(7072,7040,32, __Vtemp_481, __Vtemp_480, 
                  ((0x23U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x23U]));
    VL_CONCAT_WWI(7104,7072,32, __Vtemp_482, __Vtemp_481, 
                  ((0x22U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x22U]));
    VL_CONCAT_WWI(7136,7104,32, __Vtemp_483, __Vtemp_482, 
                  ((0x21U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x21U]));
    VL_CONCAT_WWI(7168,7136,32, __Vtemp_484, __Vtemp_483, 
                  ((0x20U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x20U]));
    VL_CONCAT_WWI(7200,7168,32, __Vtemp_485, __Vtemp_484, 
                  ((0x1fU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1fU]));
    VL_CONCAT_WWI(7232,7200,32, __Vtemp_486, __Vtemp_485, 
                  ((0x1eU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1eU]));
    VL_CONCAT_WWI(7264,7232,32, __Vtemp_487, __Vtemp_486, 
                  ((0x1dU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1dU]));
    VL_CONCAT_WWI(7296,7264,32, __Vtemp_488, __Vtemp_487, 
                  ((0x1cU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1cU]));
    VL_CONCAT_WWI(7328,7296,32, __Vtemp_489, __Vtemp_488, 
                  ((0x1bU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1bU]));
    VL_CONCAT_WWI(7360,7328,32, __Vtemp_490, __Vtemp_489, 
                  ((0x1aU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1aU]));
    VL_CONCAT_WWI(7392,7360,32, __Vtemp_491, __Vtemp_490, 
                  ((0x19U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x19U]));
    VL_CONCAT_WWI(7424,7392,32, __Vtemp_492, __Vtemp_491, 
                  ((0x18U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x18U]));
    VL_CONCAT_WWI(7456,7424,32, __Vtemp_493, __Vtemp_492, 
                  ((0x17U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x17U]));
    VL_CONCAT_WWI(7488,7456,32, __Vtemp_494, __Vtemp_493, 
                  ((0x16U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x16U]));
    VL_CONCAT_WWI(7520,7488,32, __Vtemp_495, __Vtemp_494, 
                  ((0x15U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x15U]));
    VL_CONCAT_WWI(7552,7520,32, __Vtemp_496, __Vtemp_495, 
                  ((0x14U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x14U]));
    VL_CONCAT_WWI(7584,7552,32, __Vtemp_497, __Vtemp_496, 
                  ((0x13U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x13U]));
    VL_CONCAT_WWI(7616,7584,32, __Vtemp_498, __Vtemp_497, 
                  ((0x12U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x12U]));
    VL_CONCAT_WWI(7648,7616,32, __Vtemp_499, __Vtemp_498, 
                  ((0x11U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x11U]));
    VL_CONCAT_WWI(7680,7648,32, __Vtemp_500, __Vtemp_499, 
                  ((0x10U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x10U]));
    VL_CONCAT_WWI(7712,7680,32, __Vtemp_501, __Vtemp_500, 
                  ((0xfU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfU]));
    VL_CONCAT_WWI(7744,7712,32, __Vtemp_502, __Vtemp_501, 
                  ((0xeU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeU]));
    VL_CONCAT_WWI(7776,7744,32, __Vtemp_503, __Vtemp_502, 
                  ((0xdU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdU]));
    VL_CONCAT_WWI(7808,7776,32, __Vtemp_504, __Vtemp_503, 
                  ((0xcU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcU]));
    VL_CONCAT_WWI(7840,7808,32, __Vtemp_505, __Vtemp_504, 
                  ((0xbU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbU]));
    VL_CONCAT_WWI(7872,7840,32, __Vtemp_506, __Vtemp_505, 
                  ((0xaU == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaU]));
    VL_CONCAT_WWI(7904,7872,32, __Vtemp_507, __Vtemp_506, 
                  ((9U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[9U]));
    VL_CONCAT_WWI(7936,7904,32, __Vtemp_508, __Vtemp_507, 
                  ((8U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[8U]));
    VL_CONCAT_WWI(7968,7936,32, __Vtemp_509, __Vtemp_508, 
                  ((7U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[7U]));
    VL_CONCAT_WWI(8000,7968,32, __Vtemp_510, __Vtemp_509, 
                  ((6U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[6U]));
    VL_CONCAT_WWI(8032,8000,32, __Vtemp_511, __Vtemp_510, 
                  ((5U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[5U]));
    VL_CONCAT_WWI(8064,8032,32, __Vtemp_512, __Vtemp_511, 
                  ((4U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[4U]));
    VL_CONCAT_WWI(8096,8064,32, __Vtemp_513, __Vtemp_512, 
                  ((3U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[3U]));
    VL_CONCAT_WWI(8128,8096,32, __Vtemp_514, __Vtemp_513, 
                  ((2U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[2U]));
    VL_CONCAT_WWI(8160,8128,32, __Vtemp_515, __Vtemp_514, 
                  ((1U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[1U]));
    VL_CONCAT_WWI(8192,8160,32, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_regs_68_BITS_999_TO_992_877_EQ_255_878_THEN_ETC___05F_d2517, __Vtemp_515, 
                  ((0U == (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))
                    ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0U]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
        = ((0x80U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
            ? ((0x40U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                ? ((0x20U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    ? ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xffU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfeU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfcU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xf0U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xefU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xeeU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xedU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xecU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xebU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xeaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xe0U])))))
                    : ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdeU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xddU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdcU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xd0U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xceU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xccU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xc0U]))))))
                : ((0x20U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    ? ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbeU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbcU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xb0U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xafU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xaeU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xadU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xacU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xabU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xaaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xa0U])))))
                    : ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x9aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x99U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x98U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x97U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x96U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x95U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x94U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x93U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x92U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x91U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x90U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x8aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x89U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x88U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x87U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x86U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x85U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x84U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x83U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x82U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x81U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x80U])))))))
            : ((0x40U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                ? ((0x20U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    ? ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x7aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x79U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x78U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x77U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x76U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x75U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x74U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x73U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x72U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x71U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x70U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x6aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x69U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x68U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x67U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x66U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x65U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x64U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x63U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x62U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x61U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x60U])))))
                    : ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x5aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x59U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x58U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x57U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x56U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x55U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x54U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x53U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x52U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x51U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x50U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x4aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x49U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x48U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x47U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x46U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x45U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x44U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x43U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x42U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x41U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x40U]))))))
                : ((0x20U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                    ? ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x3aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x39U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x38U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x37U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x36U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x35U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x34U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x33U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x32U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x31U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x30U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x2aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x29U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x28U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x27U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x26U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x25U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x24U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x23U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x22U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x21U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x20U])))))
                    : ((0x10U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                        ? ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1eU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1cU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x1aU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x19U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x18U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x17U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x16U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x15U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x14U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x13U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x12U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x11U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0x10U]))))
                        : ((8U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                            ? ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xeU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xcU]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0xaU])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[8U])))
                            : ((4U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                ? ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[6U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[4U]))
                                : ((2U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                    ? ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[2U])
                                    : ((1U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__imem[0U]))))))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__err__024D_IN 
        = ((9U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                   >> 0x18U)) & ((1U < (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 0x10U))) 
                                 | (1U < (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                   >> 8U)))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__halted__024D_IN 
        = ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out) 
           | (0xffU == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                        >> 0x18U)));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__024D_IN 
        = (((~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out)) 
            & ((6U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                       >> 0x18U)) | (0xeU == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x18U))))
            ? (thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd 
               + (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                           >> 8U))) : thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceRd);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__024D_IN 
        = (thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceRd 
           + ((~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out)) 
              & (5U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                        >> 0x18U))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu__024D_IN 
        = ((IData)(vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out)
            ? thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd
            : ((0x10U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                          >> 0x18U)) ? ((IData)(0xf4240U) 
                                        + thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd)
                : (thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceRd 
                   + (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__024D_IN 
        = (thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceRd 
           + ((~ (IData)(vlSelf->thiele_cpu_kami_tb__DOT__bianchi_alarm_out)) 
              & ((0U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                         >> 0x18U)) | ((1U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                               >> 0x18U)) 
                                       | (2U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 0x18U))))));
    thiele_cpu_kami_tb__DOT__dut__DOT__x_89___05Fh66810 
        = ((0x80000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
            ? ((0x40000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xfU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xeU])
                    : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xdU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xcU]))
                : ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xbU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0xaU])
                    : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[9U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[8U])))
            : ((0x40000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[7U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[6U])
                    : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[5U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[4U]))
                : ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[3U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[2U])
                    : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[1U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd[0U]))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq2 
        = ((0x17U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                      >> 0x18U)) ? ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU])
            : ((0x18U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                          >> 0x18U)) ? (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU] 
                                        - (IData)(1U))
                : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0U] 
        = ((0U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[1U] 
        = ((1U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[2U] 
        = ((2U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[3U] 
        = ((3U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[4U] 
        = ((4U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[5U] 
        = ((5U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[6U] 
        = ((6U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[7U] 
        = ((7U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[8U] 
        = ((8U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[9U] 
        = ((9U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? (0xffU & 
                                           (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                            >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0xaU] 
        = ((0xaU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? (0xffU 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0xbU] 
        = ((0xbU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? (0xffU 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0xcU] 
        = ((0xcU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? (0xffU 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0xdU] 
        = ((0xdU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? (0xffU 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0xeU] 
        = ((0xeU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? (0xffU 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0xfU] 
        = ((0xfU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? (0xffU 
                                             & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x10U] 
        = ((0x10U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x11U] 
        = ((0x11U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x12U] 
        = ((0x12U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x13U] 
        = ((0x13U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x14U] 
        = ((0x14U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x15U] 
        = ((0x15U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x16U] 
        = ((0x16U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x17U] 
        = ((0x17U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x18U] 
        = ((0x18U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x19U] 
        = ((0x19U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x1aU] 
        = ((0x1aU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x1bU] 
        = ((0x1bU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x1cU] 
        = ((0x1cU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x1dU] 
        = ((0x1dU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? (0xffU 
                                              & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                 >> 8U))
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x1eU] 
        = (IData)((((QData)((IData)(((0x1fU == (0x1fU 
                                                & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                   >> 0x10U)))
                                      ? (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                  >> 8U))
                                      : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))) 
                    << 0x20U) | (QData)((IData)(((0x1eU 
                                                  == 
                                                  (0x1fU 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                      >> 0x10U)))
                                                  ? 
                                                 (0xffU 
                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                     >> 8U))
                                                  : 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU])))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702[0x1fU] 
        = (IData)(((((QData)((IData)(((0x1fU == (0x1fU 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                    >> 0x10U)))
                                       ? (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                   >> 8U))
                                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))) 
                     << 0x20U) | (QData)((IData)(((0x1eU 
                                                   == 
                                                   (0x1fU 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                       >> 0x10U)))
                                                   ? 
                                                  (0xffU 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                      >> 8U))
                                                   : 
                                                  vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU])))) 
                   >> 0x20U));
    thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781 
        = ((0x8000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
            ? ((0x4000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xffU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfeU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfcU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf0U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xefU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeeU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xedU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xecU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xebU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe0U])))))
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdeU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xddU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdcU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd0U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xceU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xccU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc0U]))))))
                : ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbeU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbcU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb0U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xafU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaeU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xadU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xacU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xabU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa0U])))))
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x99U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x98U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x97U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x96U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x95U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x94U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x93U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x92U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x91U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x90U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x89U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x88U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x87U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x86U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x85U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x84U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x83U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x82U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x81U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x80U])))))))
            : ((0x4000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x79U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x78U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x77U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x76U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x75U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x74U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x73U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x72U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x71U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x70U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x69U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x68U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x67U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x66U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x65U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x64U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x63U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x62U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x61U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x60U])))))
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x59U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x58U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x57U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x56U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x55U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x54U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x53U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x52U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x51U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x50U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x49U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x48U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x47U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x46U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x45U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x44U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x43U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x42U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x41U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x40U]))))))
                : ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x39U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x38U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x37U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x36U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x35U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x34U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x33U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x32U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x31U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x30U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x29U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x28U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x27U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x26U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x25U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x24U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x23U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x22U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x21U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x20U])))))
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1fU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1eU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1dU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1cU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1bU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1aU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x19U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x18U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x17U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x16U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x15U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x14U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x13U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x12U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x11U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x10U]))))
                        : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcU]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbU]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaU])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[9U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[8U])))
                            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[7U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[6U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[5U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[4U]))
                                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[3U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[2U])
                                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[1U]
                                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0U]))))))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0U] 
        = ((0U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[1U] 
        = ((1U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[2U] 
        = ((2U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[3U] 
        = ((3U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[4U] 
        = ((4U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[5U] 
        = ((5U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[6U] 
        = ((6U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[7U] 
        = ((7U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[8U] 
        = ((8U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[9U] 
        = ((9U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                            >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0xaU] 
        = ((0xaU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0xbU] 
        = ((0xbU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0xcU] 
        = ((0xcU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0xdU] 
        = ((0xdU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0xeU] 
        = ((0xeU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0xfU] 
        = ((0xfU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                              >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x10U] 
        = ((0x10U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x11U] 
        = ((0x11U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x12U] 
        = ((0x12U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x13U] 
        = ((0x13U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x14U] 
        = ((0x14U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x15U] 
        = ((0x15U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x16U] 
        = ((0x16U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x17U] 
        = ((0x17U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x18U] 
        = ((0x18U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x19U] 
        = ((0x19U == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x1aU] 
        = ((0x1aU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x1bU] 
        = ((0x1bU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x1cU] 
        = ((0x1cU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU]);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x1dU] 
        = ((0x1dU == (0x1fU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                               >> 0x10U))) ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU]);
    thiele_cpu_kami_tb__DOT__dut__DOT__x_45___05Fh66774 
        = ((0x8000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
            ? ((0x4000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU])
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]))
                : ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU])
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U])))
            : ((0x4000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U])
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]))
                : ((0x2000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U])
                    : ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U]))));
    thiele_cpu_kami_tb__DOT__dut__DOT__x_46___05Fh66775 
        = ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
            ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU])
                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]))
                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU])
                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U])))
            : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U])
                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]))
                : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U])
                    : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U]))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_47___05Fh66776 
        = ((0x100000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
            ? ((0x80000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x40000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU]))
                    : ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U])))
                : ((0x40000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U]))
                    : ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U]))))
            : ((0x80000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x40000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]))
                    : ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U])))
                : ((0x40000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]))
                    : ((0x20000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U])
                        : ((0x10000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U])))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777 
        = ((0x1000U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
            ? ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1dU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1cU]))
                    : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1bU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1aU])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x19U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x18U])))
                : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x17U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x16U])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x15U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x14U]))
                    : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x13U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x12U])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x11U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x10U]))))
            : ((0x800U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                ? ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xfU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xeU])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xdU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xcU]))
                    : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xbU]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0xaU])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[9U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[8U])))
                : ((0x400U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                    ? ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[7U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[6U])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[5U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[4U]))
                    : ((0x200U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                        ? ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[3U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[2U])
                        : ((0x100U & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300)
                            ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[1U]
                            : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0U])))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_90___05Fh66811 
        = (thiele_cpu_kami_tb__DOT__dut__DOT__x_89___05Fh66810 
           + (0xffU & vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x1eU] 
        = (IData)((((QData)((IData)(((0x1fU == (0x1fU 
                                                & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                   >> 0x10U)))
                                      ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
                                      : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))) 
                    << 0x20U) | (QData)((IData)(((0x1eU 
                                                  == 
                                                  (0x1fU 
                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                      >> 0x10U)))
                                                  ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
                                                  : 
                                                 vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU])))));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911[0x1fU] 
        = (IData)(((((QData)((IData)(((0x1fU == (0x1fU 
                                                 & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                    >> 0x10U)))
                                       ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
                                       : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1fU]))) 
                     << 0x20U) | (QData)((IData)(((0x1eU 
                                                   == 
                                                   (0x1fU 
                                                    & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                       >> 0x10U)))
                                                   ? thiele_cpu_kami_tb__DOT__dut__DOT__x_52___05Fh66781
                                                   : 
                                                  vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd[0x1eU])))) 
                   >> 0x20U));
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_62___05Fh66791 
        = (thiele_cpu_kami_tb__DOT__dut__DOT__x_45___05Fh66774 
           + thiele_cpu_kami_tb__DOT__dut__DOT__x_46___05Fh66775);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_63___05Fh66792 
        = (thiele_cpu_kami_tb__DOT__dut__DOT__x_45___05Fh66774 
           - thiele_cpu_kami_tb__DOT__dut__DOT__x_46___05Fh66775);
    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d614 
        = (((0x16U == (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                       >> 0x18U)) & (0U != vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_47___05Fh66776))
            ? (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                        >> 8U)) : ((IData)(1U) + vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd));
    __Vtemp_635[0U] = ((0xc0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc0U]);
    __Vtemp_635[1U] = ((0xc1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc1U]);
    __Vtemp_635[2U] = ((0xc2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc2U]);
    __Vtemp_635[3U] = ((0xc3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc3U]);
    __Vtemp_635[4U] = ((0xc4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc4U]);
    __Vtemp_635[5U] = ((0xc5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc5U]);
    __Vtemp_635[6U] = ((0xc6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc6U]);
    __Vtemp_635[7U] = ((0xc7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc7U]);
    __Vtemp_635[8U] = ((0xc8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc8U]);
    __Vtemp_635[9U] = ((0xc9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                           >> 0x10U)))
                        ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                        : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xc9U]);
    __Vtemp_635[0xaU] = ((0xcaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                             >> 0x10U)))
                          ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcaU]);
    __Vtemp_635[0xbU] = ((0xcbU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                             >> 0x10U)))
                          ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcbU]);
    __Vtemp_635[0xcU] = ((0xccU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                             >> 0x10U)))
                          ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xccU]);
    __Vtemp_635[0xdU] = ((0xcdU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                             >> 0x10U)))
                          ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcdU]);
    __Vtemp_635[0xeU] = ((0xceU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                             >> 0x10U)))
                          ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xceU]);
    __Vtemp_635[0xfU] = ((0xcfU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                             >> 0x10U)))
                          ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                          : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcfU]);
    __Vtemp_635[0x10U] = ((0xd0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd0U]);
    __Vtemp_635[0x11U] = ((0xd1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd1U]);
    __Vtemp_635[0x12U] = ((0xd2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd2U]);
    __Vtemp_635[0x13U] = ((0xd3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd3U]);
    __Vtemp_635[0x14U] = ((0xd4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd4U]);
    __Vtemp_635[0x15U] = ((0xd5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd5U]);
    __Vtemp_635[0x16U] = ((0xd6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd6U]);
    __Vtemp_635[0x17U] = ((0xd7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd7U]);
    __Vtemp_635[0x18U] = ((0xd8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd8U]);
    __Vtemp_635[0x19U] = ((0xd9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xd9U]);
    __Vtemp_635[0x1aU] = ((0xdaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdaU]);
    __Vtemp_635[0x1bU] = ((0xdbU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdbU]);
    __Vtemp_635[0x1cU] = ((0xdcU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdcU]);
    __Vtemp_635[0x1dU] = ((0xddU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xddU]);
    __Vtemp_635[0x1eU] = ((0xdeU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdeU]);
    __Vtemp_635[0x1fU] = ((0xdfU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdfU]);
    __Vtemp_635[0x20U] = ((0xe0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe0U]);
    __Vtemp_635[0x21U] = ((0xe1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe1U]);
    __Vtemp_635[0x22U] = ((0xe2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe2U]);
    __Vtemp_635[0x23U] = ((0xe3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe3U]);
    __Vtemp_635[0x24U] = ((0xe4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe4U]);
    __Vtemp_635[0x25U] = ((0xe5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe5U]);
    __Vtemp_635[0x26U] = ((0xe6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe6U]);
    __Vtemp_635[0x27U] = ((0xe7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe7U]);
    __Vtemp_635[0x28U] = ((0xe8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe8U]);
    __Vtemp_635[0x29U] = ((0xe9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xe9U]);
    __Vtemp_635[0x2aU] = ((0xeaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeaU]);
    __Vtemp_635[0x2bU] = ((0xebU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xebU]);
    __Vtemp_635[0x2cU] = ((0xecU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xecU]);
    __Vtemp_635[0x2dU] = ((0xedU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xedU]);
    __Vtemp_635[0x2eU] = ((0xeeU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeeU]);
    __Vtemp_635[0x2fU] = ((0xefU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xefU]);
    __Vtemp_635[0x30U] = ((0xf0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf0U]);
    __Vtemp_635[0x31U] = ((0xf1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf1U]);
    __Vtemp_635[0x32U] = ((0xf2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf2U]);
    __Vtemp_635[0x33U] = ((0xf3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf3U]);
    __Vtemp_635[0x34U] = ((0xf4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf4U]);
    __Vtemp_635[0x35U] = ((0xf5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf5U]);
    __Vtemp_635[0x36U] = ((0xf6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf6U]);
    __Vtemp_635[0x37U] = ((0xf7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf7U]);
    __Vtemp_635[0x38U] = ((0xf8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf8U]);
    __Vtemp_635[0x39U] = ((0xf9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xf9U]);
    __Vtemp_635[0x3aU] = ((0xfaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfaU]);
    __Vtemp_635[0x3bU] = ((0xfbU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfbU]);
    __Vtemp_635[0x3cU] = ((0xfcU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfcU]);
    __Vtemp_635[0x3dU] = ((0xfdU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                              >> 0x10U)))
                           ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                           : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfdU]);
    __Vtemp_635[0x3eU] = (IData)((((QData)((IData)(
                                                   ((0xffU 
                                                     == 
                                                     (0xffU 
                                                      & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                         >> 0x10U)))
                                                     ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                                                     : 
                                                    vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xffU]))) 
                                   << 0x20U) | (QData)((IData)(
                                                               ((0xfeU 
                                                                 == 
                                                                 (0xffU 
                                                                  & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                                     >> 0x10U)))
                                                                 ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                                                                 : 
                                                                vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfeU])))));
    __Vtemp_635[0x3fU] = (IData)(((((QData)((IData)(
                                                    ((0xffU 
                                                      == 
                                                      (0xffU 
                                                       & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                          >> 0x10U)))
                                                      ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                                                      : 
                                                     vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xffU]))) 
                                    << 0x20U) | (QData)((IData)(
                                                                ((0xfeU 
                                                                  == 
                                                                  (0xffU 
                                                                   & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                                                      >> 0x10U)))
                                                                  ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                                                                  : 
                                                                 vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfeU])))) 
                                  >> 0x20U));
    VL_CONCAT_WWI(2080,2048,32, __Vtemp_636, __Vtemp_635, 
                  ((0xbfU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbfU]));
    VL_CONCAT_WWI(2112,2080,32, __Vtemp_637, __Vtemp_636, 
                  ((0xbeU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbeU]));
    VL_CONCAT_WWI(2144,2112,32, __Vtemp_638, __Vtemp_637, 
                  ((0xbdU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbdU]));
    VL_CONCAT_WWI(2176,2144,32, __Vtemp_639, __Vtemp_638, 
                  ((0xbcU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbcU]));
    VL_CONCAT_WWI(2208,2176,32, __Vtemp_640, __Vtemp_639, 
                  ((0xbbU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbbU]));
    VL_CONCAT_WWI(2240,2208,32, __Vtemp_641, __Vtemp_640, 
                  ((0xbaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbaU]));
    VL_CONCAT_WWI(2272,2240,32, __Vtemp_642, __Vtemp_641, 
                  ((0xb9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb9U]));
    VL_CONCAT_WWI(2304,2272,32, __Vtemp_643, __Vtemp_642, 
                  ((0xb8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb8U]));
    VL_CONCAT_WWI(2336,2304,32, __Vtemp_644, __Vtemp_643, 
                  ((0xb7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb7U]));
    VL_CONCAT_WWI(2368,2336,32, __Vtemp_645, __Vtemp_644, 
                  ((0xb6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb6U]));
    VL_CONCAT_WWI(2400,2368,32, __Vtemp_646, __Vtemp_645, 
                  ((0xb5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb5U]));
    VL_CONCAT_WWI(2432,2400,32, __Vtemp_647, __Vtemp_646, 
                  ((0xb4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb4U]));
    VL_CONCAT_WWI(2464,2432,32, __Vtemp_648, __Vtemp_647, 
                  ((0xb3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb3U]));
    VL_CONCAT_WWI(2496,2464,32, __Vtemp_649, __Vtemp_648, 
                  ((0xb2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb2U]));
    VL_CONCAT_WWI(2528,2496,32, __Vtemp_650, __Vtemp_649, 
                  ((0xb1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb1U]));
    VL_CONCAT_WWI(2560,2528,32, __Vtemp_651, __Vtemp_650, 
                  ((0xb0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xb0U]));
    VL_CONCAT_WWI(2592,2560,32, __Vtemp_652, __Vtemp_651, 
                  ((0xafU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xafU]));
    VL_CONCAT_WWI(2624,2592,32, __Vtemp_653, __Vtemp_652, 
                  ((0xaeU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaeU]));
    VL_CONCAT_WWI(2656,2624,32, __Vtemp_654, __Vtemp_653, 
                  ((0xadU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xadU]));
    VL_CONCAT_WWI(2688,2656,32, __Vtemp_655, __Vtemp_654, 
                  ((0xacU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xacU]));
    VL_CONCAT_WWI(2720,2688,32, __Vtemp_656, __Vtemp_655, 
                  ((0xabU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xabU]));
    VL_CONCAT_WWI(2752,2720,32, __Vtemp_657, __Vtemp_656, 
                  ((0xaaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaaU]));
    VL_CONCAT_WWI(2784,2752,32, __Vtemp_658, __Vtemp_657, 
                  ((0xa9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa9U]));
    VL_CONCAT_WWI(2816,2784,32, __Vtemp_659, __Vtemp_658, 
                  ((0xa8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa8U]));
    VL_CONCAT_WWI(2848,2816,32, __Vtemp_660, __Vtemp_659, 
                  ((0xa7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa7U]));
    VL_CONCAT_WWI(2880,2848,32, __Vtemp_661, __Vtemp_660, 
                  ((0xa6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa6U]));
    VL_CONCAT_WWI(2912,2880,32, __Vtemp_662, __Vtemp_661, 
                  ((0xa5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa5U]));
    VL_CONCAT_WWI(2944,2912,32, __Vtemp_663, __Vtemp_662, 
                  ((0xa4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa4U]));
    VL_CONCAT_WWI(2976,2944,32, __Vtemp_664, __Vtemp_663, 
                  ((0xa3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa3U]));
    VL_CONCAT_WWI(3008,2976,32, __Vtemp_665, __Vtemp_664, 
                  ((0xa2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa2U]));
    VL_CONCAT_WWI(3040,3008,32, __Vtemp_666, __Vtemp_665, 
                  ((0xa1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa1U]));
    VL_CONCAT_WWI(3072,3040,32, __Vtemp_667, __Vtemp_666, 
                  ((0xa0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xa0U]));
    VL_CONCAT_WWI(3104,3072,32, __Vtemp_668, __Vtemp_667, 
                  ((0x9fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9fU]));
    VL_CONCAT_WWI(3136,3104,32, __Vtemp_669, __Vtemp_668, 
                  ((0x9eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9eU]));
    VL_CONCAT_WWI(3168,3136,32, __Vtemp_670, __Vtemp_669, 
                  ((0x9dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9dU]));
    VL_CONCAT_WWI(3200,3168,32, __Vtemp_671, __Vtemp_670, 
                  ((0x9cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9cU]));
    VL_CONCAT_WWI(3232,3200,32, __Vtemp_672, __Vtemp_671, 
                  ((0x9bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9bU]));
    VL_CONCAT_WWI(3264,3232,32, __Vtemp_673, __Vtemp_672, 
                  ((0x9aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x9aU]));
    VL_CONCAT_WWI(3296,3264,32, __Vtemp_674, __Vtemp_673, 
                  ((0x99U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x99U]));
    VL_CONCAT_WWI(3328,3296,32, __Vtemp_675, __Vtemp_674, 
                  ((0x98U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x98U]));
    VL_CONCAT_WWI(3360,3328,32, __Vtemp_676, __Vtemp_675, 
                  ((0x97U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x97U]));
    VL_CONCAT_WWI(3392,3360,32, __Vtemp_677, __Vtemp_676, 
                  ((0x96U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x96U]));
    VL_CONCAT_WWI(3424,3392,32, __Vtemp_678, __Vtemp_677, 
                  ((0x95U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x95U]));
    VL_CONCAT_WWI(3456,3424,32, __Vtemp_679, __Vtemp_678, 
                  ((0x94U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x94U]));
    VL_CONCAT_WWI(3488,3456,32, __Vtemp_680, __Vtemp_679, 
                  ((0x93U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x93U]));
    VL_CONCAT_WWI(3520,3488,32, __Vtemp_681, __Vtemp_680, 
                  ((0x92U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x92U]));
    VL_CONCAT_WWI(3552,3520,32, __Vtemp_682, __Vtemp_681, 
                  ((0x91U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x91U]));
    VL_CONCAT_WWI(3584,3552,32, __Vtemp_683, __Vtemp_682, 
                  ((0x90U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x90U]));
    VL_CONCAT_WWI(3616,3584,32, __Vtemp_684, __Vtemp_683, 
                  ((0x8fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8fU]));
    VL_CONCAT_WWI(3648,3616,32, __Vtemp_685, __Vtemp_684, 
                  ((0x8eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8eU]));
    VL_CONCAT_WWI(3680,3648,32, __Vtemp_686, __Vtemp_685, 
                  ((0x8dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8dU]));
    VL_CONCAT_WWI(3712,3680,32, __Vtemp_687, __Vtemp_686, 
                  ((0x8cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8cU]));
    VL_CONCAT_WWI(3744,3712,32, __Vtemp_688, __Vtemp_687, 
                  ((0x8bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8bU]));
    VL_CONCAT_WWI(3776,3744,32, __Vtemp_689, __Vtemp_688, 
                  ((0x8aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x8aU]));
    VL_CONCAT_WWI(3808,3776,32, __Vtemp_690, __Vtemp_689, 
                  ((0x89U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x89U]));
    VL_CONCAT_WWI(3840,3808,32, __Vtemp_691, __Vtemp_690, 
                  ((0x88U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x88U]));
    VL_CONCAT_WWI(3872,3840,32, __Vtemp_692, __Vtemp_691, 
                  ((0x87U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x87U]));
    VL_CONCAT_WWI(3904,3872,32, __Vtemp_693, __Vtemp_692, 
                  ((0x86U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x86U]));
    VL_CONCAT_WWI(3936,3904,32, __Vtemp_694, __Vtemp_693, 
                  ((0x85U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x85U]));
    VL_CONCAT_WWI(3968,3936,32, __Vtemp_695, __Vtemp_694, 
                  ((0x84U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x84U]));
    VL_CONCAT_WWI(4000,3968,32, __Vtemp_696, __Vtemp_695, 
                  ((0x83U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x83U]));
    VL_CONCAT_WWI(4032,4000,32, __Vtemp_697, __Vtemp_696, 
                  ((0x82U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x82U]));
    VL_CONCAT_WWI(4064,4032,32, __Vtemp_698, __Vtemp_697, 
                  ((0x81U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x81U]));
    VL_CONCAT_WWI(4096,4064,32, __Vtemp_699, __Vtemp_698, 
                  ((0x80U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x80U]));
    VL_CONCAT_WWI(4128,4096,32, __Vtemp_700, __Vtemp_699, 
                  ((0x7fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7fU]));
    VL_CONCAT_WWI(4160,4128,32, __Vtemp_701, __Vtemp_700, 
                  ((0x7eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7eU]));
    VL_CONCAT_WWI(4192,4160,32, __Vtemp_702, __Vtemp_701, 
                  ((0x7dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7dU]));
    VL_CONCAT_WWI(4224,4192,32, __Vtemp_703, __Vtemp_702, 
                  ((0x7cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7cU]));
    VL_CONCAT_WWI(4256,4224,32, __Vtemp_704, __Vtemp_703, 
                  ((0x7bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7bU]));
    VL_CONCAT_WWI(4288,4256,32, __Vtemp_705, __Vtemp_704, 
                  ((0x7aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x7aU]));
    VL_CONCAT_WWI(4320,4288,32, __Vtemp_706, __Vtemp_705, 
                  ((0x79U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x79U]));
    VL_CONCAT_WWI(4352,4320,32, __Vtemp_707, __Vtemp_706, 
                  ((0x78U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x78U]));
    VL_CONCAT_WWI(4384,4352,32, __Vtemp_708, __Vtemp_707, 
                  ((0x77U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x77U]));
    VL_CONCAT_WWI(4416,4384,32, __Vtemp_709, __Vtemp_708, 
                  ((0x76U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x76U]));
    VL_CONCAT_WWI(4448,4416,32, __Vtemp_710, __Vtemp_709, 
                  ((0x75U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x75U]));
    VL_CONCAT_WWI(4480,4448,32, __Vtemp_711, __Vtemp_710, 
                  ((0x74U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x74U]));
    VL_CONCAT_WWI(4512,4480,32, __Vtemp_712, __Vtemp_711, 
                  ((0x73U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x73U]));
    VL_CONCAT_WWI(4544,4512,32, __Vtemp_713, __Vtemp_712, 
                  ((0x72U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x72U]));
    VL_CONCAT_WWI(4576,4544,32, __Vtemp_714, __Vtemp_713, 
                  ((0x71U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x71U]));
    VL_CONCAT_WWI(4608,4576,32, __Vtemp_715, __Vtemp_714, 
                  ((0x70U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x70U]));
    VL_CONCAT_WWI(4640,4608,32, __Vtemp_716, __Vtemp_715, 
                  ((0x6fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6fU]));
    VL_CONCAT_WWI(4672,4640,32, __Vtemp_717, __Vtemp_716, 
                  ((0x6eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6eU]));
    VL_CONCAT_WWI(4704,4672,32, __Vtemp_718, __Vtemp_717, 
                  ((0x6dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6dU]));
    VL_CONCAT_WWI(4736,4704,32, __Vtemp_719, __Vtemp_718, 
                  ((0x6cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6cU]));
    VL_CONCAT_WWI(4768,4736,32, __Vtemp_720, __Vtemp_719, 
                  ((0x6bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6bU]));
    VL_CONCAT_WWI(4800,4768,32, __Vtemp_721, __Vtemp_720, 
                  ((0x6aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x6aU]));
    VL_CONCAT_WWI(4832,4800,32, __Vtemp_722, __Vtemp_721, 
                  ((0x69U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x69U]));
    VL_CONCAT_WWI(4864,4832,32, __Vtemp_723, __Vtemp_722, 
                  ((0x68U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x68U]));
    VL_CONCAT_WWI(4896,4864,32, __Vtemp_724, __Vtemp_723, 
                  ((0x67U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x67U]));
    VL_CONCAT_WWI(4928,4896,32, __Vtemp_725, __Vtemp_724, 
                  ((0x66U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x66U]));
    VL_CONCAT_WWI(4960,4928,32, __Vtemp_726, __Vtemp_725, 
                  ((0x65U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x65U]));
    VL_CONCAT_WWI(4992,4960,32, __Vtemp_727, __Vtemp_726, 
                  ((0x64U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x64U]));
    VL_CONCAT_WWI(5024,4992,32, __Vtemp_728, __Vtemp_727, 
                  ((0x63U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x63U]));
    VL_CONCAT_WWI(5056,5024,32, __Vtemp_729, __Vtemp_728, 
                  ((0x62U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x62U]));
    VL_CONCAT_WWI(5088,5056,32, __Vtemp_730, __Vtemp_729, 
                  ((0x61U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x61U]));
    VL_CONCAT_WWI(5120,5088,32, __Vtemp_731, __Vtemp_730, 
                  ((0x60U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x60U]));
    VL_CONCAT_WWI(5152,5120,32, __Vtemp_732, __Vtemp_731, 
                  ((0x5fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5fU]));
    VL_CONCAT_WWI(5184,5152,32, __Vtemp_733, __Vtemp_732, 
                  ((0x5eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5eU]));
    VL_CONCAT_WWI(5216,5184,32, __Vtemp_734, __Vtemp_733, 
                  ((0x5dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5dU]));
    VL_CONCAT_WWI(5248,5216,32, __Vtemp_735, __Vtemp_734, 
                  ((0x5cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5cU]));
    VL_CONCAT_WWI(5280,5248,32, __Vtemp_736, __Vtemp_735, 
                  ((0x5bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5bU]));
    VL_CONCAT_WWI(5312,5280,32, __Vtemp_737, __Vtemp_736, 
                  ((0x5aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x5aU]));
    VL_CONCAT_WWI(5344,5312,32, __Vtemp_738, __Vtemp_737, 
                  ((0x59U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x59U]));
    VL_CONCAT_WWI(5376,5344,32, __Vtemp_739, __Vtemp_738, 
                  ((0x58U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x58U]));
    VL_CONCAT_WWI(5408,5376,32, __Vtemp_740, __Vtemp_739, 
                  ((0x57U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x57U]));
    VL_CONCAT_WWI(5440,5408,32, __Vtemp_741, __Vtemp_740, 
                  ((0x56U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x56U]));
    VL_CONCAT_WWI(5472,5440,32, __Vtemp_742, __Vtemp_741, 
                  ((0x55U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x55U]));
    VL_CONCAT_WWI(5504,5472,32, __Vtemp_743, __Vtemp_742, 
                  ((0x54U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x54U]));
    VL_CONCAT_WWI(5536,5504,32, __Vtemp_744, __Vtemp_743, 
                  ((0x53U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x53U]));
    VL_CONCAT_WWI(5568,5536,32, __Vtemp_745, __Vtemp_744, 
                  ((0x52U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x52U]));
    VL_CONCAT_WWI(5600,5568,32, __Vtemp_746, __Vtemp_745, 
                  ((0x51U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x51U]));
    VL_CONCAT_WWI(5632,5600,32, __Vtemp_747, __Vtemp_746, 
                  ((0x50U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x50U]));
    VL_CONCAT_WWI(5664,5632,32, __Vtemp_748, __Vtemp_747, 
                  ((0x4fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4fU]));
    VL_CONCAT_WWI(5696,5664,32, __Vtemp_749, __Vtemp_748, 
                  ((0x4eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4eU]));
    VL_CONCAT_WWI(5728,5696,32, __Vtemp_750, __Vtemp_749, 
                  ((0x4dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4dU]));
    VL_CONCAT_WWI(5760,5728,32, __Vtemp_751, __Vtemp_750, 
                  ((0x4cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4cU]));
    VL_CONCAT_WWI(5792,5760,32, __Vtemp_752, __Vtemp_751, 
                  ((0x4bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4bU]));
    VL_CONCAT_WWI(5824,5792,32, __Vtemp_753, __Vtemp_752, 
                  ((0x4aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x4aU]));
    VL_CONCAT_WWI(5856,5824,32, __Vtemp_754, __Vtemp_753, 
                  ((0x49U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x49U]));
    VL_CONCAT_WWI(5888,5856,32, __Vtemp_755, __Vtemp_754, 
                  ((0x48U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x48U]));
    VL_CONCAT_WWI(5920,5888,32, __Vtemp_756, __Vtemp_755, 
                  ((0x47U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x47U]));
    VL_CONCAT_WWI(5952,5920,32, __Vtemp_757, __Vtemp_756, 
                  ((0x46U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x46U]));
    VL_CONCAT_WWI(5984,5952,32, __Vtemp_758, __Vtemp_757, 
                  ((0x45U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x45U]));
    VL_CONCAT_WWI(6016,5984,32, __Vtemp_759, __Vtemp_758, 
                  ((0x44U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x44U]));
    VL_CONCAT_WWI(6048,6016,32, __Vtemp_760, __Vtemp_759, 
                  ((0x43U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x43U]));
    VL_CONCAT_WWI(6080,6048,32, __Vtemp_761, __Vtemp_760, 
                  ((0x42U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x42U]));
    VL_CONCAT_WWI(6112,6080,32, __Vtemp_762, __Vtemp_761, 
                  ((0x41U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x41U]));
    VL_CONCAT_WWI(6144,6112,32, __Vtemp_763, __Vtemp_762, 
                  ((0x40U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x40U]));
    VL_CONCAT_WWI(6176,6144,32, __Vtemp_764, __Vtemp_763, 
                  ((0x3fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3fU]));
    VL_CONCAT_WWI(6208,6176,32, __Vtemp_765, __Vtemp_764, 
                  ((0x3eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3eU]));
    VL_CONCAT_WWI(6240,6208,32, __Vtemp_766, __Vtemp_765, 
                  ((0x3dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3dU]));
    VL_CONCAT_WWI(6272,6240,32, __Vtemp_767, __Vtemp_766, 
                  ((0x3cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3cU]));
    VL_CONCAT_WWI(6304,6272,32, __Vtemp_768, __Vtemp_767, 
                  ((0x3bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3bU]));
    VL_CONCAT_WWI(6336,6304,32, __Vtemp_769, __Vtemp_768, 
                  ((0x3aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x3aU]));
    VL_CONCAT_WWI(6368,6336,32, __Vtemp_770, __Vtemp_769, 
                  ((0x39U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x39U]));
    VL_CONCAT_WWI(6400,6368,32, __Vtemp_771, __Vtemp_770, 
                  ((0x38U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x38U]));
    VL_CONCAT_WWI(6432,6400,32, __Vtemp_772, __Vtemp_771, 
                  ((0x37U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x37U]));
    VL_CONCAT_WWI(6464,6432,32, __Vtemp_773, __Vtemp_772, 
                  ((0x36U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x36U]));
    VL_CONCAT_WWI(6496,6464,32, __Vtemp_774, __Vtemp_773, 
                  ((0x35U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x35U]));
    VL_CONCAT_WWI(6528,6496,32, __Vtemp_775, __Vtemp_774, 
                  ((0x34U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x34U]));
    VL_CONCAT_WWI(6560,6528,32, __Vtemp_776, __Vtemp_775, 
                  ((0x33U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x33U]));
    VL_CONCAT_WWI(6592,6560,32, __Vtemp_777, __Vtemp_776, 
                  ((0x32U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x32U]));
    VL_CONCAT_WWI(6624,6592,32, __Vtemp_778, __Vtemp_777, 
                  ((0x31U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x31U]));
    VL_CONCAT_WWI(6656,6624,32, __Vtemp_779, __Vtemp_778, 
                  ((0x30U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x30U]));
    VL_CONCAT_WWI(6688,6656,32, __Vtemp_780, __Vtemp_779, 
                  ((0x2fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2fU]));
    VL_CONCAT_WWI(6720,6688,32, __Vtemp_781, __Vtemp_780, 
                  ((0x2eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2eU]));
    VL_CONCAT_WWI(6752,6720,32, __Vtemp_782, __Vtemp_781, 
                  ((0x2dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2dU]));
    VL_CONCAT_WWI(6784,6752,32, __Vtemp_783, __Vtemp_782, 
                  ((0x2cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2cU]));
    VL_CONCAT_WWI(6816,6784,32, __Vtemp_784, __Vtemp_783, 
                  ((0x2bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2bU]));
    VL_CONCAT_WWI(6848,6816,32, __Vtemp_785, __Vtemp_784, 
                  ((0x2aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x2aU]));
    VL_CONCAT_WWI(6880,6848,32, __Vtemp_786, __Vtemp_785, 
                  ((0x29U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x29U]));
    VL_CONCAT_WWI(6912,6880,32, __Vtemp_787, __Vtemp_786, 
                  ((0x28U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x28U]));
    VL_CONCAT_WWI(6944,6912,32, __Vtemp_788, __Vtemp_787, 
                  ((0x27U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x27U]));
    VL_CONCAT_WWI(6976,6944,32, __Vtemp_789, __Vtemp_788, 
                  ((0x26U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x26U]));
    VL_CONCAT_WWI(7008,6976,32, __Vtemp_790, __Vtemp_789, 
                  ((0x25U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x25U]));
    VL_CONCAT_WWI(7040,7008,32, __Vtemp_791, __Vtemp_790, 
                  ((0x24U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x24U]));
    VL_CONCAT_WWI(7072,7040,32, __Vtemp_792, __Vtemp_791, 
                  ((0x23U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x23U]));
    VL_CONCAT_WWI(7104,7072,32, __Vtemp_793, __Vtemp_792, 
                  ((0x22U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x22U]));
    VL_CONCAT_WWI(7136,7104,32, __Vtemp_794, __Vtemp_793, 
                  ((0x21U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x21U]));
    VL_CONCAT_WWI(7168,7136,32, __Vtemp_795, __Vtemp_794, 
                  ((0x20U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x20U]));
    VL_CONCAT_WWI(7200,7168,32, __Vtemp_796, __Vtemp_795, 
                  ((0x1fU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1fU]));
    VL_CONCAT_WWI(7232,7200,32, __Vtemp_797, __Vtemp_796, 
                  ((0x1eU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1eU]));
    VL_CONCAT_WWI(7264,7232,32, __Vtemp_798, __Vtemp_797, 
                  ((0x1dU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1dU]));
    VL_CONCAT_WWI(7296,7264,32, __Vtemp_799, __Vtemp_798, 
                  ((0x1cU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1cU]));
    VL_CONCAT_WWI(7328,7296,32, __Vtemp_800, __Vtemp_799, 
                  ((0x1bU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1bU]));
    VL_CONCAT_WWI(7360,7328,32, __Vtemp_801, __Vtemp_800, 
                  ((0x1aU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x1aU]));
    VL_CONCAT_WWI(7392,7360,32, __Vtemp_802, __Vtemp_801, 
                  ((0x19U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x19U]));
    VL_CONCAT_WWI(7424,7392,32, __Vtemp_803, __Vtemp_802, 
                  ((0x18U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x18U]));
    VL_CONCAT_WWI(7456,7424,32, __Vtemp_804, __Vtemp_803, 
                  ((0x17U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x17U]));
    VL_CONCAT_WWI(7488,7456,32, __Vtemp_805, __Vtemp_804, 
                  ((0x16U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x16U]));
    VL_CONCAT_WWI(7520,7488,32, __Vtemp_806, __Vtemp_805, 
                  ((0x15U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x15U]));
    VL_CONCAT_WWI(7552,7520,32, __Vtemp_807, __Vtemp_806, 
                  ((0x14U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x14U]));
    VL_CONCAT_WWI(7584,7552,32, __Vtemp_808, __Vtemp_807, 
                  ((0x13U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x13U]));
    VL_CONCAT_WWI(7616,7584,32, __Vtemp_809, __Vtemp_808, 
                  ((0x12U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x12U]));
    VL_CONCAT_WWI(7648,7616,32, __Vtemp_810, __Vtemp_809, 
                  ((0x11U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x11U]));
    VL_CONCAT_WWI(7680,7648,32, __Vtemp_811, __Vtemp_810, 
                  ((0x10U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                       >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0x10U]));
    VL_CONCAT_WWI(7712,7680,32, __Vtemp_812, __Vtemp_811, 
                  ((0xfU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                      >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xfU]));
    VL_CONCAT_WWI(7744,7712,32, __Vtemp_813, __Vtemp_812, 
                  ((0xeU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                      >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xeU]));
    VL_CONCAT_WWI(7776,7744,32, __Vtemp_814, __Vtemp_813, 
                  ((0xdU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                      >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xdU]));
    VL_CONCAT_WWI(7808,7776,32, __Vtemp_815, __Vtemp_814, 
                  ((0xcU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                      >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xcU]));
    VL_CONCAT_WWI(7840,7808,32, __Vtemp_816, __Vtemp_815, 
                  ((0xbU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                      >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xbU]));
    VL_CONCAT_WWI(7872,7840,32, __Vtemp_817, __Vtemp_816, 
                  ((0xaU == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                      >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0xaU]));
    VL_CONCAT_WWI(7904,7872,32, __Vtemp_818, __Vtemp_817, 
                  ((9U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[9U]));
    VL_CONCAT_WWI(7936,7904,32, __Vtemp_819, __Vtemp_818, 
                  ((8U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[8U]));
    VL_CONCAT_WWI(7968,7936,32, __Vtemp_820, __Vtemp_819, 
                  ((7U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[7U]));
    VL_CONCAT_WWI(8000,7968,32, __Vtemp_821, __Vtemp_820, 
                  ((6U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[6U]));
    VL_CONCAT_WWI(8032,8000,32, __Vtemp_822, __Vtemp_821, 
                  ((5U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[5U]));
    VL_CONCAT_WWI(8064,8032,32, __Vtemp_823, __Vtemp_822, 
                  ((4U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[4U]));
    VL_CONCAT_WWI(8096,8064,32, __Vtemp_824, __Vtemp_823, 
                  ((3U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[3U]));
    VL_CONCAT_WWI(8128,8096,32, __Vtemp_825, __Vtemp_824, 
                  ((2U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[2U]));
    VL_CONCAT_WWI(8160,8128,32, __Vtemp_826, __Vtemp_825, 
                  ((1U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[1U]));
    VL_CONCAT_WWI(8192,8160,32, vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d1876, __Vtemp_826, 
                  ((0U == (0xffU & (vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300 
                                    >> 0x10U))) ? vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777
                    : vlSelf->thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd[0U]));
}
