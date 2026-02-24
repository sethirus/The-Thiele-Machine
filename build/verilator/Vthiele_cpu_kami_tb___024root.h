// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vthiele_cpu_kami_tb.h for the primary calling header

#ifndef VERILATED_VTHIELE_CPU_KAMI_TB___024ROOT_H_
#define VERILATED_VTHIELE_CPU_KAMI_TB___024ROOT_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"


class Vthiele_cpu_kami_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vthiele_cpu_kami_tb___024root final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    // Anonymous structures to workaround compiler member-count bugs
    struct {
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__clk;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__rst_n;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__load_en;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__err_out;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__halted_out;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__bianchi_alarm_out;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceEn;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err__VforceVal;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err__024D_IN;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__err__024EN;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__halted;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceEn;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__halted__VforceVal;
        CData/*0:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__halted__024D_IN;
        CData/*0:0*/ __VstlFirstIteration;
        CData/*0:0*/ __Vtrigprevexpr___TOP__thiele_cpu_kami_tb__DOT__clk__0;
        CData/*0:0*/ __VactContinue;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__pc_out;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__mu_out;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__partition_ops_out;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__mdl_ops_out;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__info_gain_out;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__error_code_out;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__mu_tensor_0;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__mu_tensor_1;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__mu_tensor_2;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__mu_tensor_3;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__num_instrs;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__exec_op_i;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__exec_a_i;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__exec_b_i;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__sh_m;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__sh_pred_mode_i;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__sh_pred_param_i;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__first_bit;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__program_hex_path;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__data_hex_path;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__current_instr;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__error_code;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceRd;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceEn;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__error_code__VforceVal;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__imem;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__imem__024D_IN;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__info_gain;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceEn;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__VforceVal;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__info_gain__024D_IN;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceEn;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__VforceVal;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mdl_ops__024D_IN;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mem;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceRd;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceEn;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mem__VforceVal;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceEn;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu__VforceVal;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu__024D_IN;
        VlWide<16>/*511:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor;
        VlWide<16>/*511:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceRd;
        VlWide<16>/*511:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceEn;
    };
    struct {
        VlWide<16>/*511:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__VforceVal;
        VlWide<16>/*511:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__mu_tensor__024D_IN;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceEn;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__VforceVal;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__partition_ops__024D_IN;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__pc;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceRd;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceEn;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__pc__VforceVal;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__regs;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceRd;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceEn;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__regs__VforceVal;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq3;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d1233;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq2;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__CASE_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_ETC___05Fq4;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_63_T_ETC___05F_d300;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_47___05Fh66776;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_48___05Fh66777;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_61___05Fh66790;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d1876;
        VlWide<256>/*8191:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__IF_regs_68_BITS_999_TO_992_877_EQ_255_878_THEN_ETC___05F_d2517;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d702;
        VlWide<32>/*1023:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d911;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__IF_SEL_ARR_imem_0_BITS_31_TO_0_1_imem_0_BITS_6_ETC___05F_d614;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_62___05Fh66791;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_63___05Fh66792;
        IData/*31:0*/ thiele_cpu_kami_tb__DOT__dut__DOT__x_90___05Fh66811;
        IData/*31:0*/ __VactIterCount;
        QData/*39:0*/ thiele_cpu_kami_tb__DOT__load_data;
        QData/*63:0*/ thiele_cpu_kami_tb__DOT__sh_left;
        QData/*63:0*/ thiele_cpu_kami_tb__DOT__sh_right;
        QData/*63:0*/ thiele_cpu_kami_tb__DOT__shadow_new_mask;
        VlUnpacked<IData/*31:0*/, 256> thiele_cpu_kami_tb__DOT__instr_memory;
        VlUnpacked<IData/*31:0*/, 256> thiele_cpu_kami_tb__DOT__data_memory;
        VlUnpacked<QData/*63:0*/, 64> thiele_cpu_kami_tb__DOT__shadow_masks;
    };
    VlDelayScheduler __VdlySched;
    VlTriggerScheduler __VtrigSched_he0995f9e__0;
    VlTriggerScheduler __VtrigSched_he099605b__0;
    VlTriggerVec<1> __VstlTriggered;
    VlTriggerVec<3> __VactTriggered;
    VlTriggerVec<3> __VnbaTriggered;

    // INTERNAL VARIABLES
    Vthiele_cpu_kami_tb__Syms* const vlSymsp;

    // CONSTRUCTORS
    Vthiele_cpu_kami_tb___024root(Vthiele_cpu_kami_tb__Syms* symsp, const char* v__name);
    ~Vthiele_cpu_kami_tb___024root();
    VL_UNCOPYABLE(Vthiele_cpu_kami_tb___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
