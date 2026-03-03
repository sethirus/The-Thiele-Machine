// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vthiele_cpu_kami_tb.h for the primary calling header

#ifndef VERILATED_VTHIELE_CPU_KAMI_TB___024ROOT_H_
#define VERILATED_VTHIELE_CPU_KAMI_TB___024ROOT_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
class Vthiele_cpu_kami_tb_thiele_cpu_kami_tb;


class Vthiele_cpu_kami_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vthiele_cpu_kami_tb___024root final : public VerilatedModule {
  public:
    // CELLS
    Vthiele_cpu_kami_tb_thiele_cpu_kami_tb* thiele_cpu_kami_tb;

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __VstlFirstIteration;
    CData/*0:0*/ __Vtrigprevexpr___TOP__thiele_cpu_kami_tb____PVT__clk__0;
    CData/*0:0*/ __VactContinue;
    IData/*31:0*/ __VactIterCount;
    VlUnpacked<CData/*0:0*/, 7> __Vm_traceActivity;
    VlDelayScheduler __VdlySched;
    VlTriggerScheduler __VtrigSched_he4602a19__0;
    VlTriggerScheduler __VtrigSched_he4602ae8__0;
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
