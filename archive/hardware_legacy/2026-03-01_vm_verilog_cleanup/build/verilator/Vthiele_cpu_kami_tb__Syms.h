// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VTHIELE_CPU_KAMI_TB__SYMS_H_
#define VERILATED_VTHIELE_CPU_KAMI_TB__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "Vthiele_cpu_kami_tb.h"

// INCLUDE MODULE CLASSES
#include "Vthiele_cpu_kami_tb___024root.h"
#include "Vthiele_cpu_kami_tb_thiele_cpu_kami_tb.h"

// DPI TYPES for DPI Export callbacks (Internal use)

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES)Vthiele_cpu_kami_tb__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    Vthiele_cpu_kami_tb* const __Vm_modelp;
    bool __Vm_activity = false;  ///< Used by trace routines to determine change occurred
    uint32_t __Vm_baseCode = 0;  ///< Used by trace routines when tracing multiple models
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    Vthiele_cpu_kami_tb___024root  TOP;
    Vthiele_cpu_kami_tb_thiele_cpu_kami_tb TOP__thiele_cpu_kami_tb;

    // SCOPE NAMES
    VerilatedScope __Vscope_thiele_cpu_kami_tb;

    // CONSTRUCTORS
    Vthiele_cpu_kami_tb__Syms(VerilatedContext* contextp, const char* namep, Vthiele_cpu_kami_tb* modelp);
    ~Vthiele_cpu_kami_tb__Syms();

    // METHODS
    const char* name() { return TOP.name(); }
};

#endif  // guard
