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

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES)Vthiele_cpu_kami_tb__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    Vthiele_cpu_kami_tb* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    Vthiele_cpu_kami_tb___024root  TOP;

    // CONSTRUCTORS
    Vthiele_cpu_kami_tb__Syms(VerilatedContext* contextp, const char* namep, Vthiele_cpu_kami_tb* modelp);
    ~Vthiele_cpu_kami_tb__Syms();

    // METHODS
    const char* name() { return TOP.name(); }
};

#endif  // guard
