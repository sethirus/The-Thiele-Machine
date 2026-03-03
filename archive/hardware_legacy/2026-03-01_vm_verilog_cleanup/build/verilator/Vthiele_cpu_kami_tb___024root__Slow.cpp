// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vthiele_cpu_kami_tb.h for the primary calling header

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb__Syms.h"
#include "Vthiele_cpu_kami_tb___024root.h"

void Vthiele_cpu_kami_tb___024root___ctor_var_reset(Vthiele_cpu_kami_tb___024root* vlSelf);

Vthiele_cpu_kami_tb___024root::Vthiele_cpu_kami_tb___024root(Vthiele_cpu_kami_tb__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , __VdlySched{*symsp->_vm_contextp__}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vthiele_cpu_kami_tb___024root___ctor_var_reset(this);
}

void Vthiele_cpu_kami_tb___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

Vthiele_cpu_kami_tb___024root::~Vthiele_cpu_kami_tb___024root() {
}
