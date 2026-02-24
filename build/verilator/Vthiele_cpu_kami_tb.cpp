// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vthiele_cpu_kami_tb__pch.h"

//============================================================
// Constructors

Vthiele_cpu_kami_tb::Vthiele_cpu_kami_tb(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vthiele_cpu_kami_tb__Syms(contextp(), _vcname__, this)}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

Vthiele_cpu_kami_tb::Vthiele_cpu_kami_tb(const char* _vcname__)
    : Vthiele_cpu_kami_tb(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

Vthiele_cpu_kami_tb::~Vthiele_cpu_kami_tb() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void Vthiele_cpu_kami_tb___024root___eval_debug_assertions(Vthiele_cpu_kami_tb___024root* vlSelf);
#endif  // VL_DEBUG
void Vthiele_cpu_kami_tb___024root___eval_static(Vthiele_cpu_kami_tb___024root* vlSelf);
void Vthiele_cpu_kami_tb___024root___eval_initial(Vthiele_cpu_kami_tb___024root* vlSelf);
void Vthiele_cpu_kami_tb___024root___eval_settle(Vthiele_cpu_kami_tb___024root* vlSelf);
void Vthiele_cpu_kami_tb___024root___eval(Vthiele_cpu_kami_tb___024root* vlSelf);

void Vthiele_cpu_kami_tb::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vthiele_cpu_kami_tb::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    Vthiele_cpu_kami_tb___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        Vthiele_cpu_kami_tb___024root___eval_static(&(vlSymsp->TOP));
        Vthiele_cpu_kami_tb___024root___eval_initial(&(vlSymsp->TOP));
        Vthiele_cpu_kami_tb___024root___eval_settle(&(vlSymsp->TOP));
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    Vthiele_cpu_kami_tb___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool Vthiele_cpu_kami_tb::eventsPending() { return !vlSymsp->TOP.__VdlySched.empty(); }

uint64_t Vthiele_cpu_kami_tb::nextTimeSlot() { return vlSymsp->TOP.__VdlySched.nextTimeSlot(); }

//============================================================
// Utilities

const char* Vthiele_cpu_kami_tb::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void Vthiele_cpu_kami_tb___024root___eval_final(Vthiele_cpu_kami_tb___024root* vlSelf);

VL_ATTR_COLD void Vthiele_cpu_kami_tb::final() {
    Vthiele_cpu_kami_tb___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* Vthiele_cpu_kami_tb::hierName() const { return vlSymsp->name(); }
const char* Vthiele_cpu_kami_tb::modelName() const { return "Vthiele_cpu_kami_tb"; }
unsigned Vthiele_cpu_kami_tb::threads() const { return 1; }
void Vthiele_cpu_kami_tb::prepareClone() const { contextp()->prepareClone(); }
void Vthiele_cpu_kami_tb::atClone() const {
    contextp()->threadPoolpOnClone();
}

//============================================================
// Trace configuration

VL_ATTR_COLD void Vthiele_cpu_kami_tb::trace(VerilatedVcdC* tfp, int levels, int options) {
    vl_fatal(__FILE__, __LINE__, __FILE__,"'Vthiele_cpu_kami_tb::trace()' called on model that was Verilated without --trace option");
}
