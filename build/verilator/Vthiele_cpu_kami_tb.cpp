// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vthiele_cpu_kami_tb__pch.h"
#include "verilated_vcd_c.h"

//============================================================
// Constructors

Vthiele_cpu_kami_tb::Vthiele_cpu_kami_tb(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vthiele_cpu_kami_tb__Syms(contextp(), _vcname__, this)}
    , thiele_cpu_kami_tb{vlSymsp->TOP.thiele_cpu_kami_tb}
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
    vlSymsp->__Vm_activity = true;
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
std::unique_ptr<VerilatedTraceConfig> Vthiele_cpu_kami_tb::traceConfig() const {
    return std::unique_ptr<VerilatedTraceConfig>{new VerilatedTraceConfig{false, false, false}};
};

//============================================================
// Trace configuration

void Vthiele_cpu_kami_tb___024root__trace_decl_types(VerilatedVcd* tracep);

void Vthiele_cpu_kami_tb___024root__trace_init_top(Vthiele_cpu_kami_tb___024root* vlSelf, VerilatedVcd* tracep);

VL_ATTR_COLD static void trace_init(void* voidSelf, VerilatedVcd* tracep, uint32_t code) {
    // Callback from tracep->open()
    Vthiele_cpu_kami_tb___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<Vthiele_cpu_kami_tb___024root*>(voidSelf);
    Vthiele_cpu_kami_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {
        VL_FATAL_MT(__FILE__, __LINE__, __FILE__,
            "Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.");
    }
    vlSymsp->__Vm_baseCode = code;
    tracep->pushPrefix(std::string{vlSymsp->name()}, VerilatedTracePrefixType::SCOPE_MODULE);
    Vthiele_cpu_kami_tb___024root__trace_decl_types(tracep);
    Vthiele_cpu_kami_tb___024root__trace_init_top(vlSelf, tracep);
    tracep->popPrefix();
}

VL_ATTR_COLD void Vthiele_cpu_kami_tb___024root__trace_register(Vthiele_cpu_kami_tb___024root* vlSelf, VerilatedVcd* tracep);

VL_ATTR_COLD void Vthiele_cpu_kami_tb::trace(VerilatedVcdC* tfp, int levels, int options) {
    if (tfp->isOpen()) {
        vl_fatal(__FILE__, __LINE__, __FILE__,"'Vthiele_cpu_kami_tb::trace()' shall not be called after 'VerilatedVcdC::open()'.");
    }
    if (false && levels && options) {}  // Prevent unused
    tfp->spTrace()->addModel(this);
    tfp->spTrace()->addInitCb(&trace_init, &(vlSymsp->TOP));
    Vthiele_cpu_kami_tb___024root__trace_register(&(vlSymsp->TOP), tfp->spTrace());
}
