// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table implementation internals

#include "Vthiele_cpu_kami_tb__pch.h"
#include "Vthiele_cpu_kami_tb.h"
#include "Vthiele_cpu_kami_tb___024root.h"
#include "Vthiele_cpu_kami_tb_thiele_cpu_kami_tb.h"

// FUNCTIONS
Vthiele_cpu_kami_tb__Syms::~Vthiele_cpu_kami_tb__Syms()
{
}

Vthiele_cpu_kami_tb__Syms::Vthiele_cpu_kami_tb__Syms(VerilatedContext* contextp, const char* namep, Vthiele_cpu_kami_tb* modelp)
    : VerilatedSyms{contextp}
    // Setup internal state of the Syms class
    , __Vm_modelp{modelp}
    // Setup module instances
    , TOP{this, namep}
    , TOP__thiele_cpu_kami_tb{this, Verilated::catName(namep, "thiele_cpu_kami_tb")}
{
    // Configure time unit / time precision
    _vm_contextp__->timeunit(-9);
    _vm_contextp__->timeprecision(-12);
    // Setup each module's pointers to their submodules
    TOP.thiele_cpu_kami_tb = &TOP__thiele_cpu_kami_tb;
    // Setup each module's pointer back to symbol table (for public functions)
    TOP.__Vconfigure(true);
    TOP__thiele_cpu_kami_tb.__Vconfigure(true);
    // Setup scopes
    __Vscope_thiele_cpu_kami_tb.configure(this, name(), "thiele_cpu_kami_tb", "thiele_cpu_kami_tb", 0, VerilatedScope::SCOPE_OTHER);
    // Setup export functions
    for (int __Vfinal = 0; __Vfinal < 2; ++__Vfinal) {
        __Vscope_thiele_cpu_kami_tb.varInsert(__Vfinal,"logic_req_opcode_out", &(TOP__thiele_cpu_kami_tb.logic_req_opcode_out), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,1 ,7,0);
        __Vscope_thiele_cpu_kami_tb.varInsert(__Vfinal,"logic_req_payload_out", &(TOP__thiele_cpu_kami_tb.logic_req_payload_out), false, VLVT_UINT32,VLVD_NODIR|VLVF_PUB_RW,1 ,31,0);
        __Vscope_thiele_cpu_kami_tb.varInsert(__Vfinal,"logic_req_valid_out", &(TOP__thiele_cpu_kami_tb.logic_req_valid_out), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_thiele_cpu_kami_tb.varInsert(__Vfinal,"logic_resp_en", &(TOP__thiele_cpu_kami_tb.logic_resp_en), false, VLVT_UINT8,VLVD_NODIR|VLVF_PUB_RW,0);
        __Vscope_thiele_cpu_kami_tb.varInsert(__Vfinal,"logic_resp_in", &(TOP__thiele_cpu_kami_tb.logic_resp_in), false, VLVT_UINT64,VLVD_NODIR|VLVF_PUB_RW,1 ,33,0);
    }
}
