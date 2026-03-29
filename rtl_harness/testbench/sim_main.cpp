#include "Vthiele_cpu_kami_tb.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdlib>
#include <memory>
#include <string>

namespace {

int parse_flag_arg(int argc, char** argv, const std::string& key, int default_value = 0) {
    const std::string prefix = "+" + key + "=";
    for (int index = 1; index < argc; ++index) {
        const std::string arg = argv[index] ? argv[index] : "";
        if (arg.rfind(prefix, 0) == 0) {
            return std::atoi(arg.substr(prefix.size()).c_str());
        }
    }
    return default_value;
}

std::string parse_trace_file_arg(int argc, char** argv) {
    for (int index = 1; index < argc; ++index) {
        const std::string arg = argv[index] ? argv[index] : "";
        static const std::string prefix = "+TRACE_FILE=";
        if (arg.rfind(prefix, 0) == 0) {
            return arg.substr(prefix.size());
        }
    }
    return "";
}

}  // namespace

int main(int argc, char** argv, char**) {
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::string trace_path = parse_trace_file_arg(argc, argv);
    std::unique_ptr<VerilatedVcdC> tfp;
    if (!trace_path.empty()) {
        Verilated::traceEverOn(true);
    }

    const std::unique_ptr<Vthiele_cpu_kami_tb> top{new Vthiele_cpu_kami_tb{contextp.get()}};

    if (!trace_path.empty()) {
        tfp = std::make_unique<VerilatedVcdC>();
        top->trace(tfp.get(), 99);
        tfp->open(trace_path.c_str());
    }

    while (!contextp->gotFinish()) {
        top->eval();
        if (tfp) {
            tfp->dump(contextp->time());
        }

        if (!top->eventsPending()) {
            break;
        }
        contextp->time(top->nextTimeSlot());
    }

    if (tfp) {
        tfp->flush();
        tfp->close();
    }
    top->final();
    return 0;
}
