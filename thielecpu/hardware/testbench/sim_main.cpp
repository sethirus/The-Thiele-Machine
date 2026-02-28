#include "Vthiele_cpu_kami_tb.h"
#include "Vthiele_cpu_kami_tb___024root.h"
#include "Vthiele_cpu_kami_tb_thiele_cpu_kami_tb.h"
#include "verilated.h"

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

namespace {

struct BridgeResp {
    bool error{true};
    uint32_t value{0};
};

BridgeResp call_z3_bridge(const std::string& script, uint8_t opcode, uint32_t payload) {
    namespace fs = std::filesystem;
    const fs::path tmp = fs::temp_directory_path();
    const fs::path req = tmp / "thiele_logic_req.txt";
    const fs::path rsp = tmp / "thiele_logic_rsp.txt";

    {
        std::ofstream req_out(req);
        req_out << static_cast<unsigned>(opcode) << " " << payload << "\n";
    }

    std::ostringstream cmd;
    cmd << "python3 " << script << " --request " << req.string()
        << " --response " << rsp.string();

    std::cout << "Z3 Solving... opcode=" << static_cast<unsigned>(opcode)
              << " payload=" << payload << std::endl;

    const int rc = std::system(cmd.str().c_str());
    if (rc != 0) {
        return BridgeResp{};
    }

    std::ifstream rsp_in(rsp);
    int err = 1;
    uint32_t value = 0;
    rsp_in >> err >> value;
    return BridgeResp{err != 0, value};
}

}  // namespace

int main(int argc, char** argv, char**) {
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<Vthiele_cpu_kami_tb> top{new Vthiele_cpu_kami_tb{contextp.get()}};

    const char* env_script = std::getenv("THIELE_LOGIC_BRIDGE_SCRIPT");
    const std::string bridge_script = env_script ? env_script : "thielecpu/hardware/logic_z3_bridge.py";

    bool prev_req_valid = false;
    bool req_valid_level = false;
    bool have_pending_resp = false;
    BridgeResp pending{};

    while (!contextp->gotFinish()) {
        if (have_pending_resp && req_valid_level) {
            const uint64_t packed = (1ULL << 33) | (static_cast<uint64_t>(pending.error ? 1 : 0) << 32) |
                                    static_cast<uint64_t>(pending.value);
            top->rootp->thiele_cpu_kami_tb->logic_resp_in = packed;
            top->rootp->thiele_cpu_kami_tb->logic_resp_en = 1;
        } else {
            top->rootp->thiele_cpu_kami_tb->logic_resp_in = 0;
            top->rootp->thiele_cpu_kami_tb->logic_resp_en = 0;
        }

        top->eval();

        const bool req_valid = top->rootp->thiele_cpu_kami_tb->logic_req_valid_out;
        if (req_valid && !prev_req_valid) {
            const uint8_t opcode = top->rootp->thiele_cpu_kami_tb->logic_req_opcode_out;
            const uint32_t payload = top->rootp->thiele_cpu_kami_tb->logic_req_payload_out;
            pending = call_z3_bridge(bridge_script, opcode, payload);
            have_pending_resp = true;
        }
        prev_req_valid = req_valid;
        req_valid_level = req_valid;
        if (!req_valid) {
            have_pending_resp = false;
        }

        if (!top->eventsPending()) {
            break;
        }
        contextp->time(top->nextTimeSlot());
    }

    top->final();
    return 0;
}
