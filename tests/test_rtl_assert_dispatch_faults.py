"""Rejected assertions must stay rejected while the hardware clock continues."""
from pathlib import Path
import subprocess

import pytest
from rtl_harness import cosim

pytestmark = pytest.mark.strict_rtl


@pytest.fixture(scope="module")
def assertion_dispatch_tb(tmp_path_factory):
    work = tmp_path_factory.mktemp("assert-dispatch")
    source = (cosim.TB_DIR / "thiele_cpu_kami_tb.v").read_text()
    stop = "while (!halted_out && !err_out && cycle_count < 10000) begin"
    assert source.count(stop) == 1
    source = source.replace(stop, "while (cycle_count < 40) begin")
    declarations = """
  reg saw_assert_busy = 0;
  reg saw_first_error = 0;
  reg [31:0] first_error_code = 0;
  always @(negedge clk) begin
    if (rst_n) begin
      if (dut.lassert_phase != 0 || dut.chsh_phase != 0)
        saw_assert_busy = 1;
      if (err_out && !saw_first_error) begin
        saw_first_error = 1;
        first_error_code = error_code_out;
      end
    end
  end
"""
    source = source.replace("  reg clk = 0;", declarations + "\n  reg clk = 0;")
    point = '    $display("{");'
    assert source.count(point) == 1
    source = source.replace(point, point + '''
    $display("  \\\"saw_assert_busy\\\": %0d,", saw_assert_busy);
    $display("  \\\"first_error_code\\\": %0d,", first_error_code);
''')
    tb = work / "probe.v"
    tb.write_text(source)
    binary = work / "probe.vvp"
    subprocess.run(
        ["iverilog", "-g2012", "-o", str(binary), "-I", str(cosim.RTL_DIR),
         "-I", str(cosim.BSC_VERILOG_DIR), str(cosim.RTL_DIR / "thiele_cpu_kami.v"),
         str(tb), str(cosim._regfile_source())],
        check=True, capture_output=True, text=True, timeout=120,
    )
    return work, binary


@pytest.mark.parametrize("instruction", ["CHSH_LASSERT", "LASSERT 0 0 1 0 0"])
@pytest.mark.parametrize("fault", [None, "version", "format", "flags", "bianchi"])
def test_assertion_dispatch_rejection(assertion_dispatch_tb, instruction, fault):
    work, binary = assertion_dispatch_tb
    instructions, data, _ = cosim.program_to_hex(instruction + "\nHALT")
    word = int(instructions[0], 16)
    if fault == "version":
        word = (word & ((1 << 120) - 1)) | (3 << 120)
    elif fault == "format":
        word |= 255 << 112
    elif fault == "flags":
        word |= 1 << 96
    instructions[0] = f"{word:032X}"
    program_path, data_path = work / "program.hex", work / "data.hex"
    program_path.write_text("\n".join(instructions) + "\n")
    data_path.write_text("\n".join(data) + "\n")
    stdout = cosim.run_simulation_iverilog(
        binary, program_path, data_path, n_instrs=2,
        init_state={"INIT_TENSOR_IDX": 0, "INIT_TENSOR_VAL": 1} if fault == "bianchi" else None,
    )
    (work / f"{instruction.split()[0]}-{fault}.log").write_text(stdout)
    state = cosim.parse_verilog_output(stdout)
    assert state is not None
    assert bool(state["saw_assert_busy"]) == (fault is None)
    if fault not in (None, "bianchi"):
        assert state["err"]
        assert state["error_code"] == state["first_error_code"]
