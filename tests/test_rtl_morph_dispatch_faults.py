"""Rejected dispatch must not allocate while the clock continues after err."""
from pathlib import Path
import subprocess
import pytest
from rtl_harness import cosim

pytestmark = pytest.mark.strict_rtl

@pytest.fixture(scope="module")
def dispatch_tb(tmp_path_factory):
    work = tmp_path_factory.mktemp("morph-dispatch")
    source = (cosim.TB_DIR / "thiele_cpu_kami_tb.v").read_text()
    stop = "while (!halted_out && !err_out && cycle_count < 10000) begin"
    assert source.count(stop) == 1
    source = source.replace(stop, "while (cycle_count < 24) begin")
    point = '    $display("{");'
    assert source.count(point) == 1
    fields = {"probe_phase":"mc_phase", "probe_desc_next":"coupling_desc_next_id",
              "probe_desc_valid":"coupling_desc_valid_table", "probe_pair_next":"coupling_pair_next_id",
              "probe_pair_valid":"coupling_pair_valid_table"}
    displays = "\n".join(f'    $display("  \\\"{key}\\\": %0d,", dut.{value});' for key,value in fields.items())
    source = source.replace(point, point + "\n" + displays)
    tb = work / "thiele_cpu_kami_tb.v"
    tb.write_text(source)
    binary = work / "probe.vvp"
    cmd = ["iverilog", "-g2012", "-o", str(binary), "-I", str(cosim.RTL_DIR),
           "-I", str(cosim.BSC_VERILOG_DIR), str(cosim.RTL_DIR / "thiele_cpu_kami.v"),
           str(tb), str(cosim._regfile_source())]
    subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=120)
    return work, binary

@pytest.mark.parametrize("count", [0, 1])
@pytest.mark.parametrize("invalid_version", [False, True])
def test_morph_dispatch_allocation(dispatch_tb, count, invalid_version):
    work, binary = dispatch_tb
    instructions, data, _ = cosim.program_to_hex("PNEW {0,1} 0\nMORPH_EXT 0 1 1 0 0\nHALT")
    if invalid_version:
        word = int(instructions[1], 16)
        instructions[1] = f'{((word & ((1 << 120) - 1)) | (3 << 120)):032X}'
    data[0], data[1], data[2] = f"{count:08X}", "00000001", "00000000"
    program_path, data_path = work / "program.hex", work / "data.hex"
    program_path.write_text("\n".join(instructions) + "\n")
    data_path.write_text("\n".join(data) + "\n")
    stdout = cosim.run_simulation_iverilog(binary, program_path, data_path, n_instrs=3)
    (work / f"case-{count}-{invalid_version}.log").write_text(stdout)
    state = cosim.parse_verilog_output(stdout)
    assert state is not None
    assert state["probe_phase"] == 0
    assert bool(state["err"]) == invalid_version
    assert state["probe_desc_next"] == (1 if invalid_version else 2)
    assert state["probe_desc_valid"] == (0 if invalid_version else 2)
    assert state["probe_pair_next"] == (0 if invalid_version else count)
    assert state["probe_pair_valid"] == (0 if invalid_version else count)
    assert state["morph_next_id"] == (1 if invalid_version else 2)
