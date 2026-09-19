"""Concrete C1 cases against regenerated RTL, including arbitrary CSR boundaries."""
import pytest

from rtl_harness.cosim import program_to_hex, run_verilog
from scripts.thiele_asm import assemble

pytestmark = pytest.mark.strict_rtl


def run(program):
    result = run_verilog(program, backend="iverilog")
    assert result is not None
    return result


@pytest.mark.parametrize("instruction", [
    "TENSOR_SET 15 3 3 255 17", "TENSOR_GET 14 15 3 2 29", "CHSH_LASSERT 7",
])
def test_harness_matches_canonical_encoding(instruction):
    words, _, _ = assemble(instruction)
    encoded, _, _ = program_to_hex(instruction)
    assert int(encoded[0], 16) == words[0]


def test_all_module_slots_are_separate_from_revelation_tensor():
    program = []
    for mid in range(16):
        program += [f"TENSOR_SET {mid} 3 3 {240 + mid} 1",
                    f"TENSOR_GET {mid} {mid} 3 3 2"]
    result = run("\n".join(program + ["HALT"]))
    assert result["error_code"] == 0
    assert result["mu"] == 48
    assert result["regs"] == list(range(240, 256))
    assert result["module_tensors"] == [[0] * 15 + [240 + mid] for mid in range(16)]
    assert result["mu_tensor"] == [0] * 16


def test_tensor_overwrite_preserves_other_cells_and_modules():
    result = run("\n".join([
        "TENSOR_SET 1 0 0 41 0", "TENSOR_SET 1 0 1 42 0",
        "TENSOR_SET 2 0 0 43 0", "TENSOR_SET 1 0 0 255 0", "HALT",
    ]))
    expected = [[0] * 16 for _ in range(16)]
    expected[1][:2] = [255, 42]
    expected[2][0] = 43
    assert result["module_tensors"] == expected
    assert result["error_code"] == 0


@pytest.mark.parametrize("base,offset,address", [(4, 2, 6), (127, 1, 0), (0xFFFFFFFF, 2, 1)])
def test_heap_base_addressing_and_csr_preservation(base, offset, address):
    result = run("\n".join([
        f"INIT_CSR_HEAP_BASE {base}", "INIT_CSR_STATUS 37", "PNEW 0 16 0",
        f"LOAD_IMM 1 {offset} 0", "LOAD_IMM 2 77 0",
        "HEAP_STORE 1 2 0", "HEAP_LOAD 3 1 0", "HALT",
    ]))
    assert result["error_code"] == 0
    assert result["regs"][3] == 77
    assert result["mem"][address] == 77
    assert sum(result["mem"]) == 77
    assert result["csrs"]["heap_base"] == base
    assert result["csrs"]["status"] == 37


def test_heap_locality_checks_effective_address():
    result = run("\n".join([
        "INIT_CSR_HEAP_BASE 15", "PNEW 0 16 0", "LOAD_IMM 1 1 0",
        "LOAD_IMM 2 77 0", "HEAP_STORE 1 2 0", "HALT",
    ]))
    assert result["error_code"] == 0x0BADC0DE
    assert result["mem"] == [0] * 128
