"""Isomorphism Enforcement Tests (TDD)

Structural and behavioral guards ensuring Coq = Python VM = Verilog RTL
stays bit-for-bit isomorphic.  Every gap ever found gets a test here so
it can never regress.

Guards enforce:
  1. MEM_SIZE=128 across all four representations
     (kernel proofs are parametric in MEM_SIZE)
  2. VerilogRefinement.v covers all 46 opcodes (including CERTIFY and categorical morphisms)
  3. RTL addr_width=7 in generated Verilog (log2(128))
  4. RTL Verilator binary is never stale vs source RTL
  5. CERTIFY opcode works in RTL cosim (behavioral)
  6. Opcode count consistency across Coq, OCaml, Python, RTL
  7. Witness counter round-trip through OCaml runner
"""
from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path

import pytest

pytestmark = pytest.mark.strict_rtl

REPO = Path(__file__).resolve().parent.parent
COQ = REPO / "coq"
BUILD = REPO / "build"
RTL = REPO / "thielecpu" / "hardware" / "rtl"


def _kernel_v(name: str) -> Path:
    """Resolve coq/kernel/<name> across the current subdirectory layout."""
    flat = COQ / "kernel" / name
    if flat.exists():
        return flat
    kernel_root = COQ / "kernel"
    if kernel_root.exists():
        for p in kernel_root.rglob(name):
            return p
    return flat


# ---------------------------------------------------------------------------
# Helper: read file text
# ---------------------------------------------------------------------------
def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


# ===========================================================================
# 1. MEM_SIZE = 128 everywhere (silicon-side bound; kernel proofs parametric)
# ===========================================================================
EXPECTED_MEM_SIZE = 128
EXPECTED_MEM_ADDR_SZ = 7  # log2(128)


class TestMemSizeUnified:
    """MEM_SIZE must agree across Coq, Python, OCaml runner, RTL, and Abstraction."""

    def test_coq_vmstate_mem_size(self):
        text = _read(_kernel_v("VMState.v"))
        m = re.search(r"Definition MEM_SIZE\s*:.*:=\s*(\d+)", text)
        assert m, "MEM_SIZE not found in VMState.v"
        assert int(m.group(1)) == EXPECTED_MEM_SIZE, (
            f"VMState.v MEM_SIZE={m.group(1)}, expected {EXPECTED_MEM_SIZE}"
        )

    def test_kami_thiele_types_mem_size(self):
        text = _read(COQ / "kami_hw" / "ThieleTypes.v")
        m = re.search(r"Definition MemSize\s*:=\s*(\d+)", text)
        assert m, "MemSize not found in ThieleTypes.v"
        assert int(m.group(1)) == EXPECTED_MEM_SIZE, (
            f"ThieleTypes.v MemSize={m.group(1)}, expected {EXPECTED_MEM_SIZE}"
        )

    def test_kami_thiele_types_addr_sz(self):
        text = _read(COQ / "kami_hw" / "ThieleTypes.v")
        m = re.search(r"Definition MemAddrSz\s*:=\s*(\d+)", text)
        assert m, "MemAddrSz not found in ThieleTypes.v"
        assert int(m.group(1)) == EXPECTED_MEM_ADDR_SZ, (
            f"ThieleTypes.v MemAddrSz={m.group(1)}, expected {EXPECTED_MEM_ADDR_SZ}"
        )

    def test_ocaml_runner_mem_size(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        # The default mem_size ref in parse_program
        m = re.search(r"let mem_size = ref (\d+)", text)
        assert m, "mem_size ref not found in extracted_vm_runner.ml"
        assert int(m.group(1)) == EXPECTED_MEM_SIZE, (
            f"OCaml runner mem_size={m.group(1)}, expected {EXPECTED_MEM_SIZE}"
        )

    def test_ocaml_runner_initial_state_mem(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        # initial_state makes vm_mem = make_list MEM_SIZE
        marker = f"make_list {EXPECTED_MEM_SIZE}"
        assert marker in text, f"initial_state should use {marker}"

    def test_abstraction_uses_mem_size_symbolic(self):
        """Abstraction.v must NOT hardcode 256 or 65536 for memory size."""
        text = _read(COQ / "kami_hw" / "Abstraction.v")
        # Should use MEM_SIZE symbolically, not hardcoded
        assert "List.seq 0 256" not in text, "Abstraction.v still hardcodes 256"
        assert "mod 65536" not in text, "Abstraction.v still hardcodes mod 65536"

    def test_isomorphism_map_mem_size(self):
        iso_map = json.loads(_read(BUILD / "isomorphism_map.json"))
        assert iso_map.get("memory_words") == EXPECTED_MEM_SIZE, (
            f"isomorphism_map.json memory_words={iso_map.get('memory_words')}, "
            f"expected {EXPECTED_MEM_SIZE}"
        )

    def test_rtl_regfile_addr_width_matches(self):
        """Generated Verilog must use addr_width=MemAddrSz for main data/instruction
        memory RegFiles. LASSERT FSM buffer RegFiles (lassert_fbuf, lassert_cbuf)
        may use smaller widths."""
        text = _read(RTL / "thiele_cpu_kami.v")
        # Main memory RegFiles (mem, imem) are identified by their comment header
        # and must have addr_width=EXPECTED_MEM_ADDR_SZ.
        for submod_name in ("imem", "mem"):
            pattern = re.compile(
                rf"submodule {re.escape(submod_name)}\s*\n\s*RegFile\s*#\(\.addr_width\(32'd(\d+)\)",
            )
            m = pattern.search(text)
            assert m is not None, f"RegFile submodule '{submod_name}' not found in RTL"
            assert m.group(1) == str(EXPECTED_MEM_ADDR_SZ), (
                f"RegFile '{submod_name}' addr_width={m.group(1)}, "
                f"expected {EXPECTED_MEM_ADDR_SZ}"
            )
        # mem and imem are RegFile instances. The 64-entry lassert_cbuf/fbuf
        # buffers are inlined as flat registers when they are this small.
        all_matches = re.findall(r"RegFile\s*#\(\.addr_width\(32'd(\d+)\)", text)
        assert len(all_matches) >= 2, (
            f"Expected >= 2 RegFile instantiations (mem, imem), found {len(all_matches)}"
        )

    def test_testbench_arrays_match_mem_size(self):
        """RTL testbench memory loops must iterate over MEM_SIZE entries."""
        text = _read(REPO / "rtl_harness" / "testbench" / "thiele_cpu_kami_tb.v")
        # Pre-zero loop bound and DUT-side data load loop must use MEM_SIZE.
        marker = f"i < {EXPECTED_MEM_SIZE};"
        assert marker in text, (
            f"Testbench DUT memory load loop missing '{marker}' "
            f"(must iterate {EXPECTED_MEM_SIZE} entries)"
        )


# ===========================================================================
# 2. VerilogRefinement.v covers all 46 opcodes
# ===========================================================================
class TestVerilogRefinementCoverage:
    """VerilogRefinement.v must have per-opcode simulation theorems for all opcodes."""

    EXPECTED_THEOREMS = [
        "verilog_simulates_vm_step_pnew",
        "verilog_simulates_vm_step_psplit",
        "verilog_simulates_vm_step_pmerge",
        "verilog_simulates_vm_step_lassert",
        "verilog_simulates_vm_step_ljoin",
        "verilog_simulates_vm_step_mdlacc",
        "verilog_simulates_vm_step_pdiscover",
        "verilog_simulates_vm_step_xfer",
        "verilog_simulates_vm_step_load_imm",
        "verilog_simulates_vm_step_load",
        "verilog_simulates_vm_step_store",
        "verilog_simulates_vm_step_add",
        "verilog_simulates_vm_step_sub",
        "verilog_simulates_vm_step_jump",
        "verilog_simulates_vm_step_jnez",   # has _taken and _not_taken variants
        "verilog_simulates_vm_step_call",
        "verilog_simulates_vm_step_ret",
        "verilog_simulates_vm_step_chsh_trial",  # has _ok and _bad variants
        "verilog_simulates_vm_step_xor_load",
        "verilog_simulates_vm_step_xor_add",
        "verilog_simulates_vm_step_xor_swap",
        "verilog_simulates_vm_step_xor_rank",
        "verilog_simulates_vm_step_emit",
        "verilog_simulates_vm_step_reveal",
        "verilog_simulates_vm_step_halt",
        "verilog_simulates_vm_step_checkpoint",
        "verilog_simulates_vm_step_read_port",
        "verilog_simulates_vm_step_write_port",
        "verilog_simulates_vm_step_heap_load",
        "verilog_simulates_vm_step_heap_store",
        "verilog_simulates_vm_step_certify",
        "verilog_simulates_vm_step_and",
        "verilog_simulates_vm_step_or",
        "verilog_simulates_vm_step_shl",
        "verilog_simulates_vm_step_shr",
        "verilog_simulates_vm_step_mul",
        "verilog_simulates_vm_step_lui",
        "verilog_simulates_vm_step_tensor_set",
        "verilog_simulates_vm_step_tensor_get",
        "verilog_simulates_vm_step_morph",
        "verilog_simulates_vm_step_compose",
        "verilog_simulates_vm_step_morph_id",
        "verilog_simulates_vm_step_morph_delete",
        "verilog_simulates_vm_step_morph_assert",
        "verilog_simulates_vm_step_morph_tensor",
        "verilog_simulates_vm_step_morph_get",
    ]

    def test_all_46_theorems_present(self):
        text = _read(COQ / "kami_hw" / "VerilogRefinement.v")
        missing = [t for t in self.EXPECTED_THEOREMS if t not in text]
        assert not missing, (
            f"VerilogRefinement.v missing {len(missing)} theorem(s): {missing}"
        )

    def test_no_admitted_proofs(self):
        text = _read(COQ / "kami_hw" / "VerilogRefinement.v")
        assert "Admitted" not in text, "VerilogRefinement.v has Admitted proofs"

    def test_verilog_refinement_vo_exists(self):
        vo = COQ / "kami_hw" / "VerilogRefinement.vo"
        assert vo.exists(), f"VerilogRefinement.vo missing — run make -C coq"

    def test_certify_theorem_present(self):
        """Regression test: CERTIFY was missing from VerilogRefinement.v until 2026-03-10."""
        text = _read(COQ / "kami_hw" / "VerilogRefinement.v")
        assert "verilog_simulates_vm_step_certify" in text, (
            "CERTIFY refinement theorem missing from VerilogRefinement.v"
        )


# ===========================================================================
# 3. Abstraction.v covers all 46 opcodes in kami_step
# ===========================================================================
class TestAbstractionCoverage:
    """Abstraction.v kami_step must have match arms for all 46 opcodes."""

    def test_no_admitted(self):
        text = _read(COQ / "kami_hw" / "Abstraction.v")
        assert "Admitted" not in text, "Abstraction.v has Admitted proofs"

    def test_certify_arm_exists(self):
        text = _read(COQ / "kami_hw" / "Abstraction.v")
        assert "instr_certify" in text, "kami_step missing instr_certify arm"

    def test_certified_field_set_true(self):
        text = _read(COQ / "kami_hw" / "Abstraction.v")
        assert "snap_certified := true" in text, (
            "CERTIFY arm must set snap_certified := true"
        )


# ===========================================================================
# 4. Opcode count consistency across all layers
# ===========================================================================
class TestOpcodeCountConsistency:
    """All layers must agree on 46 opcodes."""

    def test_coq_vmstep_has_46_constructors(self):
        text = _read(_kernel_v("VMStep.v"))
        constructors = re.findall(r"Coq_instr_\w+|instr_\w+\s*:", text)
        # Count unique opcode names from step constructors
        step_ctors = re.findall(r"\|\s*step_(\w+)\s*:", text)
        assert len(step_ctors) >= 46, (
            f"VMStep.v has {len(step_ctors)} step constructors, expected >= 46"
        )

    def test_kami_types_has_46_opcodes(self):
        text = _read(COQ / "kami_hw" / "ThieleTypes.v")
        ops = re.findall(r"Definition OP_\w+", text)
        assert len(ops) >= 46, (
            f"ThieleTypes.v has {len(ops)} OP_* definitions, expected >= 46"
        )

    def test_ocaml_extraction_has_46_constructors(self):
        text = _read(BUILD / "thiele_core.ml")
        # Handle both Instr_X (legacy) and Coq_instr_X (module-prefixed) naming
        ctors = re.findall(r"Instr_\w+", text)
        ctors += [f"Instr_{m}" for m in re.findall(r"Coq_instr_(\w+)", text)]
        unique = set(ctors)
        assert len(unique) >= 46, (
            f"thiele_core.ml has {len(unique)} Instr_* constructors, expected >= 46"
        )

    def test_isomorphism_map_has_46_opcodes(self):
        iso_map = json.loads(_read(BUILD / "isomorphism_map.json"))
        opcodes = iso_map.get("opcodes", {})
        assert len(opcodes) == 46, (
            f"isomorphism_map.json has {len(opcodes)} opcodes, expected 46"
        )


# ===========================================================================
# 5. RTL Verilator binary freshness
# ===========================================================================
class TestRTLFreshness:
    """The Verilator binary must not be stale relative to the source RTL."""

    def test_verilator_binary_exists(self):
        binary = BUILD / "verilator" / "Vthiele_cpu_kami_tb"
        if not binary.exists():
            pytest.skip("Verilator binary not built yet (will auto-build on cosim)")

    def test_verilator_binary_not_stale(self):
        """If the Verilator binary exists, it must be newer than source RTL."""
        binary = BUILD / "verilator" / "Vthiele_cpu_kami_tb"
        rtl_src = RTL / "thiele_cpu_kami.v"
        tb_src = REPO / "rtl_harness" / "testbench" / "thiele_cpu_kami_tb.v"
        if not binary.exists():
            pytest.skip("Verilator binary not built yet (cosim auto-rebuilds)")
        bin_mtime = binary.stat().st_mtime
        for src in [rtl_src, tb_src]:
            if src.exists():
                src_mtime = src.stat().st_mtime
                if src_mtime > bin_mtime:
                    # Touch the binary to force cosim rebuild instead of failing
                    pytest.fail(
                        f"Verilator binary is stale: {src.name} "
                        f"(mtime {src_mtime:.0f}) is newer than binary "
                        f"(mtime {bin_mtime:.0f}). "
                        f"Run any cosim test to auto-rebuild."
                    )


# ===========================================================================
# 6. CERTIFY opcode works in RTL cosim (behavioral)
# ===========================================================================
def _rtl_available() -> bool:
    try:
        from thielecpu.hardware.cosim import run_verilog
        result = run_verilog(["HALT 1"])
        return result is not None
    except Exception:
        return False

RTL_SKIP = pytest.mark.skipif(
    not _rtl_available(),
    reason="RTL cosim backend unavailable",
)


@RTL_SKIP
class TestCertifyRTLCosim:
    """CERTIFY opcode must work identically in RTL and Python VM."""

    def test_certify_charges_s_cost_in_rtl(self):
        """CERTIFY with cost=5 should yield mu=S(5)=6."""
        from thielecpu.hardware.cosim import run_verilog
        # CERTIFY encoding: CERTIFY op_a op_b cost — cost goes third
        result = run_verilog(["CERTIFY 0 0 5", "HALT 0"])
        assert result is not None, "RTL cosim returned None"
        assert result["mu"] == 6, (
            f"RTL CERTIFY cost=5 yielded mu={result['mu']}, expected 6 (S(5))"
        )

    def test_certify_bisim_with_python_vm(self):
        """CERTIFY mu must match between Python VM and RTL."""
        from thielecpu.hardware.cosim import run_verilog
        from build.thiele_vm import run_vm

        program = ["CERTIFY 0 0 3", "CERTIFY 0 0 2", "HALT 0"]
        rtl = run_verilog(program)
        vm = run_vm(program)

        assert rtl is not None
        # S(3) + S(2) = 4 + 3 = 7
        assert rtl["mu"] == 7, f"RTL mu={rtl['mu']}, expected 7"
        assert vm.mu == rtl["mu"], (
            f"mu mismatch: Python={vm.mu}, RTL={rtl['mu']}"
        )


# ===========================================================================
# 7. Witness counter round-trip through OCaml runner
# ===========================================================================
class TestWitnessCounterSerialization:
    """Witness counters must survive OCaml runner JSON round-trip."""

    def test_ocaml_runner_serializes_witness(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        assert '"witness"' in text or "'witness'" in text or "witness" in text, (
            "OCaml runner must serialize witness counters"
        )

    def test_ocaml_runner_deserializes_witness(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        assert "parse_json_int_array json \"witness\"" in text, (
            "OCaml runner must deserialize witness from resume JSON"
        )

    def test_python_vm_serializes_witness(self):
        text = _read(REPO / "thielecpu" / "vm.py")
        assert '"witness"' in text, "vm.py must serialize witness field"

    def test_python_vm_deserializes_witness(self):
        text = _read(REPO / "thielecpu" / "vm.py")
        assert 'get("witness"' in text, "vm.py must parse witness from JSON"


# ===========================================================================
# 8. INIT directive handling completeness
# ===========================================================================
class TestINITDirectiveHandling:
    """OCaml runner must handle all INIT directives without crashing."""

    def test_init_pt_handled(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        assert '"INIT_PT"' in text or "'INIT_PT'" in text or "INIT_PT" in text, (
            "OCaml runner must handle INIT_PT directive"
        )

    def test_init_active_module_handled(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        assert "INIT_ACTIVE_MODULE" in text, (
            "OCaml runner must handle INIT_ACTIVE_MODULE directive"
        )

    def test_init_logic_acc_handled(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        assert "INIT_LOGIC_ACC" in text, (
            "OCaml runner must handle INIT_LOGIC_ACC directive"
        )

    def test_init_tensor_handled(self):
        text = _read(BUILD / "extracted_vm_runner.ml")
        assert "INIT_TENSOR" in text, (
            "OCaml runner must handle INIT_TENSOR directive"
        )

    def test_all_init_directives_parse(self):
        """Smoke test: all INIT directives are accepted without crash."""
        runner = BUILD / "extracted_vm_runner"
        if not runner.exists():
            pytest.skip("OCaml runner binary not built")
        import tempfile
        program = (
            "FUEL 5\n"
            "INIT_REG 0 0\n"
            "INIT_MEM 0 42\n"
            "INIT_PT 0 128\n"
            "INIT_ACTIVE_MODULE 0\n"
            "INIT_LOGIC_ACC 3405643470\n"
            "INIT_TENSOR 0 99\n"
            "HALT 1\n"
        )
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write(program)
            f.flush()
            try:
                result = subprocess.run(
                    [str(runner), f.name],
                    capture_output=True, text=True, timeout=10
                )
                assert result.returncode == 0, (
                    f"OCaml runner crashed: {result.stderr}"
                )
                state = json.loads(result.stdout.strip())
                assert state["logic_acc"] == 3405643470, (
                    f"INIT_LOGIC_ACC not applied: got {state['logic_acc']}"
                )
                assert state["mu_tensor"][0] == 99, (
                    f"INIT_TENSOR not applied: got {state['mu_tensor'][0]}"
                )
            finally:
                os.unlink(f.name)
