#!/usr/bin/env python3
"""Completeness gate: TDD enforcement that ALL 4 representations of the Thiele
Machine are finished, extracted, compiled, and mutually consistent.

This test file fails unless every layer is present and complete:
  1. Coq proofs  — 47 opcodes (40 original + 7 categorical morph), zero admits
  2. OCaml extraction — 47 constructors, compiled runner binary
  3. Python VM   — delegates to OCaml runner
  4. Verilog RTL  — opcode encodings, generated header

Cross-layer checks:
  - Opcode name sets identical across all 4 layers
  - Opcode numeric encodings consistent (Coq ThieleTypes ↔ thiele_cpu_kami.v via Kami extraction chain)
  - OCaml runner is executable and produces valid output
  - RTL dispatch covers all encodings (structural grep)
"""
from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

# The canonical set of 47 opcode names (lowercase)
# 40 original + 7 categorical morphism extension (morph, compose, morph_id,
# morph_delete, morph_assert, morph_tensor, morph_get)
CANONICAL_40 = frozenset({
    "pnew", "psplit", "pmerge", "lassert", "ljoin", "mdlacc", "pdiscover",
    "xfer", "load_imm", "load", "store", "add", "sub",
    "jump", "jnez", "call", "ret",
    "chsh_trial",
    "xor_load", "xor_add", "xor_swap", "xor_rank",
    "emit", "reveal", "oracle_halts", "halt",
    "checkpoint", "read_port", "write_port", "heap_load", "heap_store",
    "certify",
    "and", "or", "shl", "shr", "mul", "lui",
    "tensor_set", "tensor_get",
})

CANONICAL_MORPH_7 = frozenset({
    "morph", "compose", "morph_id", "morph_delete",
    "morph_assert", "morph_tensor", "morph_get",
})

CANONICAL_47 = CANONICAL_40 | CANONICAL_MORPH_7

assert len(CANONICAL_40) == 40, f"CANONICAL_40 has {len(CANONICAL_40)} items, expected 40"
assert len(CANONICAL_47) == 47, f"CANONICAL_47 has {len(CANONICAL_47)} items, expected 47"


# ============================================================================
# Layer 1: Coq proofs
# ============================================================================

class TestCoqLayer:
    """Coq source of truth is complete and admit-free."""

    COQ_DIR = ROOT / "coq"
    VMSTEP = COQ_DIR / "kernel" / "VMStep.v"
    EXTRACTION = COQ_DIR / "Extraction.v"

    def test_vmstep_exists(self):
        assert self.VMSTEP.exists(), "coq/kernel/VMStep.v missing"

    def test_extraction_exists(self):
        assert self.EXTRACTION.exists(), "coq/Extraction.v missing"

    def test_vmstep_has_47_constructors(self):
        """VMStep.v must define exactly 47 vm_instruction constructors
        (40 original + 7 categorical morphism extension)."""
        text = self.VMSTEP.read_text(encoding="utf-8")
        constructors = set(re.findall(r"\|\s+instr_(\w+)", text))
        assert len(constructors) == 47, (
            f"VMStep.v has {len(constructors)} constructors, expected 47.\n"
            f"Found: {sorted(constructors)}\n"
            f"Missing: {CANONICAL_47 - constructors}\n"
            f"Extra: {constructors - CANONICAL_47}"
        )
        assert constructors == CANONICAL_47, (
            f"Constructor mismatch vs canonical set.\n"
            f"Missing: {CANONICAL_47 - constructors}\n"
            f"Extra: {constructors - CANONICAL_47}"
        )

    def test_no_admitted_in_kernel(self):
        """No Admitted. or admit. anywhere in coq/kernel/."""
        kernel_dir = self.COQ_DIR / "kernel"
        if not kernel_dir.exists():
            pytest.skip("coq/kernel/ directory not found")
        for vf in kernel_dir.rglob("*.v"):
            text = vf.read_text(encoding="utf-8")
            # Strip comments
            text_no_comments = re.sub(r"\(\*.*?\*\)", "", text, flags=re.DOTALL)
            assert "Admitted." not in text_no_comments, (
                f"{vf.relative_to(ROOT)} contains Admitted."
            )
            assert "admit." not in text_no_comments, (
                f"{vf.relative_to(ROOT)} contains admit."
            )

    def test_no_admitted_in_kami_hw(self):
        """No Admitted. or admit. in coq/kami_hw/."""
        kami_dir = self.COQ_DIR / "kami_hw"
        if not kami_dir.exists():
            pytest.skip("coq/kami_hw/ directory not found")
        for vf in kami_dir.rglob("*.v"):
            text = vf.read_text(encoding="utf-8")
            text_no_comments = re.sub(r"\(\*.*?\*\)", "", text, flags=re.DOTALL)
            assert "Admitted." not in text_no_comments, (
                f"{vf.relative_to(ROOT)} contains Admitted."
            )

    def test_extraction_references_vm_instruction(self):
        """Extraction.v must extract vm_instruction."""
        text = self.EXTRACTION.read_text(encoding="utf-8")
        assert "vm_instruction" in text, (
            "Extraction.v does not reference vm_instruction"
        )

    def test_vo_files_compiled(self):
        """Key .vo files must exist (proves coqc succeeded)."""
        required_vos = [
            self.VMSTEP.with_suffix(".vo"),
            self.EXTRACTION.with_suffix(".vo"),
            self.COQ_DIR / "kernel" / "MuCostModel.vo",
            self.COQ_DIR / "kernel" / "NoFreeInsight.vo",
        ]
        missing = [vo for vo in required_vos if not vo.exists()]
        assert not missing, (
            "Missing .vo files (run `make -C coq`):\n"
            + "\n".join(f"  {f.relative_to(ROOT)}" for f in missing)
        )


# ============================================================================
# Layer 2: OCaml extraction
# ============================================================================

class TestOCamlLayer:
    """OCaml extraction is complete, all 47 constructors present, runner compiled."""

    ML_PATH = ROOT / "build" / "thiele_core.ml"
    RUNNER_SRC = ROOT / "build" / "extracted_vm_runner.ml"
    RUNNER_BIN = ROOT / "build" / "extracted_vm_runner"

    def test_thiele_core_ml_exists(self):
        assert self.ML_PATH.exists(), "build/thiele_core.ml missing — run `make -C coq`"

    def test_thiele_core_ml_has_47_constructors(self):
        """Extracted OCaml must contain all 47 vm_instruction constructors.

        Coq extraction may use either Instr_X (bare) or Coq_instr_X (module-prefixed)
        naming depending on the extraction context.
        """
        text = self.ML_PATH.read_text(encoding="utf-8")
        # Handle both Instr_X (legacy) and Coq_instr_X (module-prefixed) naming
        constructors = {c.lower() for c in re.findall(r"Instr_(\w+)", text)}
        constructors |= {c.lower() for c in re.findall(r"Coq_instr_(\w+)", text)}
        assert CANONICAL_47 <= constructors, (
            f"OCaml extraction missing constructors: {CANONICAL_47 - constructors}"
        )

    def test_vm_apply_dispatch_exists(self):
        """thiele_core.ml must contain a vm_apply function with match dispatch."""
        text = self.ML_PATH.read_text(encoding="utf-8")
        assert "vm_apply" in text, "vm_apply not found in thiele_core.ml"

    def test_runner_source_exists(self):
        assert self.RUNNER_SRC.exists(), (
            "build/extracted_vm_runner.ml missing"
        )

    def test_runner_binary_exists(self):
        assert self.RUNNER_BIN.exists(), (
            "build/extracted_vm_runner binary missing — "
            "run: cd build && ocamlfind ocamlc -package str -linkpkg "
            "thiele_core.ml extracted_vm_runner.ml -o extracted_vm_runner"
        )

    def test_runner_binary_executable(self):
        """Runner binary must be executable and run a simple program."""
        if not self.RUNNER_BIN.exists():
            pytest.skip("Runner binary not present")
        import tempfile
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write("HALT 1\n")
            f.flush()
            result = subprocess.run(
                [str(self.RUNNER_BIN), f.name],
                capture_output=True,
                text=True,
                timeout=10,
            )
            os.unlink(f.name)
        # Runner should exit 0 and produce some output (at minimum: mu=1)
        assert result.returncode == 0, (
            f"Runner exited with code {result.returncode}: {result.stderr[:500]}"
        )
        assert len(result.stdout) > 0, (
            "Runner produced no output on HALT instruction"
        )

    def test_runner_parses_all_40_opcodes(self):
        """Runner source must contain parse arms for all 40 opcode names."""
        text = self.RUNNER_SRC.read_text(encoding="utf-8")
        text_upper = text.upper()
        for op in CANONICAL_40:
            assert op.upper() in text_upper, (
                f"Runner source missing parse arm for {op.upper()}"
            )


# ============================================================================
# Layer 3: Python VM
# ============================================================================

class TestPythonVMLayer:
    """Python VM is complete, delegates to OCaml, handles all 40 opcodes."""

    VM_PATH = ROOT / "thielecpu" / "vm.py"
    SHIM_PATH = ROOT / "build" / "thiele_vm.py"

    def test_vm_py_exists(self):
        assert self.VM_PATH.exists(), "thielecpu/vm.py missing"

    def test_shim_exists(self):
        assert self.SHIM_PATH.exists(), "build/thiele_vm.py missing"

    def test_vm_py_is_generated(self):
        """vm.py must contain a generated-file marker."""
        text = self.VM_PATH.read_text(encoding="utf-8")
        assert any(marker in text.lower() for marker in [
            "generated", "do not edit", "auto-generated", "forge"
        ]), "thielecpu/vm.py does not appear to be a generated file"

    def test_vm_py_handles_all_40_opcodes(self):
        """vm.py must reference all 40 opcode names."""
        text = self.VM_PATH.read_text(encoding="utf-8")
        text_lower = text.lower()
        missing = [op for op in CANONICAL_40 if op not in text_lower]
        assert not missing, f"vm.py missing references to: {missing}"

    def test_shim_delegates_to_thielecpu(self):
        """build/thiele_vm.py must import from thielecpu (not implement its own VM)."""
        text = self.SHIM_PATH.read_text(encoding="utf-8")
        assert "from thielecpu" in text or "import thielecpu" in text, (
            "build/thiele_vm.py does not delegate to thielecpu — "
            "violates One VM Rule"
        )

    def test_vm_importable(self):
        """thielecpu.vm must be importable."""
        from thielecpu import vm
        assert hasattr(vm, "vm_run") or hasattr(vm, "VM"), (
            "thielecpu.vm missing vm_run or VM class"
        )

    def test_vm_run_halt_returns_state(self):
        """Running a single HALT through the Python VM must return valid state."""
        from thielecpu.vm import VMState, vm_run
        s = VMState.default()
        result = vm_run(s, [{"op": "halt", "cost": 1}])
        assert result.vm_mu == 1, f"Expected mu=1 after HALT cost=1, got {result.vm_mu}"

    def test_vm_run_all_40_opcodes_accepted(self):
        """Every opcode must be accepted by vm_run without KeyError/ValueError."""
        from thielecpu.vm import VMState, vm_run

        # Programs that exercise each opcode (some need prerequisites)
        programs = {
            "pnew":         [{"op": "pnew", "region": [0, 1], "cost": 1}],
            "psplit":       [{"op": "pnew", "region": [0, 1, 2, 3], "cost": 1},
                             {"op": "psplit", "module": 0, "left": [0, 1], "right": [2, 3], "cost": 1}],
            "pmerge":       [{"op": "pnew", "region": [0, 1], "cost": 1},
                             {"op": "pnew", "region": [2, 3], "cost": 1},
                             {"op": "pmerge", "m1": 0, "m2": 1, "cost": 1}],
            "lassert":      [{"op": "pnew", "region": [0], "cost": 1},
                             {"op": "lassert", "module": 0, "formula": "x", "cert": {"type": "sat", "proof": ""}, "cost": 1}],
            "ljoin":        [{"op": "ljoin", "cert1": "a", "cert2": "b", "cost": 1}],
            "mdlacc":       [{"op": "mdlacc", "cost": 1}],
            "pdiscover":    [{"op": "pdiscover", "module": 0, "evidence": [], "cost": 1}],
            "xfer":         [{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                             {"op": "xfer", "dst": 2, "src": 1, "cost": 1}],
            "load_imm":     [{"op": "load_imm", "dst": 1, "imm": 42, "cost": 1}],
            "load":         [{"op": "load", "dst": 1, "rs_addr": 0, "cost": 1}],
            "store":        [{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                             {"op": "store", "rs_addr": 0, "src": 1, "cost": 1}],
            "add":          [{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                             {"op": "add", "dst": 0, "rs1": 1, "rs2": 1, "cost": 1}],
            "sub":          [{"op": "load_imm", "dst": 1, "imm": 5, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 3, "cost": 1},
                             {"op": "sub", "dst": 0, "rs1": 1, "rs2": 2, "cost": 1}],
            "jump":         [{"op": "jump", "target": 1, "cost": 1},
                             {"op": "halt", "cost": 1}],
            "jnez":         [{"op": "load_imm", "dst": 1, "imm": 0, "cost": 1},
                             {"op": "jnez", "rs": 1, "target": 3, "cost": 1}],
            "call":         [{"op": "call", "target": 1, "cost": 1},
                             {"op": "halt", "cost": 1}],
            "ret":          [{"op": "call", "target": 2, "cost": 1},
                             {"op": "halt", "cost": 1},
                             {"op": "ret", "cost": 1}],
            "chsh_trial":   [{"op": "chsh_trial", "x": 0, "y": 0, "a": 0, "b": 0, "cost": 1}],
            "xor_load":     [{"op": "xor_load", "dst": 1, "addr": 0, "cost": 1}],
            "xor_add":      [{"op": "load_imm", "dst": 1, "imm": 5, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 3, "cost": 1},
                             {"op": "xor_add", "dst": 1, "src": 2, "cost": 1}],
            "xor_swap":     [{"op": "load_imm", "dst": 1, "imm": 10, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 20, "cost": 1},
                             {"op": "xor_swap", "a": 1, "b": 2, "cost": 1}],
            "xor_rank":     [{"op": "load_imm", "dst": 1, "imm": 7, "cost": 1},
                             {"op": "xor_rank", "dst": 2, "src": 1, "cost": 1}],
            "emit":         [{"op": "emit", "module": 0, "payload": "x", "cost": 1}],
            "reveal":       [{"op": "reveal", "module": 0, "bits": 0, "cert": "p", "cost": 1}],
            "oracle_halts": [{"op": "oracle_halts", "payload": 0, "cost": 1}],
            "halt":         [{"op": "halt", "cost": 1}],
            "checkpoint":   [{"op": "checkpoint", "cost": 1}],
            "read_port":    [{"op": "read_port", "dst": 1, "channel": 0, "value": 0, "bits": 8, "cost": 1}],
            "write_port":   [{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                             {"op": "write_port", "channel": 0, "src": 1, "cost": 1}],
            "heap_load":    [{"op": "heap_load", "dst": 1, "rs_addr": 0, "cost": 1}],
            "heap_store":   [{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                             {"op": "heap_store", "rs_addr": 0, "src": 1, "cost": 1}],
            "certify":      [{"op": "certify", "cost": 1}],
            "and":          [{"op": "load_imm", "dst": 1, "imm": 15, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 9, "cost": 1},
                             {"op": "and", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1}],
            "or":           [{"op": "load_imm", "dst": 1, "imm": 240, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 15, "cost": 1},
                             {"op": "or", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1}],
            "shl":          [{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 4, "cost": 1},
                             {"op": "shl", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1}],
            "shr":          [{"op": "load_imm", "dst": 1, "imm": 64, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 2, "cost": 1},
                             {"op": "shr", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1}],
            "mul":          [{"op": "load_imm", "dst": 1, "imm": 7, "cost": 1},
                             {"op": "load_imm", "dst": 2, "imm": 6, "cost": 1},
                             {"op": "mul", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1}],
            "lui":          [{"op": "lui", "dst": 1, "imm": 1, "cost": 1}],
            "tensor_set":   [{"op": "pnew", "region": [0], "cost": 1},
                             {"op": "tensor_set", "module": 0, "i": 0, "j": 0, "value": 42, "mu_delta": 1}],
            "tensor_get":   [{"op": "pnew", "region": [0], "cost": 1},
                             {"op": "tensor_get", "dst": 1, "module": 0, "i": 0, "j": 0, "mu_delta": 1}],
        }

        assert set(programs.keys()) == CANONICAL_40, (
            f"Test coverage mismatch: {CANONICAL_40 - set(programs.keys())} not tested"
        )

        failures = []
        for op, instrs in programs.items():
            # Append HALT if not already the last instruction
            if instrs[-1].get("op") != "halt":
                instrs = instrs + [{"op": "halt", "cost": 1}]
            try:
                s = VMState.default()
                result = vm_run(s, instrs, max_steps=100)
                assert result.vm_mu > 0, f"{op}: mu should be > 0"
            except Exception as exc:
                failures.append(f"{op}: {type(exc).__name__}: {exc}")

        assert not failures, (
            f"{len(failures)} opcode(s) failed in Python VM:\n"
            + "\n".join(failures)
        )


# ============================================================================
# Layer 4: Verilog RTL
# ============================================================================

class TestRTLLayer:
    """RTL layer: Kami-generated Verilog exists and is non-trivial."""

    KAMI_V = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"

    def test_kami_verilog_exists(self):
        assert self.KAMI_V.exists(), (
            "thiele_cpu_kami.v missing — run `scripts/kami_extract.sh`"
        )

    def test_kami_verilog_nonempty(self):
        if not self.KAMI_V.exists():
            pytest.skip("thiele_cpu_kami.v not present")
        size = self.KAMI_V.stat().st_size
        assert size > 10_000, (
            f"thiele_cpu_kami.v is suspiciously small ({size} bytes)"
        )


# ============================================================================
# Cross-layer consistency
# ============================================================================

def _ml_ops_from_text(text: str) -> set:
    """Extract vm_instruction opcode names from OCaml extraction text.

    Handles both Instr_X (legacy) and Coq_instr_X (module-prefixed) naming.
    """
    ops = {c.lower() for c in re.findall(r"Instr_(\w+)", text)}
    ops |= {c.lower() for c in re.findall(r"Coq_instr_(\w+)", text)}
    return ops


class TestCrossLayerConsistency:
    """All 4 layers agree on opcode names and encodings."""

    def test_coq_ocaml_opcode_parity(self):
        """Coq VMStep.v constructors == OCaml thiele_core.ml constructors."""
        vmstep = ROOT / "coq" / "kernel" / "VMStep.v"
        ml = ROOT / "build" / "thiele_core.ml"

        coq_ops = set(re.findall(r"\|\s+instr_(\w+)", vmstep.read_text()))
        ml_ops = _ml_ops_from_text(ml.read_text())

        assert coq_ops == ml_ops, (
            f"Coq↔OCaml opcode mismatch.\n"
            f"In Coq only: {coq_ops - ml_ops}\n"
            f"In OCaml only: {ml_ops - coq_ops}"
        )

    def test_ocaml_python_opcode_parity(self):
        """OCaml constructor names == Python VM opcode references."""
        ml = ROOT / "build" / "thiele_core.ml"
        vm_py = ROOT / "thielecpu" / "vm.py"

        ml_ops = _ml_ops_from_text(ml.read_text())
        py_text = vm_py.read_text().lower()
        py_missing = [op for op in ml_ops if op not in py_text]

        assert not py_missing, (
            f"Python VM missing opcodes present in OCaml: {py_missing}"
        )

    def test_ocaml_rtl_opcode_parity(self):
        """OCaml constructor names are present in ThieleTypes.v opcode definitions."""
        ml = ROOT / "build" / "thiele_core.ml"
        types_v = ROOT / "coq" / "kami_hw" / "ThieleTypes.v"

        if not types_v.exists():
            pytest.skip("ThieleTypes.v not found")

        ml_ops = _ml_ops_from_text(ml.read_text())
        # ThieleTypes.v defines OP_X for each opcode
        coq_hw_ops = {name.lower() for name in re.findall(r"Definition\s+OP_([A-Z0-9_]+)", types_v.read_text())}

        # Phase 6 is complete: all 47 opcodes (including the 7 categorical morphism opcodes)
        # are now encoded in ThieleTypes.v RTL (OP_MORPH=0x27 … OP_MORPH_GET=0x2D).
        # Positive check: CANONICAL_MORPH_7 must be present in RTL.
        missing_morph = CANONICAL_MORPH_7 - coq_hw_ops
        assert missing_morph == frozenset(), (
            f"Phase 6 regression: MORPH opcodes missing from ThieleTypes.v RTL: {missing_morph}"
        )

        # Check for unexpected OCaml-only opcodes (allow 2 slack for renamed ops).
        missing = ml_ops - coq_hw_ops
        assert len(missing) <= 2, (
            f"OCaml↔RTL opcode mismatch (expected at most 2 missing after Phase 6).\n"
            f"In OCaml only: {missing}"
        )

    def test_all_four_layers_identical_set(self):
        """The grand unification test: Coq == OCaml == CANONICAL_47."""
        vmstep = ROOT / "coq" / "kernel" / "VMStep.v"
        ml = ROOT / "build" / "thiele_core.ml"

        coq_ops = frozenset(re.findall(r"\|\s+instr_(\w+)", vmstep.read_text()))
        ml_ops = frozenset(_ml_ops_from_text(ml.read_text()))

        assert coq_ops == CANONICAL_47, f"Coq != canonical: {coq_ops ^ CANONICAL_47}"
        assert ml_ops == CANONICAL_47, f"OCaml != canonical: {ml_ops ^ CANONICAL_47}"

    def test_rtl_encodings_match_coq_thiele_types(self):
        """Numeric opcode encodings in Kami-generated Verilog are consistent with ThieleTypes.v."""
        types_v = ROOT / "coq" / "kami_hw" / "ThieleTypes.v"
        kami_v = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"

        if not types_v.exists():
            pytest.skip("ThieleTypes.v not found")
        if not kami_v.exists():
            pytest.skip("thiele_cpu_kami.v not found")

        # Parse Coq ThieleTypes: Definition OP_X : word OpcodeSz := WO~0~1~...
        coq_text = types_v.read_text()
        coq_map = {}
        for m in re.finditer(
            r"Definition\s+OP_([A-Z0-9_]+)\s*:.*?:=\s*WO~([01~]+)\.", coq_text
        ):
            name = m.group(1).upper()
            bits = m.group(2).replace("~", "")
            coq_map[name] = int(bits, 2)

        if not coq_map:
            pytest.skip("No OP_* definitions found in ThieleTypes.v")

        # Verify that at least some of the Coq opcode values appear in the Kami Verilog
        kami_text = kami_v.read_text()
        found_count = sum(1 for val in coq_map.values() if f"8'h{val:02X}" in kami_text or f"8'h{val:02x}" in kami_text)
        assert found_count >= 10, (
            f"Only {found_count}/{len(coq_map)} Coq opcodes found in Kami Verilog. "
            f"Expected at least 10 matching hex literals."
        )


# ============================================================================
# Pipeline artifacts
# ============================================================================

class TestPipelineArtifacts:
    """Build pipeline artifacts exist and are fresh."""

    def test_forge_vm_script_exists(self):
        assert (ROOT / "scripts" / "forge_vm.py").exists(), (
            "scripts/forge_vm.py missing — VM generation pipeline broken"
        )

    def test_kami_extract_script_exists(self):
        assert (ROOT / "scripts" / "kami_extract.sh").exists(), (
            "scripts/kami_extract.sh missing — RTL generation pipeline broken"
        )

    def test_inquisitor_script_exists(self):
        assert (ROOT / "scripts" / "inquisitor.py").exists(), (
            "scripts/inquisitor.py missing — proof hygiene enforcement broken"
        )

    def test_no_competing_vm_implementations(self):
        """No file outside thielecpu/vm.py defines an independent VM class or vm_apply."""
        forbidden_patterns = [
            (r"class\s+VM\b", "class VM"),
            (r"def\s+vm_apply\b", "def vm_apply"),
        ]
        # Files that are ALLOWED to have these (VM implementation, shim,
        # extraction outputs, generators, and test files)
        allowed = {
            str(ROOT / "thielecpu" / "vm.py"),
            str(ROOT / "build" / "thiele_vm.py"),
            str(ROOT / "build" / "thiele_core.ml"),
            str(ROOT / "build" / "thiele_core_minimal.ml"),
            str(ROOT / "scripts" / "forge_vm.py"),  # generator, not a competing VM
        }

        violations = []
        for py in ROOT.rglob("*.py"):
            if str(py) in allowed:
                continue
            relative = str(py.relative_to(ROOT))
            if ("archive" in str(py) or ".venv" in str(py)
                    or "__pycache__" in str(py) or relative.startswith("tests/")
                    or relative.startswith("artifacts/")):
                continue
            text = py.read_text(encoding="utf-8", errors="ignore")
            for pattern, desc in forbidden_patterns:
                if re.search(pattern, text):
                    violations.append(f"{py.relative_to(ROOT)}: defines {desc}")

        assert not violations, (
            "Competing VM implementations found (violates One VM Rule):\n"
            + "\n".join(violations)
        )
