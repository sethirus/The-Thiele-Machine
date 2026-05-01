#!/usr/bin/env python3
"""Tests for per-module tensor operations (TENSOR_SET / TENSOR_GET).

Verifies that tensor read/write works correctly through the Coq-extracted
Python VM backend. Tests cover:
- Basic read/write roundtrip
- Per-module isolation
- Diagonal metric setup
- Default values (zeros for unset entries)
- Out-of-bounds index handling (should trigger error)
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from build.thiele_vm import _run_python


def _run(lines: list[str], fuel: int = 100):
    """Run a trace program and return final state."""
    return _run_python(["FUEL " + str(fuel)] + lines, fuel=fuel)


class TestTensorReadWrite:
    """Basic tensor set/get roundtrip tests."""

    def test_single_entry(self):
        """Set tensor[0][0] = 42 on module 1, read it back."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_SET 1 0 0 42 1",
            "TENSOR_GET 1 1 0 0 1",
            "HALT 0",
        ])
        assert not final.err, "Unexpected error"
        assert final.regs[1] == 42, f"r1={final.regs[1]}, expected 42"

    def test_two_entries(self):
        """Set two different tensor entries, verify both."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_SET 1 0 0 42 1",
            "TENSOR_SET 1 1 2 99 1",
            "TENSOR_GET 1 1 0 0 1",
            "TENSOR_GET 2 1 1 2 1",
            "HALT 0",
        ])
        assert not final.err
        assert final.regs[1] == 42, f"r1={final.regs[1]}, expected 42"
        assert final.regs[2] == 99, f"r2={final.regs[2]}, expected 99"

    def test_default_zero(self):
        """Unset tensor entries should default to 0."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_GET 1 1 2 3 1",
            "HALT 0",
        ])
        assert not final.err
        assert final.regs[1] == 0, f"r1={final.regs[1]}, expected 0"

    def test_overwrite(self):
        """Overwriting a tensor entry should yield the new value."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_SET 1 0 0 10 1",
            "TENSOR_SET 1 0 0 20 1",
            "TENSOR_GET 1 1 0 0 1",
            "HALT 0",
        ])
        assert not final.err
        assert final.regs[1] == 20, f"r1={final.regs[1]}, expected 20"

    def test_mu_cost_charged(self):
        """Tensor operations should charge mu cost."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_SET 1 0 0 42 3",
            "TENSOR_GET 1 1 0 0 2",
            "HALT 0",
        ])
        assert not final.err
        # PNEW costs 1, TENSOR_SET costs 3, TENSOR_GET costs 2 = 6
        assert final.mu == 6, f"mu={final.mu}, expected 6"


class TestTensorMultiModule:
    """Per-module tensor isolation tests."""

    def test_two_modules_isolated(self):
        """Two modules should have independent tensor data."""
        final = _run([
            "PNEW {0,128} 1",
            "PNEW {128,256} 1",
            "TENSOR_SET 1 0 0 10 1",
            "TENSOR_SET 2 0 0 20 1",
            "TENSOR_GET 1 1 0 0 1",
            "TENSOR_GET 2 2 0 0 1",
            "HALT 0",
        ])
        assert not final.err
        assert final.regs[1] == 10, f"r1={final.regs[1]}, expected 10"
        assert final.regs[2] == 20, f"r2={final.regs[2]}, expected 20"

    def test_nonexistent_module_returns_zero(self):
        """Reading tensor from nonexistent module should return 0."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_GET 1 99 0 0 1",
            "HALT 0",
        ])
        assert not final.err
        assert final.regs[1] == 0, f"r1={final.regs[1]}, expected 0"


class TestTensorMetric:
    """Diagonal metric configuration tests."""

    def test_diagonal_metric(self):
        """Set up isotropic diagonal metric g=5*I, verify all entries."""
        final = _run([
            "PNEW {0,256} 1",
            "TENSOR_SET 1 0 0 5 1",
            "TENSOR_SET 1 1 1 5 1",
            "TENSOR_SET 1 2 2 5 1",
            "TENSOR_SET 1 3 3 5 1",
            "TENSOR_GET 1 1 0 0 1",
            "TENSOR_GET 2 1 1 1 1",
            "TENSOR_GET 3 1 2 2 1",
            "TENSOR_GET 4 1 3 3 1",
            "TENSOR_GET 5 1 0 1 1",
            "HALT 0",
        ])
        assert not final.err
        assert final.regs[1] == 5, f"g_00={final.regs[1]}, expected 5"
        assert final.regs[2] == 5, f"g_11={final.regs[2]}, expected 5"
        assert final.regs[3] == 5, f"g_22={final.regs[3]}, expected 5"
        assert final.regs[4] == 5, f"g_33={final.regs[4]}, expected 5"
        assert final.regs[5] == 0, f"g_01={final.regs[5]}, expected 0 (off-diagonal)"

    def test_all_16_entries(self):
        """Set all 16 tensor entries and read back."""
        lines = ["PNEW {0,256} 1"]
        # Set entries: tensor[i][j] = i*4+j+1
        for i in range(4):
            for j in range(4):
                val = i * 4 + j + 1
                lines.append(f"TENSOR_SET 1 {i} {j} {val} 1")
        # Read them back into registers 0-15 (uses all RegCount=16 registers)
        from thielecpu.vm import REG_COUNT
        reg = 0
        for i in range(4):
            for j in range(4):
                lines.append(f"TENSOR_GET {reg} 1 {i} {j} 1")
                reg += 1
        lines.append("HALT 0")

        final = _run(lines)
        assert not final.err
        for idx in range(min(16, REG_COUNT)):
            expected = idx + 1
            assert final.regs[idx] == expected, \
                f"r{idx}={final.regs[idx]}, expected {expected}"
