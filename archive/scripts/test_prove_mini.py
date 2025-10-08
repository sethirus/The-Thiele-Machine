"""Unit tests for the backwards reasoning mini proof demo."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.thiele_leviathan_simulator import ThieleLeviathanSimulator


def test_prove_unreachability_large_target():
    sim = ThieleLeviathanSimulator(states=2)
    assert sim.prove_unreachability(47_176_871) == "UNSAT"

