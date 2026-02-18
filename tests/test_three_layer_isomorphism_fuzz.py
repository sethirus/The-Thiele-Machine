"""Hypothesis fuzzing across Python/Coq/Verilog for the supported ISA subset."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

from hypothesis import given, settings, strategies as st

from scripts.verify_isomorphism import execute_coq, execute_verilog
from tests.test_three_layer_isomorphism import Instruction, execute_python
from thielecpu.state import ModuleId


@dataclass
class ProgramSpec:
    program: List[Instruction]


def _program_strategy():
    """Generate small programs over the supported cross-layer opcode subset."""
    pnew_idx = st.integers(min_value=0, max_value=7)
    pnew = st.builds(lambda i: Instruction("PNEW", ({i},), cost=1), pnew_idx)

    mid = st.integers(min_value=1, max_value=6)
    pred = st.integers(min_value=0, max_value=255)
    psplit = st.builds(lambda m, p: Instruction("PSPLIT", (ModuleId(m), p), cost=64), mid, pred)

    merge_pair = st.tuples(st.integers(min_value=1, max_value=6), st.integers(min_value=1, max_value=6)).filter(
        lambda pair: pair[0] != pair[1]
    )
    pmerge = st.builds(lambda pair: Instruction("PMERGE", (ModuleId(pair[0]), ModuleId(pair[1])), cost=4), merge_pair)

    instrs = st.lists(st.one_of(pnew, pmerge, psplit), min_size=1, max_size=5)

    return st.builds(lambda ops: ProgramSpec(ops + [Instruction("HALT", tuple(), cost=0)]), instrs)


def _safe_execute(program: List[Instruction]):
    """Execute program with Python semantics, skipping invalid sequences."""
    try:
        return execute_python(program)
    except (ValueError, KeyError):
        return None


@settings(max_examples=12, deadline=None)
@given(_program_strategy())
def test_fuzz_three_layer_isomorphism(program_spec: ProgramSpec) -> None:
    """Fuzz small programs and assert Python/Coq/Verilog agreement."""
    program = program_spec.program

    py_trace = _safe_execute(program)
    if py_trace is None:
        return

    coq_trace = execute_coq(program)
    verilog_trace = execute_verilog(program)

    assert py_trace.final_mu == coq_trace.final_mu == verilog_trace.final_mu
    assert py_trace.final_modules == coq_trace.final_modules == verilog_trace.final_modules

    # Compare regions as multisets (sets with multiplicity) since module IDs may differ
    # The implementations are isomorphic if they have the same SET of regions
    py_regions = sorted([tuple(sorted(r)) for r in py_trace.final_regions.values()])
    coq_regions = sorted([tuple(sorted(r)) for r in coq_trace.final_regions.values()])
    vl_regions = sorted([tuple(sorted(r)) for r in verilog_trace.final_regions.values()])

    assert py_regions == coq_regions == vl_regions, \
        f"Region sets differ:\nPython: {py_regions}\nCoq: {coq_regions}\nVerilog: {vl_regions}"

