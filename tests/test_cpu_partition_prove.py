"""An incomplete induction campaign must never be accepted as an unbounded proof."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("partition_prove", ROOT / "scripts/cpu_partition_prove.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def passing_results():
    return [dict(case, status="PASS") for case in MODULE.cases()]


def test_complete_induction_covers_every_opcode_and_old_counter():
    campaign = MODULE.cases()
    disjoint = [case for case in campaign if case["mode"] == "disjoint"]
    assert {(case["opcode"], case["counter"]) for case in disjoint} == {
        (op, counter) for op in range(3) for counter in range(1, 65)}
    assert len(disjoint) == 316
    for counter in range(1, 63):
        assert {c["pair_case"] for c in disjoint if c["opcode"] == 1 and
                c["counter"] == counter} == {"old", "left", "right"}
    assert MODULE.complete(passing_results())


@pytest.mark.parametrize("missing", ["base", "frame", "bounds-op1", "disjoint-op2-next64"])
def test_missing_obligation_fails(missing):
    assert not MODULE.complete([r for r in passing_results() if r["name"] != missing])


@pytest.mark.parametrize("status", ["FAIL", "TIMEOUT", "INCOMPLETE", "UNDECIDED"])
def test_inconclusive_or_failed_obligation_fails(status):
    results = passing_results()
    results[-1]["status"] = status
    assert not MODULE.complete(results)


def test_duplicate_cannot_replace_missing_case():
    results = passing_results()
    results[-1] = results[-2].copy()
    assert not MODULE.complete(results)


def test_mislabeled_counter_is_rejected():
    results = passing_results()
    results[-1]["counter"] = 63
    assert not MODULE.complete(results)


def test_counter_restriction_applies_only_to_old_frame(tmp_path):
    case = next(c for c in MODULE.cases() if c["name"] == "disjoint-op1-next62-right")
    script = MODULE.case_script(case, tmp_path, 300)
    assert "-set-at 1 pt_next_id 62" in script
    assert "-set-at 2 pt_next_id" not in script
    assert "connect -set pt_next_id" not in script
    assert "connect -set ptTable" not in script
    assert "connect -set ptBases" not in script
    assert "-set ptf_a 63" in script


def test_missing_pair_case_fails():
    results = [r for r in passing_results() if r["name"] != "disjoint-op1-next43-old"]
    assert not MODULE.complete(results)


def test_solver_exit_zero_without_proof_is_rejected(tmp_path, monkeypatch):
    def fake_solver(args, **kwargs):
        log = Path(args[args.index("-ql") + 1])
        log.write_text("Found and reported 0 problems.\nSAT solving reached its time limit.\n")
        return type("Completed", (), {"returncode": 0})()

    monkeypatch.setattr(MODULE.subprocess, "run", fake_solver)
    result = MODULE.execute("yosys", tmp_path, "test", "sat\n", 1, proof=True)
    assert result["status"] == "FAIL"


def test_conflicting_drivers_are_rejected_even_with_success_text(tmp_path, monkeypatch):
    def fake_solver(args, **kwargs):
        log = Path(args[args.index("-ql") + 1])
        log.write_text("Driver-driver conflict\nFound and reported 0 problems.\n" + MODULE.SUCCESS)
        return type("Completed", (), {"returncode": 0})()

    monkeypatch.setattr(MODULE.subprocess, "run", fake_solver)
    result = MODULE.execute("yosys", tmp_path, "test", "sat\n", 1, proof=True)
    assert result["status"] == "FAIL"
