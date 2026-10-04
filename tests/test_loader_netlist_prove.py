"""A partial or structurally changed comparison must not produce a green job."""
from __future__ import annotations

import copy
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("loader_prove", ROOT / "scripts/loader_netlist_prove.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def interface_fixture():
    nets, next_bit = {}, 1000
    for name, width in MODULE.RESPONSES.items():
        nets[f"system.m1${name}"] = {"bits": list(range(next_bit, next_bit + width))}
        next_bit += width
    bus = list(range(135))
    nets["system.m1$loadInstr_x_0"] = {"bits": bus}
    live = [b for b in bus if b not in MODULE.UNUSED_INSTRUCTION_BITS]
    return {"netnames": nets, "cells": {"consumer": {"port_directions": {"D": "input"},
                                                    "connections": {"D": live}}}}


def test_interface_accounts_for_every_instruction_bit():
    result = MODULE.interface_manifest(interface_fixture())
    assert len(result["compared_instruction_bits"]) == 132
    assert set(result["compared_instruction_bits"]) | set(result["unconnected_instruction_bits"]) == set(range(135))


def test_missing_live_instruction_bit_is_rejected():
    top = interface_fixture()
    top["cells"]["consumer"]["connections"]["D"].remove(7)
    with pytest.raises(ValueError, match="connectivity changed"):
        MODULE.interface_manifest(top)


def test_newly_connected_bit_requires_review():
    top = interface_fixture()
    top["cells"]["consumer"]["connections"]["D"].append(53)
    with pytest.raises(ValueError, match="connectivity changed"):
        MODULE.interface_manifest(top)


def test_error_code_aliases_are_recorded_without_merging_response_ports():
    top = interface_fixture()
    bits = top["netnames"]["system.m1$getErrorCode"]["bits"]
    bits[8] = bits[12]
    result = MODULE.interface_manifest(top)
    assert result["error_code_representatives"][8] == result["error_code_representatives"][12]
    top["netnames"]["system.m1$getErr"]["bits"] = [bits[8]]
    with pytest.raises(ValueError, match="share bits"):
        MODULE.interface_manifest(top)


@pytest.mark.parametrize("name", ["getPC", "getMu", "getErr", "RDY_loadInstr"])
def test_response_width_change_fails(name):
    top = interface_fixture()
    top["netnames"][f"system.m1${name}"]["bits"].append(9000)
    with pytest.raises(ValueError, match="response representation"):
        MODULE.interface_manifest(top)


@pytest.mark.parametrize("missing", ["prepare", "base", "step"])
def test_missing_proof_obligation_fails(missing):
    results = [{"name": name, "status": "PASS"} for name in ["prepare", "base", "step"] if name != missing]
    assert not MODULE.complete(results)


@pytest.mark.parametrize("status", ["FAIL", "TIMEOUT", "INCOMPLETE"])
def test_inconclusive_proof_fails(status):
    results = [{"name": name, "status": "PASS"} for name in ["prepare", "base", "step"]]
    results[-1]["status"] = status
    assert not MODULE.complete(results)


def test_duplicate_obligation_cannot_replace_base():
    assert not MODULE.complete([{"name": name, "status": "PASS"} for name in ["prepare", "step", "step"]])


def test_complete_campaign_requires_all_three_successes():
    assert MODULE.complete([{"name": name, "status": "PASS"} for name in ["prepare", "base", "step"]])


def test_solver_exit_zero_without_a_proof_is_failure(tmp_path, monkeypatch):
    def fake_solver(args, **kwargs):
        Path(args[args.index("-ql") + 1]).write_text("Found and reported 0 problems.\n")
        return type("Completed", (), {"returncode": 0})()

    monkeypatch.setattr(MODULE.subprocess, "run", fake_solver)
    assert MODULE.execute("yosys", tmp_path, "base", "sat\n", 1, True)["status"] == "FAIL"


def test_extra_unconstrained_port_fails_before_proof():
    data = {"modules": {name: {"ports": {"unexpected": {"direction": "input", "bits": [1]}}}
                        for name in ["gold", "gate"]}}
    interface = MODULE.interface_manifest(interface_fixture())
    with pytest.raises(ValueError, match="unexpected prepared input ports"):
        MODULE.add_observations(copy.deepcopy(data), interface)
