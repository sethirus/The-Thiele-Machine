from __future__ import annotations

import pytest

import build.thiele_vm as thiele_vm


def test_run_vm_trace_uses_extracted_runner_when_present(monkeypatch: pytest.MonkeyPatch) -> None:
    called: dict[str, object] = {}

    def _fake_run_extracted(instructions: list[str], fuel: int):
        called["instructions"] = instructions
        called["fuel"] = fuel
        return thiele_vm.VMState(pc=1, mu=2)

    monkeypatch.setattr(thiele_vm, "_run_extracted", _fake_run_extracted)
    monkeypatch.setattr(thiele_vm, "_run_python", lambda instructions, fuel: thiele_vm.VMState(pc=9, mu=9))
    monkeypatch.setattr(thiele_vm, "_runner_available", lambda: True)

    out = thiele_vm.run_vm_trace(["HALT 0"], fuel=7)
    assert out.pc == 1
    assert out.mu == 2
    assert called["instructions"] == ["HALT 0"]
    assert called["fuel"] == 7


def test_run_vm_trace_falls_back_only_when_not_strict(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(thiele_vm, "_runner_available", lambda: False)
    monkeypatch.setattr(thiele_vm, "_strict_backend_required", lambda: False)
    monkeypatch.setattr(thiele_vm, "_run_python", lambda instructions, fuel: thiele_vm.VMState(pc=3, mu=4))

    out = thiele_vm.run_vm_trace(["PNEW {1} 1", "HALT 0"], fuel=5)
    assert out.pc == 3
    assert out.mu == 4


def test_run_vm_trace_raises_when_strict_and_extracted_missing(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(thiele_vm, "_runner_available", lambda: False)
    monkeypatch.setattr(thiele_vm, "_strict_backend_required", lambda: True)

    with pytest.raises(RuntimeError, match="strict backend policy"):
        thiele_vm.run_vm_trace(["HALT 0"], fuel=1)
