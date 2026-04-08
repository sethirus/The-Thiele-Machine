from __future__ import annotations

from pathlib import Path

import pytest

from thielecpu.vm import (
    CSRState,
    CouplingData,
    MorphismState,
    VMState,
    _runner_available,
    moduleState,
    partitionGraph,
    vm_run,
)


ROOT = Path(__file__).resolve().parents[1]


def _rich_state() -> VMState:
    regs = [0] * 32
    regs[1] = 17
    regs[2] = 99

    mem = [0] * 65536
    mem[3] = 1234
    mem[19] = 5678

    return VMState(
        vm_pc=7,
        vm_mu=42,
        vm_err=False,
        vm_regs=regs,
        vm_mem=mem,
        vm_csrs=CSRState(
            csr_cert_addr=77,
            csr_status=5,
            csr_err=9,
            csr_heap_base=1024,
        ),
        vm_graph=partitionGraph(
            pg_next_id=3,
            pg_modules=[
                (
                    0,
                    moduleState(
                        module_region=[0, 1, 2],
                        module_axioms=["axiom_alpha", "axiom_beta"],
                        module_mu_tensor=[1, 2, 3, 4] + [0] * 12,
                    ),
                ),
                (
                    1,
                    moduleState(
                        module_region=[3, 4],
                        module_axioms=["axiom_gamma"],
                        module_mu_tensor=[5, 6, 7, 8] + [0] * 12,
                    ),
                ),
            ],
            pg_next_morph_id=4,
            pg_morphisms=[
                (
                    2,
                    MorphismState(
                        morph_source=0,
                        morph_target=1,
                        morph_coupling=CouplingData(
                            coupling_pairs=[(0, 3), (1, 4)],
                            coupling_label="edge_label",
                        ),
                        morph_is_identity=False,
                    ),
                )
            ],
        ),
        vm_mu_tensor=[9, 10, 11, 12] + [0] * 12,
        vm_logic_acc=314,
        vm_mstatus=2718,
        vm_witness=[1, 2, 3, 4, 5, 6, 7, 8],
        vm_certified=True,
    )


def test_generated_python_runtime_surface_covers_full_vm_state() -> None:
    state = _rich_state()
    payload = state.to_json_dict()

    assert set(payload) == {
        "pc",
        "mu",
        "err",
        "csr_err_code",
        "regs",
        "mem",
        "mu_tensor",
        "logic_acc",
        "mstatus",
        "certified",
        "witness",
        "csrs",
        "graph",
    }
    assert set(payload["csrs"]) == {"cert_addr", "status", "err", "heap_base"}
    assert set(payload["graph"]) == {"next_id", "modules", "next_morph_id", "morphisms"}

    module_payload = payload["graph"]["modules"][0]
    assert set(module_payload) == {"id", "region", "axioms", "axiom_strings", "mu_tensor"}

    morph_payload = payload["graph"]["morphisms"][0]
    assert set(morph_payload) == {"id", "source", "target", "is_identity", "coupling"}
    assert set(morph_payload["coupling"]) == {"label", "pairs"}


def test_vmstate_json_roundtrip_preserves_full_state_surface() -> None:
    state = _rich_state()
    rebuilt = VMState.from_json(state.to_json())
    assert rebuilt == state


@pytest.mark.strict_extracted
@pytest.mark.skipif(not _runner_available(), reason="OCaml runner not available")
def test_extracted_runner_zero_fuel_preserves_full_state_surface() -> None:
    state = _rich_state()
    result = vm_run(state, [], max_steps=0)
    assert result == state


def test_coq_full_state_bridge_theorems_are_present() -> None:
    text = (ROOT / "coq" / "kernel" / "PythonBisimulation.v").read_text(encoding="utf-8")

    assert "Record PythonStateFull :=" in text
    assert "Definition python_full_abs" in text
    assert "Definition python_full_repr" in text
    assert "Theorem python_step_full_refines" in text
    assert "Theorem python_run_full_refines" in text
