import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import pytest

from tools import make_self_model_v1_receipt
from tools import self_model_v1
from tools import verify_self_model_v1_receipt


def _write_trace(tmp_path: Path, workload: str, deltas: list[float], *, seed: int = 1) -> Path:
    """Create a minimal trace file for the given workload."""
    path = tmp_path / f"{workload}.jsonl"
    events = [
        {"event": "trace_start", "workload": workload, "metadata": {"seed": seed}},
    ]
    total = 0.0
    for step, delta in enumerate(deltas, start=1):
        total += delta
        events.append(
            {
                "event": "trace_step",
                "workload": workload,
                "step": step,
                "pc": step - 1,
                "op": "MDLACC",
                "mu": {
                    "mu_total": total,
                    "mu_operational": total,
                    "mu_information": 0.0,
                },
                "delta": {
                    "mu_total": delta,
                    "mu_operational": delta,
                    "mu_information": 0.0,
                },
            }
        )
    events.append({"event": "trace_end", "workload": workload, "steps": len(deltas)})
    payload = "\n".join(json.dumps(event) for event in events)
    path.write_text(payload, encoding="utf-8")
    return path


def _make_index(tmp_path: Path, traces: dict[str, list[float]]) -> Path:
    entries = []
    for idx, (workload, deltas) in enumerate(traces.items(), start=1):
        trace_path = _write_trace(tmp_path, workload, deltas, seed=idx)
        digest = hashlib.sha256(trace_path.read_bytes()).hexdigest()
        entries.append(
            {
                "workload": workload,
                "seed": idx,
                "path": str(trace_path),
                "sha256": digest,
                "steps": len(deltas),
            }
        )
    index_path = tmp_path / "index.json"
    index_path.write_text(json.dumps({"traces": entries}), encoding="utf-8")
    return index_path


def test_load_trace_index_missing(tmp_path: Path) -> None:
    missing = tmp_path / "missing.json"
    with pytest.raises(FileNotFoundError):
        self_model_v1.load_trace_index(missing)


def test_load_samples_empty_payload() -> None:
    with pytest.raises(ValueError):
        self_model_v1.load_samples({"traces": []})


def test_discover_self_model_summary(tmp_path: Path) -> None:
    index_path = _make_index(tmp_path, {"idle": [4.0, 4.0], "proof": [4.0, 4.0]})
    summary = self_model_v1.discover_self_model(
        index_path,
        blind_bits_per_step=8.0,
        epsilon_bits=0.0,
    )

    assert summary["coefficients"] == {"MDLACC": 4.0}
    assert summary["mu_question_bits"] == pytest.approx(16.0)
    assert summary["mu_answer_bits"] == pytest.approx(0.0)
    assert summary["mu_total_bits"] == pytest.approx(16.0)
    assert summary["blind_total_bits"] == pytest.approx(32.0)
    assert summary["mu_gap_bits"] == pytest.approx(16.0)

    workloads = summary["workloads"]
    assert set(workloads.keys()) == {"idle", "proof"}
    for metrics in workloads.values():
        assert metrics["mu_total_bits"] == pytest.approx(8.0)
        assert metrics["mu_gap_bits"] == pytest.approx(8.0)
        assert metrics["rmse"] == pytest.approx(0.0)


def test_receipt_round_trip(tmp_path: Path) -> None:
    index_path = _make_index(tmp_path, {"idle": [4.0, 4.0, 4.0]})
    receipt_path = tmp_path / "receipt.jsonl"
    summary_path = tmp_path / "summary.json"

    make_self_model_v1_receipt.main(
        [
            "--trace-index",
            str(index_path),
            "--output",
            str(receipt_path),
            "--summary",
            str(summary_path),
            "--blind-bits-per-step",
            "8.0",
            "--epsilon-bits",
            "0.0",
        ]
    )

    assert receipt_path.exists()
    assert summary_path.exists()

    verify_self_model_v1_receipt.main(
        [
            str(receipt_path),
            "--trace-index",
            str(index_path),
            "--blind-bits-per-step",
            "8.0",
            "--epsilon-bits",
            "0.0",
        ]
    )
