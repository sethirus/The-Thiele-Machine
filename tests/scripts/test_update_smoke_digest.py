import json
from pathlib import Path

from scripts.update_smoke_digest import update_results

TEMPLATE = """# Results

## Proofpack smoke manifest digest

| Run tag | manifest_digest_sha256 | Updated |
| --- | --- | --- |
| _pending_ | _populate from CI summary_ | _pending_ |

"""


def test_update_replaces_placeholder(tmp_path: Path) -> None:
    results_path = tmp_path / "RESULTS.md"
    results_path.write_text(TEMPLATE, encoding="utf-8")

    history_path = tmp_path / "history.json"
    update_results(
        results_path,
        "ci-20240101",
        "deadbeef",
        "2025-01-01T00:00:00Z",
        history_path=history_path,
    )

    lines = results_path.read_text(encoding="utf-8").splitlines()
    assert "| ci-20240101 | deadbeef | 2025-01-01T00:00:00Z |" in lines
    assert any(line.startswith("**Digest history:** runs=1") for line in lines)
    history = json.loads(history_path.read_text(encoding="utf-8"))
    assert history == [
        {
            "manifest_digest_sha256": "deadbeef",
            "run_tag": "ci-20240101",
            "updated": "2025-01-01T00:00:00Z",
        }
    ]


def test_update_appends_row(tmp_path: Path) -> None:
    results_path = tmp_path / "RESULTS.md"
    results_path.write_text(TEMPLATE.replace("_pending_", "ci-old", 1), encoding="utf-8")

    history_path = tmp_path / "history.json"
    history_path.write_text(
        json.dumps(
            [
                {
                    "run_tag": "ci-old",
                    "manifest_digest_sha256": "feedbead",
                    "updated": "2025-01-01T00:00:00Z",
                }
            ],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    update_results(
        results_path,
        "ci-new",
        "beadfeed",
        "2025-01-02T00:00:00Z",
        history_path=history_path,
    )

    lines = results_path.read_text(encoding="utf-8").splitlines()
    assert "| ci-new | beadfeed | 2025-01-02T00:00:00Z |" in lines
    assert "ci-old" in "\n".join(lines)
    assert any("runs=2" in line and "unique_digests=2" in line for line in lines)
    history = json.loads(history_path.read_text(encoding="utf-8"))
    assert history[-1]["run_tag"] == "ci-new"
    assert history[-1]["manifest_digest_sha256"] == "beadfeed"
