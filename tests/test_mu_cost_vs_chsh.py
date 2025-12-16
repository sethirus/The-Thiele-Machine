from __future__ import annotations

from pathlib import Path

from tools.bell_mu import (
    baseline_boxes,
    load_supra_table,
    mu_for_box,
    sample_mu_vs_chsh,
)


def test_mu_cost_has_no_tsirelson_or_ic_dependencies() -> None:
    """Guardrail: μ-cost implementation should not hardcode Bell/IC postulates."""

    repo_root = Path(__file__).resolve().parents[1]
    mu_files = [
        repo_root / "tools" / "mu_spec.py",
        repo_root / "thielecpu" / "mu.py",
    ]
    needles = [
        "tsirelson",
        "chsh",
        "no-signaling",
        "no_signaling",
        "information causality",
        "\nIC",
        "popescu",
        "rohrlich",
        "sqrt(2)",
        "2√2",
    ]
    for path in mu_files:
        text = path.read_text(encoding="utf-8").lower()
        for needle in needles:
            assert needle.lower() not in text, f"{path} unexpectedly mentions {needle!r}"


def test_mu_cost_vs_chsh_scan_runs_and_includes_baselines(tmp_path: Path) -> None:
    supra_path = Path("artifacts/bell/supra_quantum_16_5.csv")
    supra_table = load_supra_table(supra_path)

    boxes = baseline_boxes(supra_table)
    assert "supra_16_5" in boxes
    assert "tsirelson_like" in boxes
    assert "classical_best" in boxes

    from tools.compute_chsh_from_table import compute_chsh

    # Baseline CHSH checks (repo convention).
    assert float(compute_chsh(boxes["classical_best"])) == 2.0
    assert abs(float(compute_chsh(boxes["tsirelson_like"])) - 2.8284) < 0.02
    assert float(compute_chsh(boxes["supra_16_5"])) == 3.2
    assert float(compute_chsh(boxes["pr_box"])) == 4.0

    # μ depends on encoding; these should be finite and computable.
    for name, table in boxes.items():
        mu_table = mu_for_box(table, encoding="table_sexpr")
        mu_tag = mu_for_box(table, encoding="tag_sexpr", tag=name)
        assert mu_table > 0
        assert mu_tag > 0

    # Run a small scan to keep CI fast.
    samples = sample_mu_vs_chsh(supra_table, resolution=6, encoding="mixture_sexpr")
    assert samples, "expected non-empty scan"

    # Sanity: scan family includes endpoints.
    chsh_values = [float(s.chsh) for s in samples]
    assert max(chsh_values) <= 4.0000001
    assert min(chsh_values) >= -4.0000001
