from __future__ import annotations

from pathlib import Path

from experiments.red_team import scramble_entropy, structure_ablation, worst_order_schedule
from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_entropy import main as entropy_main
from verifier.check_cross_domain import verify_cross_domain
from verifier.check_cwd import verify_cwd
from verifier.check_entropy import verify_entropy


def _prepare_cross_domain(tmp_path: Path) -> Path:
    out_dir = tmp_path / "cross" / "sighted"
    cross_domain_main(
        [
            "--output-dir",
            str(out_dir),
            "--protocol",
            "sighted",
            "--seeds",
            "0",
            "--trials-per-condition",
            "2",
            "--modules",
            "4",
        ]
    )
    return out_dir


def _prepare_entropy(tmp_path: Path) -> Path:
    out_dir = tmp_path / "entropy"
    entropy_main(
        [
            "--output-dir",
            str(out_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "16",
        ]
    )
    return out_dir


def _prepare_cwd(tmp_path: Path) -> tuple[Path, Path, Path]:
    root = tmp_path / "cwd"
    sighted = root / "sighted"
    blind = root / "blind"
    destroyed = root / "destroyed"
    for protocol in ("sighted", "blind", "destroyed"):
        cwd_main(
            [
                "--output-dir",
                str(root / protocol),
                "--protocol",
                protocol,
                "--seeds",
                "2",
                "--temps",
                "0.9",
                "--trials-per-condition",
                "1",
                "--modules",
                "3",
                "--steps-per-module",
                "4",
            ]
        )
    return sighted, blind, destroyed


def test_structure_ablation_fails_verifier(tmp_path: Path) -> None:
    source = _prepare_cross_domain(tmp_path)
    attacked = tmp_path / "cross_attacked"
    structure_ablation(source, attacked)
    _, payload = verify_cross_domain(attacked, delta_aic_threshold=10.0)
    assert payload["status"] is False
    assert any(not trial["sighted_flatness"] for trial in payload["trials"])


def test_entropy_scramble_breaks_identity(tmp_path: Path) -> None:
    source = _prepare_entropy(tmp_path)
    attacked = tmp_path / "entropy_attacked"
    scramble_entropy(source, attacked)
    _, payload = verify_entropy(attacked)
    assert payload["status"] is False
    assert any(not trial["intercept_close"] for trial in payload["trials"])


def test_worst_order_schedule_breaks_penalty(tmp_path: Path) -> None:
    sighted, blind, destroyed = _prepare_cwd(tmp_path)
    attacked_blind = tmp_path / "cwd_blind_attacked"
    worst_order_schedule(blind, attacked_blind)
    _, payload = verify_cwd(sighted, attacked_blind, destroyed, epsilon=0.05, eta=0.05)
    assert payload["status"] is False
    assert any(not check["penalty_bound_holds"] for check in payload["penalty_checks"])

