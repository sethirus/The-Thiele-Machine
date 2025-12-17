from __future__ import annotations

from pathlib import Path

from thielecpu.state import State
from thielecpu.vm import VM

from tools.finite_quantum import TSIRELSON_BOUND, chsh_from_trials, tsirelson_bound_trials
from tools.bell_receipts import ReceiptTrial, program_from_trials
from tools.rng_metric import rng_metric
from tools.rng_transcript import decode_rng_transcript


def test_rng_metric_matches_empirical_chsh(tmp_path: Path) -> None:
    """D2 smoke: metric CHSH matches the deterministic Tsirelson-envelope dataset."""

    qm_trials = tsirelson_bound_trials(denom=4000)
    assert chsh_from_trials(qm_trials) == TSIRELSON_BOUND

    trials = [ReceiptTrial(x=t.x, y=t.y, a=t.a, b=t.b) for t in qm_trials]
    program = program_from_trials(trials)

    outdir = tmp_path / "rng_metric_tsirelson"
    outdir.mkdir(parents=True, exist_ok=True)

    vm = VM(State())
    vm.run(program, outdir)

    transcript = decode_rng_transcript(outdir / "step_receipts.json")
    metric = rng_metric(transcript)

    assert metric.chsh == TSIRELSON_BOUND
    assert metric.n_per_setting > 0
    assert metric.hmin_lower_bound_bits >= 0.0
    assert metric.epsilon >= 0.0
