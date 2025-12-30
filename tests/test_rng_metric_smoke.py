from __future__ import annotations

from pathlib import Path
import os

from thielecpu.state import State
from thielecpu.vm import VM

from tools.finite_quantum import TSIRELSON_BOUND, chsh_from_trials, tsirelson_bound_trials
from tools.bell_receipts import ReceiptTrial, program_from_trials
from tools.rng_metric import rng_metric
from tools.rng_transcript import decode_rng_transcript


def test_rng_metric_matches_empirical_chsh(tmp_path: Path) -> None:
    """D2 smoke: metric CHSH matches the deterministic Tsirelson-envelope dataset."""

    if os.environ.get("THIELE_EXHAUSTIVE"):
        qm_trials = tsirelson_bound_trials(denom=4000)
        assert chsh_from_trials(qm_trials) == TSIRELSON_BOUND
    else:
        # Small approximate smoke dataset for fast unit runs.
        from tools.finite_quantum import QMTrial

        n = 20
        qm_trials: list[QMTrial] = []
        for (x, y) in [(0, 1), (1, 0), (1, 1)]:
            qm_trials.extend([QMTrial(x=x, y=y, a=0, b=0) for _ in range(n)])
        # (0,0) setting: approximate P_same to 2343/4000 ~ 0.58575
        same = round(0.58575 * n)
        diff = n - same
        qm_trials.extend([QMTrial(x=0, y=0, a=0, b=0) for _ in range(same)])
        qm_trials.extend([QMTrial(x=0, y=0, a=0, b=1) for _ in range(diff)])
        # Allow small numeric deviation for the smoke dataset
        assert abs(float(chsh_from_trials(qm_trials)) - float(TSIRELSON_BOUND)) < 0.06

    trials = [ReceiptTrial(x=t.x, y=t.y, a=t.a, b=t.b) for t in qm_trials]
    program = program_from_trials(trials)

    outdir = tmp_path / "rng_metric_tsirelson"
    outdir.mkdir(parents=True, exist_ok=True)

    vm = VM(State())
    vm.run(program, outdir)

    transcript = decode_rng_transcript(outdir / "step_receipts.json")
    metric = rng_metric(transcript)

    if os.environ.get("THIELE_EXHAUSTIVE"):
        assert metric.chsh == TSIRELSON_BOUND
    else:
        assert abs(float(metric.chsh) - float(TSIRELSON_BOUND)) < 0.06

    assert metric.n_per_setting > 0
    assert metric.hmin_lower_bound_bits >= 0.0
    assert metric.epsilon >= 0.0
