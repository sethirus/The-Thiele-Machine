from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
import os

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_receipts import ReceiptTrial
from tools.chsh_receipts import decode_trials_from_receipts
from tools.finite_quantum import TSIRELSON_BOUND, chsh_from_trials, tsirelson_bound_trials


def _run(program: list[tuple[str, str]], outdir: Path) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    vm = VM(State())
    vm.run(program, outdir)
    return json.loads((outdir / "summary.json").read_text(encoding="utf-8"))


def test_divergence_certification_costs_mu_but_not_chsh(tmp_path: Path) -> None:
    """Divergence asset (operational): certification costs μ.

    Protocol:
    - Fix a Tsirelson-envelope finite dataset (CHSH = 5657/2000).
    - Run it twice:
            (A) *no certification*: no REVEAL/LJOIN/LASSERT (so CERT_ADDR stays empty)
            (B) *certification*: add a single REVEAL (sets CERT_ADDR)

    Scoreboard:
    - The receipt-defined CHSH evidence is identical across (A) and (B).
    - The μ ledger differs: (B) must pay extra μ for a cert-setting step.

    QM expectation (informal): CHSH evidence is about correlations, not about
    paying a conserved "certification μ". This system predicts an additional
    conserved-cost boundary for *verifiable/certified* claims.
    """

    denom = 4000 if os.environ.get("THIELE_EXHAUSTIVE") else 400
    if os.environ.get("THIELE_EXHAUSTIVE"):
        qm_trials = tsirelson_bound_trials(denom=denom)
        assert chsh_from_trials(qm_trials) == TSIRELSON_BOUND
    else:
        from tools.finite_quantum import QMTrial

        n = 20
        qm_trials = []
        for (x, y) in [(0, 1), (1, 0), (1, 1)]:
            qm_trials.extend([QMTrial(x=x, y=y, a=0, b=0) for _ in range(n)])
        same = round(0.58575 * n)
        diff = n - same
        qm_trials.extend([QMTrial(x=0, y=0, a=0, b=0) for _ in range(same)])
        qm_trials.extend([QMTrial(x=0, y=0, a=0, b=1) for _ in range(diff)])
        assert abs(float(chsh_from_trials(qm_trials)) - float(TSIRELSON_BOUND)) < 0.06

    trials = [ReceiptTrial(x=t.x, y=t.y, a=t.a, b=t.b) for t in qm_trials]

    # Program A: no certification step.
    program_no_cert: list[tuple[str, str]] = [("PNEW", "{1,2}")]
    for t in trials:
        program_no_cert.append(("CHSH_TRIAL", f"{t.x} {t.y} {t.a} {t.b}"))

    # Program B: add a certification-setting instruction (REVEAL).
    program_cert = list(program_no_cert)
    # REVEAL explicitly sets CERT_ADDR and (optionally) charges μ-information.
    # Use bits=1 so the μ ledger differs even though the CHSH_TRIAL stream is identical.
    program_cert.append(("REVEAL", "1 1 tsirelson-envelope"))

    out_no_cert = tmp_path / "no_cert"
    out_cert = tmp_path / "cert"

    s_no = _run(program_no_cert, out_no_cert)
    s_yes = _run(program_cert, out_cert)

    assert str(s_no["cert"]) == ""
    assert str(s_yes["cert"]) != ""

    mu_no = float(s_no["mu_total"])
    mu_yes = float(s_yes["mu_total"])
    assert mu_yes > mu_no

    # Receipt-defined CHSH evidence is identical (same CHSH_TRIAL stream).
    obs_no = decode_trials_from_receipts(out_no_cert / "step_receipts.json")
    obs_yes = decode_trials_from_receipts(out_cert / "step_receipts.json")

    got_no = [(t.x, t.y, t.a, t.b) for t in obs_no]
    got_yes = [(t.x, t.y, t.a, t.b) for t in obs_yes]
    assert got_no == got_yes

    # And the CHSH value from the decoded stream matches the Tsirelson bound.
    counts: dict[tuple[int, int, int, int], int] = {}
    per_setting = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for x, y, a, b in got_no:
        counts[(x, y, a, b)] = counts.get((x, y, a, b), 0) + 1
        per_setting[(x, y)] += 1

    def e_xy(x: int, y: int) -> Fraction:
        n = per_setting[(x, y)]
        same = counts.get((x, y, 0, 0), 0) + counts.get((x, y, 1, 1), 0)
        diff = counts.get((x, y, 0, 1), 0) + counts.get((x, y, 1, 0), 0)
        return Fraction(same - diff, n)

    s_val = e_xy(1, 1) + e_xy(1, 0) + e_xy(0, 1) - e_xy(0, 0)
    if os.environ.get("THIELE_EXHAUSTIVE"):
        assert s_val == TSIRELSON_BOUND
    else:
        assert abs(float(s_val) - float(TSIRELSON_BOUND)) < 0.06
    assert s_val <= TSIRELSON_BOUND
