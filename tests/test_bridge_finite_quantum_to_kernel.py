from __future__ import annotations

from pathlib import Path
from fractions import Fraction

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_receipts import ReceiptTrial, program_from_trials
from tools.chsh_receipts import decode_trials_from_receipts
from tools.finite_quantum import TSIRELSON_BOUND, chsh_from_trials, tsirelson_bound_trials


def test_finite_quantum_to_kernel_embedding_tsirelson_envelope(tmp_path: Path) -> None:
    """Receipt-defined finite-quantum bridge + bounded falsifier check.

    This test executes a deterministic finite trial stream whose empirical CHSH
    is exactly the VM's Tsirelson policy threshold (5657/2000).

    Property under test (operational semantics):
      compile(trials) -> run VM -> decode CHSH_TRIAL receipts == trials

    This is a falsifier: any mismatch refutes the embedding.
    """

    qm_trials = tsirelson_bound_trials(denom=4000)
    assert chsh_from_trials(qm_trials) == TSIRELSON_BOUND

    trials = [ReceiptTrial(x=t.x, y=t.y, a=t.a, b=t.b) for t in qm_trials]
    program = program_from_trials(trials)

    # Add a REVEAL to keep the run compatible with strict policies; this should
    # not affect the decoded CHSH_TRIAL receipt stream.
    program.insert(1, ("REVEAL", "1 0 finite-quantum"))

    outdir = tmp_path / "tsirelson_envelope"
    outdir.mkdir(parents=True, exist_ok=True)

    vm = VM(State())
    vm.run(program, outdir)

    receipts_path = outdir / "step_receipts.json"
    observed = decode_trials_from_receipts(receipts_path)

    expected = [(t.x, t.y, t.a, t.b) for t in trials]
    got = [(t.x, t.y, t.a, t.b) for t in observed]

    assert got == expected


def test_divergence_prediction_supra_requires_reveal(tmp_path: Path) -> None:
    """Operational divergence prediction: supra-CHSH requires revelation-class.

    Under the VM policy layer, supra-Tsirelson CHSH evidence (e.g. 16/5) without
    any REVEAL is rejected by setting ERR and halting.

    This test is intentionally operational (not probabilistic): it runs a short
    supra dataset and checks the VM logs an ERR halt when REVEAL is absent.
    """

    # Minimal supra-quantum witness stream (same as the Coq box-world example):
    # Important: the VM's Tsirelson enforcement runs when per-setting counts are
    # balanced and meet the minimum trials-per-setting threshold (currently 10).
    # Use n=10 per setting with E00=-1/5 to get S=16/5.
    trials: list[ReceiptTrial] = []
    trials.extend([ReceiptTrial(x=1, y=1, a=0, b=0)] * 10)
    trials.extend([ReceiptTrial(x=1, y=0, a=0, b=0)] * 10)
    trials.extend([ReceiptTrial(x=0, y=1, a=0, b=0)] * 10)

    # (0,0): two +1 and three -1 so E00=-1/5 -> S=16/5
    trials.extend([ReceiptTrial(x=0, y=0, a=0, b=0)] * 4)
    trials.extend([ReceiptTrial(x=0, y=0, a=0, b=1)] * 6)

    program = program_from_trials(trials)

    outdir = tmp_path / "supra_no_reveal"
    outdir.mkdir(parents=True, exist_ok=True)

    vm = VM(State())
    vm.run(program, outdir)

    trace_log = (outdir / "trace.log").read_text(encoding="utf-8")
    assert "ERR flag set - halting VM" in trace_log

    # Sanity: receipts still decode to the attempted trial stream (receipt channel
    # remains non-forgeable even when policy rejects the run).
    observed = decode_trials_from_receipts(outdir / "step_receipts.json")
    got = [(t.x, t.y, t.a, t.b) for t in observed]
    expected = [(t.x, t.y, t.a, t.b) for t in trials]
    assert got == expected

    # And the computed CHSH is indeed supra.
    # Lightweight exact computation from receipts (avoid extra helpers here).
    counts: dict[tuple[int, int, int, int], int] = {}
    per_setting = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for x, y, a, b in got:
        counts[(x, y, a, b)] = counts.get((x, y, a, b), 0) + 1
        per_setting[(x, y)] += 1
    assert len(set(per_setting.values())) == 1

    # Correlators
    def e_xy(x: int, y: int) -> Fraction:
        n = per_setting[(x, y)]
        same = counts.get((x, y, 0, 0), 0) + counts.get((x, y, 1, 1), 0)
        diff = counts.get((x, y, 0, 1), 0) + counts.get((x, y, 1, 0), 0)
        return Fraction(same - diff, n)

    s = e_xy(1, 1) + e_xy(1, 0) + e_xy(0, 1) - e_xy(0, 0)
    assert s > TSIRELSON_BOUND
