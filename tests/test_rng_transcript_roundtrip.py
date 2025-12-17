from __future__ import annotations

from pathlib import Path

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_receipts import ReceiptTrial, program_from_trials
from tools.rng_transcript import decode_rng_transcript


def test_rng_transcript_roundtrip_from_receipts(tmp_path: Path) -> None:
    """D1 falsifier: program -> receipts -> transcript trials must match."""

    trials = [
        ReceiptTrial(x=0, y=0, a=0, b=0),
        ReceiptTrial(x=0, y=1, a=0, b=0),
        ReceiptTrial(x=1, y=0, a=0, b=0),
        ReceiptTrial(x=1, y=1, a=0, b=0),
    ]

    program = program_from_trials(trials)

    outdir = tmp_path / "rng_roundtrip"
    outdir.mkdir(parents=True, exist_ok=True)

    vm = VM(State())
    vm.run(program, outdir)

    transcript = decode_rng_transcript(outdir / "step_receipts.json")
    got = [(t.x, t.y, t.a, t.b) for t in transcript.trials]
    expected = [(t.x, t.y, t.a, t.b) for t in trials]

    assert got == expected
