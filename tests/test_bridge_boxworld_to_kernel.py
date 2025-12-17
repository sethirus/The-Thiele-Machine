from __future__ import annotations

from pathlib import Path

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_receipts import ReceiptTrial, program_from_trials
from tools.chsh_receipts import decode_trials_from_receipts


def test_boxworld_to_kernel_embedding_falsifier_search_bounded(tmp_path: Path) -> None:
    """Bounded search for a counterexample to the box-world→kernel embedding.

    Property under test (operational semantics):
      Given a finite list of CHSH trials with bits, if we compile it into a VM
      program using the dedicated CHSH_TRIAL opcode, then decoding CHSH_TRIAL
      receipts yields exactly the same trial stream.

    This is a concrete falsifier: any single mismatch is a refutation.
    The search is bounded (all sequences of length 0..2 over the 16 bit-trials).
    """

    atoms = [ReceiptTrial(x=x, y=y, a=a, b=b) for x in (0, 1) for y in (0, 1) for a in (0, 1) for b in (0, 1)]

    # Enumerate all trial streams of length 0..2.
    cases: list[list[ReceiptTrial]] = [[]]
    cases.extend([[t1] for t1 in atoms])
    cases.extend([[t1, t2] for t1 in atoms for t2 in atoms])

    for idx, trials in enumerate(cases):
        outdir = tmp_path / f"case_{idx:04d}"
        outdir.mkdir(parents=True, exist_ok=True)

        program = program_from_trials(trials)

        # Always add a REVEAL so the run is "certification-compatible" even under
        # strict enforcement policies; this should not affect decoded CHSH_TRIALs.
        program.insert(1, ("REVEAL", "1 0 boxworld"))

        vm = VM(State())
        vm.run(program, outdir)

        receipts_path = outdir / "step_receipts.json"
        observed = decode_trials_from_receipts(receipts_path)

        expected = [(t.x, t.y, t.a, t.b) for t in trials]
        got = [(t.x, t.y, t.a, t.b) for t in observed]

        assert got == expected, {
            "idx": idx,
            "expected": expected,
            "got": got,
        }
