"""Keep the README's headline demo from rotting.

examples/demo_knowledge_receipt.py is the first thing the README links under
"See it in code", so it's the first code a stranger runs. It drives the live
VM through the Coq-extracted OCaml runner across four acts and checks every
act with `assert`. Nothing else in the suite touched it, which is exactly how
it drifted out of sync with the VM's data model (graph.pg_modules) and the
morphism-id convention (1-based, like module ids) while CI never said a word.
That bit me once. Now this test pins it.

It runs the demo end-to-end as a subprocess and wants exit 0 plus every act's
headline receipt in the output. Marked `strict_extracted`: it skips when
build/extracted_vm_runner is absent (the demo has no semantic fallback) and
runs unconditionally in CI, where the runner is built.
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
DEMO = REPO_ROOT / "examples" / "demo_knowledge_receipt.py"


@pytest.mark.strict_extracted
def test_demo_knowledge_receipt_runs_all_four_acts():
    assert DEMO.exists(), f"demo missing: {DEMO}"

    env = dict(os.environ, PYTHONPATH=str(REPO_ROOT))
    proc = subprocess.run(
        [sys.executable, str(DEMO)],
        cwd=str(REPO_ROOT),
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, (
        f"demo exited {proc.returncode}\n"
        f"--- stdout (tail) ---\n{proc.stdout[-3000:]}\n"
        f"--- stderr (tail) ---\n{proc.stderr[-3000:]}"
    )

    out = proc.stdout
    # Each act, and the load-bearing receipts the acts assert on. These pin
    # the exact mu values the demo's own asserts check, so a regression in the
    # VM's cost ledger surfaces here even if the demo's asserts were loosened.
    for needle in (
        "ACT 1",
        "ACT 2",
        "ACT 3",
        "ACT 4",
        "REFUSED",       # Act 1: forged claim refused
        "mu=8",          # Act 2: earned path
        "mu=13",         # Act 3: certified claim (8 + S(4)=5)
        "SEPARATED",     # Act 4: categorical separation
    ):
        assert needle in out, f"expected {needle!r} in demo output but it was absent"
