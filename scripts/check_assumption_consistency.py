#!/usr/bin/env python3
"""Fast local consistency check for the Print Assumptions receipt.

The full receipt is re-derived in CI (``make assumption-receipt-check``), which
has the CPU budget and no process reaper. Re-running all ~12k ``Print
Assumptions`` queries inside the pre-commit hook is impractical: the work is
CPU-bound over 421 modules (2-core sandbox -> hours) and this environment
SIGTERMs long-running detached processes, so the hook never finished.

This check keeps the hook honest without re-deriving the receipt. It verifies
that the committed receipt is *internally consistent* and *covers exactly the
committed probe*, so a stale or partial receipt cannot be committed silently:

  1. the receipt names the committed probe and raw-output files;
  2. the raw output's sha256 matches the hash the receipt records;
  3. the parsed block count, addressable count and summary agree;
  4. alignment succeeded with no unexpected output lines;
  5. the probe's query count equals the receipt's theorem count, and the
     queries are unique (this is the probe/receipt coverage link).

It does NOT verify theorem/axiom *results* -- that is CI's job. A pass here
means "this receipt is a coherent snapshot of this probe", not "the proofs
have not drifted".
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coq_proof_scope import FULL_ASSUMPTION_PROBE  # noqa: E402
from run_assumption_batches import split_probe  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = "artifacts/print_assumptions_all_proofs.json"


def fail(message: str) -> None:
    print(f"[assumption-consistency] FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    receipt_path = ROOT / RECEIPT
    probe_path = ROOT / FULL_ASSUMPTION_PROBE

    if not receipt_path.exists():
        fail(f"missing receipt: {RECEIPT}")
    if not probe_path.exists():
        fail(f"missing probe: {FULL_ASSUMPTION_PROBE}")

    receipt = json.loads(receipt_path.read_text())

    # 1. declared file names
    if receipt.get("probe_file") != FULL_ASSUMPTION_PROBE:
        fail(f"receipt names probe {receipt.get('probe_file')!r}, "
             f"expected {FULL_ASSUMPTION_PROBE!r}")

    raw_rel = receipt.get("raw_output_file")
    if not raw_rel:
        fail("receipt does not name a raw_output_file")
    raw_path = ROOT / raw_rel
    if not raw_path.exists():
        fail(f"receipt names raw output {raw_rel!r} which does not exist")

    # 2. raw output hash
    actual = hashlib.sha256(raw_path.read_bytes()).hexdigest()
    declared = receipt.get("raw_output_sha256")
    if actual != declared:
        fail(f"raw output hash mismatch for {raw_rel}: "
             f"receipt says {declared}, file is {actual}")

    # 3. internal counts agree
    theorems = receipt.get("addressable_theorems_probed")
    blocks = receipt.get("blocks_parsed")
    summary_count = (receipt.get("summary") or {}).get("theorems_probed")
    if not (theorems == blocks == summary_count):
        fail("receipt counts disagree: "
             f"addressable_theorems_probed={theorems}, "
             f"blocks_parsed={blocks}, "
             f"summary.theorems_probed={summary_count}")
    if not isinstance(theorems, int) or theorems <= 0:
        fail(f"receipt reports a non-positive theorem count: {theorems!r}")

    # 4. alignment
    if not receipt.get("alignment_ok"):
        fail("receipt reports alignment_ok=false")
    unexpected = receipt.get("unexpected_lines_in_output")
    if unexpected != 0:
        fail(f"receipt reports {unexpected} unexpected output lines")

    # 5. probe/receipt coverage
    _, queries = split_probe(probe_path.read_text())
    if len(set(queries)) != len(queries):
        fail("probe contains duplicate assumption queries")
    if len(queries) != theorems:
        fail(f"probe/receipt coverage mismatch: the probe asks {len(queries)} "
             f"queries but the receipt covers {theorems} theorems. "
             "The probe changed since the receipt was generated -- "
             "regenerate it with `make assumption-receipt` (CI re-derives and "
             "diffs it, so a stale receipt will fail there).")

    print(f"[assumption-consistency] receipt is a coherent snapshot of "
          f"{len(queries)} queries over {receipt.get('files_probed')} files "
          f"(hash {actual[:12]}...). "
          "Theorem/axiom results are re-derived in CI.")


if __name__ == "__main__":
    main()