#!/usr/bin/env python3
"""Run a generated Print Assumptions probe in bounded, validated batches.

All queries are re-executed. Publish combined output only after every batch
succeeds, contains one result per query, and reports no Coq error. The existing
aggregator remains responsible for classifying the resulting assumptions.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import re
import subprocess
import tempfile
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coq_proof_scope import FULL_ASSUMPTION_PROBE

BLOCK = re.compile(r"^(?:Closed under the global context|Axioms:)$", re.MULTILINE)
ERROR = re.compile(r"^\s*(?:Error:|Anomaly:|Fatal error:)", re.MULTILINE)


def split_probe(source: str) -> tuple[str, list[str]]:
    match = re.search(r"^Print Assumptions ", source, re.MULTILINE)
    if match is None:
        raise ValueError("No assumption queries found")
    first = match.start()
    prefix, body = source[:first], source[first:]
    body = re.sub(r"\(\*.*?\*\)", "", body, flags=re.DOTALL)
    queries = [line.strip() for line in body.splitlines() if line.strip()]
    if not queries or any(not re.fullmatch(r"Print Assumptions [\w.']+\.", q) for q in queries):
        raise ValueError("Unexpected command in generated assumption-query section")
    return prefix, queries


def validate_output(stdout: str, stderr: str, expected: int) -> str:
    if ERROR.search(stderr) or ERROR.search(stdout):
        raise ValueError("Coq reported an error while checking assumptions")
    blocks = list(BLOCK.finditer(stdout))
    if len(blocks) != expected:
        raise ValueError(f"Expected {expected} assumption results, received {len(blocks)}")
    return stdout[blocks[0].start():]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--batch-size", type=int, default=50)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("coq_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if min(args.jobs, args.batch_size, args.timeout) < 1:
        parser.error("jobs, batch-size, and timeout must be positive")
    coq_args = args.coq_args[1:] if args.coq_args[:1] == ["--"] else args.coq_args
    root = Path(__file__).resolve().parents[1]
    build = root / "build/probe"
    prefix, queries = split_probe((root / FULL_ASSUMPTION_PROBE).read_text())
    batches = [(lo, min(lo + args.batch_size, len(queries)))
               for lo in range(0, len(queries), args.batch_size)]
    directory = Path(tempfile.mkdtemp(prefix="assumption-batches-", dir=build))

    def run(bounds: tuple[int, int]) -> tuple[int, str, str]:
        lo, hi = bounds
        source = prefix + "\n".join(queries[lo:hi]) + "\nQuit.\n"
        stem = directory / f"{lo + 1}-{hi}"
        stem.with_suffix(".v").write_text(source)
        result = subprocess.run(["coqtop", "-quiet", *coq_args], cwd=root / "coq",
                                input=source, text=True, capture_output=True,
                                timeout=args.timeout, check=False)
        stem.with_suffix(".output.txt").write_text(result.stdout)
        stem.with_suffix(".errors.txt").write_text(result.stderr)
        if result.returncode:
            raise RuntimeError(f"Coq exited {result.returncode} for queries {lo + 1}..{hi}: {stem}")
        output = validate_output(result.stdout, result.stderr, hi - lo)
        print(f"[assumption-batch] checked {lo + 1}..{hi}", flush=True)
        return lo, output, result.stderr

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = sorted(pool.map(run, batches))
    combined = "".join(output for _, output, _ in results)
    errors = "".join(stderr for _, _, stderr in results)
    validate_output(combined, errors, len(queries))
    (build / "probe_all_output.txt").write_text(combined)
    (build / "probe_all_err.txt").write_text(errors)
    (build / "probe_batches.json").write_text(json.dumps({
        "queries": len(queries), "jobs": args.jobs, "batch_size": args.batch_size,
        "all_queries_reexecuted": True, "alignment_ok": True,
        "batch_directory": str(directory.relative_to(root)),
        "batches": [{"first": lo + 1, "last": hi} for lo, hi in batches],
    }, indent=2) + "\n")
    print(f"[assumption-batch] all {len(queries)} queries checked and combined in order", flush=True)


if __name__ == "__main__":
    main()
