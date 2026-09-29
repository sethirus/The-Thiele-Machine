#!/usr/bin/env python3
"""Run a generated Print Assumptions probe in bounded, validated batches.

Every query is checked against the current source and compiled corpus. Publish
combined output only after every batch succeeds, contains one result per query,
and reports no Coq error. The existing
aggregator remains responsible for classifying the resulting assumptions.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coq_proof_scope import FULL_ASSUMPTION_PROBE
from assumption_receipt_fingerprint import corpus_digest, _coq_source_paths


def compiled_digest(root: Path) -> str:
    """Bind saved answers to the compiled libraries Coq actually loads."""
    hasher = hashlib.sha256()
    for source in _coq_source_paths(root):
        obj = source.with_suffix(".vo")
        if not obj.exists():
            continue  # Vendor sources outside the built dependency closure.
        hasher.update(obj.relative_to(root).as_posix().encode())
        hasher.update(b"\0")
        with obj.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                hasher.update(block)
    return hasher.hexdigest()


def bind_corpus(source: str, source_digest: str, objects_digest: str) -> str:
    return f"(* Receipt inputs: {source_digest} {objects_digest} *)\n" + source

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


def batch_prefix(prefix: str, queries: list[str]) -> str:
    """Load the libraries named by this batch; Coq loads their dependencies.

    The generator emits only plain Require commands. Any unfamiliar command
    or unmatched query keeps the entire prefix, so this optimization cannot
    silently discard an import context it does not understand.
    """
    clean = re.sub(r"\(\*.*?\*\)", "", prefix, flags=re.DOTALL)
    lines = [line.strip() for line in clean.splitlines() if line.strip()]
    modules = []
    for line in lines:
        match = re.fullmatch(r"Require ([\w.']+)\.", line)
        if match is None:
            return prefix
        modules.append(match.group(1))
    needed = set()
    for query in queries:
        match = re.fullmatch(r"Print Assumptions ([\w.']+)\.", query)
        if match is None:
            return prefix
        owners = [module for module in modules if match.group(1).startswith(module + ".")]
        if not owners:
            return prefix
        needed.add(max(owners, key=len))
    return "".join(f"Require {module}.\n" for module in modules if module in needed)


def validate_output(stdout: str, stderr: str, expected: int) -> str:
    if ERROR.search(stderr) or ERROR.search(stdout):
        raise ValueError("Coq reported an error while checking assumptions")
    blocks = list(BLOCK.finditer(stdout))
    if len(blocks) != expected:
        raise ValueError(f"Expected {expected} assumption results, received {len(blocks)}")
    return stdout[blocks[0].start():]


def batch_completion(source: str, stdout: str, stderr: str, expected: int) -> dict:
    return {
        "schema": "assumption-batch-completion.v1",
        "queries": expected,
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
        "stderr_sha256": hashlib.sha256(stderr.encode()).hexdigest(),
    }


def publish_completed_batch(directory: Path, lo: int, hi: int,
                            source: str, stdout: str, stderr: str) -> None:
    """Publish a validated batch, with the completion record written last."""
    validate_output(stdout, stderr, hi - lo)
    stem = directory / f"{lo + 1}-{hi}"
    marker = stem.with_suffix(".complete.json")
    marker.unlink(missing_ok=True)
    stem.with_suffix(".v").write_text(source)
    stem.with_suffix(".output.txt").write_text(stdout)
    stem.with_suffix(".errors.txt").write_text(stderr)
    pending = stem.with_suffix(".complete.pending")
    pending.write_text(json.dumps(batch_completion(source, stdout, stderr, hi - lo)))
    pending.replace(marker)


def load_saved_batch(directory: Path, lo: int, hi: int, source: str) -> tuple[int, str, str] | None:
    """Return a completed batch's result from a work directory, or None.

    A saved result is reused only when the batch ran exactly `source` and its
    output still validates with no Coq error. A result count alone cannot tell
    two probes apart, and a truncated write from an external kill can never be
    mistaken for a completed batch.
    """
    stem = directory / f"{lo + 1}-{hi}"
    out_file, err_file = stem.with_suffix(".output.txt"), stem.with_suffix(".errors.txt")
    source_file = stem.with_suffix(".v")
    try:
        marker = json.loads(stem.with_suffix(".complete.json").read_text())
        if source_file.read_text() != source:
            return None
        stdout = out_file.read_text()
        stderr = err_file.read_text()
        if marker != batch_completion(source, stdout, stderr, hi - lo):
            return None
        output = validate_output(stdout, stderr, hi - lo)
    except (OSError, ValueError):
        return None
    return lo, output, stderr


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    # Loading the complete compiled corpus dominates each coqtop invocation.
    # A 2,000-query batch keeps the process count small while retaining bounded
    # output and restartable work units.
    parser.add_argument("--batch-size", type=int, default=2000)
    parser.add_argument("--timeout", type=int, default=900)
    # A batch killed by an external signal (this sandbox SIGTERMs long-running
    # processes) is retried in place. This is deliberately narrow: it must never
    # turn a real Coq error into a pass. Only death-by-signal -- a negative
    # return code, which CPython reports as -N for signal N -- is retried, and a
    # batch that keeps dying is re-run rather than silently dropped. A non-zero
    # exit from Coq itself, or any Error:/Anomaly: in its output, still fails
    # the run immediately via validate_output.
    parser.add_argument("--retries", type=int, default=30,
                        help="retries per batch if the Coq process is killed by a signal")
    parser.add_argument("--work-dir", default=None,
                        help="reuse an existing batch directory, completing only "
                             "batches without a valid saved result (for resuming "
                             "a run interrupted by an external signal)")
    parser.add_argument("coq_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if min(args.jobs, args.batch_size, args.timeout) < 1:
        parser.error("jobs, batch-size, and timeout must be positive")
    if args.retries < 0:
        parser.error("retries must not be negative")
    coq_args = args.coq_args[1:] if args.coq_args[:1] == ["--"] else args.coq_args
    root = Path(__file__).resolve().parents[1]
    build = root / "build/probe"
    prefix, queries = split_probe((root / FULL_ASSUMPTION_PROBE).read_text())
    source_digest = corpus_digest(root)
    objects_digest = compiled_digest(root)
    reused_batches: list[tuple[int, int]] = []
    batches = [(lo, min(lo + args.batch_size, len(queries)))
               for lo in range(0, len(queries), args.batch_size)]
    if args.work_dir:
        directory = Path(args.work_dir)
        if not directory.is_absolute():
            directory = root / directory
        if not directory.is_dir():
            raise SystemExit(f"--work-dir is not a directory: {directory}")
    else:
        directory = Path(tempfile.mkdtemp(prefix="assumption-batches-", dir=build))

    def batch_source(lo: int, hi: int) -> str:
        imports = batch_prefix(prefix, queries[lo:hi])
        return bind_corpus(imports + "\n".join(queries[lo:hi]) + "\nQuit.\n",
                           source_digest, objects_digest)

    def saved(bounds: tuple[int, int]) -> tuple[int, str, str] | None:
        lo, hi = bounds
        return load_saved_batch(directory, lo, hi, batch_source(lo, hi))

    def once(bounds: tuple[int, int]) -> tuple[int, str, str]:
        lo, hi = bounds
        source = batch_source(lo, hi)
        stem = directory / f"{lo + 1}-{hi}"
        # Invalidate before changing any member of a previous saved batch.
        stem.with_suffix(".complete.json").unlink(missing_ok=True)
        stem.with_suffix(".v").write_text(source)
        result = subprocess.run(["coqtop", "-quiet", *coq_args], cwd=root / "coq",
                                input=source, text=True, capture_output=True,
                                timeout=args.timeout, check=False)
        stem.with_suffix(".output.txt").write_text(result.stdout)
        stem.with_suffix(".errors.txt").write_text(result.stderr)
        if result.returncode:
            raise RuntimeError(f"Coq exited {result.returncode} for queries {lo + 1}..{hi}: {stem}")
        output = validate_output(result.stdout, result.stderr, hi - lo)
        publish_completed_batch(directory, lo, hi, source, result.stdout, result.stderr)
        return lo, output, result.stderr

    def run(bounds: tuple[int, int]) -> tuple[int, str, str]:
        lo, hi = bounds
        if args.work_dir:
            resumed = saved(bounds)
            if resumed is not None:
                reused_batches.append(bounds)
                print(f"[assumption-batch] reused {lo + 1}..{hi}", flush=True)
                return resumed
        for attempt in range(args.retries + 1):
            try:
                out = once(bounds)
            except subprocess.TimeoutExpired:
                # A hung batch is a real problem, not external interference.
                raise
            except RuntimeError as error:
                message = str(error)
                killed = re.search(r"exited -(\d+)", message)
                if killed is None or attempt == args.retries:
                    raise
                print(f"[assumption-batch] queries {lo + 1}..{hi} killed by "
                      f"signal {killed.group(1)} (attempt {attempt + 1}), retrying",
                      flush=True)
                time.sleep(min(2 ** attempt, 30))
                continue
            print(f"[assumption-batch] checked {lo + 1}..{hi}", flush=True)
            return out
        raise RuntimeError(f"unreachable: queries {lo + 1}..{hi}")

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = sorted(pool.map(run, batches))
    if corpus_digest(root) != source_digest or compiled_digest(root) != objects_digest:
        raise RuntimeError("Proof inputs changed during the receipt run; no combined result published")
    combined = "".join(output for _, output, _ in results)
    errors = "".join(stderr for _, _, stderr in results)
    validate_output(combined, errors, len(queries))
    (build / "probe_all_output.txt").write_text(combined)
    (build / "probe_all_err.txt").write_text(errors)
    (build / "probe_batches.json").write_text(json.dumps({
        "queries": len(queries), "jobs": args.jobs, "batch_size": args.batch_size,
        "source_digest": source_digest, "compiled_digest": objects_digest,
        "all_queries_reexecuted": not reused_batches, "alignment_ok": True,
        "reused_batches": [{"first": lo + 1, "last": hi} for lo, hi in sorted(reused_batches)],
        "batch_directory": str(directory.relative_to(root)),
        "batches": [{"first": lo + 1, "last": hi} for lo, hi in batches],
    }, indent=2) + "\n")
    print(f"[assumption-batch] all {len(queries)} queries checked and combined in order", flush=True)


if __name__ == "__main__":
    main()
