#!/usr/bin/env python3
"""Run a generated Print Assumptions probe module by module, with a cache.

The probe lists every query grouped by the library that defines it. A
compiled Coq library records the digests of every library it depends on, so
the digest of its own .vo file stands for its whole dependency closure. Each
library's answers are cached under a key made of that digest, the exact
queries, the Coq version, and the load-path flags. A later run reuses every
answer whose key still matches and reruns only the rest. Libraries that do
run are checked several to a coqtop session, up to the batch size, so shared
dependencies load once; each library's answers are cut back out by count.

Queries whose library cannot be resolved to exactly one compiled file run
with the full probe prefix and are never cached. Combined output is
published only after every group succeeds, returns one result per query, and
reports no Coq error. The aggregator still classifies the assumptions.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coq_proof_scope import FULL_ASSUMPTION_PROBE
from assumption_receipt_fingerprint import corpus_digest, _coq_source_paths

CACHE_SCHEMA = "assumption-module-cache.v1"
BLOCK = re.compile(r"^(?:Closed under the global context|Axioms:)$", re.MULTILINE)
ERROR = re.compile(r"^\s*(?:Error:|Anomaly:|Fatal error:)", re.MULTILINE)
QUERY = re.compile(r"Print Assumptions ([\w.']+)\.")


def compiled_digest(root: Path) -> str:
    """Digest of every compiled library in the corpus, recorded for reference."""
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


def split_probe(source: str) -> tuple[str, list[str]]:
    match = re.search(r"^Print Assumptions ", source, re.MULTILINE)
    if match is None:
        raise ValueError("No assumption queries found")
    first = match.start()
    prefix, body = source[:first], source[first:]
    body = re.sub(r"\(\*.*?\*\)", "", body, flags=re.DOTALL)
    queries = [line.strip() for line in body.splitlines() if line.strip()]
    if not queries or any(not QUERY.fullmatch(q) for q in queries):
        raise ValueError("Unexpected command in generated assumption-query section")
    return prefix, queries


def probe_modules(prefix: str) -> list[str] | None:
    """The libraries the probe requires, or None if the prefix holds anything else."""
    clean = re.sub(r"\(\*.*?\*\)", "", prefix, flags=re.DOTALL)
    modules = []
    for line in (line.strip() for line in clean.splitlines()):
        if not line:
            continue
        match = re.fullmatch(r"Require ([\w.']+)\.", line)
        if match is None:
            return None
        modules.append(match.group(1))
    return modules


def owner(modules: list[str], query: str) -> str | None:
    match = QUERY.fullmatch(query)
    if match is None:
        return None
    owners = [module for module in modules if match.group(1).startswith(module + ".")]
    return max(owners, key=len) if owners else None


def group_queries(prefix: str, queries: list[str]) -> list[tuple[str | None, list[str]]]:
    """Consecutive runs of queries with the same owning library, in probe order.

    A query with no owning library, or any query at all when the prefix holds
    a command other than a plain Require, gets owner None.
    """
    modules = probe_modules(prefix)
    groups: list[tuple[str | None, list[str]]] = []
    for query in queries:
        who = owner(modules, query) if modules is not None else None
        if groups and groups[-1][0] == who:
            groups[-1][1].append(query)
        else:
            groups.append((who, [query]))
    return groups


def load_path(coq_args: list[str]) -> list[tuple[Path, str]]:
    """(directory, logical prefix) pairs from -R/-Q flags, relative to coq/."""
    pairs = []
    i = 0
    while i < len(coq_args):
        if coq_args[i] in ("-R", "-Q") and i + 2 < len(coq_args):
            pairs.append((Path(coq_args[i + 1]), coq_args[i + 2]))
            i += 3
        else:
            i += 1
    return pairs


def resolve_library(module: str, coq_dir: Path, pairs: list[tuple[Path, str]]) -> Path | None:
    """The compiled file a Require of `module` loads, if exactly one candidate exists."""
    candidates = set()
    for directory, logical in pairs:
        if module.startswith(logical + "."):
            rest = module[len(logical) + 1:]
            candidates.add((coq_dir / directory / (rest.replace(".", "/") + ".vo")).resolve())
    if "." not in module:
        candidates.add((coq_dir / (module + ".vo")).resolve())
    found = [path for path in candidates if path.is_file()]
    return found[0] if len(found) == 1 else None


def file_sha256(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def cache_key(module: str, library_sha256: str, queries: list[str],
              coq_version: str, coq_args: list[str]) -> str:
    material = json.dumps({
        "schema": CACHE_SCHEMA, "module": module, "library": library_sha256,
        "queries": queries, "coq": coq_version, "args": coq_args,
    }, sort_keys=True)
    return hashlib.sha256(material.encode()).hexdigest()


def validate_output(stdout: str, stderr: str, expected: int) -> str:
    if ERROR.search(stderr) or ERROR.search(stdout):
        raise ValueError("Coq reported an error while checking assumptions")
    blocks = list(BLOCK.finditer(stdout))
    if len(blocks) != expected:
        raise ValueError(f"Expected {expected} assumption results, received {len(blocks)}")
    return stdout[blocks[0].start():]


def split_answers(output: str, counts: list[int]) -> list[str]:
    """Cut validated output into consecutive pieces of the given result counts."""
    starts = [match.start() for match in BLOCK.finditer(output)]
    if len(starts) != sum(counts):
        raise ValueError(f"Expected {sum(counts)} assumption results, received {len(starts)}")
    bounds = starts + [len(output)]
    pieces, index = [], 0
    for count in counts:
        pieces.append(output[bounds[index]:bounds[index + count]])
        index += count
    return pieces


def save_cached(directory: Path, key: str, module: str, queries: list[str],
                stdout: str, stderr: str) -> None:
    """Record a validated answer; the file appears only once it is complete."""
    validate_output(stdout, stderr, len(queries))
    directory.mkdir(parents=True, exist_ok=True)
    record = {"schema": CACHE_SCHEMA, "key": key, "module": module,
              "queries": queries, "stdout": stdout, "stderr": stderr}
    pending = directory / f"{key}.pending"
    pending.write_text(json.dumps(record))
    pending.replace(directory / f"{key}.json")


def load_cached(directory: Path, key: str, module: str,
                queries: list[str]) -> tuple[str, str] | None:
    """A saved answer for exactly this key, module, and query list, or None."""
    try:
        record = json.loads((directory / f"{key}.json").read_text())
        if (record.get("schema") != CACHE_SCHEMA or record.get("key") != key
                or record.get("module") != module or record.get("queries") != queries):
            return None
        stdout, stderr = record["stdout"], record["stderr"]
        output = validate_output(stdout, stderr, len(queries))
    except (OSError, ValueError, KeyError, TypeError):
        return None
    return output, stderr


def prune_cache(directory: Path, keep: set[str]) -> None:
    """Drop every saved answer this receipt did not use, so a cache carried
    between runs does not grow without bound."""
    for entry in directory.glob("*"):
        if entry.is_file() and entry.stem not in keep:
            entry.unlink()


def coq_version() -> str:
    try:
        return subprocess.check_output(["coqtop", "--version"], text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        return "coqtop-unavailable"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    # Only queries without a resolvable owning library are batched; each
    # batch runs with the full probe prefix.
    parser.add_argument("--batch-size", type=int, default=2000)
    parser.add_argument("--timeout", type=int, default=900)
    # A run killed by an external signal is retried in place. Only
    # death-by-signal (a negative return code) is retried; a Coq error still
    # fails the run immediately through validate_output.
    parser.add_argument("--retries", type=int, default=30,
                        help="retries per group if the Coq process is killed by a signal")
    parser.add_argument("--work-dir", default=None,
                        help="answer cache directory (default: build/probe/assumption-cache)")
    parser.add_argument("coq_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if min(args.jobs, args.batch_size, args.timeout) < 1:
        parser.error("jobs, batch-size, and timeout must be positive")
    if args.retries < 0:
        parser.error("retries must not be negative")
    coq_args = args.coq_args[1:] if args.coq_args[:1] == ["--"] else args.coq_args
    root = Path(__file__).resolve().parents[1]
    coq_dir = root / "coq"
    build = root / "build/probe"
    cache = Path(args.work_dir) if args.work_dir else build / "assumption-cache"
    if not cache.is_absolute():
        cache = root / cache
    prefix, queries = split_probe((root / FULL_ASSUMPTION_PROBE).read_text())
    source_digest = corpus_digest(root)
    objects_digest = compiled_digest(root)
    version = coq_version()
    pairs = load_path(coq_args)

    units: list[dict] = []
    position = 0
    for module, group in group_queries(prefix, queries):
        library = resolve_library(module, coq_dir, pairs) if module else None
        if library is None:
            for lo in range(0, len(group), args.batch_size):
                chunk = group[lo:lo + args.batch_size]
                units.append({"module": module, "queries": chunk, "first": position + lo,
                              "imports": prefix, "key": None, "library": None})
        else:
            digest = file_sha256(library)
            units.append({"module": module, "queries": group, "first": position,
                          "imports": f"Require {module}.\n", "library": (library, digest),
                          "key": cache_key(module, digest, group, version, coq_args)})
        position += len(group)

    reused: list[str] = []
    executed: list[str] = []
    answers: dict[int, tuple[str, str]] = {}
    pending: list[dict] = []
    for index, unit in enumerate(units):
        unit["index"] = index
        saved = (load_cached(cache, unit["key"], unit["module"], unit["queries"])
                 if unit["key"] is not None else None)
        if saved is None:
            pending.append(unit)
        else:
            answers[index] = saved
            reused.append(unit["module"])
            print(f"[assumption-batch] reused {unit['module']}", flush=True)

    # Cached libraries share sessions up to the batch size; queries without a
    # resolvable library keep the full prefix and run alone.
    chunks: list[list[dict]] = []
    for unit in pending:
        if (unit["key"] is not None and chunks and chunks[-1][0]["key"] is not None
                and sum(len(u["queries"]) for u in chunks[-1]) + len(unit["queries"])
                <= args.batch_size):
            chunks[-1].append(unit)
        else:
            chunks.append([unit])

    def execute(chunk: list[dict]) -> None:
        imports = chunk[0]["imports"] if chunk[0]["key"] is None else "".join(
            unit["imports"] for unit in chunk)
        chunk_queries = [query for unit in chunk for query in unit["queries"]]
        source = imports + "\n".join(chunk_queries) + "\nQuit.\n"
        label = ", ".join(str(unit["module"]) for unit in chunk)
        for attempt in range(args.retries + 1):
            result = subprocess.run(["coqtop", "-quiet", *coq_args], cwd=coq_dir,
                                    input=source, text=True, capture_output=True,
                                    timeout=args.timeout, check=False)
            if result.returncode < 0 and attempt < args.retries:
                print(f"[assumption-batch] {label} killed by signal "
                      f"{-result.returncode} (attempt {attempt + 1}), retrying", flush=True)
                time.sleep(min(2 ** attempt, 30))
                continue
            if result.returncode:
                raise RuntimeError(f"Coq exited {result.returncode} for {label}")
            output = validate_output(result.stdout, result.stderr, len(chunk_queries))
            pieces = split_answers(output, [len(unit["queries"]) for unit in chunk])
            for position, (unit, piece) in enumerate(zip(chunk, pieces)):
                # The session's diagnostics are kept once, with its first library.
                stderr = result.stderr if position == 0 else ""
                if unit["key"] is not None:
                    save_cached(cache, unit["key"], unit["module"], unit["queries"],
                                piece, stderr)
                answers[unit["index"]] = (piece, stderr)
                executed.append(str(unit["module"]))
            print(f"[assumption-batch] checked {label} ({len(chunk_queries)} queries)",
                  flush=True)
            return
        raise RuntimeError(f"unreachable: {label}")

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(execute, chunks))
    results = [(unit["first"],) + answers[unit["index"]] for unit in units]
    changed = [unit["module"] for unit in units if unit["library"] is not None
               and file_sha256(unit["library"][0]) != unit["library"][1]]
    if corpus_digest(root) != source_digest or changed:
        raise RuntimeError("Proof inputs changed during the receipt run; no combined result published")
    combined = "".join(output for _, output, _ in results)
    errors = "".join(stderr for _, _, stderr in results)
    validate_output(combined, errors, len(queries))
    (build / "probe_all_output.txt").write_text(combined)
    (build / "probe_all_err.txt").write_text(errors)
    try:
        cache_label = cache.relative_to(root).as_posix()
    except ValueError:
        cache_label = str(cache)
    (build / "probe_batches.json").write_text(json.dumps({
        "queries": len(queries), "jobs": args.jobs, "batch_size": args.batch_size,
        "source_digest": source_digest, "compiled_digest": objects_digest,
        "all_queries_reexecuted": not reused, "alignment_ok": True,
        "groups": len(units), "reused_groups": len(reused), "executed_groups": len(executed),
        "cache_directory": cache_label,
    }, indent=2) + "\n")
    prune_cache(cache, {unit["key"] for unit in units if unit["key"] is not None})
    print(f"[assumption-batch] all {len(queries)} queries checked and combined in order "
          f"({len(executed)} groups run, {len(reused)} reused)", flush=True)


if __name__ == "__main__":
    main()
