"""PREREG C (Phase 1): GWOSC event catalog ingest (metadata only).

This is a prereg-style, manifest-bound pipeline that only fetches *public JSON*
from GWOSC's Event API (no waveform/strain files yet):

  init -> fetch -> analyze

It is intended to support later blind tests over strain data without changing
any locked parsing/splitting rules.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

try:
    # Prefer requests if available (clean timeouts).
    import requests  # type: ignore
except Exception:  # pragma: no cover
    requests = None  # type: ignore

# Ensure repository root is importable when running as a file path.
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.prereg_common import (
    ManifestSpec,
    init_manifest,
    require_manifest,
    safe_relpath,
    update_manifest_artifacts,
    verify_params_exact,
    verify_tool_hashes,
    write_json,
)


DEFAULT_ROOT = REPO_ROOT / "benchmarks" / "gwosc_blind_c"
MANIFEST_NAME = "MANIFEST_C.json"

TOOL_FILES = [
    REPO_ROOT / "tools" / "prereg_common.py",
    REPO_ROOT / "tools" / "prereg_c_gwosc_catalog.py",
]

GWOSC_BASE = "https://gwosc.org/eventapi/json/"


@dataclass(frozen=True)
class EventRow:
    release: str
    event: str
    gps_time: Optional[float]
    json_url: str


def _http_get_json(url: str, *, timeout_s: float = 30.0) -> Any:
    if requests is None:
        raise RuntimeError("requests is required for GWOSC fetch (pip install requests)")
    resp = requests.get(url, timeout=timeout_s)
    resp.raise_for_status()
    return resp.json()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _http_get_json_with_receipt(url: str, *, timeout_s: float = 30.0) -> Tuple[Any, Dict[str, Any]]:
    if requests is None:
        raise RuntimeError("requests is required for GWOSC fetch (pip install requests)")
    t0 = time.time()
    resp = requests.get(url, timeout=timeout_s)
    dt = time.time() - t0
    content = resp.content
    receipt = {
        "url": url,
        "status_code": int(resp.status_code),
        "elapsed_s": float(dt),
        "content_sha256": _sha256_bytes(content),
        "content_bytes": int(len(content)),
        "headers": {
            # Keep a small, stable subset.
            "content_type": resp.headers.get("Content-Type"),
            "date": resp.headers.get("Date"),
            "etag": resp.headers.get("ETag"),
            "last_modified": resp.headers.get("Last-Modified"),
        },
    }
    resp.raise_for_status()
    return resp.json(), receipt


def _iter_events_from_release(release: str, *, timeout_s: float) -> Iterable[EventRow]:
    # Release JSON has a top-level {"events": {name: {..}}}.
    url = f"{GWOSC_BASE}{release}"
    payload = _http_get_json(url, timeout_s=timeout_s)
    events = payload.get("events") or {}
    if not isinstance(events, dict):
        raise ValueError(f"Unexpected GWOSC payload shape for {release}: events={type(events)}")

    for event_name, obj in events.items():
        if not isinstance(obj, dict):
            continue
        gps = obj.get("GPS")
        gps_f: Optional[float] = None
        try:
            if gps is not None:
                gps_f = float(gps)
        except Exception:
            gps_f = None
        yield EventRow(release=release, event=str(event_name), gps_time=gps_f, json_url=url)


def cmd_init(args: argparse.Namespace) -> int:
    root: Path = args.root
    root.mkdir(parents=True, exist_ok=True)
    spec = ManifestSpec(name=MANIFEST_NAME, root=root)

    params = {
        "releases": list(args.releases),
        "split_policy": args.split_policy,
        "test_ratio": float(args.test_ratio),
        "timeout_s": float(args.timeout_s),
        "max_events": int(args.max_events) if args.max_events is not None else None,
    }

    init_manifest(spec, params=params, tool_files=TOOL_FILES)
    print(f"Wrote {spec.path}")
    return 0


def cmd_fetch(args: argparse.Namespace) -> int:
    root: Path = args.root
    spec = ManifestSpec(name=MANIFEST_NAME, root=root)
    manifest = require_manifest(spec)
    verify_tool_hashes(manifest, TOOL_FILES)
    verify_params_exact(
        manifest,
        {
            "releases": list(args.releases),
            "split_policy": args.split_policy,
            "test_ratio": float(args.test_ratio),
            "timeout_s": float(args.timeout_s),
            "max_events": int(args.max_events) if args.max_events is not None else None,
        },
    )

    releases_dir = root / "releases"
    releases_dir.mkdir(parents=True, exist_ok=True)

    fetch_receipt: Dict[str, Any] = {
        "gwosc_base": GWOSC_BASE,
        "timeout_s": float(args.timeout_s),
        "fetched_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "releases": {},
    }

    rows: List[Dict[str, Any]] = []
    for rel in args.releases:
        url = f"{GWOSC_BASE}{rel}"
        payload, receipt = _http_get_json_with_receipt(url, timeout_s=float(args.timeout_s))
        fetch_receipt["releases"][rel] = receipt

        # Cache the fetched JSON so the run is inspectable.
        rel_path = releases_dir / f"{rel}.json"
        rel_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

        events = payload.get("events") or {}
        if not isinstance(events, dict):
            raise ValueError(
                f"Unexpected GWOSC payload shape for {rel}: events={type(events)}"
            )
        for event_name, obj in events.items():
            if not isinstance(obj, dict):
                continue
            gps = obj.get("GPS")
            gps_f: Optional[float] = None
            try:
                if gps is not None:
                    gps_f = float(gps)
            except Exception:
                gps_f = None
            rows.append(
                {
                    "release": rel,
                    "event": str(event_name),
                    "gps_time": gps_f,
                    "json_url": url,
                }
            )

    rows.sort(key=lambda r: (r["gps_time"] is None, r["gps_time"] or 0.0, r["release"], r["event"]))
    if args.max_events is not None:
        rows = rows[: int(args.max_events)]

    out_events = root / "events.jsonl"
    with out_events.open("w", encoding="utf-8") as handle:
        for r in rows:
            handle.write(json.dumps(r, sort_keys=True) + "\n")

    receipt_path = root / "fetch_receipt.json"
    receipt_path.write_text(
        json.dumps(fetch_receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    out_index = root / "DATA_C_INDEX.json"
    write_json(
        out_index,
        {
            "gwosc_base": GWOSC_BASE,
            "releases": list(args.releases),
            "n_events": len(rows),
            "events_jsonl": safe_relpath(out_events, REPO_ROOT),
            "fetch_receipt_json": safe_relpath(receipt_path, REPO_ROOT),
            "release_json_files": {
                rel: safe_relpath((releases_dir / f"{rel}.json"), REPO_ROOT)
                for rel in args.releases
            },
        },
    )

    update_manifest_artifacts(
        spec,
        artifact_paths={
            "events_jsonl": out_events,
            "data_index_json": out_index,
            "fetch_receipt_json": receipt_path,
        },
    )

    print(f"Wrote {out_events}")
    print(f"Wrote {receipt_path}")
    print(f"Wrote {out_index}")
    return 0


def _read_jsonl(path: Path) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


def cmd_analyze(args: argparse.Namespace) -> int:
    root: Path = args.root
    spec = ManifestSpec(name=MANIFEST_NAME, root=root)
    manifest = require_manifest(spec)
    verify_tool_hashes(manifest, TOOL_FILES)
    verify_params_exact(
        manifest,
        {
            "releases": list(args.releases),
            "split_policy": args.split_policy,
            "test_ratio": float(args.test_ratio),
            "timeout_s": float(args.timeout_s),
            "max_events": int(args.max_events) if args.max_events is not None else None,
        },
    )

    events_path = root / "events.jsonl"
    if not events_path.exists():
        raise FileNotFoundError("Missing events.jsonl; run fetch first")

    events = _read_jsonl(events_path)
    n = len(events)
    if n == 0:
        raise RuntimeError("No events fetched")

    # Integrity checks: sorted and unique.
    pairs = [(e.get("release"), e.get("event")) for e in events]
    if len(set(pairs)) != len(pairs):
        raise RuntimeError("Duplicate (release,event) rows in events.jsonl")

    def _key(e: Dict[str, Any]) -> Tuple[int, float, str, str]:
        gps = e.get("gps_time")
        if gps is None:
            return (1, 0.0, str(e.get("release")), str(e.get("event")))
        return (0, float(gps), str(e.get("release")), str(e.get("event")))

    if events != sorted(events, key=_key):
        raise RuntimeError("events.jsonl is not sorted by (gps_time, release, event)")

    # Deterministic chronological split: last test_ratio fraction is test.
    test_n = max(1, int(round(n * float(args.test_ratio))))
    train_n = max(0, n - test_n)

    cutoff_idx = max(0, train_n - 1)
    cutoff_row = events[cutoff_idx] if train_n > 0 else None
    cutoff = {
        "train_n": train_n,
        "test_n": test_n,
        "cutoff_index": cutoff_idx if cutoff_row is not None else None,
        "cutoff_gps_time": cutoff_row.get("gps_time") if cutoff_row is not None else None,
        "cutoff_release": cutoff_row.get("release") if cutoff_row is not None else None,
        "cutoff_event": cutoff_row.get("event") if cutoff_row is not None else None,
    }

    analysis = {
        "counts": {"total": n, "train": train_n, "test": test_n},
        "params": manifest.get("params"),
        "split_policy": "chronological_tail",
        "cutoff": cutoff,
        "passes": {
            "nonempty": n > 0,
            "has_test": test_n > 0,
        },
    }

    out_path = root / "analysis_C.json"
    out_path.write_text(json.dumps(analysis, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    update_manifest_artifacts(spec, artifact_paths={"analysis_json": out_path})
    print(f"Wrote {out_path}")
    return 0


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="prereg_c_gwosc_catalog")
    p.add_argument("--root", type=Path, default=DEFAULT_ROOT)

    sub = p.add_subparsers(dest="cmd", required=True)

    def add_common(sp: argparse.ArgumentParser) -> None:
        sp.add_argument(
            "--releases",
            nargs="+",
            default=["GWTC-3-confident"],
            help="GWOSC Event API release name(s), e.g. GWTC-3-confident",
        )
        sp.add_argument("--split-policy", default="chronological")
        sp.add_argument("--test-ratio", type=float, default=0.25)
        sp.add_argument("--timeout-s", type=float, default=30.0)
        sp.add_argument("--max-events", type=int, default=None)

    p_init = sub.add_parser("init")
    add_common(p_init)
    p_init.set_defaults(func=cmd_init)

    p_fetch = sub.add_parser("fetch")
    add_common(p_fetch)
    p_fetch.set_defaults(func=cmd_fetch)

    p_analyze = sub.add_parser("analyze")
    add_common(p_analyze)
    p_analyze.set_defaults(func=cmd_analyze)

    return p


def main(argv: Optional[List[str]] = None) -> int:
    args = _build_parser().parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
