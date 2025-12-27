#!/usr/bin/env python3
"""Bridge for Verilog CPU PYEXEC requests.

The Verilog RTL exposes a PYEXEC instruction which asserts `py_req` and supplies
`py_code_addr`. In this repo's Icarus build, `$system` is not available, so the
hardware co-sim testbench uses file-based IPC instead:

- The testbench writes a request file: "<id> <code_addr_hex>".
- This bridge runs as a long-lived server watching that file.
- For each new request id, the bridge performs the requested action *for real*
    (receipt generation + verification) and writes a response file:
    "<id> <rc_int>".

Requests:
- code_addr 0x0001: generate inverse_genesis NUSD receipt
- code_addr 0x0002: verify that receipt
- code_addr 0x0003: generate genesis_compression NUSD receipt + GIF
- code_addr 0x0004: verify that receipt
- code_addr 0x0005: return 32-bit digest from genesis receipt (derived from video_sha256)

Return codes:
- 0: success
- non-zero: failure
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path


def _run(cmd: list[str], *, cwd: Path) -> int:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        # Keep stdout/stderr short; the Verilog demo wants clean output.
        tail = (proc.stdout + "\n" + proc.stderr).strip().splitlines()[-12:]
        sys.stderr.write("PYEXEC command failed:\n")
        sys.stderr.write("  cmd: " + " ".join(cmd) + "\n")
        if tail:
            sys.stderr.write("  tail:\n")
            for line in tail:
                sys.stderr.write("    " + line + "\n")
    return int(proc.returncode)


def _handle_request(*, code_addr: int, repo_root: Path) -> int:
    receipt_path = (repo_root / "artifacts" / "inverse_genesis_nusd_receipt.jsonl").resolve()

    genesis_receipt_path = (repo_root / "artifacts" / "genesis_compression_nusd_receipt.jsonl").resolve()
    genesis_gif_path = (repo_root / "artifacts" / "genesis_compression.gif").resolve()

    if code_addr == 0x0001:
        cmd = [
            sys.executable,
            str((repo_root / "tools" / "make_nusd_receipt.py").resolve()),
            "--domain",
            "inverse_genesis",
            "--output",
            str(receipt_path),
            "--no-calibration",
            "--inverse-seed",
            "20251226",
            "--inverse-steps",
            "1024",
            "--inverse-dt",
            "0.01",
            "--inverse-noise-std",
            "0.002",
            "--inverse-trajectories",
            "4",
            "--inverse-max-terms",
            "6",
            "--inverse-min-gain-bits",
            "0.1",
            "--inverse-bits-per-sample",
            "64.0",
        ]
        return _run(cmd, cwd=repo_root)

    if code_addr == 0x0002:
        cmd = [
            sys.executable,
            str((repo_root / "tools" / "verify_nusd_receipt.py").resolve()),
            str(receipt_path),
            "--skip-calibration",
        ]
        return _run(cmd, cwd=repo_root)

    if code_addr == 0x0003:
        cmd = [
            sys.executable,
            str((repo_root / "tools" / "make_nusd_receipt.py").resolve()),
            "--domain",
            "genesis_compression",
            "--output",
            str(genesis_receipt_path),
            "--no-calibration",
            "--genesis-rule",
            "critters",
            "--genesis-include-control",
            "--genesis-display-phase-invert",
            "--genesis-init-density",
            "0.50",
            "--genesis-init-patch-frac",
            "1.0",
            "--genesis-render-hud",
            "--genesis-no-render-delta",
            "--genesis-render-motion",
            "--genesis-render-trail",
            "--genesis-trail-decay",
            "245",
            "--genesis-trail-threshold",
            "64",
            "--genesis-width",
            "128",
            "--genesis-height",
            "128",
            "--genesis-steps",
            "6000",
            "--genesis-seed",
            "20251226",
            "--genesis-budget-bits",
            "28000",
            "--genesis-dictionary-size",
            "8",
            "--genesis-pressure-stride",
            "5",
            "--genesis-sample-every",
            "120",
            "--genesis-sample-steps",
            "0",
            "1000",
            "2000",
            "3000",
            "4000",
            "5000",
            "6000",
            "--genesis-gif-path",
            str(genesis_gif_path),
            "--genesis-gif-scale",
            "4",
            "--genesis-gif-fps",
            "20",
        ]
        return _run(cmd, cwd=repo_root)

    if code_addr == 0x0004:
        cmd = [
            sys.executable,
            str((repo_root / "tools" / "verify_nusd_receipt.py").resolve()),
            str(genesis_receipt_path),
            "--skip-calibration",
        ]
        return _run(cmd, cwd=repo_root)

    if code_addr == 0x0005:
        # Return a stable 32-bit digest from the latest genesis receipt.
        # This lets RTL assert invariants beyond rc codes.
        try:
            import json

            if not genesis_receipt_path.exists():
                sys.stderr.write("PYEXEC digest: missing genesis receipt\n")
                return 0

            video_sha = None
            with genesis_receipt_path.open("r", encoding="utf-8") as handle:
                for line in handle:
                    obj = json.loads(line)
                    if obj.get("event") == "genesis_compression_result":
                        res = obj.get("result", {})
                        video_sha = res.get("video_sha256")
                        break
            if not isinstance(video_sha, str) or len(video_sha) < 8:
                sys.stderr.write("PYEXEC digest: missing/invalid video_sha256 in receipt\n")
                return 0
            return int(video_sha[:8], 16) & 0xFFFFFFFF
        except Exception:
            return 0

    sys.stderr.write(f"Unknown code_addr {code_addr:#x}\n")
    return 3


def _atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", required=True, help="repository root path")

    ap.add_argument("--server", action="store_true", help="run as long-lived file-IPC server")
    ap.add_argument("--req-path", help="request file path (server mode)")
    ap.add_argument("--resp-path", help="response file path (server mode)")
    ap.add_argument("--max-requests", type=int, default=0, help="stop after N requests (0=forever)")

    # Legacy/single-shot mode (kept for convenience)
    ap.add_argument("--code-addr", help="PYEXEC code address (hex or int)")
    ap.add_argument("--result-path", help="where to write 32-bit result")
    ap.add_argument(
        "--print-result",
        action="store_true",
        help="print the 32-bit result to stdout (single-shot mode)",
    )
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()

    if args.server:
        if not args.req_path or not args.resp_path:
            sys.stderr.write("--server requires --req-path and --resp-path\n")
            return 2

        req_path = Path(args.req_path).resolve()
        resp_path = Path(args.resp_path).resolve()

        served = 0
        while True:
            # Blocking handshake: wait for a writer to send a single line.
            try:
                with req_path.open("r", encoding="utf-8") as handle:
                    raw = handle.readline().strip()
            except OSError:
                time.sleep(0.02)
                continue

            if not raw:
                continue

            parts = raw.split()
            if len(parts) < 2:
                continue

            try:
                req_id = int(parts[0], 0)
                code_addr = int(parts[1], 0)
            except ValueError:
                continue

            rc = _handle_request(code_addr=code_addr, repo_root=repo_root)
            # Blocking response: open for write and send a single line.
            try:
                with resp_path.open("w", encoding="utf-8") as handle:
                    handle.write(f"{req_id} {rc}\n")
                    handle.flush()
            except OSError:
                # If we can't write the response, keep going; RTL will time out.
                pass

            served += 1
            if args.max_requests and served >= args.max_requests:
                return 0

    # Single-shot mode
    if not args.code_addr or (not args.result_path and not args.print_result):
        sys.stderr.write(
            "Single-shot mode requires --code-addr and either --result-path or --print-result (or use --server)\n"
        )
        return 2

    try:
        code_addr = int(args.code_addr, 0)
    except ValueError:
        sys.stderr.write("Invalid --code-addr\n")
        return 2

    rc = _handle_request(code_addr=code_addr, repo_root=repo_root)
    if args.print_result:
        sys.stdout.write(str(rc) + "\n")
        sys.stdout.flush()
        return 0

    result_path = Path(args.result_path).resolve()
    _atomic_write_text(result_path, str(rc) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
