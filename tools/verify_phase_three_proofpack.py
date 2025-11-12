#!/usr/bin/env python3
"""Verify the phase-three proofpack archive."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tarfile
import tempfile
from hashlib import sha256
from pathlib import Path
from typing import Callable, Iterable, Tuple

BUNDLE_DIRNAME = "phase_three_bundle"
DEFAULT_TARBALL = Path("artifacts/phase_three/phase_three_proofpack.tar.gz")
RECEIPT_FILES = {
    "bell": "bell_receipt.jsonl",
    "law": "law_receipt.jsonl",
    "nusd_lattice": "nusd_lattice.jsonl",
    "nusd_tseitin": "nusd_tseitin.jsonl",
    "nusd_automaton": "nusd_automaton.jsonl",
    "nusd_turbulence": "nusd_turbulence.jsonl",
    "head_to_head": "turbulence_head_to_head.jsonl",
}
HARNESS_DIR = "coq"
RECEIPTS_DIR = "receipts"
DATASET_NAME = "mu_bit_correlation_data.json"


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "bundle",
        type=Path,
        nargs="?",
        default=DEFAULT_TARBALL,
        help="phase-three proofpack archive or directory",
    )
    parser.add_argument("--coqc", default="coqc", help="coqc binary to invoke when compiling harnesses")
    parser.add_argument(
        "--keep-temp",
        action="store_true",
        help="keep temporary extraction directory for inspection",
    )
    return parser.parse_args(argv)


def compute_sha256(path: Path) -> str:
    digest = sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def extract_bundle(path: Path, keep_temp: bool) -> Tuple[Path, Callable[[], None]]:
    if path.is_dir():
        bundle_path = path
        cleanup = (lambda: None)
    else:
        tmpdir = Path(tempfile.mkdtemp(prefix="phase_three_bundle_"))
        with tarfile.open(path, "r:*") as archive:
            archive.extractall(tmpdir)
        bundle_path = tmpdir / BUNDLE_DIRNAME
        if not bundle_path.exists():
            raise FileNotFoundError(f"expected top-level directory '{BUNDLE_DIRNAME}' in archive {path}")
        cleanup = (lambda: None) if keep_temp else (lambda: shutil.rmtree(tmpdir))
    return bundle_path.resolve(), cleanup


def verify_manifest(bundle_root: Path) -> None:
    manifest_path = bundle_root / "manifest.json"
    if not manifest_path.exists():
        raise FileNotFoundError(f"manifest missing at {manifest_path}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    files = manifest.get("files", [])
    for entry in files:
        rel = entry.get("path")
        sha = entry.get("sha256")
        target = bundle_root / rel
        if not target.exists():
            raise FileNotFoundError(f"manifest listed {rel} but file is missing")
        computed = compute_sha256(target)
        if computed != sha:
            raise ValueError(f"sha256 mismatch for {rel}: expected {sha}, observed {computed}")


def run_python(script: str, args: list[str]) -> None:
    command = [sys.executable, script, *args]
    subprocess.run(command, check=True)


def verify_receipts(bundle_root: Path) -> None:
    receipts_root = bundle_root / RECEIPTS_DIR
    dataset_path = bundle_root / DATASET_NAME
    run_python(
        "tools/verify_bell_receipt.py",
        [str(receipts_root / RECEIPT_FILES["bell"]), "--coqtop", "coqtop"],
    )
    run_python(
        "tools/verify_law_receipt.py",
        [str(receipts_root / RECEIPT_FILES["law"]), "--coq-binary", "coqtop"],
    )
    for label in ("nusd_lattice", "nusd_tseitin", "nusd_automaton", "nusd_turbulence"):
        run_python("tools/verify_nusd_receipt.py", [str(receipts_root / RECEIPT_FILES[label])])
    run_python(
        "tools/verify_turbulence_head_to_head.py",
        [
            str(receipts_root / RECEIPT_FILES["head_to_head"]),
            "--calibration-file",
            str(dataset_path),
        ],
    )


def build_coq(bundle_root: Path, coqc: str) -> None:
    harness = bundle_root / HARNESS_DIR / "PhaseThreeWitness.v"
    if not harness.exists():
        raise FileNotFoundError(f"phase-three harness missing at {harness}")
    dependencies = [
        bundle_root / HARNESS_DIR / "bell_receipt" / "BellCheckInstance.v",
        bundle_root / HARNESS_DIR / "law_receipt" / "LawCheckInstance.v",
    ]
    for dep in dependencies:
        if not dep.exists():
            raise FileNotFoundError(f"expected dependency harness at {dep}")
        subprocess.run(
            [
                coqc,
                "-q",
                "-Q",
                "coq/thielemachine/coqproofs",
                "ThieleMachine",
                "-Q",
                str(bundle_root / HARNESS_DIR),
                "ThieleArtifacts",
                str(dep),
            ],
            check=True,
        )
    subprocess.run(
        [
            coqc,
            "-q",
            "-Q",
            "coq/thielemachine/coqproofs",
            "ThieleMachine",
            "-Q",
            str(bundle_root / HARNESS_DIR),
            "ThieleArtifacts",
            str(harness),
        ],
        check=True,
    )


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    bundle_root, cleanup = extract_bundle(args.bundle, args.keep_temp)
    try:
        verify_manifest(bundle_root)
        verify_receipts(bundle_root)
        build_coq(bundle_root, args.coqc)
        print("Phase-three proofpack verified successfully.")
    finally:
        cleanup()


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    main()
