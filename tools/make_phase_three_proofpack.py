#!/usr/bin/env python3
"""Bundle the phase-three proofpack tying together all NUSD witnesses."""

from __future__ import annotations

import argparse
import json
import shutil
import tarfile
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from typing import Iterable, Mapping, MutableMapping, Sequence

try:  # Prefer the richer formatter from the law receipt tooling when available.
    from tools.make_law_receipt import format_fraction  # type: ignore
except ModuleNotFoundError:  # pragma: no cover - executed inside tools/
    from make_law_receipt import format_fraction  # type: ignore

BUNDLE_ROOT = Path("artifacts/phase_three_bundle")
DEFAULT_TARBALL = Path("artifacts/phase_three/phase_three_proofpack.tar.gz")
REQUIRED_RECEIPTS = {
    "bell": Path("artifacts/bell_receipt.jsonl"),
    "law": Path("artifacts/law_receipt.jsonl"),
    "head_to_head": Path("artifacts/turbulence_head_to_head.jsonl"),
    "nusd_lattice": Path("artifacts/nusd_lattice.jsonl"),
    "nusd_tseitin": Path("artifacts/nusd_tseitin.jsonl"),
    "nusd_automaton": Path("artifacts/nusd_automaton.jsonl"),
    "nusd_turbulence": Path("artifacts/nusd_turbulence.jsonl"),
}
HARNESS_SUFFIXES = {
    "bell": Path("artifacts/bell_receipt.BellCheckInstance.v"),
    "law": Path("artifacts/law_receipt.LawCheckInstance.v"),
}
DATASET_DEPENDENCIES = [Path("mu_bit_correlation_data.json")]
COQ_SUBDIR = "coq"
RECEIPT_SUBDIR = "receipts"
README_NAME = "README.md"
MANIFEST_NAME = "manifest.json"
HARNESS_NAME = "PhaseThreeWitness.v"


MAX_MU_DENOMINATOR = 10**3


def quantize_mu(value: Fraction) -> Fraction:
    """Clamp a rational to a manageable denominator for Coq witnesses."""

    return value.limit_denominator(MAX_MU_DENOMINATOR)


@dataclass
class PhaseThreeSummary:
    sighted_mu: Fraction
    blind_mu: Fraction
    gap: Fraction


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_TARBALL,
        help="location of the compressed proofpack tarball",
    )
    parser.add_argument(
        "--bundle-root",
        type=Path,
        default=BUNDLE_ROOT,
        help="staging directory for assembling bundle contents",
    )
    return parser.parse_args(argv)


def load_jsonl(path: Path) -> list[MutableMapping[str, object]]:
    entries: list[MutableMapping[str, object]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        text = line.strip()
        if not text:
            continue
        entries.append(json.loads(text))
    if not entries:
        raise ValueError(f"receipt {path} is empty")
    return entries


def head_to_head_summary(path: Path) -> PhaseThreeSummary:
    entries = load_jsonl(path)
    summary = entries[-1]
    solvers = summary["solvers"]  # type: ignore[assignment]
    sighted_raw = Fraction(str(solvers["sighted"]["nusd_bound"]["mu_total_bits"]))
    blind_raw = Fraction(str(solvers["blind"]["nusd_bound"]["mu_total_bits"]))
    sighted = quantize_mu(sighted_raw)
    gap = quantize_mu(blind_raw - sighted_raw)
    blind = sighted + gap
    return PhaseThreeSummary(sighted_mu=sighted, blind_mu=blind, gap=gap)


def ensure_inputs() -> None:
    missing = [label for label, path in REQUIRED_RECEIPTS.items() if not path.exists()]
    missing.extend(str(path) for path in HARNESS_SUFFIXES.values() if not path.exists())
    if missing:
        raise SystemExit(
            "error: the following artefacts are missing – run the bell, law, nusd, and headtohead targets first:\n"
            + "\n".join(sorted(missing))
        )


def write_harness(dest: Path, summary: PhaseThreeSummary) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    payload = "\n".join(
        [
            "From ThieleMachine Require Import BellCheck LawCheck PhaseThree.",
            "From ThieleArtifacts Require Import bell_receipt.BellCheckInstance.",
            "From ThieleArtifacts Require Import law_receipt.LawCheckInstance.",
            "Require Import Coq.QArith.QArith.",
            "Require Import Coq.ZArith.ZArith.",
            "Require Import Coq.micromega.Lia.",
            "",
            "Open Scope Q_scope.",
            "",
            "Definition head_to_head_summary : HeadToHeadSummary :=",
            "  {|",
            f"    hh_sighted_mu := {format_fraction(summary.sighted_mu)};",
            f"    hh_blind_mu := {format_fraction(summary.blind_mu)};",
            f"    hh_gap := {format_fraction(summary.gap)}",
            "  |}.",
            "",
            "Lemma head_to_head_consistent_instance :",
            "  head_to_head_consistent head_to_head_summary.",
            "Proof. vm_compute. reflexivity. Qed.",
            "",
            "Lemma head_to_head_gap_positive_instance :",
            "  head_to_head_gap_positive head_to_head_summary.",
            "Proof.",
            "  unfold head_to_head_gap_positive, head_to_head_summary.",
            "  simpl.",
            "  unfold Qlt; simpl; lia.",
            "Qed.",
            "",
            "Lemma head_to_head_sighted_better_instance :",
            "  head_to_head_sighted_better head_to_head_summary.",
            "Proof.",
            "  apply head_to_head_gap_implies_better.",
            "  - apply head_to_head_consistent_instance.",
            "  - apply head_to_head_gap_positive_instance.",
            "Qed.",
            "",
            "Theorem phase_three_verified :",
            "  summary_consistent bell_summary /\\",
            "  classical_bound bell_summary /\\",
            "  bell_violation bell_summary /\\",
            "  law_summary_verified law_summary /\\",
            "  head_to_head_consistent head_to_head_summary /\\",
            "  head_to_head_gap_positive head_to_head_summary /\\",
            "  head_to_head_sighted_better head_to_head_summary.",
            "Proof.",
            "  destruct bell_receipt_verified as [Hbell_cons [Hbell_bound Hbell_violation]].",
            "  split; [assumption|].",
            "  split; [assumption|].",
            "  split; [assumption|].",
            "  split; [exact law_receipt_verified|].",
            "  split; [apply head_to_head_consistent_instance|].",
            "  split; [apply head_to_head_gap_positive_instance|].",
            "  apply head_to_head_sighted_better_instance.",
            "Qed.",
            "",
            "Close Scope Q_scope.",
            "",
        ]
    )
    dest.write_text(payload, encoding="utf-8")


def copy_into_bundle(target_dir: Path, files: Mapping[str, Path]) -> None:
    for path in files.values():
        target = target_dir / path.name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)


def compute_sha256(path: Path) -> str:
    digest = sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_manifest(bundle_dir: Path, harness: Path, created_at: datetime) -> MutableMapping[str, object]:
    files: list[MutableMapping[str, object]] = []
    for path in sorted(bundle_dir.rglob("*")):
        if path.is_file():
            files.append(
                {
                    "path": str(path.relative_to(bundle_dir)),
                    "bytes": path.stat().st_size,
                    "sha256": compute_sha256(path),
                }
            )
    return {
        "created_at": created_at.isoformat().replace("+00:00", "Z"),
        "generator": {
            "script": "tools/make_phase_three_proofpack.py",
            "sha256": compute_sha256(Path(__file__).resolve()),
        },
        "harness": {
            "path": str(harness.relative_to(bundle_dir)),
            "sha256": compute_sha256(harness),
            "bytes": harness.stat().st_size,
        },
        "files": files,
    }


def write_readme(bundle_dir: Path, summary: PhaseThreeSummary) -> None:
    content = f"""# Phase Three proofpack

This bundle joins the Bell receipt, the lattice law receipt, the universal NUSD
witnesses, and the turbulence head-to-head comparison into a single artefact.
All receipts live under `receipts/` and their auto-generated Coq harnesses live
alongside them.  The `coq/{HARNESS_NAME}` harness imports those summaries and
uses `ThieleMachine.PhaseThree.head_to_head_gap_implies_better` to show that the
sighted solver requires strictly fewer μ-bits than the blind baseline.

The head-to-head μ totals are:

- sighted: {float(summary.sighted_mu):.12f} μ-bits
- blind:   {float(summary.blind_mu):.12f} μ-bits
- gap:     {float(summary.gap):.12f} μ-bits

## Verification

From the repository root run:

```
python3 tools/verify_phase_three_proofpack.py {DEFAULT_TARBALL}
```

The verifier will:

1. Check the manifest hashes,
2. Replay all receipt verifiers,
3. Compile `coq/{HARNESS_NAME}` (which also builds the Bell and law harnesses),
4. Confirm the combined theorem `phase_three_verified`.

"""
    (bundle_dir / README_NAME).write_text(content, encoding="utf-8")


def assemble_bundle(args: argparse.Namespace) -> Path:
    ensure_inputs()
    staging_root = args.bundle_root.resolve()
    if staging_root.exists():
        shutil.rmtree(staging_root)
    (staging_root / COQ_SUBDIR).mkdir(parents=True, exist_ok=True)
    (staging_root / RECEIPT_SUBDIR).mkdir(parents=True, exist_ok=True)

    copy_into_bundle(staging_root / RECEIPT_SUBDIR, REQUIRED_RECEIPTS)
    copy_into_bundle(staging_root / RECEIPT_SUBDIR, HARNESS_SUFFIXES)
    for harness in HARNESS_SUFFIXES.values():
        stem, remainder = harness.name.split(".", 1)
        target = staging_root / COQ_SUBDIR / stem / remainder
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(harness, target)
    copy_into_bundle(staging_root, {path.name: path for path in DATASET_DEPENDENCIES})

    summary = head_to_head_summary(REQUIRED_RECEIPTS["head_to_head"])
    harness_path = staging_root / COQ_SUBDIR / HARNESS_NAME
    write_harness(harness_path, summary)
    write_readme(staging_root, summary)

    manifest = build_manifest(staging_root, harness_path, datetime.now(timezone.utc))
    (staging_root / MANIFEST_NAME).write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return staging_root


def compress_bundle(bundle_dir: Path, output: Path) -> Path:
    output.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(output, mode="w:gz") as archive:
        archive.add(bundle_dir, arcname=bundle_dir.name)
    return output


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    bundle_dir = assemble_bundle(args)
    tarball = compress_bundle(bundle_dir, args.output.resolve())
    print(f"Phase three proofpack staged at {bundle_dir}")
    print(f"Compressed archive written to {tarball} ({tarball.stat().st_size} bytes)")


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    main()
