"""CLI wrapper for the C1 physics divergence verifier."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from verifier.physics_divergence import (
    PhysicsDivergenceVerificationError,
    verify_physics_divergence,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a C1 physics divergence run directory")
    parser.add_argument("run_dir", type=Path, help="Directory containing claim.json + physics.receipt.json")
    parser.add_argument(
        "--trust-manifest",
        required=True,
        type=Path,
        help="Path to trust_manifest.json authorising the receipt signer",
    )
    parser.add_argument("--out", type=Path, default=None, help="Optional output JSON path")
    parser.add_argument("--claim", default="claim.json", help="Claim JSON filename (default: claim.json)")
    parser.add_argument(
        "--receipt",
        default="physics.receipt.json",
        help="TRS-1.0 receipt filename (default: physics.receipt.json)",
    )
    parser.add_argument(
        "--calibration",
        default="calibration.json",
        help="Calibration JSON filename (default: calibration.json)",
    )

    args = parser.parse_args(argv)

    try:
        result = verify_physics_divergence(
            args.run_dir,
            trust_manifest_path=args.trust_manifest,
            claim_name=args.claim,
            receipt_name=args.receipt,
            calibration_name=args.calibration,
        )
    except PhysicsDivergenceVerificationError as exc:
        print(f"C1 verification failed: {exc}", file=sys.stderr)
        return 2

    payload = {
        "status": "ok",
        "result": result,
    }

    if args.out is not None:
        args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
