# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Command line certificate checker for LASSERT proofs."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from thielecpu.certcheck import CertificateError, verify_certificate


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Check LRAT/model certificates")
    parser.add_argument("--cnf", required=True, help="Path to DIMACS CNF file")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--lrat", help="Path to LRAT proof")
    group.add_argument("--model", help="Path to satisfying assignment")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    cnf_path = Path(args.cnf)
    if not cnf_path.exists():
        parser.error(f"CNF file not found: {cnf_path}")
    if args.lrat:
        proof_path = Path(args.lrat)
        if not proof_path.exists():
            parser.error(f"LRAT proof not found: {proof_path}")
        proof_type = "LRAT"
        model_path = None
    else:
        proof_path = None
        model_path = Path(args.model)
        if not model_path.exists():
            parser.error(f"model file not found: {model_path}")
        proof_type = "MODEL"
    try:
        verify_certificate(
            cnf_path=cnf_path,
            proof_type=proof_type,
            proof_path=proof_path,
            model_path=model_path,
        )
    except CertificateError as exc:
        print(f"certificate invalid: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
