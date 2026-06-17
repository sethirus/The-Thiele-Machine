#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from build.thiele_vm import run_vm_trace
from thielecpu.receipt import (
    build_execution_receipt_payload,
    canonicalize_program_source,
    load_private_key_from_hex_file,
    sign_receipt_payload,
    split_init_lines,
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    raw_args = list(sys.argv[1:] if argv is None else argv)
    metadata_provided = False
    metadata_text = None
    if "--metadata" in raw_args:
        index = raw_args.index("--metadata")
        if index + 1 >= len(raw_args):
            raise SystemExit("create_execution_receipt.py: error: argument --metadata: expected one argument")
        metadata_provided = True
        metadata_text = raw_args[index + 1]
        del raw_args[index:index + 2]

    parser = argparse.ArgumentParser(description="Create a signed TRS-1.0 execution receipt for a Thiele source program.")
    parser.add_argument("program", help="Path to the Thiele source program")
    parser.add_argument("--output", required=True, help="Output receipt JSON path")
    parser.add_argument("--sign", required=True, help="Path to file containing 32-byte Ed25519 private key as hex")
    parser.add_argument("--key-id", required=True, help="Signer key identifier")
    parser.add_argument("--include-public-key", action="store_true", help="Embed the signer public key in the receipt")
    args = parser.parse_args(raw_args)
    args.metadata = metadata_text
    args.metadata_provided = metadata_provided
    return args


def main() -> int:
    args = parse_args()
    program_path = Path(args.program).resolve()
    metadata = ...
    if args.metadata_provided:
        metadata = json.loads(args.metadata)

    canonical_program = canonicalize_program_source(program_path)
    canonical_lines = canonical_program["canonical_lines"]
    init_lines = split_init_lines(canonical_lines)
    fuel = canonical_program["fuel"]

    pre_state = run_vm_trace(init_lines, fuel=fuel)
    post_state = run_vm_trace(canonical_lines, fuel=fuel)

    payload = build_execution_receipt_payload(
        program_path=program_path,
        pre_state=pre_state,
        post_state=post_state,
        metadata=metadata,
        key_id=args.key_id,
    )
    private_key = load_private_key_from_hex_file(Path(args.sign))
    receipt = sign_receipt_payload(payload, private_key=private_key, include_public_key=args.include_public_key)

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {output_path}")
    print(f"kind={receipt['kind']}")
    print(f"global_digest={receipt['global_digest']}")
    print(f"mu_delta={receipt['execution']['mu_delta']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())