# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""Generate a canonical Tsirelson receipt trace for verification."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Iterable, List

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.mu_spec import calculate_mu_cost
from thielecpu.receipts import (
    InstructionWitness,
    StepObservation,
    StepReceipt,
    WitnessState,
)
from tools.receipts import compute_global_digest
from thielecpu.receipts import ensure_kernel_keys, _resolve_verify_key, _load_verify_key_bytes, sign_receipt


TSIRELSON_ALICE_SETTING = 0
TSIRELSON_ALICE_OUTCOME = 0
TSIRELSON_BOB_SETTING = 1
TSIRELSON_BOB_OUTCOME = 0


def _empty_cert() -> dict:
    """Return the default empty certificate payload."""

    return {
        "smt_query": "",
        "solver_reply": "",
        "metadata": "",
        "timestamp": 0,
        "sequence": 0,
    }


def simulate_step(
    instruction: InstructionWitness, pre_state: WitnessState
) -> tuple[WitnessState, StepObservation]:
    """Mirror the concrete Coq step function for the receipts we emit."""

    op = instruction.op
    if op == "PNEW":
        post_state = WitnessState(
            pc=pre_state.pc + 1,
            status=pre_state.status,
            mu_acc=pre_state.mu_acc,
            cert_addr=pre_state.cert_addr,
        )
        observation = StepObservation(
            event={"tag": "InferenceComplete"},
            mu_delta=0,
            cert=_empty_cert(),
        )
    elif op == "PYEXEC":
        payload = str(instruction.payload)
        post_state = WitnessState(
            pc=pre_state.pc + 1,
            status=pre_state.status,
            mu_acc=pre_state.mu_acc,
            cert_addr=pre_state.cert_addr,
        )
        cert = _empty_cert()
        if payload == "alice_measurement":
            cert["timestamp"] = TSIRELSON_ALICE_SETTING
            cert["sequence"] = TSIRELSON_ALICE_OUTCOME
        elif payload == "bob_measurement":
            cert["timestamp"] = TSIRELSON_BOB_SETTING
            cert["sequence"] = TSIRELSON_BOB_OUTCOME
        observation = StepObservation(
            event={"tag": "PolicyCheck", "value": payload},
            mu_delta=0,
            cert=cert,
        )
    elif op == "EMIT":
        payload = str(instruction.payload)
        post_state = WitnessState(
            pc=pre_state.pc + 1,
            status=pre_state.status,
            mu_acc=pre_state.mu_acc,
            cert_addr=pre_state.cert_addr,
        )
        observation = StepObservation(
            event={"tag": "ErrorOccurred", "value": payload},
            mu_delta=0,
            cert=_empty_cert(),
        )
    elif op == "LASSERT":
        query = str(instruction.payload)
        mu_delta = calculate_mu_cost(query, 1, 1)
        post_state = WitnessState(
            pc=pre_state.pc + 1,
            status=pre_state.status,
            mu_acc=pre_state.mu_acc + mu_delta,
            cert_addr=pre_state.cert_addr,
        )
        observation = StepObservation(
            event={"tag": "PolicyCheck", "value": query},
            mu_delta=mu_delta,
            cert={
                "smt_query": query,
                "solver_reply": "",
                "metadata": "",
                "timestamp": 0,
                "sequence": 0,
            },
        )
    elif op == "MDLACC":
        post_state = WitnessState(
            pc=pre_state.pc + 1,
            status=pre_state.status,
            mu_acc=pre_state.mu_acc,
            cert_addr=pre_state.cert_addr,
        )
        observation = StepObservation(event=None, mu_delta=0, cert=_empty_cert())
    else:
        raise ValueError(f"Unsupported instruction for receipts: {op}")

    return post_state, observation


def assemble_receipts(instructions: Iterable[InstructionWitness]) -> List[StepReceipt]:
    """Assemble receipts for ``instructions`` using deterministic witnesses."""

    pre_state = WitnessState()
    receipts: List[StepReceipt] = []
    for index, instruction in enumerate(instructions):
        post_state, observation = simulate_step(instruction, pre_state)
        receipts.append(
            StepReceipt.assemble(
                index,
                instruction,
                pre_state,
                post_state,
                observation,
            )
        )
        pre_state = post_state
    return receipts


TSIRELSON_INSTRUCTIONS: List[InstructionWitness] = [
    InstructionWitness("PNEW", [0, 1]),
    InstructionWitness("PYEXEC", "prepare_shared_partition"),
    InstructionWitness("PYEXEC", "alice_measurement"),
    InstructionWitness("PYEXEC", "bob_measurement"),
    InstructionWitness("EMIT", "tsirelson_outcome"),
]


def main(path: Path) -> None:
    receipts = assemble_receipts(TSIRELSON_INSTRUCTIONS)
    steps = [r.to_dict() for r in receipts]
    # compute global digest from step_hashes
    step_hashes = [s.get("step_hash") for s in steps if s.get("step_hash")]
    global_digest = compute_global_digest(step_hashes) if step_hashes else ""
    receipt = {
        "spec_version": "1.1",
        "steps": steps,
        "global_digest": global_digest,
    }

    # Best-effort: ensure kernel keys and expose kernel_pubkey + top-level signature
    try:
        ensure_kernel_keys()
        # sign the full receipt payload using deterministic kernel signing (nacl)
        sig = sign_receipt(receipt)
        # expose public key
        verify_key_path = _resolve_verify_key()
        vk_bytes = _load_verify_key_bytes(verify_key_path)
        pub_hex = vk_bytes.hex() if vk_bytes is not None else ""
        receipt["kernel_pubkey"] = pub_hex
        receipt["signature"] = sig
    except Exception:
        pass

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {len(receipts)} receipts to {path}")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Emit a canonical Tsirelson receipt trace for verification",
    )
    parser.add_argument(
        "output",
        nargs="?",
        default="examples/tsirelson_step_receipts.json",
        type=Path,
        help="Path to the receipts JSON file to generate",
    )
    args = parser.parse_args()

    main(args.output)
