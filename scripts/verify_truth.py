#!/usr/bin/env python3
"""Generate a Coq verification file from step receipts and optionally compile it.

Usage: python scripts/verify_truth.py <receipts.json> <out_coq.v>

This is a drop-in Python replacement for the inline heredoc used by
`scripts/verify_truth.sh` so it can be invoked directly from PowerShell.
"""
from pathlib import Path
import sys

from thielecpu.receipts import load_receipts

def coq_string(value: str) -> str:
    escaped = (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\t", "\\t")
    )
    return f'"{escaped}"'


def coq_instruction(op: str, payload):
    if op == "LASSERT":
        return f"(LASSERT {coq_string(str(payload))})"
    if op == "MDLACC":
        return "MDLACC"
    if op == "PNEW":
        elems = "; ".join(f"{int(x)}%nat" for x in payload)
        return f"(PNEW [{elems}])"
    if op == "PYEXEC":
        return f"(PYEXEC {coq_string(str(payload))})"
    if op == "EMIT":
        return f"(EMIT {coq_string(str(payload))})"
    raise ValueError(f"Unsupported instruction in receipts: {op}")


def coq_event(event):
    if event is None:
        return "None"
    tag = event.get("tag")
    if tag == "PolicyCheck":
        return f"Some (PolicyCheck {coq_string(event.get('value', ''))})"
    if tag == "InferenceComplete":
        return "Some InferenceComplete"
    if tag == "ErrorOccurred":
        return f"Some (ErrorOccurred {coq_string(event.get('value', ''))})"
    raise ValueError(f"Unknown event tag: {tag}")


def coq_cert(cert):
    return (
        "{| smt_query := "
        + coq_string(cert.get("smt_query", ""))
        + ";\n     solver_reply := "
        + coq_string(cert.get("solver_reply", ""))
        + ";\n     metadata := "
        + coq_string(cert.get("metadata", ""))
        + ";\n     timestamp := "
        + str(int(cert.get("timestamp", 0)))
        + ";\n     sequence := "
        + str(int(cert.get("sequence", 0)))
        + " |}"
    )


def coq_state(name: str, state: dict) -> str:
    return (
        f"Definition {name} : ConcreteState :=\n"
        f"  {{| pc := {int(state['pc'])};\n"
        f"     status := {int(state['status'])};\n"
        f"     mu_acc := {int(state['mu_acc'])};\n"
        f"     cert_addr := {coq_string(str(state['cert_addr']))} |}}.\n"
    )


def coq_observation(name: str, obs) -> str:
    return (
        f"Definition {name} : StepObs :=\n"
        f"  {{| ev := {coq_event(obs.event)};\n"
        f"     mu_delta := {int(obs.mu_delta)};\n"
        f"     cert := {coq_cert(obs.cert)} |}}.\n"
    )


def generate(receipts_path: Path, coq_path: Path) -> None:
    receipts = load_receipts(receipts_path)

    if not receipts:
        print("No receipts to verify", file=sys.stderr)
        raise SystemExit(1)

    coq_lines = [
        "From Coq Require Import String ZArith List Bool.",
        "From ThieleMachine Require Import ThieleMachineConcrete BellInequality.",
        "Import ListNotations.",
        "Open Scope string_scope.",
        "Open Scope Z_scope.",
        "",
    ]

    receipt_names = []
    instr_exprs = []

    for idx, receipt in enumerate(receipts):
        pre_name = f"step{idx}_pre"
        post_name = f"step{idx}_post"
        obs_name = f"step{idx}_obs"
        receipt_name = f"receipt{idx}"
        instr_expr = coq_instruction(receipt.instruction.op, receipt.instruction.payload)
        coq_lines.append(coq_state(pre_name, receipt.pre_state))
        coq_lines.append(coq_state(post_name, receipt.post_state))
        coq_lines.append(coq_observation(obs_name, receipt.observation))
        receipt_def = (
            f"Definition {receipt_name} : ConcreteReceipt :=\n"
            f"  {{| receipt_instr := {instr_expr};\n"
            f"     receipt_pre := {pre_name};\n"
            f"     receipt_post := {post_name};\n"
            f"     receipt_obs := {obs_name} |}}.\n"
        )
        coq_lines.append(receipt_def)
        receipt_names.append(receipt_name)
        instr_exprs.append(instr_expr)

    program_list = "; ".join(instr_exprs)
    receipts_list = "; ".join(receipt_names)
    start_state = "step0_pre"

    coq_lines.append(
        "Definition recorded_program : list ThieleInstr :=\n"
        f"  [{program_list}].\n"
    )

    coq_lines.append(
        "Definition recorded_receipts : list ConcreteReceipt :=\n"
        f"  [{receipts_list}].\n"
    )

    coq_lines.append(
        "Definition recorded_frames : list (BridgeReceiptFrame ThieleInstr ConcreteState StepObs) :=\n"
        "  map concrete_receipt_frame recorded_receipts.\n"
    )

    coq_lines.append(
        f"Definition recorded_start : ConcreteState := {start_state}.\n"
    )

    coq_lines.append(
        "Lemma recorded_receipts_correct :\n"
        "  concrete_receipts_of recorded_start recorded_program = recorded_receipts.\n"
        "Proof. reflexivity. Qed.\n"
    )

    coq_lines.append(
        "Lemma recorded_frames_sound :\n"
        "  @receipts_sound _ _ _ concrete_step_frame recorded_start recorded_frames.\n"
        "Proof.\n"
        "  unfold recorded_frames.\n"
        "  rewrite <- recorded_receipts_correct.\n"
        "  apply concrete_receipts_sound.\n"
        "Qed.\n"
    )

    coq_path.parent.mkdir(parents=True, exist_ok=True)
    coq_path.write_text("\n".join(coq_lines), encoding="utf-8")
    print(f"Wrote Coq file to {coq_path}")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python scripts/verify_truth.py <receipts.json> <out_coq.v>", file=sys.stderr)
        raise SystemExit(2)
    receipts_path = Path(sys.argv[1])
    coq_path = Path(sys.argv[2])
    generate(receipts_path, coq_path)
