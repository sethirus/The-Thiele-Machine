#!/usr/bin/env python3

from __future__ import annotations

"""Generate an external-facing DI randomness confrontation artifact.

This script is deliberately receipts-only and deterministic.

Given a step receipts file (JSON array of StepReceipt), it writes a JSON summary
that compares:

1) A standard CHSH-based DI bound (CHSH -> Hmin) that depends only on the trial
   transcript.
2) A Thiele-style "certified" bound that gates randomness on explicit
   structure-addition (cert_addr empty -> non-empty transition).

This produces a clean “conflict chart” in the minimal sense:
- Same transcript => standard DI curve yields >0 randomness when CHSH>2.
- Thiele-certified curve yields 0 unless structure-addition occurs.

The goal is not to settle DI assumptions, but to make assumptions explicit,
reproducible, and auditable from receipts.
"""

import argparse
import json
from pathlib import Path

from thielecpu.receipts import load_receipts

from tools.di_randomness_bounds import TSIRELSON_BOUND_Q, hmin_lower_bound_bits_from_chsh
from tools.rng_metric import rng_metric
from tools.rng_transcript import decode_rng_transcript


_CERT_SETTER_OPS = {"REVEAL", "EMIT", "LJOIN", "LASSERT"}


def _is_cert_setter_op(op: str) -> bool:
    return str(op).strip().upper() in _CERT_SETTER_OPS


def _receipt_envelope(receipts_path: Path) -> dict[str, object]:
    receipts = list(load_receipts(receipts_path))
    if not receipts:
        return {
            "cert_setter_ops": sorted(_CERT_SETTER_OPS),
            "cert_setter_steps": 0,
            "mu_acc_init": 0,
            "mu_acc_final": 0,
            "mu_acc_delta": 0,
            "mu_delta_total": 0.0,
            "f_count": 0,
            "count_le_f_count": True,
        }

    cert_setter_receipts = [r for r in receipts if _is_cert_setter_op(r.instruction.op)]
    cert_setter_steps = len(cert_setter_receipts)

    # Check assumption: every cert-setter step must pay > 0 mu
    # Note: mu_delta is what was paid in that step.
    cert_setter_positive_cost_assumption_holds = all(
        float(r.observation.mu_delta) > 0 for r in cert_setter_receipts
    )

    mu_acc_init = int(receipts[0].pre_state.get("mu_acc", 0))
    mu_acc_final = int(receipts[-1].post_state.get("mu_acc", mu_acc_init))
    mu_acc_delta = int(mu_acc_final - mu_acc_init)
    mu_delta_total = float(sum(float(r.observation.mu_delta) for r in receipts))

    # Coq-side envelope: f_count(K) = max(0, K), with K being Δμ.
    f_count = max(0, mu_acc_delta)

    count_le_f_count = None
    if cert_setter_positive_cost_assumption_holds:
        count_le_f_count = bool(cert_setter_steps <= f_count)

    return {
        "cert_setter_ops": sorted(_CERT_SETTER_OPS),
        "cert_setter_steps": int(cert_setter_steps),
        "mu_acc_init": int(mu_acc_init),
        "mu_acc_final": int(mu_acc_final),
        "mu_acc_delta": int(mu_acc_delta),
        "mu_delta_total": float(mu_delta_total),
        "f_count": int(f_count),
        "count_le_f_count": count_le_f_count,
        "cert_setter_positive_cost_assumption_holds": cert_setter_positive_cost_assumption_holds,
    }


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--receipts",
        type=Path,
        default=Path("examples/tsirelson_step_receipts.json"),
        help="Path to step_receipts.json (default: examples/tsirelson_step_receipts.json)",
    )
    ap.add_argument(
        "--out",
        type=Path,
        required=True,
        help="Output JSON path (artifact)",
    )
    args = ap.parse_args()

    receipts_path: Path = args.receipts
    out_path: Path = args.out

    transcript = decode_rng_transcript(receipts_path)
    metric = rng_metric(transcript)

    envelope = _receipt_envelope(receipts_path)

    # Standard DI curve (no structure-addition gating) using the clipped CHSH.
    standard_hmin = hmin_lower_bound_bits_from_chsh(min(metric.chsh, TSIRELSON_BOUND_Q))

    artifact = {
        "schema_version": "TM-DI-CONFLICT-1",
        "inputs": {"receipts": str(receipts_path.as_posix())},
        "observed": {
            "n_trials": len(transcript.trials),
            "n_per_setting": metric.n_per_setting,
            "chsh": {"num": metric.chsh.numerator, "den": metric.chsh.denominator},
            "has_structure_addition": bool(transcript.has_structure_addition),
            "cert_setter_ops": envelope["cert_setter_ops"],
            "cert_setter_steps": envelope["cert_setter_steps"],
            "mu_acc_init": envelope["mu_acc_init"],
            "mu_acc_final": envelope["mu_acc_final"],
            "mu_acc_delta": envelope["mu_acc_delta"],
            "mu_delta_total": envelope["mu_delta_total"],
        },
        "bounds": {
            "standard_di": {
                "assumption": "CHSH-only DI bound; ignores certification/structure-addition channels",
                "hmin_lower_bound_bits": float(standard_hmin),
            },
            "thiele_certified": {
                "assumption": "DI bound gated on explicit structure-addition (cert transition) in receipts",
                "hmin_lower_bound_bits": float(metric.hmin_lower_bound_bits),
                "epsilon": float(metric.epsilon),
            },
            "thiele_cert_step_envelope": {
                "assumption": "Coq: executed cert-setter count ≤ f_count(Δμ)=max(0,Δμ), with cert-setters costing ≥1 μ",
                "f_count": envelope["f_count"],
                "count_le_f_count": envelope["count_le_f_count"],
                "cert_setter_positive_cost_assumption_holds": envelope["cert_setter_positive_cost_assumption_holds"],
            },
        },
    }

    _write_json(out_path, artifact)
    print(f"wrote: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
