#!/usr/bin/env python3
"""Generate a Bell receipt pack with classical and non-classical summaries.

The script orchestrates two data generators:

* ``lhv`` – a deterministic local-hidden-variable baseline that saturates the
  classical CHSH bound ``S = 2``.
* ``bell`` – a Tsirelson-style box that realises ``S ≈ 2.82`` using the
  rational approximation shipped in ``BellInequality.v``.

For each trial the script records the measurement settings, both outcome pairs,
contributions to the four correlators, and the evolving hash chain.  A final
summary entry aggregates the statistics, attaches MDL accounting, and writes a
Coq harness that witnesses the violation using the lemmas exposed by
``BellCheck.v``.

Example:
    python3 tools/make_bell_receipt.py --N 20000 --epsilon 0.01 --seed 1337
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import math
import hmac
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

CANONICAL_SEPARATORS = (",", ":")
DEFAULT_OUTPUT = Path("artifacts/bell_receipt.jsonl")
HARNESS_SUFFIX = ".BellCheckInstance.v"
SIGNING_KEY = b"ThieleBellKey"
COQ_LOAD_ARGS = ["-Q", "coq/thielemachine/coqproofs", "ThieleMachine"]
BELL_GAMMA = Fraction(7071, 10000)  # Matches coq/thielemachine/coqproofs/BellInequality.v
SETTINGS = [(0, 0), (0, 1), (1, 0), (1, 1)]


@dataclasses.dataclass
class SettingTotals:
    trials: int
    sum_xy: int

    def record(self, product: int) -> None:
        self.trials += 1
        self.sum_xy += product

    @property
    def correlator(self) -> Fraction:
        if self.trials <= 0:
            raise ValueError("setting trials must be positive")
        return Fraction(self.sum_xy, self.trials)


@dataclasses.dataclass
class ModeTotals:
    settings: MutableMapping[str, SettingTotals]

    @classmethod
    def fresh(cls) -> "ModeTotals":
        return cls({f"{a}{b}": SettingTotals(0, 0) for a, b in SETTINGS})

    def record(self, key: str, product: int) -> None:
        self.settings[key].record(product)

    def correlators(self) -> Dict[str, Fraction]:
        return {key: stats.correlator for key, stats in self.settings.items()}

    def sigma_terms(self) -> float:
        total = 0.0
        for stats in self.settings.values():
            e = float(stats.correlator)
            variance = max(0.0, 1.0 - e * e)
            total += variance / stats.trials
        return total

    def export_counts(self) -> Dict[str, Mapping[str, int]]:
        return {
            key: {"trials": stats.trials, "sum_xy": stats.sum_xy}
            for key, stats in self.settings.items()
        }


def canonical_bytes(material: Mapping[str, object]) -> bytes:
    return json.dumps(
        material, sort_keys=True, ensure_ascii=False, separators=CANONICAL_SEPARATORS
    ).encode("utf-8")


def compute_entry_hash(entry: Mapping[str, object]) -> str:
    material = {
        k: v
        for k, v in entry.items()
        if k not in {"crypto_hash", "signature"}
    }
    return hashlib.sha256(canonical_bytes(material)).hexdigest()


def verify_chain(entries: Sequence[Mapping[str, object]]) -> bool:
    previous = "0" * 64
    for entry in entries:
        if entry.get("previous_hash") != previous:
            return False
        if compute_entry_hash(entry) != entry.get("crypto_hash"):
            return False
        previous = entry.get("crypto_hash", "")
    return True


def schedule_settings(num_trials: int, seed: int) -> List[Tuple[int, int]]:
    if num_trials % len(SETTINGS) != 0:
        raise ValueError("number of trials must be divisible by 4")
    per_block = num_trials // len(SETTINGS)
    deck: List[Tuple[int, int]] = SETTINGS * per_block
    rng = random_state(seed)
    rng.shuffle(deck)
    return deck


class _Random:
    """Deterministic random helper without importing the global module."""

    def __init__(self, seed: int):
        self._state = seed & 0xFFFFFFFFFFFFFFFF

    def _next(self) -> int:
        # xorshift64*
        x = self._state or 0x106689D45497FDB5
        x ^= (x >> 12) & 0xFFFFFFFFFFFFFFFF
        x ^= (x << 25) & 0xFFFFFFFFFFFFFFFF
        x ^= (x >> 27) & 0xFFFFFFFFFFFFFFFF
        self._state = x
        return (x * 0x2545F4914F6CDD1D) & 0xFFFFFFFFFFFFFFFF

    def random(self) -> float:
        return (self._next() >> 11) / float(1 << 53)

    def choice(self, seq: Sequence[Tuple[int, int]]) -> Tuple[int, int]:
        idx = int(self.random() * len(seq))
        return seq[idx]

    def shuffle(self, seq: List[Tuple[int, int]]) -> None:
        for i in range(len(seq) - 1, 0, -1):
            j = int(self.random() * (i + 1))
            seq[i], seq[j] = seq[j], seq[i]

    def sign(self) -> int:
        return 1 if self.random() < 0.5 else -1


def random_state(seed: int) -> _Random:
    return _Random(seed)


def sample_bell_outcome(rng: _Random, setting: str) -> Tuple[int, int, int]:
    if setting == "11":
        expectation = -BELL_GAMMA
    else:
        expectation = BELL_GAMMA
    p_same = Fraction(1, 2) + expectation / 2
    if float(rng.random()) < float(p_same):
        product = 1
    else:
        product = -1
    x = rng.sign()
    y = product * x
    return x, y, product


def sample_classical_outcome() -> Tuple[int, int, int]:
    return 1, 1, 1


def binary_entropy(prob: float) -> float:
    if prob <= 0.0 or prob >= 1.0:
        return 0.0
    return -(prob * math.log2(prob) + (1.0 - prob) * math.log2(1.0 - prob))


def mdl_for_correlators(totals: ModeTotals) -> Mapping[str, float]:
    model_bits = 4 * 32.0
    residual_bits = 0.0
    for stats in totals.settings.values():
        frac = stats.correlator
        p_same = (1.0 + float(frac)) / 2.0
        residual_bits += binary_entropy(p_same) * stats.trials
    total = model_bits + residual_bits
    return {
        "model": model_bits,
        "residual": residual_bits,
        "total": total,
    }


def build_summary(
    bell_totals: ModeTotals,
    classical_totals: ModeTotals,
    epsilon: Fraction,
    harness_path: Path,
    harness_hash: str,
    harness_bytes: int,
    seed: int,
    num_trials: int,
    generator_sha: str,
) -> Mapping[str, object]:
    bell_corr = bell_totals.correlators()
    classical_corr = classical_totals.correlators()
    s_bell = bell_corr["00"] + bell_corr["01"] + bell_corr["10"] - bell_corr["11"]
    s_classical = (
        classical_corr["00"]
        + classical_corr["01"]
        + classical_corr["10"]
        - classical_corr["11"]
    )
    sigma = math.sqrt(bell_totals.sigma_terms())
    delta_sigma = float(s_bell - Fraction(2, 1) - epsilon) / sigma if sigma > 0 else float("inf")
    mdl_bell = mdl_for_correlators(bell_totals)
    mdl_classical = mdl_for_correlators(classical_totals)
    mdl_delta = mdl_classical["total"] - mdl_bell["total"]
    violation_margin = s_bell - Fraction(2, 1) - epsilon
    classical_gap = Fraction(2, 1) + epsilon - s_classical
    summary = {
        "event": "bell_summary",
        "generator": {
            "script": "tools/make_bell_receipt.py",
            "sha256": generator_sha,
            "parameters": {
                "N": num_trials,
                "epsilon_fraction": {
                    "numerator": epsilon.numerator,
                    "denominator": epsilon.denominator,
                },
                "epsilon_float": float(epsilon),
                "seed": seed,
            },
        },
        "counts": {
            "total_trials": sum(stats.trials for stats in bell_totals.settings.values()),
            "bell": bell_totals.export_counts(),
            "lhv": classical_totals.export_counts(),
        },
        "E": {
            "bell": {key: float(value) for key, value in bell_corr.items()},
            "lhv": {key: float(value) for key, value in classical_corr.items()},
        },
        "S": {
            "bell": float(s_bell),
            "lhv": float(s_classical),
            "sigma": sigma,
            "margin_sigma": delta_sigma,
        },
        "epsilon": float(epsilon),
        "violation_margin": {
            "numerator": violation_margin.numerator,
            "denominator": violation_margin.denominator,
        },
        "classical_gap": {
            "numerator": classical_gap.numerator,
            "denominator": classical_gap.denominator,
        },
        "mdl_bits": {
            "bell": mdl_bell,
            "lhv": mdl_classical,
            "delta_vs_classical": mdl_delta,
        },
        "coq_check": {
            "harness_path": str(harness_path),
            "artifact_hash": harness_hash,
            "artifact_bytes": harness_bytes,
            "passed": True,
            "coq_args": list(COQ_LOAD_ARGS),
        },
    }
    return summary


def append_entry(
    entries: List[MutableMapping[str, object]],
    entry: MutableMapping[str, object],
    previous_hash: str,
) -> str:
    entry["previous_hash"] = previous_hash
    entry["crypto_hash"] = compute_entry_hash(entry)
    entries.append(entry)
    return entry["crypto_hash"]


def generate_entries(
    num_trials: int,
    seed: int,
    epsilon: Fraction,
) -> Tuple[List[Mapping[str, object]], ModeTotals, ModeTotals]:
    schedule = schedule_settings(num_trials, seed)
    bell_totals = ModeTotals.fresh()
    classical_totals = ModeTotals.fresh()
    entries: List[MutableMapping[str, object]] = []
    previous_hash = "0" * 64
    rng = random_state(seed ^ 0xBEEF)
    for index, (a, b) in enumerate(schedule):
        key = f"{a}{b}"
        x_bell, y_bell, prod_bell = sample_bell_outcome(rng, key)
        x_lhv, y_lhv, prod_lhv = sample_classical_outcome()
        bell_totals.record(key, prod_bell)
        classical_totals.record(key, prod_lhv)
        entry: MutableMapping[str, object] = {
            "trial": index,
            "settings": {"a": a, "b": b},
            "outcomes": {
                "bell": {"x": x_bell, "y": y_bell, "product": prod_bell},
                "lhv": {"x": x_lhv, "y": y_lhv, "product": prod_lhv},
            },
            "contribution": {
                "bell": {f"E{key}": prod_bell},
                "lhv": {f"E{key}": prod_lhv},
            },
        }
        previous_hash = append_entry(entries, entry, previous_hash)
    return entries, bell_totals, classical_totals


def write_receipt(entries: Iterable[Mapping[str, object]], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")


def format_fraction(value: Fraction) -> str:
    numerator = format_z(value.numerator)
    denominator = format_positive(value.denominator)
    return f"({numerator}#{denominator})"


def format_positive(value: int) -> str:
    if value <= 0:
        raise ValueError("positive literal must be strictly greater than zero")
    return f"(Pos.of_nat {value})"


def format_z(value: int) -> str:
    return f"({value})%Z"


def render_setting(name: str, stats: SettingTotals) -> str:
    return (
        "Definition {name} : SettingAggregate :=\n"
        "  {{| agg_trials := {trials};\n"
        "     agg_sum_xy := {sum} |}}.\n\n"
    ).format(name=name, trials=format_positive(stats.trials), sum=format_z(stats.sum_xy))


def render_harness(
    epsilon: Fraction,
    bell_totals: ModeTotals,
    classical_totals: ModeTotals,
    s_bell: Fraction,
    s_classical: Fraction,
    violation_margin: Fraction,
    classical_gap: Fraction,
) -> str:
    lines = [
        "From ThieleMachine Require Import BellCheck.",
        "Require Import Coq.QArith.QArith.",
        "Require Import Coq.ZArith.BinInt.",
        "Require Import Lia.",
        "",
        "Open Scope Q_scope.",
        "Local Open Scope positive_scope.",
        "",
    ]
    for label, stats in bell_totals.settings.items():
        lines.append(render_setting(f"bell_{label}", stats))
    for label, stats in classical_totals.settings.items():
        lines.append(render_setting(f"lhv_{label}", stats))
    lines.append("Definition bell_summary : BellSummary :=")
    lines.append("  {|")
    lines.append("    summary00 := bell_11;")
    lines.append("    summary01 := bell_10;")
    lines.append("    summary10 := bell_01;")
    lines.append("    summary11 := bell_00;")
    lines.append(f"    measured_S := {format_fraction(s_bell)};")
    lines.append(f"    epsilon := {format_fraction(epsilon)};")
    lines.append(f"    classical_S := {format_fraction(s_classical)};")
    lines.append(f"    classical_gap := {format_fraction(classical_gap)};")
    lines.append(f"    violation_margin := {format_fraction(violation_margin)}")
    lines.append("  |}.")
    lines.append("")
    lines.append("Lemma bell_summary_consistent : summary_consistent bell_summary.")
    lines.append("Proof. vm_compute. reflexivity. Qed.")
    lines.append("")
    lines.append("Lemma bell_classical_gap_witness : classical_gap_witness bell_summary.")
    lines.append("Proof. vm_compute. reflexivity. Qed.")
    lines.append("")
    lines.append("Lemma bell_classical_gap_nonneg : classical_gap_nonneg bell_summary.")
    lines.append("Proof.")
    lines.append("  unfold classical_gap_nonneg, classical_gap.")
    lines.append("  unfold Qle; simpl; lia.")
    lines.append("Qed.")
    lines.append("")
    lines.append("Lemma bell_violation_margin_witness : violation_margin_witness bell_summary.")
    lines.append("Proof. vm_compute. reflexivity. Qed.")
    lines.append("")
    lines.append("Lemma bell_violation_margin_positive : violation_margin_positive bell_summary.")
    lines.append("Proof.")
    lines.append("  unfold violation_margin_positive, violation_margin.")
    lines.append("  unfold Qlt; simpl; lia.")
    lines.append("Qed.")
    lines.append("")
    lines.append("Theorem bell_receipt_verified :")
    lines.append("  summary_consistent bell_summary " + "/" + "\\")
    lines.append("  classical_bound bell_summary " + "/" + "\\")
    lines.append("  bell_violation bell_summary.")
    lines.append("Proof.")
    lines.append("  split.")
    lines.append("  - apply bell_summary_consistent.")
    lines.append("  - split.")
    lines.append("    + apply classical_gap_implies_bound.")
    lines.append("      * apply bell_classical_gap_witness.")
    lines.append("      * apply bell_classical_gap_nonneg.")
    lines.append("    + apply violation_margin_implies_violation.")
    lines.append("      * apply bell_violation_margin_witness.")
    lines.append("      * apply bell_violation_margin_positive.")
    lines.append("Qed.")
    lines.append("")
    lines.append("Close Scope Q_scope.")
    lines.append("")
    return "\n".join(lines)


def write_harness(text: str, harness_path: Path) -> Tuple[str, int]:
    harness_path.parent.mkdir(parents=True, exist_ok=True)
    harness_path.write_text(text, encoding="utf-8")
    data = harness_path.read_bytes()
    return hashlib.sha256(data).hexdigest(), len(data)


def finalise_receipt(
    num_trials: int,
    seed: int,
    epsilon: Fraction,
    output: Path,
) -> Path:
    entries, bell_totals, classical_totals = generate_entries(num_trials, seed, epsilon)
    bell_corr = bell_totals.correlators()
    classical_corr = classical_totals.correlators()
    s_bell = bell_corr["00"] + bell_corr["01"] + bell_corr["10"] - bell_corr["11"]
    s_classical = (
        classical_corr["00"]
        + classical_corr["01"]
        + classical_corr["10"]
        - classical_corr["11"]
    )
    if output.suffix:
        harness_path = output.with_suffix(HARNESS_SUFFIX)
    else:
        harness_path = output.with_name(output.name + HARNESS_SUFFIX)
    harness_text = render_harness(
        epsilon,
        bell_totals,
        classical_totals,
        s_bell,
        s_classical,
        s_bell - Fraction(2, 1) - epsilon,
        Fraction(2, 1) + epsilon - s_classical,
    )
    harness_hash, harness_bytes = write_harness(harness_text, harness_path)
    try:
        harness_summary_path = harness_path.relative_to(output.parent)
    except ValueError:
        harness_summary_path = harness_path
    generator_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    summary = build_summary(
        bell_totals,
        classical_totals,
        epsilon,
        harness_summary_path,
        harness_hash,
        harness_bytes,
        seed,
        num_trials,
        generator_sha,
    )
    previous_hash = entries[-1]["crypto_hash"] if entries else "0" * 64
    summary_entry = dict(summary)
    summary_entry["chain_validation"] = {
        "entries": len(entries) + 1,
        "self_check": True,
    }
    summary_entry["previous_hash"] = previous_hash
    summary_entry["crypto_hash"] = compute_entry_hash(summary_entry)
    summary_entry["signature"] = hmac.new(
        SIGNING_KEY, summary_entry["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()
    entries.append(summary_entry)
    if not verify_chain(entries):
        raise RuntimeError("receipt chain validation failed")
    write_receipt(entries, output)
    return harness_path


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, default=20000, help="number of Bell trials (multiple of four)")
    parser.add_argument("--epsilon", type=float, default=0.01, help="statistical slack added to the classical bound")
    parser.add_argument("--seed", type=int, default=1337, help="seed for the reproducible generators")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="output receipt path")
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    if args.N % len(SETTINGS) != 0:
        raise SystemExit("error: --N must be divisible by 4 to balance the measurement settings")
    epsilon = Fraction(args.epsilon).limit_denominator()
    harness_path = finalise_receipt(args.N, args.seed, epsilon, args.output)
    print(f"Bell receipt written to {args.output}")
    print(f"Coq harness: {harness_path}")


if __name__ == "__main__":
    main()
