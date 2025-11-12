#!/usr/bin/env python3
"""Generate multi-domain No Unpaid Sight Debt receipts."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
from pathlib import Path
from typing import Iterable, List, Mapping, MutableMapping

try:
    from tools.make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain
except ModuleNotFoundError:  # script executed from within tools/
    from make_law_receipt import append_entry, compute_entry_hash, nusd_payload, verify_chain
from mu_calibration import CalibrationSummary, compute_calibration_summary
from nusd_domains import (
    DOMAIN_REGISTRY,
    AutomatonDomain,
    DiscoveryDomain,
    DomainResult,
    LatticeDomain,
    TseitinDomain,
    TurbulenceDomain,
)

DEFAULT_OUTPUT = Path("artifacts/nusd_receipt.jsonl")
DEFAULT_TEMPERATURE = 300.0
DEFAULT_CALIBRATION = Path("mu_bit_correlation_data.json")
SIGNING_KEY = b"ThieleNUSDKey"


def available_domains() -> List[str]:
    return sorted(DOMAIN_REGISTRY.keys())


def instantiate_domain(args: argparse.Namespace, *, record_entries: bool = True) -> DiscoveryDomain:
    if args.domain == LatticeDomain.name:
        return LatticeDomain(
            sites=args.sites,
            steps=args.steps,
            seed=args.seed,
            record_entries=record_entries,
        )
    if args.domain == TseitinDomain.name:
        return TseitinDomain(
            Path(args.tseitin_spec),
            step_index=args.tseitin_step,
            record_entries=record_entries,
        )
    if args.domain == AutomatonDomain.name:
        return AutomatonDomain(
            rule=args.automaton_rule,
            width=args.automaton_width,
            steps=args.automaton_steps,
            seed=args.automaton_seed,
            wrap=not args.automaton_no_wrap,
            record_entries=record_entries,
        )
    if args.domain == TurbulenceDomain.name:
        return TurbulenceDomain(
            seed=args.turbulence_seed,
            samples=args.turbulence_samples,
            grid=args.turbulence_grid,
            record_entries=record_entries,
        )
    raise ValueError(f"unknown domain {args.domain}")


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--domain",
        choices=available_domains(),
        default=LatticeDomain.name,
        help="domain to run (default: lattice)",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="receipt output path")
    parser.add_argument("--temperature", type=float, default=DEFAULT_TEMPERATURE)
    parser.add_argument(
        "--epsilon-bits",
        type=float,
        default=None,
        help="override the domain-provided ε slack in bits",
    )
    parser.add_argument(
        "--calibration-file",
        type=Path,
        default=DEFAULT_CALIBRATION,
        help="μ-bit calibration dataset",
    )
    parser.add_argument("--no-calibration", action="store_true", help="skip calibration metadata")

    lattice = parser.add_argument_group("lattice")
    lattice.add_argument("--sites", type=int, default=8)
    lattice.add_argument("--steps", type=int, default=16)
    lattice.add_argument("--seed", type=int, default=2025)

    tseitin = parser.add_argument_group("tseitin")
    tseitin.add_argument(
        "--tseitin-spec",
        type=Path,
        default=Path("spec/golden/tseitin_small.json"),
        help="path to the golden Tseitin certificate",
    )
    tseitin.add_argument("--tseitin-step", type=int, default=0)

    automaton = parser.add_argument_group("automaton")
    automaton.add_argument("--automaton-rule", type=int, default=110)
    automaton.add_argument("--automaton-width", type=int, default=32)
    automaton.add_argument("--automaton-steps", type=int, default=32)
    automaton.add_argument("--automaton-seed", type=int, default=1337)
    automaton.add_argument("--automaton-no-wrap", action="store_true")

    turbulence = parser.add_argument_group("turbulence")
    turbulence.add_argument("--turbulence-seed", type=int, default=314159)
    turbulence.add_argument("--turbulence-samples", type=int, default=96)
    turbulence.add_argument("--turbulence-grid", type=int, default=32)

    return parser.parse_args(argv)


def load_calibration(args: argparse.Namespace) -> CalibrationSummary | None:
    if args.no_calibration:
        return None
    path = args.calibration_file
    if not path.exists():
        raise FileNotFoundError(f"calibration dataset {path} is missing")
    return compute_calibration_summary(path)


def build_entries(result: DomainResult) -> List[MutableMapping[str, object]]:
    entries: List[MutableMapping[str, object]] = []
    previous_hash = "0" * 64
    for entry in result.entries:
        payload = dict(entry)
        previous_hash = append_entry(entries, payload, previous_hash)
    return entries


def append_summary(
    entries: List[MutableMapping[str, object]],
    result: DomainResult,
    domain_name: str,
    temperature: float,
    epsilon_bits: float,
    calibration: CalibrationSummary | None,
    calibration_path: Path | None,
) -> None:
    nusd = nusd_payload(result.mdl, temperature, epsilon_bits, calibration)
    generator_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    summary: MutableMapping[str, object] = {
        "event": "nusd_summary",
        "generator": {
            "script": "tools/make_nusd_receipt.py",
            "sha256": generator_sha,
            "parameters": dict(result.parameters),
        },
        "domain": {
            "name": domain_name,
            "detail": result.detail,
            "provenance": result.provenance,
        },
        "mdl_bits": result.mdl,
        "nusd_bound": nusd,
        "temperature_kelvin": temperature,
        "epsilon_bits": epsilon_bits,
        "calibration_dataset": str(calibration_path) if calibration_path else None,
        "chain_validation": {"entries": len(entries) + 1, "self_check": True},
    }
    if entries:
        summary["previous_hash"] = entries[-1]["crypto_hash"]
    else:
        summary["previous_hash"] = "0" * 64
    summary["signature_algorithm"] = "HMAC-SHA256"
    summary["crypto_hash"] = compute_entry_hash(summary)
    summary["signature"] = hmac.new(
        SIGNING_KEY, summary["crypto_hash"].encode("utf-8"), hashlib.sha256
    ).hexdigest()
    entries.append(summary)


def write_receipt(path: Path, entries: List[MutableMapping[str, object]]) -> None:
    if not verify_chain(entries):
        raise RuntimeError("receipt chain verification failed")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, sort_keys=True))
            handle.write("\n")


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    domain = instantiate_domain(args, record_entries=True)
    result = domain.run()
    epsilon_bits = args.epsilon_bits if args.epsilon_bits is not None else result.epsilon_bits
    calibration_summary = load_calibration(args)
    entries = build_entries(result)
    calibration_path: Path | None = None
    if calibration_summary is not None:
        calibration_path = args.calibration_file
    append_summary(
        entries,
        result,
        args.domain,
        args.temperature,
        epsilon_bits,
        calibration_summary,
        calibration_path,
    )
    write_receipt(args.output, entries)
    print(f"NUSD receipt written to {args.output}")


if __name__ == "__main__":
    main()
