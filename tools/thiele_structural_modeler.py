#!/usr/bin/env python3
"""CLI for structure-aware modelling using the NUSD discovery domains."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, Mapping, MutableMapping

from nusd_domains import AutomatonDomain, DiscoveryDomain, TurbulenceDomain


def instantiate_domain(args: argparse.Namespace) -> DiscoveryDomain:
    if args.domain == "automaton":
        return AutomatonDomain(
            rule=args.rule,
            width=args.width,
            steps=args.steps,
            seed=args.seed,
            wrap=not args.no_wrap,
            record_entries=False,
        )
    if args.domain == "turbulence":
        return TurbulenceDomain(
            seed=args.seed,
            samples=args.samples,
            grid=args.grid,
            record_entries=False,
        )
    raise ValueError(f"unsupported domain {args.domain}")


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--domain", choices=["automaton", "turbulence"], default="automaton")
    parser.add_argument("--seed", type=int, default=1337, help="random seed for the domain generator")
    parser.add_argument("--export", type=Path, help="optional JSON output path")

    automaton = parser.add_argument_group("automaton")
    automaton.add_argument("--rule", type=int, default=110)
    automaton.add_argument("--width", type=int, default=64)
    automaton.add_argument("--steps", type=int, default=64)
    automaton.add_argument("--no-wrap", action="store_true", help="disable cyclic boundary conditions")

    turbulence = parser.add_argument_group("turbulence")
    turbulence.add_argument("--samples", type=int, default=96)
    turbulence.add_argument("--grid", type=int, default=32)

    return parser.parse_args(argv)


def summarise(result_mdl: Mapping[str, float], epsilon_bits: float) -> MutableMapping[str, float]:
    model_bits = float(result_mdl.get("model_bits", 0.0))
    residual_bits = float(result_mdl.get("residual_bits", 0.0))
    baseline_bits = float(result_mdl.get("baseline_bits", model_bits + residual_bits))
    mu_total = model_bits + residual_bits - float(epsilon_bits)
    return {
        "mu_question_bits": model_bits,
        "mu_answer_bits": residual_bits,
        "mu_total_bits": mu_total,
        "baseline_bits": baseline_bits,
        "delta_vs_baseline": baseline_bits - (model_bits + residual_bits),
    }


def render_summary(domain: DiscoveryDomain, summary: Mapping[str, float]) -> None:
    print(f"Domain: {domain.name}")
    print(f"μ_question bits: {summary['mu_question_bits']:.6f}")
    print(f"μ_answer bits:   {summary['mu_answer_bits']:.6f}")
    print(f"μ_total bits:    {summary['mu_total_bits']:.6f}")
    print(f"baseline bits:   {summary['baseline_bits']:.6f}")
    print(f"delta vs base:   {summary['delta_vs_baseline']:.6f}")


def main(argv: Iterable[str] | None = None) -> None:
    args = parse_args(argv)
    domain = instantiate_domain(args)
    result = domain.run()
    summary = summarise(result.mdl, result.epsilon_bits)
    render_summary(domain, summary)
    if args.export:
        payload = {
            "domain": domain.name,
            "parameters": dict(domain.parameters),
            "summary": summary,
        }
        args.export.parent.mkdir(parents=True, exist_ok=True)
        args.export.write_text(json.dumps(payload, indent=2))
        print(f"Saved summary to {args.export}")


if __name__ == "__main__":
    main()
