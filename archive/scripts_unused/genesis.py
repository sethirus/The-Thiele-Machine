from __future__ import annotations

import argparse
from dataclasses import replace
from pathlib import Path

from tqdm import tqdm

from thielecpu.genesis import GenesisConfig, plot_history, run_genesis


_PHASES = [
    "INIT",
    "DISCOVER",
    "CLASSIFY",
    "DECOMPOSE",
    "EXECUTE",
    "MERGE",
    "VERIFY",
    "SUCCESS",
]


def _banner(phase: str) -> None:
    width = 70
    print("\n" + "=" * width)
    print(f"{phase:>10}  ::  Thiele Genesis")
    print("=" * width)


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Genesis: evolutionary selection overlay running on real Thiele VM Python execution")

    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--population", type=int, default=1000)
    p.add_argument("--generations", type=int, default=50)
    p.add_argument("--rounds", type=int, default=40)
    p.add_argument("--initial-fuel", type=int, default=64)

    p.add_argument("--base-choices", type=int, default=8)
    p.add_argument("--growth-per-round", type=int, default=4)

    p.add_argument("--env-mod", type=int, default=7)
    p.add_argument("--env-residue", type=int, default=3)
    p.add_argument("--env-scale", type=float, default=12.0)

    p.add_argument("--elite", type=float, default=0.20)
    p.add_argument("--mutation", type=float, default=0.15)

    p.add_argument("--bet-budget", type=float, default=0.80)
    p.add_argument("--surprise-cost", type=float, default=1.0)

    p.add_argument("--outdir", type=str, default="")

    return p.parse_args()


def main() -> None:
    args = _parse_args()

    _banner(_PHASES[0])
    print("Model: GPT-5.2 (Preview)")

    outdir = Path(args.outdir) if args.outdir else None

    cfg = GenesisConfig(
        seed=args.seed,
        population=args.population,
        generations=args.generations,
        rounds_per_generation=args.rounds,
        initial_fuel=args.initial_fuel,
        base_choices=args.base_choices,
        growth_per_round=args.growth_per_round,
        env_mod=args.env_mod,
        env_residue=args.env_residue,
        env_scale=args.env_scale,
        elite_fraction=args.elite,
        mutation_rate=args.mutation,
        bet_budget_fraction=args.bet_budget,
        surprise_cost_scale=args.surprise_cost,
        outdir=outdir,
    )

    _banner(_PHASES[1])
    print("Hidden environment (printed for verification):")
    print(f"  reachability: i % {cfg.env_mod} == {cfg.env_residue}")
    print(f"  within-reachable p(i) ∝ exp(-i/{cfg.env_scale})")

    _banner(_PHASES[2])
    print(f"Population: {cfg.population}")
    print(f"Generations: {cfg.generations}  Rounds/gen: {cfg.rounds_per_generation}")

    _banner(_PHASES[3])
    print("Each agent runs real VM sandbox execution per round.")

    _banner(_PHASES[4])
    # The heavy work happens inside run_genesis; we just keep the terminal lively.
    for _ in tqdm(range(1), desc="Genesis run", unit="run"):
        out = run_genesis(cfg)

    _banner(_PHASES[5])
    print("Selection: elitism + mutation completed.")

    _banner(_PHASES[6])
    plot_path = plot_history(out)
    if plot_path is not None:
        print(f"Plot written: {plot_path}")
    else:
        print("Plot skipped (missing/empty history).")

    _banner(_PHASES[7])
    print(f"Artifacts: {out}")
    print(f"  - config.json")
    print(f"  - history.csv")
    print(f"  - sample_genes.json")
    if plot_path is not None:
        print(f"  - plot.png")


if __name__ == "__main__":
    main()
