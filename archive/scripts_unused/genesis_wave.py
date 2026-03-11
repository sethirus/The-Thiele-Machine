#!/usr/bin/env python3

from __future__ import annotations

import argparse
from pathlib import Path

from tqdm import tqdm

from thielecpu.genesis_wave import WaveConfig, plot_history, run_genesis_wave


def _banner(phase: str, title: str = "Thiele Genesis Wave") -> None:
    line = "=" * 70
    print("\n" + line)
    print(f"{phase:^70}")
    print(line)
    if phase.strip() == "INIT":
        print("Model: GPT-5.2 (Preview)")


def main() -> None:
    p = argparse.ArgumentParser(description="Genesis Wave: interference-driven evolutionary betting")
    p.add_argument("--population", type=int, default=800)
    p.add_argument("--generations", type=int, default=60)
    p.add_argument("--rounds", type=int, default=60)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--outdir", type=str, default="artifacts/genesis_wave_smoke")

    p.add_argument("--detectors", type=int, default=16)
    p.add_argument("--paths-min", type=int, default=2)
    p.add_argument("--paths-max", type=int, default=8)
    p.add_argument("--mag-scale", type=float, default=1.0)
    p.add_argument("--phase-pi-prob", type=float, default=0.50)
    p.add_argument("--regen", type=int, default=4)

    args = p.parse_args()

    outdir = Path(args.outdir)

    _banner("INIT", "Thiele Genesis Wave")

    _banner("DISCOVER")
    print("Interference oracle:")
    print(f"  detectors: {args.detectors}")
    print(f"  paths/detector: [{args.paths_min},{args.paths_max}]")
    print(f"  magnitudes: exponential(scale={args.mag_scale})")
    print(f"  hidden phase: sign=-1 with p={args.phase_pi_prob}")
    print(f"  fuel regen/round: {args.regen}")

    _banner("CLASSIFY")
    print(f"Population: {args.population}")
    print(f"Generations: {args.generations}  Rounds/gen: {args.rounds}")

    _banner("DECOMPOSE")
    print("Each agent runs real VM sandbox execution per round.")

    cfg = WaveConfig(
        seed=args.seed,
        population=args.population,
        generations=args.generations,
        rounds_per_generation=args.rounds,
        detectors=args.detectors,
        paths_min=args.paths_min,
        paths_max=args.paths_max,
        mag_scale=args.mag_scale,
        phase_pi_prob=args.phase_pi_prob,
        regen_per_round=args.regen,
        outdir=outdir,
    )

    _banner("EXECUTE")
    for _ in tqdm([0], desc="Genesis wave run"):
        outdir = run_genesis_wave(cfg)

    _banner("MERGE")
    print("Selection: elitism + mutation completed.")

    _banner("VERIFY")
    plot_path = plot_history(outdir)
    if plot_path is not None:
        print(f"Plot written: {plot_path}")

    _banner("SUCCESS")
    print(f"Artifacts: {outdir}")
    for name in ["config.json", "history.csv", "sample_genes.json", "plot.png"]:
        pth = outdir / name
        if pth.exists():
            print(f"  - {pth}")


if __name__ == "__main__":
    main()
