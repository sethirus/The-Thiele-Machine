#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Run Search Campaign

Systematic batch runner for extremal box search campaigns.
Runs large batches of searches across multiple scenarios.

Usage:
    python tools/run_search_campaign.py --scenarios 2x2x2x2,3x3x2x2 --runs-per-scenario 500 --mu-budget 10000

Outputs:
    artifacts/nl_search/campaigns/<campaign_id>/
        - summary.json: Overall campaign summary
        - scenario_*/: Per-scenario results
            - run_*/: Per-run results
            - extremal_candidates.json: Collected extremal candidates
"""

import argparse
import datetime
import hashlib
import json
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


@dataclass
class CampaignConfig:
    """Configuration for a search campaign."""
    scenarios: List[str] = field(default_factory=lambda: ["2x2x2x2"])
    runs_per_scenario: int = 100
    seed_start: int = 1
    mu_budget: int = 10000
    output_dir: Path = Path("artifacts/nl_search/campaigns")
    strategies: List[str] = field(default_factory=lambda: ["louvain", "spectral", "degree", "balanced"])
    parallel: int = 1
    emit_traces: bool = True


@dataclass
class RunResult:
    """Result from a single search run."""
    seed: int
    shape: Tuple[int, ...]
    bell_value: float
    is_extremal: bool
    canonical_hash: str
    mu_discovery: int
    mu_execution: int
    structure_verdict: str
    runtime_seconds: float
    success: bool = True
    error: Optional[str] = None


@dataclass
class ScenarioResult:
    """Aggregated result from a scenario."""
    shape: str
    total_runs: int
    successful_runs: int
    extremal_count: int
    best_bell_value: float
    best_hash: str
    average_bell_value: float
    average_runtime: float
    candidates: List[Dict[str, Any]] = field(default_factory=list)


def parse_shape(shape_str: str) -> Tuple[int, ...]:
    """Parse shape string like '2x2x2x2' into tuple."""
    parts = shape_str.lower().replace(',', 'x').split('x')
    return tuple(int(p.strip()) for p in parts)


def shape_to_str(shape: Tuple[int, ...]) -> str:
    """Convert shape tuple to string."""
    return 'x'.join(map(str, shape))


def generate_campaign_id() -> str:
    """Generate a unique campaign ID."""
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    random_suffix = hashlib.sha256(str(time.time()).encode()).hexdigest()[:6]
    return f"campaign_{timestamp}_{random_suffix}"


def run_single_search(
    shape: Tuple[int, ...],
    seed: int,
    mu_budget: int,
    strategies: List[str],
    output_dir: Path,
    emit_traces: bool
) -> RunResult:
    """Run a single extremal search and return the result."""
    shape_str = ','.join(map(str, shape))
    strategies_str = ','.join(strategies)
    
    start_time = time.time()
    
    cmd = [
        sys.executable,
        "tools/thiele_extremal_search.py",
        "--shape", shape_str,
        "--seed", str(seed),
        "--mu-budget", str(mu_budget),
        "--strategies", strategies_str,
        "--output", str(output_dir)
    ]
    
    if emit_traces:
        cmd.extend(["--emit-vm-trace", "--emit-rtl-trace"])
    
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=300  # 5 minute timeout per run
        )
        
        runtime = time.time() - start_time
        
        if result.returncode != 0:
            return RunResult(
                seed=seed,
                shape=shape,
                bell_value=0.0,
                is_extremal=False,
                canonical_hash="",
                mu_discovery=0,
                mu_execution=0,
                structure_verdict="ERROR",
                runtime_seconds=runtime,
                success=False,
                error=result.stderr[:500] if result.stderr else "Unknown error"
            )
        
        # Parse the summary file
        summary_path = output_dir / "search_summary.json"
        if summary_path.exists():
            with open(summary_path, 'r', encoding='utf-8') as f:
                summary = json.load(f)
            
            return RunResult(
                seed=seed,
                shape=shape,
                bell_value=summary.get("bell_value", 0.0),
                is_extremal=summary.get("is_extremal", False),
                canonical_hash=summary.get("canonical_hash", ""),
                mu_discovery=summary.get("mu_discovery", 0),
                mu_execution=summary.get("mu_execution", 0),
                structure_verdict=summary.get("structure_verdict", "UNKNOWN"),
                runtime_seconds=runtime,
                success=True
            )
        else:
            return RunResult(
                seed=seed,
                shape=shape,
                bell_value=0.0,
                is_extremal=False,
                canonical_hash="",
                mu_discovery=0,
                mu_execution=0,
                structure_verdict="NO_SUMMARY",
                runtime_seconds=runtime,
                success=False,
                error="No summary file generated"
            )
    
    except subprocess.TimeoutExpired:
        return RunResult(
            seed=seed,
            shape=shape,
            bell_value=0.0,
            is_extremal=False,
            canonical_hash="",
            mu_discovery=0,
            mu_execution=0,
            structure_verdict="TIMEOUT",
            runtime_seconds=300.0,
            success=False,
            error="Run timed out after 5 minutes"
        )
    except Exception as e:
        return RunResult(
            seed=seed,
            shape=shape,
            bell_value=0.0,
            is_extremal=False,
            canonical_hash="",
            mu_discovery=0,
            mu_execution=0,
            structure_verdict="EXCEPTION",
            runtime_seconds=time.time() - start_time,
            success=False,
            error=str(e)
        )


def run_scenario(
    shape_str: str,
    config: CampaignConfig,
    scenario_dir: Path
) -> ScenarioResult:
    """Run all searches for a single scenario."""
    shape = parse_shape(shape_str)
    scenario_dir.mkdir(parents=True, exist_ok=True)
    
    results: List[RunResult] = []
    candidates: List[Dict[str, Any]] = []
    
    print(f"\n  Running {config.runs_per_scenario} searches for {shape_str}...")
    
    for i in range(config.runs_per_scenario):
        seed = config.seed_start + i
        run_dir = scenario_dir / f"run_{seed:05d}"
        run_dir.mkdir(parents=True, exist_ok=True)
        
        result = run_single_search(
            shape=shape,
            seed=seed,
            mu_budget=config.mu_budget,
            strategies=config.strategies,
            output_dir=run_dir,
            emit_traces=config.emit_traces
        )
        
        results.append(result)
        
        # Collect extremal candidates
        if result.success and result.is_extremal:
            candidates.append({
                "seed": seed,
                "bell_value": result.bell_value,
                "canonical_hash": result.canonical_hash,
                "structure_verdict": result.structure_verdict,
                "run_dir": str(run_dir)
            })
        
        # Progress update
        if (i + 1) % 10 == 0 or (i + 1) == config.runs_per_scenario:
            success_count = sum(1 for r in results if r.success)
            extremal_count = sum(1 for r in results if r.is_extremal)
            print(f"    Progress: {i+1}/{config.runs_per_scenario} "
                  f"(success: {success_count}, extremal: {extremal_count})")
    
    # Aggregate results
    successful_results = [r for r in results if r.success]
    extremal_results = [r for r in results if r.is_extremal]
    
    best_result = max(successful_results, key=lambda r: r.bell_value) if successful_results else None
    
    scenario_result = ScenarioResult(
        shape=shape_str,
        total_runs=len(results),
        successful_runs=len(successful_results),
        extremal_count=len(extremal_results),
        best_bell_value=best_result.bell_value if best_result else 0.0,
        best_hash=best_result.canonical_hash if best_result else "",
        average_bell_value=sum(r.bell_value for r in successful_results) / len(successful_results) if successful_results else 0.0,
        average_runtime=sum(r.runtime_seconds for r in results) / len(results) if results else 0.0,
        candidates=candidates
    )
    
    # Save scenario summary
    scenario_summary = {
        "shape": shape_str,
        "total_runs": scenario_result.total_runs,
        "successful_runs": scenario_result.successful_runs,
        "extremal_count": scenario_result.extremal_count,
        "best_bell_value": scenario_result.best_bell_value,
        "best_hash": scenario_result.best_hash,
        "average_bell_value": scenario_result.average_bell_value,
        "average_runtime": scenario_result.average_runtime,
        "candidates": candidates
    }
    
    summary_path = scenario_dir / "scenario_summary.json"
    summary_path.write_text(json.dumps(scenario_summary, indent=2), encoding='utf-8')
    
    # Save candidates separately for easy access
    if candidates:
        candidates_path = scenario_dir / "extremal_candidates.json"
        candidates_path.write_text(json.dumps(candidates, indent=2), encoding='utf-8')
    
    return scenario_result


def run_campaign(config: CampaignConfig) -> Dict[str, Any]:
    """Run the full search campaign."""
    campaign_id = generate_campaign_id()
    campaign_dir = config.output_dir / campaign_id
    campaign_dir.mkdir(parents=True, exist_ok=True)
    
    print("=" * 60)
    print("SEARCH CAMPAIGN")
    print("=" * 60)
    print(f"Campaign ID: {campaign_id}")
    print(f"Output directory: {campaign_dir}")
    print(f"Scenarios: {config.scenarios}")
    print(f"Runs per scenario: {config.runs_per_scenario}")
    print(f"μ-budget: {config.mu_budget}")
    print(f"Total runs: {len(config.scenarios) * config.runs_per_scenario}")
    
    campaign_start = time.time()
    scenario_results: List[ScenarioResult] = []
    
    for scenario in config.scenarios:
        scenario_dir = campaign_dir / f"scenario_{scenario.replace(',', 'x')}"
        result = run_scenario(scenario, config, scenario_dir)
        scenario_results.append(result)
    
    campaign_runtime = time.time() - campaign_start
    
    # Aggregate campaign results
    total_runs = sum(s.total_runs for s in scenario_results)
    total_successful = sum(s.successful_runs for s in scenario_results)
    total_extremal = sum(s.extremal_count for s in scenario_results)
    
    # Collect all candidates across scenarios
    all_candidates = []
    for result in scenario_results:
        for candidate in result.candidates:
            candidate["scenario"] = result.shape
            all_candidates.append(candidate)
    
    # Sort by Bell value
    all_candidates.sort(key=lambda c: c.get("bell_value", 0.0), reverse=True)
    
    campaign_summary = {
        "campaign_id": campaign_id,
        "timestamp": datetime.datetime.now().isoformat(),
        "config": {
            "scenarios": config.scenarios,
            "runs_per_scenario": config.runs_per_scenario,
            "mu_budget": config.mu_budget,
            "seed_start": config.seed_start,
            "strategies": config.strategies
        },
        "results": {
            "total_runs": total_runs,
            "successful_runs": total_successful,
            "total_extremal_candidates": total_extremal,
            "campaign_runtime_seconds": campaign_runtime
        },
        "scenarios": [
            {
                "shape": s.shape,
                "total_runs": s.total_runs,
                "successful_runs": s.successful_runs,
                "extremal_count": s.extremal_count,
                "best_bell_value": s.best_bell_value,
                "best_hash": s.best_hash,
                "average_bell_value": s.average_bell_value
            }
            for s in scenario_results
        ],
        "top_candidates": all_candidates[:20]  # Top 20 overall
    }
    
    # Save campaign summary
    summary_path = campaign_dir / "campaign_summary.json"
    summary_path.write_text(json.dumps(campaign_summary, indent=2), encoding='utf-8')
    
    # Save all candidates
    if all_candidates:
        candidates_path = campaign_dir / "all_extremal_candidates.json"
        candidates_path.write_text(json.dumps(all_candidates, indent=2), encoding='utf-8')
    
    # Print summary
    print("\n" + "=" * 60)
    print("CAMPAIGN COMPLETE")
    print("=" * 60)
    print(f"Total runtime: {campaign_runtime:.1f}s")
    print(f"Total runs: {total_runs}")
    print(f"Successful: {total_successful}")
    print(f"Extremal candidates: {total_extremal}")
    
    print("\n--- Per-Scenario Summary ---")
    for s in scenario_results:
        print(f"  {s.shape}: {s.extremal_count}/{s.total_runs} extremal, "
              f"best Bell={s.best_bell_value:.4f}")
    
    if all_candidates:
        print("\n--- Top 5 Candidates ---")
        for c in all_candidates[:5]:
            print(f"  {c['canonical_hash']}: Bell={c['bell_value']:.4f} "
                  f"({c.get('scenario', 'unknown')})")
    
    print(f"\nResults saved to: {campaign_dir}")
    
    return campaign_summary


def main():
    parser = argparse.ArgumentParser(description="Run search campaign for extremal boxes")
    parser.add_argument(
        "--scenarios",
        type=str,
        default="2x2x2x2",
        help="Comma-separated list of scenarios (e.g., '2x2x2x2,3x3x2x2')"
    )
    parser.add_argument(
        "--runs-per-scenario",
        type=int,
        default=100,
        help="Number of runs per scenario"
    )
    parser.add_argument(
        "--seed-start",
        type=int,
        default=1,
        help="Starting seed value"
    )
    parser.add_argument(
        "--mu-budget",
        type=int,
        default=10000,
        help="μ-budget per run"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/nl_search/campaigns"),
        help="Output directory for campaigns"
    )
    parser.add_argument(
        "--strategies",
        type=str,
        default="louvain,spectral,degree,balanced",
        help="Comma-separated list of partition discovery strategies"
    )
    parser.add_argument(
        "--no-traces",
        action="store_true",
        help="Don't emit VM/RTL traces (faster)"
    )
    
    args = parser.parse_args()
    
    scenarios = [s.strip() for s in args.scenarios.split(",")]
    strategies = [s.strip() for s in args.strategies.split(",")]
    
    config = CampaignConfig(
        scenarios=scenarios,
        runs_per_scenario=args.runs_per_scenario,
        seed_start=args.seed_start,
        mu_budget=args.mu_budget,
        output_dir=args.output,
        strategies=strategies,
        emit_traces=not args.no_traces
    )
    
    run_campaign(config)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
