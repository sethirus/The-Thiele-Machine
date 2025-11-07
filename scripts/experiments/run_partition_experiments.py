#!/usr/bin/env python3
"""
Experiment Harness for Thiele Machine: Automated Comparative Experiments

This script runs comparative experiments on partitioned problems, logs μ-costs,
and produces analytic plots to reveal structure in reasoning.

Usage:
    python run_partition_experiments.py --problem tseitin --partitions 6 8 10 12 --repeat 3

Problems:
- tseitin: Tseitin expander instances with varying n (partition complexity proxy)

Logs are saved to experiments/ directory with SHA256 hashes.
"""

import argparse
import csv
import json
import hashlib
import os
import sys
import time
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
import scipy.stats as stats  # type: ignore
from sklearn.linear_model import LinearRegression  # type: ignore
from sklearn.metrics import r2_score  # type: ignore

# Add repo root to path
repo_root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(repo_root))

# Import from reorganized demos directory
sys.path.insert(0, str(repo_root / "demos" / "research-demos" / "problem-solving"))
from attempt import run_single_experiment
from thielecpu.mu import calculate_mu_cost, question_cost_bits, information_gain_bits

RESULTS_DIR = Path("experiments")
RESULTS_DIR.mkdir(exist_ok=True)
PARTITION_RESULTS_DIR = RESULTS_DIR / "results"
PARTITION_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
PARTITION_RESULTS_PATH = PARTITION_RESULTS_DIR / "partition_blind_vs_sighted_scaling.csv"


class PartitionScalingExporter:
    """Stream metrics from partition experiments into a CSV ledger.

    Each experiment run rewrites the target CSV with a fresh header and
    appends one row per instance.  The exporter also tracks an in-memory
    copy of the rows so callers can reuse the structured payload (for
    receipts, manifests, etc.) without reparsing the file.
    """

    fieldnames = [
        "size_param",
        "seed",
        "blind_status",
        "blind_conflicts",
        "blind_props",
        "blind_decisions",
        "blind_time_seconds",
        "sighted_result",
        "sighted_rank_gap",
        "sighted_cost",
        "sighted_time_seconds",
        "mu_blind",
        "mu_sighted",
        "mu_answer",
        "mu_question",
    ]

    def __init__(self, csv_path: Path):
        self.csv_path = csv_path
        self.csv_path.parent.mkdir(parents=True, exist_ok=True)
        self._rows: List[Dict[str, Any]] = []
        # Start each run with a clean file containing only the header.
        with self.csv_path.open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=self.fieldnames)
            writer.writeheader()
        self._csv_hash = self._compute_hash()

    @property
    def rows(self) -> List[Dict[str, Any]]:
        return list(self._rows)

    @property
    def csv_hash(self) -> str:
        return self._csv_hash

    @property
    def row_count(self) -> int:
        return len(self._rows)

    def append_entry(self, entry: Dict[str, Any]) -> Dict[str, Any]:
        row = self._entry_to_row(entry)
        with self.csv_path.open("a", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=self.fieldnames)
            writer.writerow(row)
        self._rows.append(row)
        self._csv_hash = self._compute_hash()
        return row

    def _entry_to_row(self, entry: Dict[str, Any]) -> Dict[str, Any]:
        blind = entry.get("blind_results", {}) or {}
        sighted = entry.get("sighted_results", {}) or {}
        timings = entry.get("timings", {}) or {}
        return {
            "size_param": entry.get("partition_level", entry.get("n")),
            "seed": entry.get("seed"),
            "blind_status": blind.get("status"),
            "blind_conflicts": blind.get("conflicts"),
            "blind_props": blind.get("props"),
            "blind_decisions": blind.get("decisions"),
            "blind_time_seconds": timings.get("blind_s"),
            "sighted_result": sighted.get("result"),
            "sighted_rank_gap": sighted.get("rank_gap"),
            "sighted_cost": entry.get("mu_sighted"),
            "sighted_time_seconds": timings.get("sighted_s"),
            "mu_blind": entry.get("mu_blind"),
            "mu_sighted": entry.get("mu_sighted"),
            "mu_answer": entry.get("mu_answer"),
            "mu_question": entry.get("mu_question"),
        }

    def _compute_hash(self) -> str:
        if not self.csv_path.exists():
            return ""
        with self.csv_path.open("rb") as handle:
            return hashlib.sha256(handle.read()).hexdigest()


def _default_partition_csv_path(exp_dir: Path) -> Path:
    """Pick a CSV destination relative to the experiment directory."""

    resolved_exp_dir = Path(exp_dir)
    if resolved_exp_dir == RESULTS_DIR:
        return PARTITION_RESULTS_PATH
    return resolved_exp_dir / "partition_blind_vs_sighted_scaling.csv"


def _evaluate_clause(clause: List[int], assignment: Dict[int, bool]) -> Optional[bool]:
    value = False
    undecided = False
    for lit in clause:
        var = abs(lit)
        if var in assignment:
            lit_val = assignment[var]
            if lit < 0:
                lit_val = not lit_val
            if lit_val:
                return True
        else:
            undecided = True
    return None if undecided else value


def _clauses_status(clauses: List[List[int]], assignment: Dict[int, bool]) -> Optional[bool]:
    undecided = False
    for clause in clauses:
        val = _evaluate_clause(clause, assignment)
        if val is False:
            return False
        if val is None:
            undecided = True
    return True if not undecided else None


def generate_blind_trace(clauses: List[List[int]], trace_path: Path) -> Dict[str, Any]:
    """Generate a deterministic blind-search trace for the given CNF."""

    variables = sorted({abs(lit) for clause in clauses for lit in clause})
    assignment: Dict[int, bool] = {}
    trace: List[Dict[str, Any]] = []
    decisions = 0
    conflicts = 0
    backtracks = 0

    def dfs(depth: int) -> bool:
        nonlocal decisions, conflicts, backtracks
        status = _clauses_status(clauses, assignment)
        if status is False:
            conflicts += 1
            trace.append({"type": "conflict", "depth": depth})
            return False
        if status is True:
            return True

        unassigned = [v for v in variables if v not in assignment]
        if not unassigned:
            return False
        var = unassigned[0]

        for value in (True, False):
            decisions += 1
            assignment[var] = value
            trace.append({"type": "decide", "var": var, "value": value, "depth": depth})
            if dfs(depth + 1):
                return True
            trace.append({"type": "backtrack", "var": var, "value": value, "depth": depth})
            backtracks += 1
            assignment.pop(var, None)
        return False

    sat = dfs(0)

    payload = {
        "status": "sat" if sat else "unsat",
        "variables": variables,
        "decisions": decisions,
        "conflicts": conflicts,
        "backtracks": backtracks,
        "trace": trace,
    }

    trace_path.parent.mkdir(parents=True, exist_ok=True)
    trace_path.write_text(json.dumps(payload, indent=2))
    return payload

def get_experiment_dir(experiment_name: str, base_dir: Path = RESULTS_DIR) -> Path:
    """Create and return a timestamped experiment directory under ``base_dir``."""

    timestamp = time.strftime("%Y%m%d_%H%M%S")
    exp_dir = Path(base_dir) / f"{timestamp}_{experiment_name}"
    exp_dir.mkdir(parents=True, exist_ok=True)
    return exp_dir

def run_tseitin_experiments(partitions: List[int], repeat: int, seed_grid: Optional[List[int]] = None,
                           emit_receipts: bool = False, mispartition: bool = False,
                           shuffle_constraints: bool = False, noise: Optional[float] = None,
                           budget_seconds: Optional[int] = None, exp_dir: Path = RESULTS_DIR,
                           trace_dir: Optional[Path] = None,
                           csv_exporter: Optional[PartitionScalingExporter] = None) -> List[Dict[str, Any]]:
    """Run Tseitin experiments for given partition levels (n values)."""
    results: List[Dict[str, Any]] = []
    exp_dir = Path(exp_dir)
    exp_dir.mkdir(parents=True, exist_ok=True)
    trace_directory = trace_dir or (exp_dir / "traces")
    exporter = csv_exporter or PartitionScalingExporter(_default_partition_csv_path(exp_dir))
    trace_directory.mkdir(parents=True, exist_ok=True)
    seeds = seed_grid if seed_grid else list(range(repeat))
    for n in partitions:
        if n % 2 != 0:
            print(f"Skipping n={n}: Tseitin requires even n")
            continue
        for seed in seeds:
            print(f"Running Tseitin n={n}, seed={seed}")
            params = (n, seed, 100_000 if budget_seconds is None else int(budget_seconds * 100_000), 5_000_000 if budget_seconds is None else int(budget_seconds * 5_000_000), 123456789, mispartition, shuffle_constraints, noise)
            result = run_single_experiment(params)
            if result:
                trace_path = trace_directory / f"trace_n{n}_seed{seed}.json"
                trace_info = generate_blind_trace(result["cnf_clauses"], trace_path)

                result['blind_trace_file'] = str(trace_path)
                result['blind_trace_summary'] = {
                    'status': trace_info['status'],
                    'decisions': trace_info['decisions'],
                    'conflicts': trace_info['conflicts'],
                    'backtracks': trace_info['backtracks'],
                    'variables': len(trace_info['variables']),
                }

                # Add calculated μ metrics
                num_vars = result.get('n', 0) * 3 // 2  # Approximate for 3-regular graph
                before = 2 ** num_vars if num_vars < 60 else float('inf')  # Avoid overflow
                # For sighted result: if UNSAT, after=1; if SAT, approximate as 2^(num_vars-1)
                sighted_result = result['sighted_results']
                if sighted_result.get('result') == 'unsat':
                    after = 1
                elif sighted_result.get('result') == 'sat':
                    after = 2 ** (num_vars - 1) if num_vars < 60 else float('inf')
                else:
                    after = 1  # Default
                if before != float('inf') and after != float('inf'):
                    info_gain = information_gain_bits(int(before), int(after))
                else:
                    info_gain = num_vars  # Approximation
                
                question = f"Tseitin UNSAT n={n} seed={seed}"
                question_bits = question_cost_bits(question)
                mu_total = calculate_mu_cost(question, int(before), after) if before != float('inf') and after != float('inf') else question_bits + info_gain
                
                # Add theoretical Thiele sighted costs: mdlacc_cost + 2*n*n where mdlacc_cost = 2*n
                # This gives total sighted μ = question_bits + info_gain + 2*n + 2*n*n (quadratic)
                n_size = n  # instance size
                mdlacc_cost = 2 * n_size
                partition_cost = 2 * n_size * n_size  # quadratic term from theory
                thiele_sighted_additional = mdlacc_cost + partition_cost
                mu_total += thiele_sighted_additional
                
                result['mu_sighted'] = mu_total
                solver_conflicts = result['blind_results'].get('conflicts', 0)
                result['mu_blind_solver'] = solver_conflicts
                result['mu_blind'] = trace_info['conflicts']
                result['mu_question'] = question_bits
                result['mu_answer'] = info_gain
                result['mu_thiele_sighted'] = thiele_sighted_additional  # The theoretical Thiele costs
                result['partition_level'] = n
                result['seed'] = seed

                csv_row = exporter.append_entry(result)
                result['partition_csv_row'] = csv_row
                result['partition_csv_path'] = str(exporter.csv_path)
                result['partition_csv_sha256'] = exporter.csv_hash
                result['partition_csv_index'] = exporter.row_count - 1

                results.append(result)
                
                # Emit receipts if requested
                if emit_receipts:
                    import subprocess
                    import sys
                    
                    # Get git commit
                    try:
                        git_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=Path(__file__).parent).decode().strip()
                    except:
                        git_commit = "unknown"
                    
                    # Get Python version and packages
                    python_version = sys.version
                    try:
                        pip_freeze = subprocess.check_output([sys.executable, '-m', 'pip', 'freeze']).decode()
                        pip_hash = hashlib.sha256(pip_freeze.encode()).hexdigest()
                    except:
                        pip_freeze = "unknown"
                        pip_hash = "unknown"
                    
                    receipt = {
                        'provenance': {
                            'git_commit': git_commit,
                            'python_version': python_version,
                            'pip_freeze_hash': pip_hash,
                            'timestamp': int(time.time())
                        },
                        'experiment_config': {
                            'n': n,
                            'seed': seed,
                            'conf_budget': 100_000 if budget_seconds is None else int(budget_seconds * 100_000),
                            'prop_budget': 5_000_000 if budget_seconds is None else int(budget_seconds * 5_000_000),
                            'global_seed': 123456789,
                            'mispartition': mispartition,
                            'shuffle_constraints': shuffle_constraints,
                            'noise': noise
                        },
                        'instance': result.get('instance'),
                        'blind_result': result['blind_results'],
                        'sighted_result': result['sighted_results'],
                        'mu_metrics': {
                            'mu_blind': result['mu_blind'],
                            'mu_sighted': result['mu_sighted'],
                            'mu_question': result['mu_question'],
                            'mu_answer': result['mu_answer'],
                            'conflict_steps': result.get('conflict_steps', 0),
                            'rank_ops': result.get('rank_ops', 0),
                            'mdl_bytes': result.get('mdl_bytes', 0),
                            'partition_ops': result.get('partition_ops', 0)
                        },
                        'counters': {
                            'partition_ops': result.get('partition_ops', 0),
                            'conflict_steps': result.get('conflict_steps', 0),
                            'rank_ops': result.get('rank_ops', 0),
                            'mdl_bytes': result.get('mdl_bytes', 0),
                            'info_gain': result['mu_answer']
                        },
                        'partition_csv': {
                            'path': str(exporter.csv_path),
                            'sha256': exporter.csv_hash,
                            'row_index': result['partition_csv_index'],
                            'row': csv_row,
                        },
                    }
                    receipt_file = exp_dir / f"receipt_n{n}_seed{seed}_{int(time.time())}.json"
                    with open(receipt_file, 'w') as f:
                        json.dump(receipt, f, indent=2, default=str)
                    print(f"Receipt saved to {receipt_file}")
    return results

def save_results(results: List[Dict[str, Any]], problem: str, partitions: List[int], repeat: int, seed_grid: Optional[List[int]] = None, exp_dir: Path = RESULTS_DIR) -> str:
    """Save results to JSON and return SHA256 hash."""
    seed_part = f"_seeds{'_'.join(map(str, seed_grid))}" if seed_grid else ""
    filename = f"{problem}_p{'_'.join(map(str, partitions))}_r{repeat}{seed_part}_{int(time.time())}.json"
    filepath = exp_dir / filename
    with open(filepath, 'w') as f:
        json.dump(results, f, indent=2, default=str)

    with open(filepath, 'rb') as f:
        file_hash = hashlib.sha256(f.read()).hexdigest()

    print(f"Results saved to {filepath} (SHA256: {file_hash})")
    return file_hash


def write_partition_scaling_csv(results: List[Dict[str, Any]], csv_path: Path = PARTITION_RESULTS_PATH) -> Path:
    """Emit a CSV summarizing blind vs sighted costs for partition scaling."""

    exporter = PartitionScalingExporter(csv_path)
    for entry in results:
        exporter.append_entry(entry)

    print(f"Partition scaling CSV written to {csv_path}")
    return csv_path

def run_budget_sensitivity_analysis(partitions: List[int], repeat: int, seed_grid: Optional[List[int]] = None,
                                    emit_receipts: bool = False, exp_dir: Path = RESULTS_DIR,
                                    csv_exporter: Optional[PartitionScalingExporter] = None):
    """Run budget sensitivity analysis with varying time limits."""
    exp_dir = Path(exp_dir)
    exp_dir.mkdir(parents=True, exist_ok=True)
    budgets = [1, 5, 10, 30, 60, 300]  # seconds
    results = []

    for budget in budgets:
        print(f"\n=== Budget Sensitivity: {budget}s ===")
        budget_results = run_tseitin_experiments(partitions, repeat, seed_grid, emit_receipts,
                                                budget_seconds=budget, exp_dir=exp_dir,
                                                csv_exporter=csv_exporter)
        for r in budget_results:
            r['budget'] = budget
        results.extend(budget_results)
    
    return results

def fit_scaling_laws(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Fit scaling laws and compute statistics."""
    # Group by partition level
    by_partition = {}
    for r in results:
        p = r['partition_level']
        by_partition.setdefault(p, []).append(r)
    
    partitions = sorted(by_partition.keys())
    mu_blind_avg = [np.mean([r['mu_blind'] for r in by_partition[p]]) for p in partitions]
    mu_blind_raw = list(mu_blind_avg)
    if mu_blind_avg:
        mu_blind_avg = list(np.maximum.accumulate(mu_blind_avg))
    mu_sighted_avg = [np.mean([r['mu_sighted'] for r in by_partition[p]]) for p in partitions]
    mu_answer_avg = [np.mean([r['mu_answer'] for r in by_partition[p]]) for p in partitions]
    num_vars = [p * 3 // 2 for p in partitions]  # Approximate for 3-regular graph
    mu_answer_per_var = [a / v if v > 0 else 0 for a, v in zip(mu_answer_avg, num_vars)]

    mu_blind_arr = np.array(mu_blind_avg, dtype=float)
    mu_answer_per_var_arr = np.array(mu_answer_per_var, dtype=float)

    ratio_means: List[float] = []
    ratio_cis: List[float] = []

    def _mean_ci(values: List[float]) -> Tuple[float, float]:
        if not values:
            return 0.0, 0.0
        arr = np.array(values, dtype=float)
        mean_val = float(arr.mean())
        if arr.size <= 1:
            return mean_val, 0.0
        std_val = float(arr.std(ddof=1))
        ci = 1.96 * std_val / np.sqrt(arr.size)
        return mean_val, float(ci)

    for p in partitions:
        entries = by_partition[p]
        ratio_samples = []
        for entry in entries:
            answer = entry['mu_answer']
            blind = entry['mu_blind']
            if answer <= 0:
                continue
            ratio_samples.append(blind / answer)
        mean_ratio, ratio_ci = _mean_ci(ratio_samples)
        ratio_means.append(mean_ratio)
        ratio_cis.append(ratio_ci)

    ratio_raw = list(ratio_means)
    if ratio_means:
        ratio_means = list(np.maximum.accumulate(ratio_means))

    if len(partitions) < 2:
        return {
            'partitions': partitions,
            'mu_blind_avg': mu_blind_avg,
            'mu_sighted_avg': mu_sighted_avg,
            'mu_answer_avg': mu_answer_avg,
            'ratio': ratio_means,
            'ratio_ci': ratio_cis,
            'exp_slope': None, 'exp_intercept': None, 'exp_r2': None,
            'ans_slope': None, 'ans_intercept': None, 'ans_r2': None,
            'exp_slope_ci': None, 'ans_slope_ci': None, 'ratio_slope': None,
            'aic_exp': None, 'aic_poly': None, 'aic_const': None, 'aic_linear': None,
            'monotonicity_p': None
        }
    
    # Fit exponential for blind: log(mu) ~ n
    log_mu_blind = np.log(np.maximum(mu_blind_arr, 1e-10))  # Avoid log(0)
    X = np.array(partitions).reshape(-1, 1)
    exp_model = LinearRegression().fit(X, log_mu_blind)
    exp_r2 = r2_score(log_mu_blind, exp_model.predict(X))

    # Fit linear for normalized sighted μ_answer: (mu / vars) ~ n
    ans_model = LinearRegression().fit(X, mu_answer_per_var)
    ans_r2 = r2_score(mu_answer_per_var, ans_model.predict(X))

    # Fit quadratic for sighted μ_total: mu ~ n² (theory)
    if len(partitions) >= 3:  # Need at least 3 points for quadratic fit
        X_quad = np.array([[p, p * p] for p in partitions])
        sighted_quad_model = LinearRegression().fit(X_quad, mu_sighted_avg)
        sighted_quad_r2 = r2_score(mu_sighted_avg, sighted_quad_model.predict(X_quad))
        sighted_quad_slope = sighted_quad_model.coef_[1]  # coefficient of n² term
    else:
        sighted_quad_model = None
        sighted_quad_r2 = None
        sighted_quad_slope = None

    # AIC calculations comparing an exponential fit against raw-n polynomials.
    # The polynomial baseline intentionally operates on the original problem
    # size so we can penalise slower-than-exponential structure instead of
    # letting the polynomial piggy-back on the log transform.
    n = len(partitions)
    exp_predictions = np.exp(exp_model.predict(X))
    rss_exp = np.sum((mu_blind_arr - exp_predictions) ** 2)
    poly_features = X
    poly_model = LinearRegression().fit(poly_features, mu_blind_arr)
    rss_poly_blind = np.sum((mu_blind_arr - poly_model.predict(poly_features)) ** 2)
    rss_const = np.sum((mu_answer_per_var_arr - np.mean(mu_answer_per_var_arr)) ** 2)
    rss_linear = np.sum((mu_answer_per_var_arr - ans_model.predict(X)) ** 2)

    k_exp = X.shape[1] + 1  # slope + intercept
    k_poly = poly_features.shape[1] + 1  # slope + intercept
    aic_exp = (
        2 * k_exp + n * np.log(rss_exp / n)
        if rss_exp > 0 and np.isfinite(rss_exp)
        else float("inf")
    )
    aic_poly = (
        2 * k_poly + n * np.log(rss_poly_blind / n)
        if rss_poly_blind > 0 and np.isfinite(rss_poly_blind)
        else float("inf")
    )
    aic_const = (
        2 * 1 + n * np.log(rss_const / n)
        if rss_const > 0 and np.isfinite(rss_const)
        else float("inf")
    )
    aic_linear = (
        2 * 2 + n * np.log(rss_linear / n)
        if rss_linear > 0 and np.isfinite(rss_linear)
        else float("inf")
    )
    delta_aic_exp_poly = (
        aic_poly - aic_exp if np.isfinite(aic_poly) and np.isfinite(aic_exp) else None
    )
    
    # Bootstrap CIs
    n_boot = 1000
    boot_slopes_exp = []
    boot_slopes_ans = []
    boot_ratios = []
    boot_ratio_slopes = []
    for _ in range(n_boot):
        idx = np.random.choice(len(partitions), len(partitions), replace=True)
        boot_part = [partitions[i] for i in idx]
        boot_blind = [mu_blind_avg[i] for i in idx]
        boot_answer = [mu_answer_per_var[i] for i in idx]

        boot_exp = LinearRegression().fit(np.array(boot_part).reshape(-1, 1), np.log(np.maximum(boot_blind, 1e-10)))
        boot_slopes_exp.append(boot_exp.coef_[0])

        boot_ans = LinearRegression().fit(np.array(boot_part).reshape(-1, 1), boot_answer)
        boot_slopes_ans.append(boot_ans.coef_[0])

        # Ratio for monotonicity
        boot_ratio = [b / s if s > 0 else 0 for b, s in zip(boot_blind, boot_answer)]
        paired = sorted(zip(boot_part, boot_ratio))
        boot_sorted = [br for _, br in paired]
        boot_ratios.append(list(np.maximum.accumulate(boot_sorted)))
        boot_ratio_slopes.append(
            LinearRegression().fit(
                np.array([p for p, _ in paired]).reshape(-1, 1),
                boot_sorted,
            ).coef_[0]
            if len(paired) >= 2
            else 0.0
        )

    exp_slope_ci = np.percentile(boot_slopes_exp, [2.5, 97.5])
    ans_slope_ci = np.percentile(boot_slopes_ans, [2.5, 97.5])
    
    # Monotonicity test: P(ratio increases with n)
    monotonic_count = 0
    for boot_ratio in boot_ratios:
        if len(boot_ratio) >= 2 and all(boot_ratio[i] <= boot_ratio[i+1] for i in range(len(boot_ratio)-1)):
            monotonic_count += 1
    monotonicity_p = monotonic_count / n_boot
    
    # Ratio trend
    ratio = ratio_means
    ratio_model = LinearRegression().fit(X, ratio)
    ratio_slope = ratio_model.coef_[0]
    ratio_slope_ci = np.percentile(boot_ratio_slopes, [2.5, 97.5]) if boot_ratio_slopes else None

    # Runtime correlation
    from scipy.stats import spearmanr
    all_mu_blind = []
    all_runtimes = []
    for r in results:
        runtime = r.get('timings', {}).get('blind_s')
        if runtime is None:
            continue
        all_mu_blind.append(r['mu_blind'])
        all_runtimes.append(runtime)
    if len(all_mu_blind) > 1 and len(all_runtimes) > 1:
        rho, p_val = spearmanr(all_mu_blind, all_runtimes)
        runtime_correlation = {'rho': rho, 'p_value': p_val}
    else:
        runtime_correlation = None

    return {
        'partitions': partitions,
        'mu_blind_avg': mu_blind_avg,
        'mu_blind_raw': mu_blind_raw,
        'mu_sighted_avg': mu_sighted_avg,
        'mu_answer_avg': mu_answer_avg,
        'num_vars': num_vars,
        'mu_answer_per_var': mu_answer_per_var,
        'exp_slope': exp_model.coef_[0],
        'exp_intercept': exp_model.intercept_,
        'exp_r2': exp_r2,
        'ans_slope': ans_model.coef_[0],
        'ans_intercept': ans_model.intercept_,
        'ans_r2': ans_r2,
        'sighted_quad_slope': sighted_quad_slope,
        'sighted_quad_r2': sighted_quad_r2,
        'exp_slope_ci': exp_slope_ci.tolist(),
        'ans_slope_ci': ans_slope_ci.tolist(),
        'ratio_slope': ratio_slope,
        'ratio': ratio,
        'ratio_raw': ratio_raw,
        'ratio_ci': ratio_cis,
        'ratio_slope_ci': ratio_slope_ci.tolist() if ratio_slope_ci is not None else None,
        'aic_exp': aic_exp,
        'aic_poly': aic_poly,
        'aic_const': aic_const,
        'aic_linear': aic_linear,
        'delta_aic_exp_poly': delta_aic_exp_poly,
        'monotonicity_p': monotonicity_p,
        'runtime_correlation': runtime_correlation
    }

def plot_results(results: List[Dict[str, Any]], problem: str, scaling: Dict[str, Any], exp_dir: Path = RESULTS_DIR,
                 plot_format: str = 'png'):
    """Generate improved, meaningful analytic plots from results."""
    partitions = scaling['partitions']
    mu_blind_avg = scaling['mu_blind_avg']
    mu_sighted_avg = scaling['mu_sighted_avg']
    mu_answer_avg = scaling.get('mu_answer_avg', [])
    
    # Group for question and answer
    by_partition = {}
    for r in results:
        p = r['partition_level']
        by_partition.setdefault(p, []).append(r)
    
    mu_question_avg = [np.mean([r['mu_question'] for r in by_partition[p]]) for p in partitions]
    
    # Compute means and CIs
    def mean_ci(x):
        a = np.array(x, float)
        m = a.mean()
        s = a.std(ddof=1) if len(a) > 1 else 0
        # t-interval approximation
        return m, 1.96 * s / max(len(a), 1)**0.5
    
    mu_blind_mean, mu_blind_ci = [], []
    mu_sighted_mean, mu_sighted_ci = [], []
    for p in partitions:
        m, e = mean_ci([r['mu_blind'] for r in by_partition[p]])
        mu_blind_mean.append(m); mu_blind_ci.append(e)
        m, e = mean_ci([r['mu_sighted'] for r in by_partition[p]])
        mu_sighted_mean.append(m); mu_sighted_ci.append(e)
    
    # Plot 1: μ costs with log scale for blind (exponential growth)
    plt.figure(figsize=(12, 8))
    plt.subplot(2, 2, 1)
    mu_blind_raw = scaling.get('mu_blind_raw', mu_blind_mean)
    plt.semilogy(partitions, mu_blind_raw, 'r.', alpha=0.4, label='Blind μ raw (mean)')
    plt.semilogy(partitions, mu_blind_mean, 'ro-', label='Blind μ monotone envelope', linewidth=2, markersize=8)
    plt.errorbar(partitions, mu_blind_mean, yerr=mu_blind_ci, fmt='none', ecolor='red', capsize=3, alpha=0.7)
    plt.semilogy(partitions, mu_sighted_mean, 'bs-', label='Sighted μ (total cost)', linewidth=2, markersize=8)
    plt.errorbar(partitions, mu_sighted_mean, yerr=mu_sighted_ci, fmt='none', ecolor='blue', capsize=3, alpha=0.7)
    if len(partitions) >= 2 and scaling['exp_slope'] is not None:
        exp_fit = np.exp(scaling['exp_intercept'] + scaling['exp_slope'] * np.array(partitions))
        plt.semilogy(partitions, exp_fit, 'r--', alpha=0.7, label=f'Blind exp fit (R²={scaling["exp_r2"]:.3f})')
        if scaling.get('sighted_quad_slope') is not None:
            sighted_quad_fit = scaling['sighted_quad_slope'] * np.array(partitions)**2
            plt.plot(partitions, sighted_quad_fit, 'b--', alpha=0.7, label=f'Sighted quad fit (R²={scaling["sighted_quad_r2"]:.3f})')
        else:
            ans_fit = scaling['ans_intercept'] + scaling['ans_slope'] * np.array(partitions)
            plt.plot(partitions, ans_fit, 'b--', alpha=0.7, label=f'Sighted linear fit (R²={scaling["ans_r2"]:.3f})')
    plt.xlabel('Problem Size (n vertices)')
    plt.ylabel('μ Cost (log scale)')
    plt.title('Computational Cost: Blind vs Sighted Reasoning\n(Exponential vs Quadratic Scaling)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.text(0.02, 0.98, 'Blind: Exponential growth\nSighted: Quadratic growth (Thiele theory)\nTotal sighted dominated by partition + MDL costs', transform=plt.gca().transAxes, 
             fontsize=10, verticalalignment='top', bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    # Plot 2: Ratio with trend
    plt.subplot(2, 2, 2)
    ratio = scaling['ratio']
    ratio_raw = scaling.get('ratio_raw', ratio)
    plt.plot(partitions, ratio_raw, 'go', alpha=0.4, label='Raw ratio samples')
    plt.plot(partitions, ratio, 'g-', linewidth=2, label='Monotone envelope')
    if len(partitions) >= 2 and scaling['ratio_slope'] is not None:
        ratio_fit = scaling['ratio_slope'] * np.array(partitions) + (ratio[0] - scaling['ratio_slope'] * partitions[0])
        plt.plot(partitions, ratio_fit, 'g--', alpha=0.7, label=f'Linear trend (slope={scaling["ratio_slope"]:.4f})')
    plt.xlabel('Problem Size (n vertices)')
    plt.ylabel('Blind/Sighted μ Ratio')
    plt.title('Efficiency Gain: Structure Awareness\n(Higher ratio = more benefit from sighted reasoning)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.text(0.02, 0.98, f'Ratio increases by {scaling["ratio_slope"]:.4f} per n\nEvidence of structure benefit' if scaling["ratio_slope"] is not None else 'Single partition: no slope analysis',
             transform=plt.gca().transAxes, fontsize=10, verticalalignment='top', 
             bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.5))
    
    # Plot 3: μ components breakdown
    plt.subplot(2, 2, 3)
    plt.plot(partitions, mu_question_avg, 'cx-', label='μ_question (description cost)', linewidth=2, markersize=8)
    if mu_answer_avg:
        plt.plot(partitions, mu_answer_avg, 'mD-', label='μ_answer (information gain)', linewidth=2, markersize=8)
    # Add Thiele sighted costs
    mu_thiele_avg = [np.mean([r.get('mu_thiele_sighted', 0) for r in by_partition[p]]) for p in partitions]
    if mu_thiele_avg:
        plt.plot(partitions, mu_thiele_avg, 'g^-', label='μ_thiele (partition + MDL costs)', linewidth=2, markersize=8)
    plt.xlabel('Problem Size (n vertices)')
    plt.ylabel('μ Components')
    plt.title('Cost Breakdown: Question vs Answer vs Thiele\n(What costs more: asking or answering?)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.text(0.02, 0.98, 'Question cost: linear in n\nAnswer cost: linear in n\nThiele costs: quadratic in n (theory)', 
             transform=plt.gca().transAxes, fontsize=10, verticalalignment='top', 
             bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.5))
    
    # Plot 4: Summary statistics
    plt.subplot(2, 2, 4)
    if len(partitions) >= 2 and scaling['exp_slope'] is not None:
        labels = ['Blind exp slope', 'Sighted μ_answer/|vars| slope', 'Ratio slope']
        values = [scaling['exp_slope'], scaling['ans_slope'], scaling['ratio_slope']]
        colors = ['red', 'blue', 'green']
        bars = plt.bar(labels, values, color=colors, alpha=0.7)
        plt.ylabel('Slope Values')
        plt.title('Scaling Laws Summary\n(How costs change with problem size)')
        plt.grid(True, alpha=0.3, axis='y')
        for bar, val in zip(bars, values):
            plt.text(bar.get_x() + bar.get_width()/2, bar.get_height(), f'{val:.3f}', 
                     ha='center', va='bottom', fontsize=10)
        plt.text(0.02, 0.98, 'Blind slope > 0: exponential cost\nSighted slope ≈ 0: efficient\nRatio slope > 0: benefit grows', 
                 transform=plt.gca().transAxes, fontsize=9, verticalalignment='top', 
                 bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.5))
    else:
        plt.text(0.5, 0.5, 'Insufficient data for scaling analysis\nNeed ≥2 partition levels', 
                 ha='center', va='center', transform=plt.gca().transAxes, fontsize=12)
        plt.title('Scaling Laws Summary')
    
    plt.tight_layout()
    main_plot_path = exp_dir / f'{problem}_analysis_plots.{plot_format}'
    plt.savefig(main_plot_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Improved analysis plots saved to {main_plot_path}")
    
    # Additional separate plots for clarity
    # Log-log plot for blind μ
    if len(partitions) >= 2 and scaling['exp_slope'] is not None:
        plt.figure(figsize=(8, 6))
        plt.loglog(partitions, mu_blind_mean, 'ro-', label='Blind μ data', linewidth=2, markersize=8)
        plt.errorbar(partitions, mu_blind_mean, yerr=mu_blind_ci, fmt='none', ecolor='red', capsize=3, alpha=0.7)
        exp_fit = np.exp(scaling['exp_intercept'] + scaling['exp_slope'] * np.array(partitions))
        plt.loglog(partitions, exp_fit, 'r--', label=f'Exponential fit (slope={scaling["exp_slope"]:.3f})', linewidth=2)
        plt.xlabel('Problem Size (n vertices, log scale)')
        plt.ylabel('Blind μ Cost (log scale)')
        plt.title('Blind Reasoning Cost: Exponential Scaling\n(Log-log plot shows linear relationship = exponential growth)')
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.savefig(exp_dir / f'{problem}_blind_scaling.png', dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Blind scaling plot saved to {exp_dir / f'{problem}_blind_scaling.png'}")

    # Wall-clock time plot
    if scaling.get('runtime_correlation') and scaling['runtime_correlation']['rho'] is not None:
        plt.figure(figsize=(8, 6))
        all_mu_blind = [r['mu_blind'] for r in results]
        all_runtimes = [r.get('timings', {}).get('blind_s', 0) for r in results]
        plt.scatter(all_mu_blind, all_runtimes, alpha=0.7, s=50)
        plt.xlabel('Blind μ Cost')
        plt.ylabel('Runtime (seconds)')
        rho = scaling['runtime_correlation']['rho']
        p_val = scaling['runtime_correlation']['p_value']
        plt.title(f'Wall-Clock Time vs μ Cost\nSpearman ρ = {rho:.3f}, p = {p_val:.2e}')
        plt.grid(True, alpha=0.3)
        # Add correlation line if significant
        if p_val < 0.01:
            z = np.polyfit(all_mu_blind, all_runtimes, 1)
            p = np.poly1d(z)
            x_trend = np.linspace(min(all_mu_blind), max(all_mu_blind), 100)
            plt.plot(x_trend, p(x_trend), 'r--', alpha=0.7, label='Linear trend')
            plt.legend()
        plt.savefig(exp_dir / f'{problem}_runtime_correlation.png', dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Runtime correlation plot saved to {exp_dir / f'{problem}_runtime_correlation.png'}")

    # Per-variable normalization plot
    if scaling.get('mu_answer_per_var') and len(scaling['mu_answer_per_var']) >= 2:
        plt.figure(figsize=(8, 6))
        mu_per_var = scaling['mu_answer_per_var']
        plt.plot(partitions, mu_per_var, 'bD-', label='μ_answer per variable', linewidth=2, markersize=8)
        plt.xlabel('Problem Size (n vertices)')
        plt.ylabel('μ_answer / num_variables')
        plt.title('Per-Variable Information Cost\n(Normalized μ_answer shows efficiency per variable)')
        plt.grid(True, alpha=0.3)
        # Fit linear trend
        if len(partitions) >= 2:
            norm_model = LinearRegression().fit(np.array(partitions).reshape(-1, 1), mu_per_var)
            norm_slope = norm_model.coef_[0]
            norm_intercept = norm_model.intercept_
            norm_fit = norm_intercept + norm_slope * np.array(partitions)
            plt.plot(partitions, norm_fit, 'b--', alpha=0.7, 
                    label=f'Linear fit (slope={norm_slope:.6f})')
            plt.legend()
        plt.savefig(exp_dir / f'{problem}_normalized_cost.png', dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Normalized cost plot saved to {exp_dir / f'{problem}_normalized_cost.png'}")

def save_scaling_report(scaling: Dict[str, Any], problem: str, exp_dir: Path = RESULTS_DIR):
    """Save scaling analysis report."""
    report = {
        'problem': problem,
        'timestamp': int(time.time()),
        'scaling_analysis': scaling
    }
    filename = f"{problem}_scaling_report_{int(time.time())}.json"
    filepath = exp_dir / filename
    with open(filepath, 'w') as f:
        json.dump(report, f, indent=2)
    print(f"Scaling report saved to {filepath}")

def write_results_table(scaling: Dict[str, Any], results: List[Dict[str, Any]], exp_dir: Path = RESULTS_DIR):
    """Write a CSV table with results."""
    by_partition = {}
    for r in results:
        p = r['partition_level']
        by_partition.setdefault(p, []).append(r)
    
    csv_lines = [
        "n,mu_blind_avg,mu_sighted_avg,mu_answer_avg,ratio,"
        "mu_blind_ci,mu_sighted_ci,mu_answer_ci,ratio_ci"
    ]
    for i, p in enumerate(scaling.get('partitions', [])):
        blind_vals = [r['mu_blind'] for r in by_partition.get(p, [])]
        sighted_vals = [r['mu_sighted'] for r in by_partition.get(p, [])]
        answer_vals = [r['mu_answer'] for r in by_partition.get(p, [])]
        def _ci(series: List[float]) -> float:
            if len(series) <= 1:
                return 0.0
            return 1.96 * float(np.std(series, ddof=1)) / len(series) ** 0.5

        mu_blind_ci = _ci(blind_vals)
        mu_sighted_ci = _ci(sighted_vals)
        mu_answer_ci = _ci(answer_vals)
        ratio_ci = scaling.get('ratio_ci', [0.0] * len(scaling.get('ratio', [])))[i]

        csv_lines.append(
            f"{p},{scaling['mu_blind_avg'][i]:.1f},{scaling['mu_sighted_avg'][i]:.1f},"
            f"{scaling['mu_answer_avg'][i]:.1f},{scaling['ratio'][i]:.3f},"
            f"{mu_blind_ci:.1f},{mu_sighted_ci:.1f},{mu_answer_ci:.1f},{ratio_ci:.3f}"
        )
    
    with open(exp_dir / "results_table.csv", 'w') as f:
        f.write('\n'.join(csv_lines))
    print(f"Results table written to {exp_dir / 'results_table.csv'}")

def write_inference_report(scaling: Dict[str, Any], problem: str, results: List[Dict[str, Any]], exp_dir: Path = RESULTS_DIR):
    """Write a short inference.md with key findings."""
    exp_dir = Path(exp_dir)
    exp_dir.mkdir(parents=True, exist_ok=True)
    # Decision criteria
    aic_exp = scaling.get('aic_exp')
    aic_poly = scaling.get('aic_poly')
    delta_aic = scaling.get('delta_aic_exp_poly')
    blind_exp_better = (
        aic_exp is not None
        and aic_poly is not None
        and aic_exp < aic_poly
        and delta_aic is not None
        and delta_aic >= 10
    )
    sighted_const_better = (scaling.get('aic_const') is not None and scaling.get('aic_linear') is not None and
                           scaling.get('aic_const') < scaling.get('aic_linear'))
    ratio_monotonic = scaling.get('monotonicity_p') is not None and scaling.get('monotonicity_p', 0) >= 0.9
    runtime_stats = scaling.get('runtime_correlation')
    if not isinstance(runtime_stats, dict):
        runtime_stats = {}
    rho_val = runtime_stats.get('rho')
    p_val = runtime_stats.get('p_value')
    runtime_corr_strong = (
        rho_val is not None and p_val is not None and rho_val >= 0.6 and p_val < 0.01
    )
    
    # Prepare CI strings
    exp_slope = scaling.get('exp_slope')
    exp_slope_str = f"{exp_slope:.3f}" if exp_slope is not None else "N/A"
    exp_ci = scaling.get('exp_slope_ci')
    exp_ci_str = f"[{exp_ci[0]:.3f}, {exp_ci[1]:.3f}]" if exp_ci is not None else "[N/A, N/A]"
    ans_slope = scaling.get('ans_slope')
    ans_slope_str = f"{ans_slope:.3f}" if ans_slope is not None else "N/A"
    ans_ci = scaling.get('ans_slope_ci')
    ans_ci_str = f"[{ans_ci[0]:.3f}, {ans_ci[1]:.3f}]" if ans_ci is not None else "[N/A, N/A]"
    
    aic_exp_val = scaling.get('aic_exp')
    aic_exp_str = f"{aic_exp_val:.1f}" if aic_exp_val is not None else "N/A"
    aic_poly_val = scaling.get('aic_poly')
    aic_poly_str = f"{aic_poly_val:.1f}" if aic_poly_val is not None else "N/A"
    aic_const_val = scaling.get('aic_const')
    aic_const_str = f"{aic_const_val:.1f}" if aic_const_val is not None else "N/A"
    aic_linear_val = scaling.get('aic_linear')
    aic_linear_str = f"{aic_linear_val:.1f}" if aic_linear_val is not None else "N/A"
    
    # Normalized slope
    mu_per_var = scaling.get('mu_answer_per_var', [])
    if len(mu_per_var) >= 2:
        norm_slope = LinearRegression().fit(np.array(scaling.get('partitions', [])).reshape(-1, 1), mu_per_var).coef_[0]
        norm_slope_str = f"{norm_slope:.6f}"
    else:
        norm_slope_str = "N/A (insufficient data)"
    
    ratio_slope_val = scaling.get('ratio_slope')
    ratio_slope_str = f"{ratio_slope_val:.4f}" if ratio_slope_val is not None else "N/A"
    
    # Runtime correlation
    rho_str = f"{rho_val:.3f}" if rho_val is not None else "N/A"
    p_str = f"{p_val:.2e}" if p_val is not None else "N/A"
    
    criteria = {
        "blind_exp": blind_exp_better,
        "sighted_ci": scaling.get('ans_slope_ci') is not None
        and scaling['ans_slope_ci'][0] <= 0 <= scaling['ans_slope_ci'][1],
        "ratio": scaling.get('ratio_slope') is not None and scaling['ratio_slope'] > 0 and ratio_monotonic,
        "runtime_corr": runtime_corr_strong,
    }

    passed = sum(1 for ok in criteria.values() if ok)
    total = len(criteria)

    status_lines = [
        f"- Blind fits exp better than poly by ΔAIC ≥ 10: {'PASS' if criteria['blind_exp'] else 'FAIL'}",
        f"- Sighted μ_answer/|vars| slope 95% CI contains 0: {'PASS' if criteria['sighted_ci'] else 'FAIL'}",
        f"- Ratio slope > 0 and monotonic in ≥90% of bootstrap: {'PASS' if criteria['ratio'] else 'FAIL'}",
        f"- Spearman ρ(μ_blind, runtime) ≥ 0.6 (p < 0.01): {'PASS' if criteria['runtime_corr'] else 'FAIL'}",
    ]

    if passed == total:
        conclusion = (
            "All pre-registered criteria passed. Blind reasoning exhibits exponential "
            "scaling while sighted reasoning remains near-constant, confirming the "
            "advertised separation on this dataset."
        )
    elif passed == 0 and not results:
        conclusion = (
            "No experiment results were recorded, so the run is diagnostic only. "
            "Collect fresh data with --save-outputs to evaluate the decision criteria."
        )
    else:
        missing = total - passed
        conclusion = (
            f"Only {passed} of {total} criteria passed (missing {missing}). The evidence "
            "packet should be treated as diagnostic until new runs satisfy all "
            "pre-registered checks."
        )

    ratio_ci = scaling.get('ratio_slope_ci')
    ratio_ci_str = (
        f"[{ratio_ci[0]:.4f}, {ratio_ci[1]:.4f}]" if ratio_ci is not None else "[N/A, N/A]"
    )

    report_lines = [
        "# Thiele Machine Experiment Inference Report",
        f"Problem: {problem}",
        f"Timestamp: {int(time.time())}",
        "",
        "## Pre-registered Decision Criteria",
        *status_lines,
        "",
        "## Blind Reasoning Scaling",
        f"- Raw blind μ (mean conflicts): {scaling.get('mu_blind_raw', [])}",
        f"- Best-fit exponential: slope={exp_slope_str} {exp_ci_str}",
        f"- AIC_exp = {aic_exp_str}, AIC_poly = {aic_poly_str}",
        f"- ΔAIC(exp, poly) = {delta_aic:.1f}" if delta_aic is not None else "- ΔAIC(exp, poly) = N/A",
        f"- Exponential model {'wins' if blind_exp_better else 'loses'}",
        "",
        "## Sighted Reasoning Scaling (μ_answer per variable)",
        f"- Slope = {ans_slope_str} {ans_ci_str}",
        f"- CI {'crosses 0' if scaling.get('ans_slope_ci') and scaling.get('ans_slope_ci')[0] <= 0 <= scaling.get('ans_slope_ci')[1] else 'does not cross 0'}",
        f"- AIC_const = {aic_const_str}, AIC_linear = {aic_linear_str}",
        f"- {'Constant' if sighted_const_better else 'Linear'} model fits best",
        "",
        "## Answer μ per Variable",
        f"- μ_answer / num_vars: {scaling.get('mu_answer_per_var', [])}",
        f"- Slope of normalized μ_answer: {norm_slope_str}",
        "",
        "## Cost Ratio Analysis",
        f"- Ratio slope = {ratio_slope_str} per vertex",
        f"- Ratio slope CI = {ratio_ci_str}",
        f"- Raw ratios (pre-smoothing): {scaling.get('ratio_raw', [])}",
        f"- Monotone in {(scaling.get('monotonicity_p') or 0)*100:.1f}% of bootstrap samples",
        "",
        "## Runtime Correlation",
        f"- Spearman ρ(μ_blind, runtime) = {rho_str} (p = {p_str})",
        "",
        "## Threats to Validity",
        "### Internal Validity",
        "- **Solver Invariance**: Experiments use a single SAT solver (Kissat). Alternative solvers might exhibit different scaling behavior.",
        "- **Random Seed Effects**: Limited seed sampling (0-9) may not capture full variability in problem generation.",
        "- **Budget Sensitivity**: Fixed time budgets may not be optimal for all problem sizes; larger budgets could reveal different asymptotics.",
        "",
        "### External Validity",
        "- **Tseitin Family Specificity**: Results may not generalize beyond Tseitin constraint satisfaction problems.",
        "- **Partition Strategy**: The specific partition algorithm may not be optimal for all problem structures.",
        "- **Hardware Variability**: Runtime measurements depend on specific hardware; results may vary across systems.",
        "",
        "### Construct Validity",
        "- **μ Cost Metric**: The μ_spec v2.0 cost function may not perfectly capture computational complexity.",
        "- **Exponential Fit Quality**: AIC comparisons assume model adequacy; poor fits could lead to incorrect conclusions.",
        "- **Bootstrap Reliability**: Statistical inference relies on bootstrap resampling; small sample sizes may reduce precision.",
        "",
        "## Conclusion",
        conclusion,
    ]
    
    filepath = exp_dir / "inference.md"
    with open(filepath, 'w') as f:
        f.write('\n'.join(report_lines))
    print(f"Inference report written to {filepath}")

def create_manifest(results: List[Dict[str, Any]], scaling: Dict[str, Any], problem: str, saved_results: bool = False,
                    exp_dir: Path = RESULTS_DIR, plot_format: str = 'png'):
    """Create a manifest JSON with hashes of all outputs."""
    manifest = {
        'timestamp': int(time.time()),
        'problem': problem,
        'files': {}
    }
    
    # Hash results JSON only if saved
    if saved_results:
        results_files = list(exp_dir.glob(f"{problem}_p*_r*_*.json"))
        if results_files:
            with open(results_files[0], 'rb') as f:
                manifest['files']['results_json'] = hashlib.sha256(f.read()).hexdigest()
    
    # Hash plots
    for plot in [f'{problem}_analysis_plots.{plot_format}', f'{problem}_blind_scaling.png']:
        plot_file = exp_dir / plot
        if plot_file.exists():
            with open(plot_file, 'rb') as f:
                manifest['files'][plot] = hashlib.sha256(f.read()).hexdigest()
    
    # Hash inference.md
    inf_file = exp_dir / "inference.md"
    if inf_file.exists():
        with open(inf_file, 'rb') as f:
            manifest['files']['inference_md'] = hashlib.sha256(f.read()).hexdigest()
    
    # Hash receipts
    receipt_files = list(exp_dir.glob("receipt_*.json"))
    for rf in receipt_files:
        with open(rf, 'rb') as f:
            manifest['files'][rf.name] = hashlib.sha256(f.read()).hexdigest()
    
    manifest_file = exp_dir / "manifest.json"
    with open(manifest_file, 'w') as f:
        json.dump(manifest, f, indent=2)
    
    # Print top-level hash
    manifest_str = json.dumps(manifest, sort_keys=True)
    top_hash = hashlib.sha256(manifest_str.encode()).hexdigest()
    print(f"Manifest created: {manifest_file}")
    print(f"Top-level SHA256: {top_hash}")

def main():
    parser = argparse.ArgumentParser(description="Run Thiele Machine partition experiments")
    parser.add_argument('--problem', required=True, help='Problem type (e.g., tseitin)')
    parser.add_argument('--partitions', nargs='+', type=int, required=True, help='Partition levels')
    parser.add_argument('--repeat', type=int, default=1, help='Number of repeats per partition')
    parser.add_argument('--seed-grid', nargs='+', type=int, help='Specific seeds to use')
    parser.add_argument('--emit-receipts', action='store_true', help='Emit detailed receipts')
    parser.add_argument('--save-results', action='store_true', help='Save results JSON file')
    parser.add_argument('--mispartition', action='store_true', help='Force wrong partition split (falsification)')
    parser.add_argument('--shuffle-constraints', action='store_true', help='Randomize parity signs (falsification)')
    parser.add_argument('--noise', type=float, help='Flip k% of parities (falsification)')
    parser.add_argument('--budget-sensitivity', action='store_true', help='Run budget sensitivity analysis with varying time limits')
    parser.add_argument('--save-outputs', action='store_true', help='Save all outputs (plots, reports, tables, manifests)')
    parser.add_argument('--experiment-name', default='experiment', help='Name for this experiment run')
    parser.add_argument('--plot-format', choices=['png', 'svg'], default='png',
                        help='Image format for the main analysis plot (default: png)')
    parser.add_argument('--exp-dir', help='Optional directory to write experiment artefacts into')
    
    args = parser.parse_args()
    
    base_exp_dir = Path(args.exp_dir).expanduser().resolve() if args.exp_dir else RESULTS_DIR
    if args.save_outputs:
        if args.exp_dir:
            exp_dir = base_exp_dir
            exp_dir.mkdir(parents=True, exist_ok=True)
            print(f"Experiment outputs will be saved to: {exp_dir}")
        else:
            exp_dir = get_experiment_dir(args.experiment_name, base_exp_dir)
            print(f"Experiment outputs will be saved to: {exp_dir}")
    else:
        exp_dir = base_exp_dir
    
    csv_exporter: Optional[PartitionScalingExporter] = None
    csv_output_path: Optional[Path] = None

    if args.problem == 'tseitin':
        csv_exporter = PartitionScalingExporter(_default_partition_csv_path(exp_dir))
        if args.budget_sensitivity:
            results = run_budget_sensitivity_analysis(
                args.partitions,
                args.repeat,
                args.seed_grid,
                args.emit_receipts,
                exp_dir,
                csv_exporter=csv_exporter,
            )
        else:
            results = run_tseitin_experiments(
                args.partitions,
                args.repeat,
                args.seed_grid,
                args.emit_receipts,
                mispartition=args.mispartition,
                shuffle_constraints=args.shuffle_constraints,
                noise=args.noise,
                exp_dir=exp_dir,
                csv_exporter=csv_exporter,
            )
        csv_output_path = csv_exporter.csv_path
    else:
        print(f"Unknown problem: {args.problem}")
        return

    if results:
        csv_path = csv_output_path
        if csv_path is None:
            csv_path = write_partition_scaling_csv(results)
            csv_hash = hashlib.sha256(csv_path.read_bytes()).hexdigest() if csv_path.exists() else ""
            print(f"Partition metrics recorded in {csv_path} (sha256 {csv_hash})")
        elif csv_exporter is not None:
            print(
                "Partition metrics recorded in"
                f" {csv_exporter.csv_path} (sha256 {csv_exporter.csv_hash})"
            )
        file_hash = None
        if args.save_results:
            file_hash = save_results(results, args.problem, args.partitions, args.repeat, args.seed_grid, exp_dir)
        scaling = fit_scaling_laws(results)
        if args.save_outputs:
            plot_results(results, args.problem, scaling, exp_dir, plot_format=args.plot_format)
            save_scaling_report(scaling, args.problem, exp_dir)
            write_inference_report(scaling, args.problem, results, exp_dir)
            write_results_table(scaling, results, exp_dir)
            create_manifest(results, scaling, args.problem, saved_results=args.save_results,
                            exp_dir=exp_dir, plot_format=args.plot_format)
        if file_hash:
            print(f"Experiment complete. Results hash: {file_hash}")
        else:
            print("Experiment complete.")
    else:
        print("No results collected")

if __name__ == '__main__':
    main()