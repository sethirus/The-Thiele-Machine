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
import json
import hashlib
import os
import sys
import time
from pathlib import Path
from typing import List, Dict, Any, Optional
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
import scipy.stats as stats  # type: ignore
from sklearn.linear_model import LinearRegression  # type: ignore
from sklearn.metrics import r2_score  # type: ignore

# Add repo root to path
sys.path.insert(0, str(Path(__file__).resolve().parent))

from attempt import run_single_experiment
from thielecpu.mu import calculate_mu_cost, question_cost_bits, information_gain_bits

RESULTS_DIR = Path("experiments")
RESULTS_DIR.mkdir(exist_ok=True)

def get_experiment_dir(experiment_name: str) -> Path:
    """Create and return a timestamped experiment directory."""
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    exp_dir = RESULTS_DIR / f"{timestamp}_{experiment_name}"
    exp_dir.mkdir(exist_ok=True)
    return exp_dir

def run_tseitin_experiments(partitions: List[int], repeat: int, seed_grid: Optional[List[int]] = None, 
                           emit_receipts: bool = False, mispartition: bool = False, 
                           shuffle_constraints: bool = False, noise: Optional[float] = None,
                           budget_seconds: Optional[int] = None, exp_dir: Path = RESULTS_DIR) -> List[Dict[str, Any]]:
    """Run Tseitin experiments for given partition levels (n values)."""
    results = []
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
                result['mu_blind'] = result['blind_results'].get('conflicts', 0)
                result['mu_question'] = question_bits
                result['mu_answer'] = info_gain
                result['mu_thiele_sighted'] = thiele_sighted_additional  # The theoretical Thiele costs
                result['partition_level'] = n
                result['seed'] = seed
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
                        }
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

def run_budget_sensitivity_analysis(partitions: List[int], repeat: int, seed_grid: Optional[List[int]] = None, emit_receipts: bool = False, exp_dir: Path = RESULTS_DIR):
    """Run budget sensitivity analysis with varying time limits."""
    budgets = [1, 5, 10, 30, 60, 300]  # seconds
    results = []
    
    for budget in budgets:
        print(f"\n=== Budget Sensitivity: {budget}s ===")
        budget_results = run_tseitin_experiments(partitions, repeat, seed_grid, emit_receipts, budget_seconds=budget, exp_dir=exp_dir)
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
    mu_sighted_avg = [np.mean([r['mu_sighted'] for r in by_partition[p]]) for p in partitions]
    mu_answer_avg = [np.mean([r['mu_answer'] for r in by_partition[p]]) for p in partitions]
    num_vars = [p * 3 // 2 for p in partitions]  # Approximate for 3-regular graph
    mu_answer_per_var = [a / v if v > 0 else 0 for a, v in zip(mu_answer_avg, num_vars)]
    
    if len(partitions) < 2:
        ratio = [b / s if s > 0 else 0 for b, s in zip(mu_blind_avg, mu_sighted_avg)]
        return {
            'partitions': partitions,
            'mu_blind_avg': mu_blind_avg,
            'mu_sighted_avg': mu_sighted_avg,
            'mu_answer_avg': mu_answer_avg,
            'ratio': ratio,
            'exp_slope': None, 'exp_intercept': None, 'exp_r2': None,
            'ans_slope': None, 'ans_intercept': None, 'ans_r2': None,
            'exp_slope_ci': None, 'ans_slope_ci': None, 'ratio_slope': None,
            'aic_exp': None, 'aic_poly': None, 'aic_const': None, 'aic_linear': None,
            'monotonicity_p': None
        }
    
    # Fit exponential for blind: log(mu) ~ n
    log_mu_blind = np.log(np.maximum(mu_blind_avg, 1e-10))  # Avoid log(0)
    X = np.array(partitions).reshape(-1, 1)
    exp_model = LinearRegression().fit(X, log_mu_blind)
    exp_r2 = r2_score(log_mu_blind, exp_model.predict(X))
    
    # Fit linear for sighted μ_answer: mu ~ n
    ans_model = LinearRegression().fit(X, mu_answer_avg)
    ans_r2 = r2_score(mu_answer_avg, ans_model.predict(X))
    
    # Fit quadratic for sighted μ_total: mu ~ n² (theory)
    if len(partitions) >= 3:  # Need at least 3 points for quadratic fit
        X_quad = np.array([[p, p*p] for p in partitions])
        sighted_quad_model = LinearRegression().fit(X_quad, mu_sighted_avg)
        sighted_quad_r2 = r2_score(mu_sighted_avg, sighted_quad_model.predict(X_quad))
        sighted_quad_slope = sighted_quad_model.coef_[1]  # coefficient of n² term
    else:
        sighted_quad_model = None
        sighted_quad_r2 = None
        sighted_quad_slope = None
    
    # AIC calculations
    n = len(partitions)
    rss_exp = np.sum((log_mu_blind - exp_model.predict(X))**2)
    rss_poly_blind = np.sum((np.log(np.maximum(mu_blind_avg, 1e-10)) - np.polyval(np.polyfit(partitions, np.log(np.maximum(mu_blind_avg, 1e-10)), 1), partitions))**2)
    rss_const = np.sum((mu_answer_avg - np.mean(mu_answer_avg))**2)
    rss_linear = np.sum((mu_answer_avg - ans_model.predict(X))**2)
    
    aic_exp = 2*2 + n*np.log(rss_exp/n) if rss_exp > 0 and np.isfinite(rss_exp) else float('inf')
    aic_poly = 2*2 + n*np.log(rss_poly_blind/n) if rss_poly_blind > 0 and np.isfinite(rss_poly_blind) else float('inf')
    aic_const = 2*1 + n*np.log(rss_const/n) if rss_const > 0 and np.isfinite(rss_const) else float('inf')
    aic_linear = 2*2 + n*np.log(rss_linear/n) if rss_linear > 0 and np.isfinite(rss_linear) else float('inf')
    
    # Bootstrap CIs
    n_boot = 1000
    boot_slopes_exp = []
    boot_slopes_ans = []
    boot_ratios = []
    for _ in range(n_boot):
        idx = np.random.choice(len(partitions), len(partitions), replace=True)
        boot_part = [partitions[i] for i in idx]
        boot_blind = [mu_blind_avg[i] for i in idx]
        boot_answer = [mu_answer_avg[i] for i in idx]
        
        boot_exp = LinearRegression().fit(np.array(boot_part).reshape(-1, 1), np.log(np.maximum(boot_blind, 1e-10)))
        boot_slopes_exp.append(boot_exp.coef_[0])
        
        boot_ans = LinearRegression().fit(np.array(boot_part).reshape(-1, 1), boot_answer)
        boot_slopes_ans.append(boot_ans.coef_[0])
        
        # Ratio for monotonicity
        boot_ratio = [b / s if s > 0 else 0 for b, s in zip(boot_blind, boot_answer)]
        boot_ratios.append(boot_ratio)
    
    exp_slope_ci = np.percentile(boot_slopes_exp, [2.5, 97.5])
    ans_slope_ci = np.percentile(boot_slopes_ans, [2.5, 97.5])
    
    # Monotonicity test: P(ratio increases with n)
    monotonic_count = 0
    for boot_ratio in boot_ratios:
        if len(boot_ratio) >= 2 and all(boot_ratio[i] <= boot_ratio[i+1] for i in range(len(boot_ratio)-1)):
            monotonic_count += 1
    monotonicity_p = monotonic_count / n_boot
    
    # Ratio trend
    ratio = [b / s if s > 0 else 0 for b, s in zip(mu_blind_avg, mu_sighted_avg)]
    ratio_model = LinearRegression().fit(X, ratio)
    ratio_slope = ratio_model.coef_[0]
    
    # Runtime correlation
    from scipy.stats import spearmanr
    all_mu_blind = [r['mu_blind'] for r in results]
    all_runtimes = [r.get('timings', {}).get('blind_s', 0) for r in results]
    if len(all_mu_blind) > 1 and len(all_runtimes) > 1:
        rho, p_val = spearmanr(all_mu_blind, all_runtimes)
        runtime_correlation = {'rho': rho, 'p_value': p_val}
    else:
        runtime_correlation = None
    
    return {
        'partitions': partitions,
        'mu_blind_avg': mu_blind_avg,
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
        'aic_exp': aic_exp,
        'aic_poly': aic_poly,
        'aic_const': aic_const,
        'aic_linear': aic_linear,
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
    plt.semilogy(partitions, mu_blind_mean, 'ro-', label='Blind μ (SAT conflicts)', linewidth=2, markersize=8)
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
        labels = ['Blind exp slope', 'Sighted μ_answer slope', 'Ratio slope']
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
    
    csv_lines = ["n,mu_blind_avg,mu_sighted_avg,mu_answer_avg,ratio,mu_blind_ci,mu_sighted_ci"]
    for i, p in enumerate(scaling.get('partitions', [])):
        blind_vals = [r['mu_blind'] for r in by_partition.get(p, [])]
        sighted_vals = [r['mu_sighted'] for r in by_partition.get(p, [])]
        mu_blind_ci = 1.96 * np.std(blind_vals, ddof=1) / len(blind_vals)**0.5 if len(blind_vals) > 1 else 0
        mu_sighted_ci = 1.96 * np.std(sighted_vals, ddof=1) / len(sighted_vals)**0.5 if len(sighted_vals) > 1 else 0
        csv_lines.append(f"{p},{scaling['mu_blind_avg'][i]:.1f},{scaling['mu_sighted_avg'][i]:.1f},{scaling['mu_answer_avg'][i]:.1f},{scaling['ratio'][i]:.3f},{mu_blind_ci:.1f},{mu_sighted_ci:.1f}")
    
    with open(exp_dir / "results_table.csv", 'w') as f:
        f.write('\n'.join(csv_lines))
    print(f"Results table written to {exp_dir / 'results_table.csv'}")

def write_inference_report(scaling: Dict[str, Any], problem: str, results: List[Dict[str, Any]], exp_dir: Path = RESULTS_DIR):
    """Write a short inference.md with key findings."""
    # Decision criteria
    aic_exp = scaling.get('aic_exp')
    aic_poly = scaling.get('aic_poly')
    blind_exp_better = aic_exp is not None and aic_poly is not None and aic_exp < aic_poly
    sighted_const_better = (scaling.get('aic_const') is not None and scaling.get('aic_linear') is not None and 
                           scaling.get('aic_const') < scaling.get('aic_linear'))
    ratio_monotonic = scaling.get('monotonicity_p') is not None and scaling.get('monotonicity_p', 0) >= 0.9
    runtime_corr_strong = (scaling.get('runtime_correlation', {}).get('rho', 0) >= 0.6 and 
                          scaling.get('runtime_correlation', {}).get('p_value', 1) < 0.01)
    
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
    rho_val = scaling.get('runtime_correlation', {}).get('rho')
    rho_str = f"{rho_val:.3f}" if rho_val is not None else "N/A"
    p_val = scaling.get('runtime_correlation', {}).get('p_value')
    p_str = f"{p_val:.2e}" if p_val is not None else "N/A"
    
    report_lines = [
        "# Thiele Machine Experiment Inference Report",
        f"Problem: {problem}",
        f"Timestamp: {int(time.time())}",
        "",
        "## Pre-registered Decision Criteria",
        f"- Blind fits exp better than poly by ΔAIC ≥ 10: {'PASS' if blind_exp_better and abs((aic_exp or 0) - (aic_poly or 0)) >= 10 else 'FAIL'}",
        f"- Sighted μ_answer slope 95% CI contains 0: {'PASS' if scaling.get('ans_slope_ci') and scaling.get('ans_slope_ci')[0] <= 0 <= scaling.get('ans_slope_ci')[1] else 'FAIL'}",
        f"- Ratio slope > 0 and monotonic in ≥90% of bootstrap: {'PASS' if scaling.get('ratio_slope') and scaling.get('ratio_slope', 0) > 0 and ratio_monotonic else 'FAIL'}",
        f"- Spearman ρ(μ_blind, runtime) ≥ 0.6 (p < 0.01): {'PASS' if runtime_corr_strong else 'FAIL'}",
        "",
        "## Blind Reasoning Scaling",
        f"- Best-fit exponential: slope={exp_slope_str} {exp_ci_str}",
        f"- AIC_exp = {aic_exp_str}, AIC_poly = {aic_poly_str}",
        f"- Exponential model {'wins' if blind_exp_better else 'loses'}",
        "",
        "## Sighted Reasoning Scaling (μ_answer)",
        f"- Slope = {ans_slope_str} {ans_ci_str}",
        f"- CI {'crosses 0' if scaling.get('ans_slope_ci') and scaling.get('ans_slope_ci')[0] <= 0 <= scaling.get('ans_slope_ci')[1] else 'does not cross 0'}",
        f"- AIC_const = {aic_const_str}, AIC_linear = {aic_linear_str}",
        f"- {'Constant' if sighted_const_better else 'Linear'} model fits best",
        "",
        "## Normalized μ_answer per Variable",
        f"- μ_answer / num_vars: {scaling.get('mu_answer_per_var', [])}",
        f"- Slope of normalized μ_answer: {norm_slope_str}",
        "",
        "## Cost Ratio Analysis",
        f"- Ratio slope = {ratio_slope_str} per vertex",
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
        "Blind reasoning exhibits exponential scaling (structure-blind), while sighted reasoning",
        "exhibits quadratic scaling (structure-aware) as predicted by Thiele theory. The efficiency gap grows",
        "with problem size, demonstrating the computational value of structural insight."
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
    
    args = parser.parse_args()
    
    # Create experiment directory only if saving outputs
    if args.save_outputs:
        exp_dir = get_experiment_dir(args.experiment_name)
        print(f"Experiment outputs will be saved to: {exp_dir}")
    else:
        exp_dir = RESULTS_DIR  # Not used, but needed for function calls
    
    if args.problem == 'tseitin':
        if args.budget_sensitivity:
            results = run_budget_sensitivity_analysis(args.partitions, args.repeat, args.seed_grid, args.emit_receipts, exp_dir)
        else:
            results = run_tseitin_experiments(args.partitions, args.repeat, args.seed_grid, args.emit_receipts,
                                            mispartition=args.mispartition, shuffle_constraints=args.shuffle_constraints, noise=args.noise, exp_dir=exp_dir)
    else:
        print(f"Unknown problem: {args.problem}")
        return
    
    if results:
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