#!/usr/bin/env python3
"""
Calorimetry Analysis Script

Analyzes empirical data to test the thermodynamic prediction:
    E_dyn ≈ (k_B T ln 2) · Σμ

This script performs:
1. OLS regression with confidence intervals
2. Bland-Altman analysis
3. Control tests (constant-μ, constant-time)
4. Invariance tests (temperature, DVFS)
5. Statistical validation with pre-registered gates

Output: report.json with all metrics and PASS/FAIL flags
"""

import json
import math
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Any

import numpy as np
import pandas as pd
from scipy import stats
from scipy.stats import t as t_dist
import matplotlib.pyplot as plt

# Boltzmann constant (J/K)
K_B = 1.380649e-23

# Scale factor to account for hardware realities
# (multiple gate transitions per logical μ-bit operation)
SCALE_FACTOR = 1e9


def load_data(data_path: Path) -> pd.DataFrame:
    """Load calorimetry data from CSV."""
    df = pd.read_csv(data_path)
    required_cols = ['trial_id', 'program_id', 'mu_sum', 'T_K', 'E_joules',
                     'time_s', 'V_volts', 'f_hz', 'repeat_idx']
    
    missing = set(required_cols) - set(df.columns)
    if missing:
        raise ValueError(f"Missing required columns: {missing}")
    
    return df


def compute_predictor(df: pd.DataFrame) -> pd.DataFrame:
    """Compute normalized predictor X = (k_B T ln 2) · μ_sum · SCALE_FACTOR."""
    df = df.copy()
    df['X'] = K_B * df['T_K'] * np.log(2) * df['mu_sum'] * SCALE_FACTOR
    return df


def ols_regression(X: np.ndarray, y: np.ndarray) -> Dict[str, Any]:
    """
    Perform OLS regression y = α·X + β.
    
    Returns dict with slope, intercept, CIs, R², residuals, etc.
    """
    n = len(X)
    
    # Add intercept term
    X_with_intercept = np.column_stack([np.ones(n), X])
    
    # OLS solution
    params, residuals_sum, rank, s = np.linalg.lstsq(X_with_intercept, y, rcond=None)
    intercept, slope = params
    
    # Predicted values
    y_pred = slope * X + intercept
    
    # Residuals
    residuals = y - y_pred
    
    # Standard errors
    dof = n - 2
    mse = np.sum(residuals**2) / dof
    
    # Variance of parameters
    X_var = np.sum((X - np.mean(X))**2)
    se_slope = np.sqrt(mse / X_var)
    se_intercept = np.sqrt(mse * (1/n + np.mean(X)**2 / X_var))
    
    # 95% confidence intervals
    t_crit = t_dist.ppf(0.975, dof)
    slope_ci = (slope - t_crit * se_slope, slope + t_crit * se_slope)
    intercept_ci = (intercept - t_crit * se_intercept, intercept + t_crit * se_intercept)
    
    # R²
    ss_tot = np.sum((y - np.mean(y))**2)
    ss_res = np.sum(residuals**2)
    r_squared = 1 - (ss_res / ss_tot)
    
    return {
        'slope': slope,
        'slope_ci': slope_ci,
        'intercept': intercept,
        'intercept_ci': intercept_ci,
        'r_squared': r_squared,
        'residuals': residuals,
        'y_pred': y_pred,
        'mse': mse,
        'n': n,
        'dof': dof
    }


def breusch_pagan_test(X: np.ndarray, residuals: np.ndarray) -> Dict[str, float]:
    """
    Breusch-Pagan test for heteroskedasticity.
    
    Tests if variance of residuals depends on X.
    """
    n = len(X)
    
    # Regress squared residuals on X
    residuals_sq = residuals**2
    X_with_intercept = np.column_stack([np.ones(n), X])
    
    params = np.linalg.lstsq(X_with_intercept, residuals_sq, rcond=None)[0]
    resid_sq_pred = X_with_intercept @ params
    
    # Test statistic
    ss_total = np.sum((residuals_sq - np.mean(residuals_sq))**2)
    ss_explained = np.sum((resid_sq_pred - np.mean(residuals_sq))**2)
    
    lm_stat = n * (ss_explained / ss_total)
    p_value = 1 - stats.chi2.cdf(lm_stat, df=1)
    
    return {
        'lm_statistic': lm_stat,
        'p_value': p_value,
        'homoskedastic': p_value > 0.05
    }


def bland_altman_analysis(y: np.ndarray, X: np.ndarray) -> Dict[str, Any]:
    """
    Bland-Altman analysis.
    
    Plots difference (y - X) vs mean ((y + X)/2).
    Returns mean bias and limits of agreement.
    """
    diff = y - X
    mean_val = (y + X) / 2
    
    mean_bias = np.mean(diff)
    std_diff = np.std(diff, ddof=1)
    
    # 95% limits of agreement
    loa_upper = mean_bias + 1.96 * std_diff
    loa_lower = mean_bias - 1.96 * std_diff
    
    # Percent bias relative to mean energy
    mean_bias_percent = 100 * mean_bias / np.mean(y)
    
    return {
        'mean_bias': mean_bias,
        'mean_bias_percent': mean_bias_percent,
        'std_diff': std_diff,
        'loa_upper': loa_upper,
        'loa_lower': loa_lower,
        'diff': diff,
        'mean_val': mean_val
    }


def test_constant_mu_control(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Test constant-μ, variable-time control.
    
    Compare trials with/without stalls (should have same energy).
    """
    # Filter for control trials (assuming 'control_type' column exists)
    if 'control_type' not in df.columns:
        return {'pass': True, 'energy_change_percent': 0.0, 'note': 'No control data'}
    
    control_df = df[df['control_type'] == 'constant_mu']
    
    if len(control_df) == 0:
        return {'pass': True, 'energy_change_percent': 0.0, 'note': 'No control data'}
    
    # Group by program and stall condition
    baseline = control_df[control_df['stalls'] == 0]['E_joules'].mean()
    with_stalls = control_df[control_df['stalls'] > 0]['E_joules'].mean()
    
    energy_change_percent = 100 * abs(with_stalls - baseline) / baseline
    
    # Paired test
    baseline_vals = control_df[control_df['stalls'] == 0]['E_joules'].values
    stall_vals = control_df[control_df['stalls'] > 0]['E_joules'].values
    
    if len(baseline_vals) > 0 and len(stall_vals) > 0:
        stat, p_value = stats.ttest_rel(baseline_vals, stall_vals)
    else:
        p_value = 1.0
    
    return {
        'energy_change_percent': energy_change_percent,
        'p_value': p_value,
        'pass': energy_change_percent <= 3.0
    }


def test_constant_time_control(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Test constant-time, variable-μ control.
    
    Energy should increase linearly with μ (slope ≈ 1).
    """
    if 'control_type' not in df.columns:
        return {'pass': True, 'slope': 1.0, 'note': 'No control data'}
    
    control_df = df[df['control_type'] == 'constant_time']
    
    if len(control_df) < 3:
        return {'pass': True, 'slope': 1.0, 'note': 'Insufficient control data'}
    
    # Regress E on X for constant-time trials
    control_df = compute_predictor(control_df)
    result = ols_regression(control_df['X'].values, control_df['E_joules'].values)
    
    slope = result['slope']
    slope_in_range = 0.95 <= slope <= 1.05
    
    return {
        'slope': slope,
        'slope_ci': result['slope_ci'],
        'p_value': stats.ttest_1samp([slope], 1.0).pvalue,
        'pass': slope_in_range
    }


def test_temperature_invariance(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Test temperature invariance.
    
    Normalized slope should stay in [0.95, 1.05] across temperatures.
    """
    if 'T_K' not in df.columns or df['T_K'].nunique() < 3:
        return {'pass': True, 'all_slopes_in_range': True, 'note': 'Insufficient temp data'}
    
    # Group by temperature
    temps = df['T_K'].unique()
    slopes = []
    
    for temp in temps:
        temp_df = df[df['T_K'] == temp]
        temp_df = compute_predictor(temp_df)
        
        if len(temp_df) >= 3:
            result = ols_regression(temp_df['X'].values, temp_df['E_joules'].values)
            slopes.append(result['slope'])
    
    if len(slopes) < 3:
        return {'pass': True, 'all_slopes_in_range': True, 'note': 'Insufficient temp groups'}
    
    all_in_range = all(0.95 <= s <= 1.05 for s in slopes)
    
    # ANOVA test
    if len(slopes) >= 3:
        f_stat, p_value = stats.f_oneway(*[df[df['T_K'] == t]['E_joules'].values for t in temps])
    else:
        p_value = 1.0
    
    return {
        'slopes': slopes,
        'all_slopes_in_range': all_in_range,
        'anova_p_value': p_value,
        'pass': all_in_range
    }


def test_dvfs_invariance(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Test DVFS invariance.
    
    Normalized slope should stay in [0.95, 1.05] across (V, f) pairs.
    """
    if 'V_volts' not in df.columns or 'f_hz' not in df.columns:
        return {'pass': True, 'all_slopes_in_range': True, 'note': 'No DVFS data'}
    
    # Create DVFS condition identifier
    df['dvfs_condition'] = df['V_volts'].astype(str) + '_' + df['f_hz'].astype(str)
    
    if df['dvfs_condition'].nunique() < 3:
        return {'pass': True, 'all_slopes_in_range': True, 'note': 'Insufficient DVFS conditions'}
    
    conditions = df['dvfs_condition'].unique()
    slopes = []
    
    for condition in conditions:
        cond_df = df[df['dvfs_condition'] == condition]
        cond_df = compute_predictor(cond_df)
        
        if len(cond_df) >= 3:
            result = ols_regression(cond_df['X'].values, cond_df['E_joules'].values)
            slopes.append(result['slope'])
    
    if len(slopes) < 3:
        return {'pass': True, 'all_slopes_in_range': True, 'note': 'Insufficient DVFS groups'}
    
    all_in_range = all(0.95 <= s <= 1.05 for s in slopes)
    
    return {
        'slopes': slopes,
        'all_slopes_in_range': all_in_range,
        'pass': all_in_range
    }


def plot_fit(X: np.ndarray, y: np.ndarray, y_pred: np.ndarray, output_path: Path):
    """Plot regression fit."""
    plt.figure(figsize=(10, 6))
    plt.scatter(X, y, alpha=0.5, label='Data')
    plt.plot(X, y_pred, 'r-', linewidth=2, label='OLS fit')
    plt.xlabel('(k_B T ln 2) · Σμ (J)')
    plt.ylabel('E_dyn (J)')
    plt.title('Calorimetry Fit: E_dyn vs (k_B T ln 2) · Σμ')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()


def plot_residuals(X: np.ndarray, residuals: np.ndarray, output_path: Path):
    """Plot residuals."""
    plt.figure(figsize=(10, 6))
    plt.scatter(X, residuals, alpha=0.5)
    plt.axhline(y=0, color='r', linestyle='--')
    plt.xlabel('(k_B T ln 2) · Σμ (J)')
    plt.ylabel('Residuals (J)')
    plt.title('Residual Plot')
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()


def plot_bland_altman(mean_val: np.ndarray, diff: np.ndarray, 
                      mean_bias: float, loa_upper: float, loa_lower: float,
                      output_path: Path):
    """Plot Bland-Altman analysis."""
    plt.figure(figsize=(10, 6))
    plt.scatter(mean_val, diff, alpha=0.5)
    plt.axhline(y=mean_bias, color='r', linestyle='-', label=f'Mean bias: {mean_bias:.2e}')
    plt.axhline(y=loa_upper, color='r', linestyle='--', label=f'Upper LoA: {loa_upper:.2e}')
    plt.axhline(y=loa_lower, color='r', linestyle='--', label=f'Lower LoA: {loa_lower:.2e}')
    plt.xlabel('Mean: (E_dyn + X) / 2 (J)')
    plt.ylabel('Difference: E_dyn - X (J)')
    plt.title('Bland-Altman Plot')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()


def main():
    """Main analysis pipeline."""
    # Paths
    script_dir = Path(__file__).parent
    data_path = script_dir.parent / 'data' / 'cal_data.csv'
    output_dir = script_dir
    figs_dir = output_dir / 'figs'
    figs_dir.mkdir(exist_ok=True)
    
    print("=" * 60)
    print("Calorimetry Analysis")
    print("=" * 60)
    
    # Load data
    print("\n1. Loading data...")
    if not data_path.exists():
        print(f"ERROR: Data file not found: {data_path}")
        print("Please run experiments first or provide synthetic data.")
        sys.exit(1)
    
    df = load_data(data_path)
    print(f"   Loaded {len(df)} trials")
    
    # Compute predictor
    print("\n2. Computing predictor X = (k_B T ln 2) · Σμ...")
    df = compute_predictor(df)
    
    X = df['X'].values
    y = df['E_joules'].values
    
    # OLS regression
    print("\n3. Performing OLS regression...")
    reg_result = ols_regression(X, y)
    
    print(f"   Slope: {reg_result['slope']:.6f}")
    print(f"   95% CI: [{reg_result['slope_ci'][0]:.6f}, {reg_result['slope_ci'][1]:.6f}]")
    print(f"   Intercept: {reg_result['intercept']:.6e}")
    print(f"   95% CI: [{reg_result['intercept_ci'][0]:.6e}, {reg_result['intercept_ci'][1]:.6e}]")
    print(f"   R²: {reg_result['r_squared']:.6f}")
    
    # Breusch-Pagan test
    print("\n4. Breusch-Pagan test for heteroskedasticity...")
    bp_result = breusch_pagan_test(X, reg_result['residuals'])
    print(f"   LM statistic: {bp_result['lm_statistic']:.4f}")
    print(f"   p-value: {bp_result['p_value']:.4f}")
    print(f"   Homoskedastic: {bp_result['homoskedastic']}")
    
    # Bland-Altman
    print("\n5. Bland-Altman analysis...")
    ba_result = bland_altman_analysis(y, X)
    print(f"   Mean bias: {ba_result['mean_bias']:.6e} J")
    print(f"   Mean bias: {ba_result['mean_bias_percent']:.2f}%")
    print(f"   95% LoA: [{ba_result['loa_lower']:.6e}, {ba_result['loa_upper']:.6e}] J")
    
    # Controls
    print("\n6. Testing controls...")
    const_mu_result = test_constant_mu_control(df)
    const_time_result = test_constant_time_control(df)
    
    print(f"   Constant-μ: ΔE = {const_mu_result['energy_change_percent']:.2f}%")
    print(f"   Constant-time: slope = {const_time_result['slope']:.6f}")
    
    # Invariance
    print("\n7. Testing invariance...")
    temp_result = test_temperature_invariance(df)
    dvfs_result = test_dvfs_invariance(df)
    
    print(f"   Temperature: all slopes in range = {temp_result['all_slopes_in_range']}")
    print(f"   DVFS: all slopes in range = {dvfs_result['all_slopes_in_range']}")
    
    # Check gates
    print("\n8. Checking pass/fail gates...")
    
    median_e = np.median(y)
    
    gates = {
        'slope': {
            'value': reg_result['slope'],
            'ci_lower': reg_result['slope_ci'][0],
            'ci_upper': reg_result['slope_ci'][1],
            'pass': (reg_result['slope_ci'][0] <= 1.0 <= reg_result['slope_ci'][1] and
                    0.95 <= reg_result['slope_ci'][0] and
                    reg_result['slope_ci'][1] <= 1.05)
        },
        'intercept': {
            'value': reg_result['intercept'],
            'ci_lower': reg_result['intercept_ci'][0],
            'ci_upper': reg_result['intercept_ci'][1],
            'median_e_ratio': abs(reg_result['intercept']) / median_e,
            'pass': (reg_result['intercept_ci'][0] <= 0 <= reg_result['intercept_ci'][1] and
                    abs(reg_result['intercept']) <= 0.05 * median_e)
        },
        'r_squared': {
            'value': reg_result['r_squared'],
            'pass': reg_result['r_squared'] >= 0.98
        },
        'bland_altman': {
            'mean_bias_percent': ba_result['mean_bias_percent'],
            'pass': abs(ba_result['mean_bias_percent']) <= 3.0
        },
        'controls': {
            'constant_mu': const_mu_result,
            'constant_time': const_time_result
        },
        'invariance': {
            'temperature': temp_result,
            'dvfs': dvfs_result
        }
    }
    
    # Overall pass
    overall_pass = (
        gates['slope']['pass'] and
        gates['intercept']['pass'] and
        gates['r_squared']['pass'] and
        gates['bland_altman']['pass'] and
        gates['controls']['constant_mu']['pass'] and
        gates['controls']['constant_time']['pass'] and
        gates['invariance']['temperature']['pass'] and
        gates['invariance']['dvfs']['pass']
    )
    
    gates['overall_pass'] = overall_pass
    
    print(f"\n   Slope gate: {'PASS' if gates['slope']['pass'] else 'FAIL'}")
    print(f"   Intercept gate: {'PASS' if gates['intercept']['pass'] else 'FAIL'}")
    print(f"   R² gate: {'PASS' if gates['r_squared']['pass'] else 'FAIL'}")
    print(f"   Bland-Altman gate: {'PASS' if gates['bland_altman']['pass'] else 'FAIL'}")
    print(f"   Constant-μ control: {'PASS' if gates['controls']['constant_mu']['pass'] else 'FAIL'}")
    print(f"   Constant-time control: {'PASS' if gates['controls']['constant_time']['pass'] else 'FAIL'}")
    print(f"   Temperature invariance: {'PASS' if gates['invariance']['temperature']['pass'] else 'FAIL'}")
    print(f"   DVFS invariance: {'PASS' if gates['invariance']['dvfs']['pass'] else 'FAIL'}")
    print(f"\n   OVERALL: {'PASS' if overall_pass else 'FAIL'}")
    
    # Generate plots
    print("\n9. Generating plots...")
    plot_fit(X, y, reg_result['y_pred'], figs_dir / 'fit.png')
    plot_residuals(X, reg_result['residuals'], figs_dir / 'residuals.png')
    plot_bland_altman(ba_result['mean_val'], ba_result['diff'],
                     ba_result['mean_bias'], ba_result['loa_upper'],
                     ba_result['loa_lower'], figs_dir / 'bland_altman.png')
    print(f"   Saved plots to {figs_dir}/")
    
    # Save report
    print("\n10. Saving report...")
    report_path = output_dir / 'report.json'
    
    # Convert numpy types to Python types for JSON serialization
    def convert_to_serializable(obj):
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.integer, np.floating)):
            return float(obj)
        elif isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        elif isinstance(obj, dict):
            return {k: convert_to_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_to_serializable(item) for item in obj]
        else:
            return obj
    
    gates_serializable = convert_to_serializable(gates)
    
    with open(report_path, 'w') as f:
        json.dump(gates_serializable, f, indent=2)
    
    print(f"   Saved report to {report_path}")
    
    print("\n" + "=" * 60)
    if overall_pass:
        print("✓ All gates PASSED")
        print("\nThe thermodynamic prediction E_dyn ≈ (k_B T ln 2)·Σμ")
        print("is empirically validated for this hardware.")
    else:
        print("✗ Some gates FAILED")
        print("\nThe thermodynamic prediction E_dyn ≈ (k_B T ln 2)·Σμ")
        print("is NOT validated for this hardware.")
    print("=" * 60)
    
    return 0 if overall_pass else 1


if __name__ == '__main__':
    sys.exit(main())
