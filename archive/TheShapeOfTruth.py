"""
THE SHAPE OF TRUTH — CLI EDITION

A story-driven executable that:
  • Builds an empirical law W ≈ aK·K + ad·d + aT·T + b0
  • Audits predictions with a pretty ledger and residual plots
  • Offers regularized and robust alternatives to damp zero-heavy rows
  • Probes logical consistency in Z3 with adjustable axiom presets

Usage examples:
  python TheShapeOfTruth_cli.py --model ols --axioms loose --plots
  python TheShapeOfTruth_cli.py --model ridge --ridge-lambda 25 --axioms medium
  python TheShapeOfTruth_cli.py --model robust --huber-delta 100 --axioms strict --save-dir out

If z3-solver isn’t installed, Act IV will gracefully skip with a note.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
import argparse
import os
import math
import numpy as np
import pandas as pd

# --------------------------- Data -------------------------------------------

@dataclass
class Record:
    name: str
    W: float
    K: float
    d: float
    T: float


def get_fossil_record() -> List[Record]:
    # 20 experiments (narration fixed)
    return [
        Record('Reversal',                5,     5, 1, 1),
        Record('Mandelbrot',           5444.0, 312, 2, 50),
        Record('Game of Life',          900.0, 264, 4, 2),
        Record('Axiom of Blindness',     10.0, 184, 1, 1),
        Record('Geometry of Truth',     112.0, 264, 1, 4),
        Record('Lensing',                 0.0,   0, 2, 1),
        Record('N-Body and FLRW',         0.0,   0, 3, 1),
        Record('Phyllotaxis',             0.0,   0, 2, 1),
        Record('Universality',            0.0, 112, 1, 1),
        Record('Thiele Machine',          0.0,   0, 1, 1),
        Record('NUSD Law',                0.0,  72, 1, 1),
        Record('Universality Demo',       0.0, 992, 1, 1),
        Record('Physical Realization',    0.0,  96, 1, 1),
        Record('Scale Comparison',        0.0,  96, 1, 1),
        Record('Capstone Demonstration',  0.0, 224, 1, 1),
        Record('Process Isomorphism',     0.0, 280, 1, 1),
        Record('Geometric Logic',         0.0, 240, 1, 1),
        Record('Halting Experiments',     0.0, 264, 1, 1),
        Record('Geometry of Coherence',   7.46, 96, 1, 1),
        Record('Conclusion',              7.46, 96, 1, 1),
    ]


def design_matrix(records: List[Record]) -> Tuple[np.ndarray, np.ndarray, List[str]]:
    X = np.array([[r.K, r.d, r.T, 1.0] for r in records], dtype=float)
    y = np.array([r.W for r in records], dtype=float)
    names = [r.name for r in records]
    return X, y, names

# ------------------------ Regressions ---------------------------------------

def r2_score(y: np.ndarray, yhat: np.ndarray) -> float:
    ss_res = float(np.sum((y - yhat) ** 2))
    ss_tot = float(np.sum((y - np.mean(y)) ** 2))
    return 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0


def fit_ols(X: np.ndarray, y: np.ndarray) -> Tuple[np.ndarray, np.ndarray, float]:
    coeffs, *_ = np.linalg.lstsq(X, y, rcond=None)
    yhat = X @ coeffs
    return coeffs, yhat, r2_score(y, yhat)


def fit_ridge(X: np.ndarray, y: np.ndarray, lam: float = 25.0) -> Tuple[np.ndarray, np.ndarray, float]:
    I = np.eye(X.shape[1])
    coeffs = np.linalg.solve(X.T @ X + lam * I, X.T @ y)
    yhat = X @ coeffs
    return coeffs, yhat, r2_score(y, yhat)


def huber_weights(residuals: np.ndarray, delta: float) -> np.ndarray:
    abs_r = np.abs(residuals)
    w = np.ones_like(residuals)
    mask = abs_r > delta
    w[mask] = delta / abs_r[mask]
    return w


def fit_robust_huber(X: np.ndarray, y: np.ndarray, delta: float = 100.0, iters: int = 200, tol: float = 1e-6) -> Tuple[np.ndarray, np.ndarray, float]:
    n = len(y)
    w = np.ones(n)
    coeffs = np.zeros(X.shape[1])
    for _ in range(iters):
        W = np.diag(w)
        XtWX = X.T @ W @ X
        XtWy = X.T @ W @ y
        new_coeffs = np.linalg.lstsq(XtWX, XtWy, rcond=None)[0]
        yhat = X @ new_coeffs
        r = y - yhat
        new_w = huber_weights(r, delta)
        if np.linalg.norm(new_coeffs - coeffs) < tol:
            coeffs = new_coeffs
            w = new_w
            break
        coeffs = new_coeffs
        w = new_w
    yhat = X @ coeffs
    return coeffs, yhat, r2_score(y, yhat)

# ------------------------ Ledger & Plots ------------------------------------

def build_ledger(names: List[str], y: np.ndarray, yhat: np.ndarray, X: np.ndarray) -> pd.DataFrame:
    df = pd.DataFrame({
        "Experiment": names,
        "W_actual": y,
        "W_pred": yhat,
        "Residual": y - yhat,
        "K": X[:, 0],
        "d": X[:, 1],
        "T": X[:, 2],
    })
    df["Pass(W>=Pred)"] = df["W_actual"] >= df["W_pred"]
    return df.sort_values(by="Experiment").reset_index(drop=True)


def plot_residuals(yhat: np.ndarray, residuals: np.ndarray, title: str, outpath: Optional[str] = None):
    import matplotlib.pyplot as plt  # local import to keep CLI snappy if no plots
    plt.figure()
    plt.scatter(yhat, residuals)
    plt.axhline(0, linestyle='--')
    plt.xlabel("Fitted values (ŷ)")
    plt.ylabel("Residuals (y - ŷ)")
    plt.title(title)
    if outpath:
        plt.savefig(outpath, bbox_inches="tight")
    plt.show()

# ------------------------ Z3 Playground -------------------------------------

def z3_try_counterexample(coeffs: np.ndarray, preset: str = "loose") -> Tuple[Optional[Dict[str, float]], str]:
    try:
        from z3 import Reals, Solver, And, Or, Not, Implies, sat, unsat
    except Exception as e:
        return None, f"z3 not available: {e}"

    aK, ad, aT, b0 = [float(v) for v in coeffs]
    W, K, d, T = Reals('W K d T')

    law = (W >= aK * K + ad * d + aT * T + b0)

    s = Solver()
    s.add(W >= 0, K >= 0, d >= 0, T >= 0)

    if preset in ("medium", "strict"):
        s.add(Implies(And(K == 0, d == 0), T == 0))  # forbid pure-time ghosts
        d1 = And(d >= 1 - 1e-9, d <= 1 + 1e-9)
        d2 = And(d >= 2 - 1e-9, d <= 2 + 1e-9)
        d3 = And(d >= 3 - 1e-9, d <= 3 + 1e-9)
        d4 = And(d >= 4 - 1e-9, d <= 4 + 1e-9)
        s.add(Or(d1, d2, d3, d4))

    if preset == "strict":
        c1, c2, c3 = 0.01, 5.0, 10.0
        s.add(W >= c1 * K)
        s.add(T <= c2 * K + c3)

    s.add(Not(law))  # ask for violation
    res = s.check()
    if res == unsat:
        return None, "unsat (no counterexample under this preset)"
    if res == sat:
        m = s.model()
        def f(z):
            v = m.eval(z)
            try:
                return float(str(v.as_decimal(12)).replace('?', ''))
            except Exception:
                try:
                    return float(v.numerator_as_long()) / float(v.denominator_as_long())
                except Exception:
                    return float(str(v))
        ce = {"W": f(W), "K": f(K), "d": f(d), "T": f(T)}
        return ce, "sat (counterexample found)"
    return None, "unknown"

# --------------------------- Narrative runner --------------------------------

def run_narrative(model: str, ridge_lambda: float, huber_delta: float, plots: bool, save_dir: str, axioms: str):
    print("=" * 60)
    print("THE SHAPE OF TRUTH: AN EXECUTABLE THESIS (CLI edition)")
    print("=" * 60)
    print("This program is a journey in four acts. It attempts to model a")
    print("single, empirical law for the cost of computation.\n")

    os.makedirs(save_dir, exist_ok=True)

    # ---------------- ACT I ----------------
    print("\n--- ACT I: GATHERING THE EVIDENCE ---\n")
    records = get_fossil_record()
    print(f"Fossil record generated: {len(records)} experiments.\n")

    X, y, names = design_matrix(records)

    # ---------------- ACT II ----------------
    print("\n--- ACT II: TESTING A SIMPLE TRUTH ---\n")
    naive_pass = sum(1 for r in records if r.W >= r.K)
    print(f"AUDIT RESULT (W >= K): {naive_pass} PASS, {len(records) - naive_pass} FAIL.\n")

    # ---------------- ACT III ----------------
    print("\n--- ACT III: FINDING THE HIDDEN LAW ---\n")
    if model == "ols":
        coeffs, yhat, r2 = fit_ols(X, y)
    elif model == "ridge":
        coeffs, yhat, r2 = fit_ridge(X, y, lam=ridge_lambda)
    elif model == "robust":
        coeffs, yhat, r2 = fit_robust_huber(X, y, delta=huber_delta)
    else:
        raise ValueError("Unknown model")

    aK, ad, aT, b0 = coeffs
    print("DISCOVERY: A candidate law (linear in K, d, T):")
    print(f"  W ~ {aK:.6f}·K + {ad:.6f}·d + {aT:.6f}·T + {b0:.6f}")
    print(f"Goodness-of-fit: R² = {r2:.3f}")

    ledger = build_ledger(names, y, yhat, X)
    ledger_path = os.path.join(save_dir, f"ledger_{model}.csv")
    ledger.to_csv(ledger_path, index=False)

    # Pretty print top of ledger
    with pd.option_context('display.max_columns', None, 'display.width', 120):
        print("\nAUDIT LEDGER (first 10 rows):")
        print(ledger.head(10).to_string(index=False))

    passes = int((ledger["Pass(W>=Pred)"].values).sum())
    fails = len(ledger) - passes
    print(f"\nFINAL AUDIT: {passes} PASS, {fails} FAIL.\n")

    if plots:
        # Residual plots
        try:
            import matplotlib.pyplot as plt  # noqa: F401
            resid = y - yhat
            out_plt = os.path.join(save_dir, f"residuals_{model.upper()}.png")
            plot_residuals(yhat, resid, f"Residuals vs Fitted ({model.upper()})", out_plt)
            print(f"Saved residual plot → {out_plt}")
        except Exception as e:
            print("(Plotting skipped:", e, ")")

    # Save model summary
    summary_df = pd.DataFrame([{
        'Model': model,
        'aK': aK, 'ad': ad, 'aT': aT, 'offset': b0, 'R2': r2
    }])
    summary_path = os.path.join(save_dir, "model_summary.csv")
    if os.path.exists(summary_path):
        old = pd.read_csv(summary_path)
        summary_df = pd.concat([old, summary_df], ignore_index=True)
    summary_df.to_csv(summary_path, index=False)
    print(f"Model summary saved -> {summary_path}")
    print(f"Ledger saved -> {ledger_path}")

    # ---------------- ACT IV ----------------
    print("\n--- ACT IV: THE LIMITS OF LOGIC ---\n")
    print("Treat the empirical law as an axiom in a perfect logic. Is it consistent?")
    ce, msg = z3_try_counterexample(coeffs, preset=axioms)
    if ce is None:
        print("Z3 verdict:", msg)
    else:
        print("VERDICT: INCONSISTENT under axiom preset:", axioms)
        print("  MONSTER:", ce)
        pred = float(aK * ce['K'] + ad * ce['d'] + aT * ce['T'] + b0)
        print(f"  Audit: W={ce['W']:.6f} but law demands >= {pred:.6f}. Broken.\n")

    # ---------------- CONCLUSION ----------------
    print("\n--- CONCLUSION ---")
    print("1) Simple laws (W >= K) fail.")
    print("2) A linear empirical law fits much better, optionally with ridge/robust variants.")
    print("3) As an axiom, the law may be inconsistent unless more structure is encoded.")
    print("The Shape of Truth lives between data, model, and logic.")


# --------------------------- CLI --------------------------------------------

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="The Shape of Truth — CLI edition")
    p.add_argument("--model", choices=["ols", "ridge", "robust"], default="ols", help="Regression model to use")
    p.add_argument("--ridge-lambda", type=float, default=25.0, help="Ridge regularization strength λ")
    p.add_argument("--huber-delta", type=float, default=100.0, help="Huber delta for robust IRLS")
    p.add_argument("--plots", action="store_true", help="Generate residual plots")
    p.add_argument("--save-dir", default="shape_of_truth_out", help="Directory to write CSVs/plots")
    p.add_argument("--axioms", choices=["loose", "medium", "strict"], default="loose", help="Axiom preset for Z3")
    return p.parse_args()


if __name__ == "__main__":
    args = parse_args()
    run_narrative(
        model=args.model,
        ridge_lambda=args.ridge_lambda,
        huber_delta=args.huber_delta,
        plots=args.plots,
        save_dir=args.save_dir,
        axioms=args.axioms,
    )
