# Agent experiment prompt — reproduce Landauer, Einstein, and CWD with the μ‑ledger


## Overview
- Purpose: run reproducible software experiments that use the project's μ‑ledger to (A) recover Landauer and Einstein–Smoluchowski laws and (B) test the Compositional Work Decomposition (CWD) prediction.
- Outputs: CSVs, plots, verifier JSONs, short PDF reports.

## Repository references
- μ‑ledger code: [`coq/kernel/MuLedgerConservation.v`](coq/kernel/MuLedgerConservation.v:21)
- VM step semantics: [`coq/kernel/VMStep.v`](coq/kernel/VMStep.v:61)
- VM state: [`coq/kernel/VMState.v`](coq/kernel/VMState.v:241)

## Global parameters (defaults)
- Seeds: [0,1,2,3,4]
- Trials per condition: 50
- Temperature grid T: [0.5, 1.0, 2.0]
- Tolerances: epsilon=0.05, delta=0.05, eta=0.05
- k_B = 1 (units)

## Layout of produced artifacts
- results/<experiment>/<T>/<seed>.csv
- plots/<experiment>/*.png
- reports/<experiment>_report.pdf
- verifier/<experiment>_verifier.json

## A. Landauer experiment (implementation blueprint)

### Goal
Recover Landauer bound numerically:
$$ \langle W\rangle / (kT\ln 2) \approx \sum_t \mu_{t} $$
where μ_t comes from the μ‑ledger (`ledger_entries`).

### Minimal system
- Choose small discrete microstate space, e.g. N=4 initial microstates, erase to M=1.
- Sighted protocol: policy that conditions on the system's macrostate and routes steps to deterministically reduce accessible microstates.
- Blind protocol: same actions but without conditioning on module identity.

### Per‑trial logging (CSV columns)
seed, T, trial_id, sum_mu_bits, work, work_over_kTln2, protocol

### Work proxy
- Use Metropolis energy changes: record ΔE for accepted transitions; sum positive energy inputs as work.
- Consistent sign: work positive when energy increases.

### Example driver (python)
```python
# python
import numpy as np, pandas as pd
def run_erasure(seed, T, protocol, steps=100):
    np.random.seed(seed)
    # initialize microstate distribution
    # implement sighted or blind transition kernel
    # record per-step mu_bits and ΔE
    # return sum_mu_bits, total_work
```

### Verifier checks
- For each trial assert |work/(kT ln2) - sum_mu_bits| <= epsilon.
- Aggregate: report mean and stddev.

## B. Einstein–Smoluchowski experiment (diffusion–mobility)

### Goal
Show D = μ_mech * kT (estimate numerically).

### Setup
- Ensemble of walkers in 1D; Metropolis updates at temperature T.
- Optional small bias force F to measure drift.

### Estimators
- D ≈ slope of MSD(t)/(2t) for large t.
- μ_mech ≈ slope of mean displacement / (F t).

### CSV output
seed, T, F, D_est, mu_mech_est, D_minus_mu_kT

### Driver sketch
```python
# python
def run_walkers(seed, T, F, n_walkers=1000, steps=1000):
    # simulate ensemble, record positions every τ
    # compute MSD and mean displacement
    # estimate D and mu_mech
    return D_est, mu_mech_est
```

### Verifier
- Assert |D_est - mu_mech_est * kT| <= delta.
- Compare sighted vs blind: report information metric (AIC or entropy production proxy).

## C. Compositional Work Decomposition (CWD)

### Goal
- Predict minimal average work for K-module composition:
  W_min/(kT ln2) = sum_i μ_answer^(i)
- Blind protocol penalty: ΔW >= kT ln2 * I(Module;Policy)

### Setup
- K independent modules; generate tasks with known μ_answer per module.
- Implement sighted routing and blind policy.

### Measurements
- Σμ_sighted, W_sighted, W_blind, I(Module;Policy)
- Estimate mutual information from action distributions:
  I = Σ_{m,a} p(m,a) log p(m,a)/(p(m)p(a))

### CSV
K, seed, sum_mu_sighted, W_sighted, W_blind, I_est, penalty

### Verifier assertions
- |W_sighted/(kT ln2) - sum_mu_sighted| <= epsilon
- W_blind - W_sighted >= kT ln2 * I_est - eta

## D. Reproducibility & scripts

### Command-line driver (suggested)
```bash
# bash
python experiments/run_landauer.py --T 1.0 --trials 50 --seeds 0 1 2 3 4
python experiments/run_einstein.py --T 1.0 --F 0.01 --trials 50
python experiments/run_cwd.py --K 4 --trials 50
```

### Verifier runner
```python
# python
from verifier import check_landauer, check_einstein, check_cwd
check_landauer("results/landauer", eps=0.05)
check_einstein("results/einstein", delta=0.05)
check_cwd("results/cwd", eps=0.05, eta=0.05)
```

## E. Minimal toy check
- N=4→M=1 erasure; expected sum_mu_bits = log2(4)=2
- T=1, k=1 ⇒ expected W/(kT ln2) ≈ 2

## F. Notes on integration with μ‑ledger
- The μ‑ledger API points: [`coq/kernel/MuLedgerConservation.v:21`](coq/kernel/MuLedgerConservation.v:21) and [`coq/kernel/SimulationProof.v:99`](coq/kernel/SimulationProof.v:99).
- When instrumenting code, emit ledger entries per step as integer bits (log2 ratio) or as raw instruction_cost from VM and convert to bits consistently.

## G. Deliverables checklist
- [ ] Implement drivers and simulators
- [ ] Produce CSVs and plots
- [ ] Produce verifier outputs (JSON) and summary reports
- [ ] Package commands to reproduce

## H. Implementation tips
- Use fixed seeds; save raw logs for audit.
- Estimate mutual information with plug-in estimator and report bias correction.
- Use bootstrap to produce confidence intervals.

## Contact
- File issues in scripts/ or open a PR with results.

End of prompt file.
## Progress log and finalization

Progress (finalized):
- [x] Create prompt file [`scripts/agent_experiment_prompt.md`](scripts/agent_experiment_prompt.md:1)
- [x] Implement skeleton experiment driver [`experiments/run_landauer.py`](experiments/run_landauer.py:1)
- [x] Implement skeleton experiment driver [`experiments/run_einstein.py`](experiments/run_einstein.py:1)
- [x] Implement skeleton experiment driver [`experiments/run_cwd.py`](experiments/run_cwd.py:1)
- [x] Add verifier module [`verifier/check_landauer.py`](verifier/check_landauer.py:1)
- [x] Add verifier module [`verifier/check_einstein.py`](verifier/check_einstein.py:1)
- [x] Add verifier module [`verifier/check_cwd.py`](verifier/check_cwd.py:1)
- [x] Add plotting utilities [`experiments/plot_utils.py`](experiments/plot_utils.py:1)
- [x] Run a minimal toy test (N=4→M=1) and record results in [`results/landauer/T=1.0/seed=0.csv`](results/landauer/T=1.0/seed=0.csv:1)

Completed automated runs (clickable summaries):
- [`experiments/vm_integration_adapter.py`](experiments/vm_integration_adapter.py:1) dry-run executed — created CSV [`results/ledger/sample_ledger.csv`](results/ledger/sample_ledger.csv:1).
- [`experiments/run_landauer.py`](experiments/run_landauer.py:1) dry-run executed (sighted & blind samples) — created CSV [`results/landauer/T=1.0/seed=0.csv`](results/landauer/T=1.0/seed=0.csv:1).
- [`experiments/run_einstein.py`](experiments/run_einstein.py:1) dry-run executed — created CSV [`results/einstein/T=1.0/seed=0.csv`](results/einstein/T=1.0/seed=0.csv:1).
- [`experiments/run_cwd.py`](experiments/run_cwd.py:1) dry-run executed — created CSV [`results/cwd/K=4/seed=0.csv`](results/cwd/K=4/seed=0.csv:1) (includes computed penalty column).
- [`experiments/run_einstein.py`](experiments/run_einstein.py:1) high-sampling run executed — created updated CSV [`results/einstein/T=1.0/seed=0.csv`](results/einstein/T=1.0/seed=0.csv:1).
- [`verifier/check_landauer.py`](verifier/check_landauer.py:1) executed — wrote verifier [`verifier/landauer_verifier.json`](verifier/landauer_verifier.json:1) (sighted@T=1.0 passed).
- [`verifier/check_einstein.py`](verifier/check_einstein.py:1) executed — wrote verifier [`verifier/einstein_verifier.json`](verifier/einstein_verifier.json:1) (einstein@T=1.0 failed on sample runs).
- [`verifier/check_cwd.py`](verifier/check_cwd.py:1) executed — wrote verifier [`verifier/cwd_verifier.json`](verifier/cwd_verifier.json:1) (sighted & blind sample checks passed).

Integration checklist (final status):
- [x] Inspect [`coq/kernel/SimulationProof.v:99`](coq/kernel/SimulationProof.v:99) and [`coq/kernel/VMStep.v:61`](coq/kernel/VMStep.v:61) to map `vm_apply/advance_state` to runtime logging.
- [x] Add an adapter that emits per-step ledger CSVs (timestamp, step_id, vm_mu_bits, instruction_cost, raw_ledger_entry).
- [x] Replace toy work proxies in: [`experiments/run_landauer.py`](experiments/run_landauer.py:1), [`experiments/run_einstein.py`](experiments/run_einstein.py:1), [`experiments/run_cwd.py`](experiments/run_cwd.py:1) so they read ledger entries and compute Σμ.
- [x] Validate per-step entries with verifier smoke tests and end-to-end small-N toy runs.

Final notes and next actions (blocking):
- All orchestration and implementation work completed; remaining blocker is Einstein verifier failing on sample runs. To finish scientifically, either:
  - Increase Einstein sampling significantly (interactive long run), or
  - Improve estimator code in [`experiments/run_einstein.py`](experiments/run_einstein.py:1) (recommended: discard transients, robust slope fitting, bootstrap CI).
- Once Einstein verifier passes, update any remaining reporting and finalize PDFs.

End of file.


## I. Next iteration guidance (how to proceed from the Einstein verifier failure)

- Situation summary:
  - The refined runner [`experiments/run_einstein_refined.py`](experiments/run_einstein_refined.py:1) produced a summary at [`results/einstein_refined/T=1.0/seed=0_summary.json`](results/einstein_refined/T=1.0/seed=0_summary.json:1) showing Dminus_median ≈ 0.25 and the verifier [`verifier/check_einstein.py`](verifier/check_einstein.py:1) currently reports:
    - verdicts: "einstein@T=1.0": false
    - diagnostics: mean_diff ≈ 0.2517, std_diff ≈ 0.0106, n = 80
- Objectives for next iteration:
  - Decide whether the gap is statistical (insufficient sampling) or estimator bias.
  - Iterate with a medium run to test estimator changes quickly, then run a production run if the medium test looks promising.

- Recommended estimator improvements (apply in `experiments/run_einstein_refined.py` or the minimal runner):
  - Discard transients: when fitting slope use only t > t_cut (suggest t_cut = 0.1 * max_time or drop first 10% of samples).
  - Use robust slope: prefer Huber IRLS result (already implemented) but add explicit transient discard and increase max_iter/delta tuning.
  - Increase median-of-means blocks (e.g., --k-blocks 10) to reduce outlier influence.
  - Add a bootstrap CI around D_minus_mu_kT: resample trials to estimate mean_diff CI and report.
  - Report raw per-trial D_minus_mu_kT values alongside medians for diagnostics.

- Quick commands
  - Medium test (fast iteration):
    - python experiments/run_einstein_refined.py --seeds 0 --T 1.0 --F 0.01 --trials 40 --n_walkers 20000 --steps 2000 --out results/einstein_refined_medium --k-blocks 8
    - python verifier/check_einstein.py results/einstein_refined_medium
  - Longer production (if medium test looks stable):
    - python experiments/run_einstein_refined.py --seeds 0 --T 1.0 --F 0.01 --trials 160 --n_walkers 80000 --steps 10000 --out results/einstein_refined_long --k-blocks 10
    - python verifier/check_einstein.py results/einstein_refined_long

- How to run the verifier and interpret results:
  - Run: python3 verifier/check_einstein.py <results_dir>
  - The verifier writes [`verifier/einstein_verifier.json`](verifier/einstein_verifier.json:1) with:
    - verdicts: boolean pass/fail per T
    - diagnostics: mean_diff (mean |D - μ kT|), std_diff, n
  - Passing criterion (default): mean_diff <= delta (delta default 0.05). If mean_diff is larger than delta but CI covers delta, consider either increasing sampling or tightening estimators.

- Checklist to complete after iteration:
  - [ ] Run medium test and attach `results/einstein_refined_medium/*`
  - [ ] Run verifier and save `verifier/einstein_verifier.json`
  - [ ] If still failing, implement estimator changes and re-run medium test
  - [ ] If medium test passes, run long production and re-run verifier
  - [ ] Update this prompt file with final verdict and attach plots/reports

- Notes for collaborators:
  - Keep fixed seeds and save raw per-trial CSVs for reproducibility.
  - Prefer medium iteration cycles (faster) to reduce turnaround.
  - When editing estimators, include a short unit test or small synthetic dataset demonstrating improved bias/resilience.
