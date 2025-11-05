# Calorimetry Proofpack v1

## Overview

This proofpack contains the infrastructure for empirically testing the thermodynamic prediction:

```
E_dyn ≈ (k_B T ln 2) · Σμ · S
```

where:
- `E_dyn` is the dynamic energy consumed (joules)
- `k_B = 1.380649×10⁻²³` J/K (Boltzmann constant)
- `T` is temperature (Kelvin)
- `Σμ` is the cumulative μ-bit cost from the Thiele Machine
- `S` is a hardware-dependent scale factor (accounts for multiple gate transitions per logical μ-bit)

**Note on Scale Factor:** The theoretical Landauer limit predicts `E = k_B T ln 2` per bit at temperature T. In practice, FPGA and ASIC implementations involve many physical gate transitions per logical μ-bit operation. The scale factor `S` captures this hardware reality. For the synthetic test data, `S = 10⁹` is used to generate realistic energy levels (nanojoules range).

When collecting real experimental data, the scale factor will be determined empirically from the measured slope of the regression. The prediction is validated if the slope (which equals S) is consistent across different programs and conditions.

## What Must Be Proven

For the Verilog runner, demonstrate that `E_dyn ≈ (k_B T ln 2)·Σμ·S` **across different programs and operating conditions**, not just one demo. The "≈" means a slope ~1 (after accounting for scale factor) with tight confidence and a near-zero intercept.

## Pass/Fail Criteria (CI Gates)

### 1. Slope ≈ 1
In a regression of E_dyn (joules) on (k_B T ln 2)·Σμ:
- 95% CI for slope **contains 1.0** and lies within **[0.95, 1.05]**

### 2. Intercept ≈ 0
- 95% CI contains 0
- |intercept| ≤ 5% of median E_dyn

### 3. Tight Fit
- R² ≥ 0.98
- Bland–Altman mean bias within **±3%**

### 4. Controls Pass

**Constant-μ, variable time:**
- Add stalls/nops; energy change ≤ **3%**

**Constant-time, variable μ:**
- Mispartition/shuffle to raise μ; energy rises with slope in [0.95, 1.05]

### 5. Invariance Checks

**Temperature sweep:**
- Normalize by k_B T ln 2
- Normalized slope stays in [0.95, 1.05] across ≥3 temps

**DVFS sweep (if available):**
- Same normalized slope across ≥3 (V, f) pairs

## Quick Checklist

- [ ] Idle baseline measured and stored
- [ ] Programs cover low→high μ; controls included
- [ ] N≥10 repeats; randomized order; receipts for every run
- [ ] Data collected with μ, T, E, time, V, f, seeds, commit
- [ ] Analysis script run; report.json shows:
  - [ ] slope CI contains 1 and in [0.95,1.05]
  - [ ] intercept CI contains 0 and ≤5% of median E
  - [ ] R² ≥ 0.98; Bland–Altman bias ≤3%
  - [ ] constant-μ/time control tests pass
  - [ ] temperature & DVFS invariance pass
- [ ] MANIFEST.json + signatures written
- [ ] CI green on re-analysis

## Data Collection Protocol

### 0. Prep & Calibration (once)

**Idle baseline:**
- Measure board idle power for ≥60s
- Store P_idle with confidence interval

**Sensor sanity:**
- Use two sources if possible (on-board sensor + shunt/ADC)
- If only one, do a quick load-step to check linearity

**Temperature sensor:**
- Record board temp or ambient (convert to Kelvin)
- Consistent reading per trial required

### 1. Define Program Suite

Pick ≥8 programs covering a μ range:

- **Low μ:** small structured instance
- **Mid μ:** standard Tseitin cases
- **High μ:** mispartition/shuffled (blind) variants
- **Controls:**
  - a) Constant-μ, variable time (add stalls)
  - b) Constant-time, variable μ (shuffle to increase μ)

Each program must emit a **signed receipt** with Σμ, seeds, and commit hash.

### 2. Randomized Runs (to kill drift)

For each **condition** (T or DVFS setting):

1. Randomize program order
2. Do **N ≥ 10 repeats** per program
3. For each trial:
   - Record start timestamp
   - Zero an energy integrator
   - Start your Verilog job
   - Sample V, I at ≥1 kHz (or use on-board energy counter)
   - Stop, integrate E = ∫(V·I - P_idle)dt = E_dyn
   - Log: μ_sum, T_K, V, f, board_id, repeat, time_s, and receipt digest

## File Layout

```
proofpacks/calorimetry_v1/
  README.md                 # This file
  MANIFEST.json             # Hashes of all files
  receipts/                 # Signed μ-ledger receipts per trial
  data/
    cal_data.csv            # One row per trial (see schema below)
    idle_baseline.csv       # Raw idle samples + summary
    sensors.json            # Shunt value / sensor IDs / sample rate
  analysis/
    analyze_calorimetry.py  # Statistical analysis script
    report.json             # Slopes, CIs, R², Bland–Altman, p-values
    figs/
      fit.png
      residuals.png
      bland_altman.png
      temp_sweep.png
      dvfs_sweep.png
  ci/
    run_ci.sh               # Executes analysis and checks gates
```

## Data Schema

### cal_data.csv

```csv
trial_id,program_id,mu_sum,T_K,E_joules,time_s,V_volts,f_hz,board_id,seed,repeat_idx,receipt_sha256,code_commit,sensor_source
```

**Columns:**
- `trial_id`: Unique trial identifier
- `program_id`: Program name/identifier
- `mu_sum`: Total μ-bits consumed (Σμ)
- `T_K`: Temperature in Kelvin
- `E_joules`: Dynamic energy consumed (joules)
- `time_s`: Execution time (seconds)
- `V_volts`: Operating voltage
- `f_hz`: Operating frequency
- `board_id`: Board/hardware identifier
- `seed`: Random seed for program
- `repeat_idx`: Repeat number (0-9 for N=10)
- `receipt_sha256`: SHA-256 hash of receipt file
- `code_commit`: Git commit hash
- `sensor_source`: Sensor identifier

### idle_baseline.csv

```csv
timestamp,V_volts,I_amps,P_watts
```

### sensors.json

```json
{
  "shunt_resistance_ohms": 0.01,
  "sensor_ids": ["on_board_pmic", "external_ina226"],
  "sample_rate_hz": 1000,
  "calibration_date": "2025-11-03",
  "board_id": "fpga_board_001"
}
```

## Analysis Requirements

The analysis script (`analysis/analyze_calorimetry.py`) must:

### 1. Compute Normalized Predictor

```
X = (k_B T ln 2) · μ_sum
```

where k_B = 1.380649×10⁻²³ J/K

### 2. OLS Fit

```
E_dyn = α·X + β
```

Compute:
- 95% CIs for α, β
- R²
- Residual plots
- Breusch–Pagan test (no trend vs μ)

### 3. Bland–Altman Analysis

Plot difference `(E_dyn - X)` vs mean `(E_dyn + X)/2`

Report:
- Mean bias
- 95% limits of agreement

### 4. Control Tests

**Constant-μ trials:**
- Compare with/without stalls
- Paired t-test or Wilcoxon
- Expect |ΔE| ≤ 3%

**Constant-time trials:**
- Compare low vs high μ
- Expect slope ≈ 1, p ≪ 0.01

### 5. Invariance Tests

**Temperature sweep:**
- Fit slopes per temperature
- ANOVA or overlap of CIs
- All in [0.95, 1.05]

**DVFS sweep:**
- Fit slopes per (V, f) pair
- Same check as temperature

### 6. Output Format

`analysis/report.json`:

```json
{
  "slope": {
    "value": 1.02,
    "ci_lower": 0.98,
    "ci_upper": 1.06,
    "pass": false
  },
  "intercept": {
    "value": 0.001,
    "ci_lower": -0.002,
    "ci_upper": 0.004,
    "median_e_ratio": 0.002,
    "pass": true
  },
  "r_squared": {
    "value": 0.99,
    "pass": true
  },
  "bland_altman": {
    "mean_bias_percent": 1.2,
    "pass": true
  },
  "controls": {
    "constant_mu": {
      "energy_change_percent": 2.1,
      "pass": true
    },
    "constant_time": {
      "slope": 1.01,
      "pass": true
    }
  },
  "invariance": {
    "temperature": {
      "all_slopes_in_range": true,
      "pass": true
    },
    "dvfs": {
      "all_slopes_in_range": true,
      "pass": true
    }
  },
  "overall_pass": false
}
```

## Provenance & Receipts

Every trial must link to a **receipt** via `receipt_sha256`:

**Receipt contents:**
- μ_sum with breakdown
- Seeds and solver options
- Code commit hash
- Spec versions
- Verifier stdout (byte caps, hashes)

**Signing:**
- Sign MANIFEST.json and cal_data.csv digest
- Ed25519 signature
- Include key_id, sig_domain: "ThieleCal|v1"

## Minimal Hardware Checklist

- **Sampling:** ≥1 kHz power samples, timestamped
- **Idle subtraction:** Always subtract P_idle measured same day
- **Warm-up:** 60s warm-up before first trial and between large load changes
- **Temp:** Record temperature reading per trial
- **Repeatability:** N≥10 per point, randomize order

## Running the Proofpack

### Generate Data (with real hardware)

```bash
# 1. Calibrate sensors
python analysis/calibrate_sensors.py

# 2. Measure idle baseline
python analysis/measure_idle.py --duration 60

# 3. Run experiments
python analysis/run_experiments.py \
  --programs programs.json \
  --repeats 10 \
  --randomize

# 4. Generate receipts
python analysis/generate_receipts.py
```

### Analyze Data

```bash
# Run statistical analysis
cd analysis/
python analyze_calorimetry.py

# Check CI gates
cd ../ci/
./run_ci.sh
```

### Verify Receipts

```bash
# Verify all receipts
python analysis/verify_receipts.py

# Check manifest
python analysis/verify_manifest.py
```

## What Makes This "Undeniable"

1. **Pre-registered gates:** Exact pass/fail criteria defined before data collection
2. **Raw data published:** Anyone can re-run analysis
3. **Reproducible:** If passes on your board, others can replicate
4. **No hand-waving:** Automated statistical tests with p-values
5. **Controls included:** Structure-sensitivity demonstrated
6. **Invariance tested:** Results hold across conditions

## Notes

- Don't have DVFS or exact temp control? Record what you do have. The normalized slope test still works.
- If any gate fails → CI red, proofpack flagged
- This is speculative infrastructure - no actual hardware measurements exist yet
- The framework is complete and ready for real data when hardware becomes available

## Status

**⚠️ INFRASTRUCTURE ONLY - NO EXPERIMENTAL DATA**

This proofpack contains the complete infrastructure for calorimetry validation, but does not include actual hardware measurements. The analysis scripts can run on synthetic data for testing purposes.

To use this proofpack:
1. Implement hardware measurement interface
2. Collect real calorimetry data following the protocol above
3. Run analysis and verify CI gates pass

**If all gates pass,** the thermodynamic prediction E_dyn ≈ (k_B T ln 2)·Σμ is empirically validated for your hardware. **If any gate fails,** the prediction is falsified and should not be claimed.
