# Replication Guide

This repository is published as a *falsifiable* scientific artifact.  The goal of this guide is to make it easy for external
researchers to rerun the public proofpacks, regenerate the μ-ledgers, and attempt to falsify the two quantitative predictions
of the Thiele composition law.

## 1. Environment setup

1. Clone the repository and create a Python 3.12 environment.
2. Install the project in editable mode:
   ```sh
   python -m pip install --upgrade pip
   pip install -e .
   ```
3. (Optional) Install Coq 8.18 via `opam` if you want to replay the mechanised proofs.  The falsifiability scans only require
   Python and the checked-in proofpacks.

## 2. Running the falsifiability scan

The falsifiability dashboard is driven by a single command:

```sh
python -m tools.falsifiability_analysis --update-readme README.md --write-markdown falsifiability_snapshot.md
```

This command

- parses every proofpack beneath `artifacts/experiments/`,
- checks that the Landauer work inequality is never violated beyond the allowed `ε`,
- reports blind versus sighted runtime ratios for turbulence and cross-domain ledgers,
- refreshes the README dashboard block, and
- writes the raw Markdown table to `falsifiability_snapshot.md` for inspection.

The build (both locally and in CI) fails if any Landauer trial exhibits a negative slack.

## 3. Landauer replication

1. Run the scan as shown above.
2. Open `artifacts/experiments/<run>/proofpack/landauer/landauer_steps.jsonl` to inspect the per-step μ-ledgers.
3. Inspect the accompanying `landauer_metadata.json` file to recover the Boltzmann constant, temperature, and ε used.
4. The README dashboard reports two numbers you should try to beat:
   - `min(W/kTln2 − Σμ)` — any negative value is a potential counterexample.
   - `worst deficit beyond ε` — this is the margin after allowing the stated noise tolerance.
5. To contribute a new Landauer run, copy the existing directory structure, add your `landauer_steps.jsonl` and
   `landauer_metadata.json`, run the falsifiability scan, and submit the diff as a pull request.

## 4. Turbulence replication

The turbulence protocol compares blind, sighted, and destroyed solvers on multi-scale fluid datasets.

1. Recreate the archived run:
   ```sh
   make proofpack-turbulence-high RUN_TAG=replication-$(date -u +%Y%m%d%H%M%S)
   ```
2. The command generates new proofpacks under `artifacts/experiments/<RUN_TAG>/`.
3. Run the falsifiability scan.  It will report the mean final runtime ratio and per-module ratios.
4. Compare your ratios with the README dashboard (currently ≈2.49× blind/sighted).  Larger gaps reinforce the prediction,
   while ratios below one are immediate counterexamples.
5. If you find a ratio below one, open a `counterexample` issue with the ledger snippet, command line used, and environment
   details so others can rerun it.

## 5. Cross-domain replication

1. Replay the cross-domain proofpack:
   ```sh
   python scripts/run_proofpack_pipeline.py --profile cross-domain --run-tag cross-domain-replication
   ```
   (All required inputs ship with the repository.)
2. Re-run the falsifiability scan to update the dashboard.
3. Because this dataset is shallow the blind/sighted ratio is currently below one, making it the easiest place to search for a
   counterexample.  If you manage to push the ratio above one with legitimate structure, document it thoroughly.

## 6. Publishing results

- After rerunning any experiment, commit the resulting artefacts under `artifacts/experiments/<RUN_TAG>/`.
- Re-run `python -m tools.falsifiability_analysis --update-readme README.md` and `python -m tools.generate_admit_report`.
- Ensure `git status` shows the README dashboard and `ADMIT_REPORT.txt` updated accordingly.
- Submit a pull request with:
  - the new proofpack directory,
  - the updated README dashboard,
  - a brief summary of the conditions tested,
  - an explicit statement about whether the falsifiable predictions were upheld or violated.

## 7. Reporting counterexamples

If the falsifiability scan reports negative slack or a blind/sighted ratio ≤ 1:

1. Capture the exact CLI invocation and its output.
2. Copy the relevant subset of the proofpack (e.g., the offending `landauer_steps.jsonl` rows) into a gist or the PR.
3. Open an issue with the `counterexample` label and link back to your branch/PR.
4. Expect reviewers to ask for raw data and reproduction scripts.  The goal is to reproduce or refute the anomaly quickly.

By following this playbook you help stress-test the proposed law of compositional information.  Whether you confirm the bound or
break it, please publish your scripts and ledgers so the community can benefit.
