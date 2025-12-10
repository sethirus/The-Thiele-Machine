# NUSD Reviewer Pack

This pack aligns the three “locks” requested for the audit: a theorem-level derivation, a
physics-facing prediction, and an engineering artifact that exhibits the μ-gap in practice.  Each
section points to the supporting scripts and receipts.

## Lock 1 — Math: Golden-angle theorem

- **Definitions.**  The dedicated note formalises the μ-functional with a fixed continued-fraction
  prefix \(k = \lceil \log_2 N \rceil\) and the squared-discrepancy residual for \(N\) seeds.【F:docs/NUSD_Golden_Angle_Theorem.md†L3-L20】
- **Result.**  The golden angle \(\theta_\varphi = 1/\varphi^2\) uniquely minimises \(\mu_{\text{total}}\) among irrational
  rotations under that functional; rationals remain inadmissible because their residual diverges.【F:docs/NUSD_Golden_Angle_Theorem.md†L22-L43】
- **Numerical verification.**  The table below comes from `tools/analyze_golden_angle.py` and confirms
  that the golden angle wins against classical irrationals and random samples once the ledger is
  evaluated with \(N=128,256,512\).【17c7c3†L1-L25】

| angle | seeds | μ_question | μ_answer | μ_total |
|-------|-------|------------|----------|---------|
| golden | 128 | 7.000 | 0.135 | 7.135 |
| golden | 256 | 8.000 | 0.112 | 8.112 |
| golden | 512 | 9.000 | 0.147 | 9.147 |
| √2 mod 1 | 512 | 14.265 | 0.137 | 14.402 |
| π mod 1 | 512 | 21.780 | 2.145 | 23.925 |

- **Mapping back.**  State = Fermat spiral, μ-question encodes the continued-fraction prefix, μ-answer
  is the log-discrepancy, NUSD forbids collisions (rationals), and the observable prediction is
  \(\theta = 1/\varphi^2\) from the theorem.

## Lock 2 — Physics: finite invariant signal speed

- **Model.**  The physics note introduces a 1+1D causal lattice, with μ-question tracking a proposed
  light-cone radius and μ-answer penalising any excursion outside that cone.【F:docs/NUSD_Finite_Signal_Speed.md†L1-L24】
- **Experiment.**  `tools/analyze_signal_speed.py` simulates a worldline at unit speed and evaluates the
  ledger in Lorentz-drifted frames.  Every frame is minimised at the same finite propagation speed,
  demonstrating a universal bound rather than a coordinate artefact.【9bdbca†L1-L22】

| frame drift | candidate c | μ_question | μ_answer | μ_total |
|-------------|-------------|------------|----------|---------|
| +0.00 | 1.00 | 1.000 | 0.000 | 1.000 |
| −0.40 | 1.00 | 1.000 | 0.000 | 1.000 |
| +0.40 | 1.00 | 1.000 | 0.000 | 1.000 |

- **Mapping.**  State = trajectory \((t, x)\); μ-question = \(\log_2(1+c^2)\); μ-answer accumulates the
  squared violation beyond the cone; NUSD enforces the finite cone in every inertial frame; the
  prediction is the shared minimiser \(c = 1\).

## Lock 3 — Engineering: structural discovery receipts

### 3.1 Turbulence head-to-head

The turbulence receipt remains the core engineering witness: sighted vs blind solvers on the shared
pseudo-turbulent trace, with the signed ledger recording a linear μ-gap.【F:docs/HOWTO_VERIFY_HEAD_TO_HEAD.md†L1-L46】【87a264†L1-L3】

| samples | μ_total (blind) | μ_total (sighted) | μ_gap | generation time (s) |
|---------|-----------------|-------------------|-------|---------------------|
| 96 | 1540.022 | 4.192 | 1535.829 | 0.205 |
| 192 | 3076.012 | 5.041 | 3070.971 | 0.177 |
| 384 | 6148.002 | 5.587 | 6142.415 | 0.186 |

The signed summary line (e.g. `mu_gap_bits = 1535.829…`) and the verifier
`tools/verify_turbulence_head_to_head.py` provide the replayable certificate.【d54365†L1-L20】

### 3.2 Structure-aware modelling CLI

To make the engineering lock reproducible without a full receipt run, the new
`tools/thiele_structural_modeler.py` exposes the automaton and turbulence discovery domains via a
single CLI.  Two canonical runs illustrate the structural compression:

- **Rule 110 automaton** — 64×64 grid inferred exactly with 8 μ-question bits and no residuals, versus
  4032 baseline bits.【a9c754†L1-L6】
- **Turbulence AR(1)** — 96-sample trace compressed to ~1.12 bits (model + residual), beating the blind
  baseline by over two bits even before calibration.【3e22a5†L1-L6】

Invocations match the commands above; the optional `--export` flag writes a JSON summary so reviewers
can diff the parameters and μ-ledgers directly.

### 3.3 Turbulence law receipts (v1 → v2)

Two receipts are now available:

1. `make turbulence-law` – the original three-cascade witness (v1);【F:docs/NUSD_Turbulence_Law.md†L1-L53】
2. `make turbulence-law-v2` – the upgraded, multi-dataset search that outputs the conservation
   law \(E_{t+1} = E_t\) and records kilobit-scale μ-gaps on the isotropic1024 and channel-flow
   DNS excerpts.【F:docs/NUSD_Turbulence_Law_v2.md†L1-L44】

3. `python3 tools/make_turbulence_closure_v1_receipt.py` – the closure witness that compresses
   gradients to ≈1.6 μ-bits across the same bundles while blind encoding spends ≥1.2 kilobits.
   See `docs/NUSD_Turbulence_Closure_v1.md` for the per-series ledger and reproduction guide.【F:docs/NUSD_Turbulence_Closure_v1.md†L1-L32】

Both receipts are HMAC-signed, include the blind baselines, and ship with verifiers that recompute
the ledger end to end.【F:artifacts/turbulence_law_receipt.jsonl†L85-L171】【F:artifacts/turbulence_law_v2_receipt.jsonl†L1-L200】

### 3.4 Self-model receipt

`make self-model-v1` turns the VM instrumentation on itself, discovers the symbolic law
\(\Delta \mu_{\text{total}} = 7.142857·[\text{op} = \texttt{MDLACC}]\), and signs a receipt that
compresses the combined workloads to 76.95 μ-bits versus 264 μ-bits for blind logging—a 187.05-bit
gap.【F:docs/NUSD_Self_Model_v1.md†L1-L35】【F:artifacts/self_model_v1_receipt.jsonl†L1-L6】  The document
also lists the per-workload ledgers (idle, partition, proof, turbulence) so reviewers can inspect the
μ_question/μ_answer balance directly.【F:docs/NUSD_Self_Model_v1.md†L23-L33】  Verification mirrors the
other receipts via `python3 tools/verify_self_model_v1_receipt.py`, which recomputes the ledger and
checks the HMAC chain.【F:docs/NUSD_Self_Model_v1.md†L37-L44】

Together these locks provide algebraic certainty, a physics-facing prediction, and an engineered
artifact that replays the NUSD law end to end.
