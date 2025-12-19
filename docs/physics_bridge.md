# Physics Bridge: From μ-Ledger Events to Measurable Resources

This note captures the explicit mapping from Thiele Machine μ-ledger events to physically measurable observables and the falsifiable predictions that fall out of that mapping. It is intended to be a working contract for committee review and for future experiments.

**Claim (scoped, falsifiable):** For the Ω→Ω′ workloads instantiated by the thermodynamic bridge harness, the μ-ledger is a lower bound on the bits of state-space reduction. Under the bridge postulate \(Q_{\min} = k_B T \ln 2 \cdot \mu\), any physical execution that realizes the same Ω→Ω′ map must dissipate at least \(k_B T \ln 2 \cdot \log_2(|\Omega|/|\Omega'|)\) of heat. Evidence mode (`EVIDENCE_STRICT=1`) fails closed if any layer emits zero/missing μ or attempts normalization; development mode (`ALLOW_MU_NORMALIZE=1`) records any substituted μ as `mu_normalized=true` with a reason.

**Reproducibility note:** The harness scripts accept `--out <path>` so artifacts can be generated anywhere. The default `results/*.json` outputs are intentionally gitignored so local runs don’t pollute the repository.

## 1. Translation dictionary (definitions, not prose)
- **Physical microstate space (Ω):** An implementation with \(n\) resolvable bits has \(|\Omega| = 2^n\) admissible states. A constraint or certificate defines \(\Omega' \subseteq \Omega\) with reduction factor \(|\Omega|/|\Omega'|\). In the executed workloads, \(\Omega\) counts the admissible singleton modules within a candidate pool (e.g., 2, 4, 16, 64 possible elements) because the canonical partition mask is 64-bit and the current RTL encoding only supports operand-encoded singletons.
- **Revelation as state-space reduction:** Any step that asserts structure (e.g., `PNEW`, `PSPLIT`, `MDLACC`, `REVEAL`) is a map \(\Omega \to \Omega'\). The normalized certificate bitlength (MDL or explicit info charge) is the canonical \(\mu\) debit for that reduction. Genesis remains free; the μ debits reported here arise from explicit `PNEW` + MDL auto-charging, not from the initial module.
- **Bridge postulate (thermodynamic resource):** Charging \(\mu\) bits for \(\Omega \to \Omega'\) lower-bounds the physical entropy reduction and hence the heat/work cost: \(Q_{\min} = k_B T \ln 2 \cdot \mu\), up to an explicit device inefficiency factor \(\epsilon \ge 1\).
- **Operational invariants:**
  - \(\mu\) is monotone non-decreasing along a trace (proved in Coq; enforced by the μ-parity gates).
  - Genesis is free; every nontrivial revelation must increase \(\mu\). Zero \(\mu\) at trace end is only allowed for the genesis-only trace.
  - Normalization is explicit: `mu_raw` (emitted by each layer) vs `mu` (effective). Any normalization is flagged and justified; absent `ALLOW_MU_NORMALIZE`, missing/zero μ is a hard failure. With `EVIDENCE_STRICT=1`, normalization is refused even if `ALLOW_MU_NORMALIZE` is set.

## 2. Bridge theorem (sanity anchor)
Given:
1. **Kernel inequality (proved):** No Free Insight ⇒ \(\mu\) never decreases under allowed instructions.
2. **Bridge postulate (assumed):** \(\mu\) bits of revelation imply \(Q_{\min} = k_B T \ln 2 \cdot \mu\).

Then for any trace implementing \(\Omega \to \Omega'\):
\[ Q_{\text{dissipated}} \ge k_B T \ln 2 \cdot \log_2(|\Omega|/|\Omega'|) \]
Because \(\mu \ge \log_2(|\Omega|/|\Omega'|)\) by construction, the ledger enforces the Landauer-style lower bound when paired with the thermodynamic postulate.

## 3. Falsifiable prediction (non-rhetorical)
For a workload that differs only by the enforced constraints (e.g., fixing 1 bit, 2 bits, enforcing parity, fixing a nibble), the measured energy/heat must scale with \(\mu\) at slope \(k_B T \ln 2\) (within stated inefficiency bounds). A sustained sub-linear slope falsifies the bridge; a super-linear slope quantifies implementation overhead.

## 4. Experimental protocol (publishable, reproducible)
- **Workload construction:** Use the thermodynamic bridge harness to emit traces where the only difference is the Ω reduction over singleton modules drawn from candidate pools of size \(2^k\). Keep instruction count, data size, and clocking identical and fail if a requested region is not representable in RTL.
- **Recorded ledger fields:** Per-step `mu_raw` and `mu`, Ω and Ω′ sizes, and normalization flags for Python/Coq/RTL layers, plus `evidence_strict` to signal whether normalization was permitted.
- **Physical measurement:** Run on instrumented hardware (or a calibrated switching-energy simulator) with fixed temperature \(T\). Measure per-run energy or heat; report sampling error and calibration metadata.
- **Analysis:** Fit measured energy against \(k_B T \ln 2 \cdot \mu\). Report residuals and whether points fall below the lower bound. Publish both raw measurements and the emitted ledger for cross-checking.
- **Controls:** A genesis-only trace should report \(\mu = 0\) and near-zero energy above idle. Any nontrivial trace must report \(\mu > 0\); a zero μ reading is a test failure, not “alignment.”

### How to generate artifacts

- Thermodynamic singleton bundle: `python scripts/thermo_experiment.py --out /abs/path/thermo_experiment.json`
- Structural heat bundle: `python scripts/structural_heat_experiment.py --out /abs/path/structural_heat_experiment.json`
- Time dilation bundle: `python scripts/time_dilation_experiment.py --out /abs/path/time_dilation_experiment.json`

## 5. Implementation status and next work
- **Status:** The equivalence bundle already emits `mu_raw`, `mu`, and normalization metadata for Python, extracted Coq, and RTL, and fails closed when μ is missing unless `ALLOW_MU_NORMALIZE=1` is set.
- **Next steps:**
  - Add an instrumented runner to log wall power and temperature alongside the existing bundle output.
  - Gate traces so that a zero μ from any layer on a nontrivial Ω reduction fails immediately.
  - Publish a reference dataset (Ω sizes, μ, energy) for the 1-bit/2-bit/parity trio and include regression plots in the thesis.

## 6. Executed thermodynamic bundle (Dec 2025)
We ran four Ω→Ω′ workloads that reveal a singleton module drawn from pools of size \(2, 4, 16, 64\) with the thermodynamic bridge harness (`scripts/thermo_experiment.py`). The harness produces a JSON artifact (default: `results/thermo_experiment.json`, override with `--out`) capturing per-run μ, normalization status, scaling ratios, and Landauer lower bounds at 300 K:

| scenario | μ (python) | μ_raw (extracted/rtl) | normalized? | log₂(|Ω|/|Ω′|) | k_B·T·ln2·μ (J) | μ/log₂(|Ω|/|Ω′|) |
| --- | --- | --- | --- | --- | --- | --- |
| singleton_from_2 | 2 | 2 / 2 | no | 1 | 5.74×10⁻²¹ | 2.0 |
| singleton_from_4 | 3 | 3 / 3 | no | 2 | 8.61×10⁻²¹ | 1.5 |
| singleton_from_16 | 5 | 5 / 5 | no | 4 | 1.44×10⁻²⁰ | 1.25 |
| singleton_from_64 | 7 | 7 / 7 | no | 6 | 2.02×10⁻²⁰ | 1.167 |

Notes:
- The bundle now encodes an explicit μ-delta into the `PNEW` instruction stream (Coq trace + RTL word). The Python VM consumes the same μ-delta (no implicit MDLACC), so `mu_raw` matches across layers and evidence mode can pass without normalization.
- Aligned=True in the bundle confirms regs/mem/μ match across layers for these traces.

## 7. Structural heat anomaly harness (Jan 2026)

To stress the “structure has binding energy” claim, `scripts/structural_heat_experiment.py` generates a paired workload over the same 1 GiB erase task:

- **erase_random_noise:** no structural certificate; μ only reflects the erase itself.
- **erase_structured_sorted:** the buffer is assumed sorted; μ debits include the \(\log_2(n!)\) reduction for \(n = 2^{20}\) records via an explicit `info_charge` receipt.

The emitted artifact (default: `results/structural_heat_experiment.json`) records μ, \(\log_2(|\Omega|/|\Omega'|)\), and the Landauer lower bound at the configured temperature. For Ω bookkeeping the harness treats a 1 GiB buffer as \(8\times\) that many bits of microstate capacity. The structured workload pays dramatically more μ and therefore reports a higher Landauer floor than the random erase, making the “structural heat” differential concrete and testable once physical instrumentation is wired in.

## 8. Time dilation budget experiment (Feb 2026)

`scripts/time_dilation_experiment.py` implements the ledger-speed limit story: a module receives a fixed μ budget per global tick and must spend it on communication (EMIT-like payloads) before local computation. The resulting artifact `results/time_dilation_experiment.json` shows the compute rate dropping monotonically—from 32 steps/tick with no communication to 8 steps/tick under heavy communication—while μ totals remain conserved at a fixed per-tick budget. Evidence mode can extend this harness by instrumenting actual EMIT payloads and RTL traces; the current run is a ledger-level proof-of-concept that “speed” is constrained by μ spend, aligning the bridge toward a Lorentz-style speed limit.

## 9. Demonstrations (Feb 2026)
- **Visual proof (speed-limit curve):** `scripts/plot_time_dilation_curve.py` plots `results/time_dilation_experiment.json` as `results/time_dilation_curve.svg`, showing the monotonic compute-rate drop as communication μ rises.
- **Hardware proof (waveform):** `scripts/generate_waveform.py` compiles `thiele_cpu_tb.v` with Icarus and emits `results/thiele_cpu_tb.vcd`; the `mu` staircase is visible against `clk` in any VCD viewer (GTKWave).
- **Halting trap (budgeted loop):** `scripts/halting_trap.py` simulates an infinite loop with a finite μ budget, producing `results/halting_trap.json` where execution halts at budget with status `mu_overflow` and a recorded μ trace.
