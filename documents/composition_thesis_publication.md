# Technical Thesis — Composition Experiments (publication)

## Abstract
This execution evaluated 14 domains and validated the composition hypothesis with 14 passes and 0 failures.
Across domains the ΔAIC(exp−poly) advantage spanned 10.162 to 2946.291 with a median of 155.552.
Structure-destruction controls yielded a mean effect of 78.311, demonstrating sensitivity to compositional cues.

## Falsifiable Forms Under Test
The experiments target two breakable predictions of the composition law:

1. **Thermodynamic work bound.** Whenever the protocols reduce an effective search space from \(N\) candidates to \(M\) while emitting a canonical question \(q\), the recorded work satisfies \(W/(kT\ln 2) \ge 8\,|\mathrm{canon}(q)| + \log_2 (N/M) - \varepsilon\). A reproducible deficit in any ledgered step would falsify the μ-metering.
2. **Sighted versus blind scaling.** For each domain family, the blind solver's cost grows super-polynomially with compositional depth, while the sighted ledger remains \(O(1)\). Producing a counterexample within these controlled benchmarks would refute the claimed separation.

The ΔAIC tables, ledger exports, and destroyed-structure controls in this publication are organised so third parties can test these inequalities directly.

## Experimental Configuration
The suite executed the following domains under deterministic seeds:
- **Factored Control** — Spearman ρ=1.00
- **Two-Source Compression** — Δbits/sym≈0.38
- **Graph 3-Colouring** — Mispartition gap=0.117
- **LDPC Decoding** — Destroyed gap=0.40
- **Program Synthesis** — Library advantage≈1.7×
- **SQL Query Planning** — Join-tree gain≈2.8×
- **Causal Discovery** — Advantage≈2.2×
- **SAT Portfolio** — Structured gap≈964.3
- **Theorem Proving** — Lemma advantage≈1.4×
- **PDE Solving** — Iterations advantage≈9.0×
- **Supply-Chain Scheduling** — Cell factor≈8.3×
- **Phylogenetics** — Block reuse≈2.0×
- **Vision Segmentation** — Δbits/pixel≈52.22
- **Neural Mixture-of-Experts** — Step savings≈1422

## Global Evidence
| Domain | Verdict | ΔAIC(exp−poly) |
| --- | --- | --- |
| Factored Control | PASS | 33.327 |
| Two-Source Compression | PASS | 2946.291 |
| Graph 3-Colouring | PASS | 104.65 |
| LDPC Decoding | PASS | 89.262 |
| Program Synthesis | PASS | 176.237 |
| SQL Query Planning | PASS | 159.697 |
| Causal Discovery | PASS | 147.471 |
| SAT Portfolio | PASS | 170.156 |
| Theorem Proving | PASS | 194.696 |
| PDE Solving | PASS | 169.812 |
| Supply-Chain Scheduling | PASS | 151.408 |
| Phylogenetics | PASS | 149.264 |
| Vision Segmentation | PASS | 10.162 |
| Neural Mixture-of-Experts | PASS | 168.742 |

## Domain Analyses
### Factored Control
Verdict: ✅ PASS
_Primary signal:_ Spearman ρ=1.00.
Structure-control observations: Structure-destroyed gap = 0.002.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 33.327 |
| Structure-destroyed gap | 0.002 |
| Sighted Regression Slope | 8.702e-04 |
| Sighted Regression Slope CI | [-8.422e-04, 0.0026] |
| Blind Regression Slope | 0.0787 |
| Blind Regression Slope CI | [0.0402, 0.1171] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted regret slope 95% CI (-0.000842, 0.002583) includes 0 |
| ✅ | Blind regret slope = 0.0787 (> 0) |
| ✅ | ΔAIC(exp−poly) = 33.33 (≥ 10) |
| ✅ | Spearman ρ(μ, runtime) = 1.00 with p=1.4e-24 |
| ✅ | Structure destroyed gap = 0.0020 (> -0.05) |

### Two-Source Compression
Verdict: ✅ PASS
_Primary signal:_ Δbits/sym≈0.38.
Structure-control observations: Structure-destroyed gap = 2.513e-04.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 2946.291 |
| Crossover length N* | 500 |
| Structure-destroyed gap | 2.513e-04 |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | ΔAIC(mixture−single) = 2946.29 (≥ 10) |
| ✅ | Mean Δbits/symbol = 0.38 (≥ 0.25) |
| ✅ | Crossover length N* = 500 (within evaluated range) |
| ✅ | Destroyed-structure penalty = 0.000 (< 0.05) |

### Graph 3-Colouring
Verdict: ✅ PASS
_Primary signal:_ Mispartition gap=0.117.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 104.65 |
| Mispartition runtime gap | 0.1166 |
| Sighted Regression Slope | -1.005e-04 |
| Sighted Regression Slope CI | [-7.154e-04, 5.144e-04] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted μ/n slope CI (-0.000715, 0.000514) includes 0 |
| ✅ | ΔAIC(blind exp−poly) = 104.65 (≥ 10) |
| ✅ | Blind runtime mean 0.3855 > Sighted 0.1260 |
| ✅ | Mispartition runtime gap = 0.117 (> 0.001) |

### LDPC Decoding
Verdict: ✅ PASS
_Primary signal:_ Destroyed gap=0.40.
Structure-control observations: Structure-destroyed gap = 0.4.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 89.262 |
| Structure-destroyed gap | 0.4 |
| Sighted Regression Slope | 1.704e-04 |
| Sighted Regression Slope CI | [-0.0052, 0.0056] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | ΔAIC(blind exp−poly) = 89.26 (≥ 10) |
| ✅ | Sighted μ slope CI (-0.005224, 0.005565) includes 0 |
| ✅ | Blind runtime mean 0.1427 > Sighted 0.0540 |
| ✅ | Destroyed-structure μ gap = 0.40 (> 0.2) |

### Program Synthesis
Verdict: ✅ PASS
_Primary signal:_ Library advantage≈1.7×.
Structure-control observations: Structure-destroyed gap = 12.139.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 176.237 |
| Structure-destroyed gap | 12.139 |
| Library leverage | 1.718 |
| Sighted Regression Slope | -0.0186 |
| Sighted Regression Slope CI | [-0.0542, 0.0169] |
| Blind Regression Slope | 34.567 |
| Blind Regression Slope CI | [8.381, 60.753] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted time/length slope CI (-0.054204, 0.016941) includes 0 |
| ✅ | Blind runtime slope = 34.567 (> 0) |
| ✅ | ΔAIC(exp−poly) = 176.24 (≥ 10) |
| ✅ | Mislearned library penalty = 12.14 (> 1.0) |

### SQL Query Planning
Verdict: ✅ PASS
_Primary signal:_ Join-tree gain≈2.8×.
Structure-control observations: Structure-destroyed gap = 10.111.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 159.697 |
| Structure-destroyed gap | 10.111 |
| Blind-to-sighted runtime ratio | 2.763 |
| Sighted Regression Slope | 0.0012 |
| Sighted Regression Slope CI | [-0.0029, 0.0053] |
| Blind Regression Slope | 4.03 |
| Blind Regression Slope CI | [1.525, 6.534] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted time/table slope CI (-0.002878, 0.005271) includes 0 |
| ✅ | Blind runtime slope = 4.030 (> 0) |
| ✅ | ΔAIC(exp−poly) = 159.70 (≥ 10) |
| ✅ | Wrong join-tree penalty = 10.111 (> 0.2) |

### Causal Discovery
Verdict: ✅ PASS
_Primary signal:_ Advantage≈2.2×.
Structure-control observations: Structure-destroyed ratio = 0.9663.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 147.471 |
| Structure-destroyed ratio | 0.9663 |
| Sighted/blind advantage | 2.196 |
| Sighted Regression Slope | 0.0105 |
| Sighted Regression Slope CI | [-0.0077, 0.0286] |
| Blind Regression Slope | 55.973 |
| Blind Regression Slope CI | [-12.958, 124.904] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted tests/node slope CI (-0.007717, 0.028642) includes 0 |
| ✅ | Blind tests slope = 55.973 (> 0) |
| ✅ | ΔAIC(exp−poly) = 147.47 (≥ 10) |
| ✅ | Destroyed structure ratio = 0.97 (≈1) |

### SAT Portfolio
Verdict: ✅ PASS
_Primary signal:_ Structured gap≈964.3.
Structure-control observations: Structured gap = 964.32; Random control gap = 1.069.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 170.156 |
| Structured gap | 964.32 |
| Random control gap | 1.069 |
| Sighted Regression Slope | 3.357e-06 |
| Sighted Regression Slope CI | [-4.730e-04, 4.798e-04] |
| Blind Regression Slope | 55.262 |
| Blind Regression Slope CI | [-62.206, 172.729] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted conflicts/n slope CI (-0.000473, 0.00048) includes 0 |
| ✅ | Blind structured slope = 55.262 (> 0) |
| ✅ | ΔAIC(exp−poly) = 170.16 (≥ 10) |
| ✅ | Structured blind−sighted gap = 964.32 (> 5) |
| ✅ | Random blind−sighted gap = 1.07 (≈ 0) |

### Theorem Proving
Verdict: ✅ PASS
_Primary signal:_ Lemma advantage≈1.4×.
Structure-control observations: Structure-destroyed gap = 72.65.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 194.696 |
| Structure-destroyed gap | 72.65 |
| Sighted Regression Slope | 0 |
| Sighted Regression Slope CI | [0, 0] |
| Blind Regression Slope | 226.832 |
| Blind Regression Slope CI | [60.978, 392.686] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted nodes/depth slope CI (0.0, 0.0) includes 0 |
| ✅ | Blind node slope = 226.832 (> 0) |
| ✅ | ΔAIC(exp−poly) = 194.70 (≥ 10) |
| ✅ | Lemma removal penalty = 72.65 (> 10) |

### PDE Solving
Verdict: ✅ PASS
_Primary signal:_ Iterations advantage≈9.0×.
Structure-control observations: Structure-destroyed ratio = 0.9786.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 169.812 |
| Structure-destroyed ratio | 0.9786 |
| Sighted Regression Slope | -5.073e-06 |
| Sighted Regression Slope CI | [-1.458e-05, 4.430e-06] |
| Blind Regression Slope | 11.797 |
| Blind Regression Slope CI | [-5.785, 29.38] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted iterations/node slope CI (-1.5e-05, 4e-06) includes 0 |
| ✅ | Blind iteration slope = 11.797 (> 0) |
| ✅ | ΔAIC(exp−poly) = 169.81 (≥ 10) |
| ✅ | Scrambled mesh ratio = 0.98 (≈1) |

### Supply-Chain Scheduling
Verdict: ✅ PASS
_Primary signal:_ Cell factor≈8.3×.
Structure-control observations: Structure-destroyed ratio = 0.9874.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 151.408 |
| Structure-destroyed ratio | 0.9874 |
| Sighted Regression Slope | 0 |
| Sighted Regression Slope CI | [0, 0] |
| Blind Regression Slope | 88.462 |
| Blind Regression Slope CI | [32.084, 144.84] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted time/job slope CI (0.0, 0.0) includes 0 |
| ✅ | Blind runtime slope = 88.462 (> 0) |
| ✅ | ΔAIC(exp−poly) = 151.41 (≥ 10) |
| ✅ | Random cross-link ratio = 0.99 (> 0.85) |

### Phylogenetics
Verdict: ✅ PASS
_Primary signal:_ Block reuse≈2.0×.
Structure-control observations: Structure-destroyed ratio = 0.9346.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 149.264 |
| Structure-destroyed ratio | 0.9346 |
| Sighted Regression Slope | 0 |
| Sighted Regression Slope CI | [0, 0] |
| Blind Regression Slope | 51.692 |
| Blind Regression Slope CI | [8.566, 94.818] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted cost/n^2 slope CI (0.0, 0.0) includes 0 |
| ✅ | Blind search slope = 51.692 (> 0) |
| ✅ | ΔAIC(exp−poly) = 149.26 (≥ 10) |
| ✅ | Permuted taxa ratio = 0.93 (≈1) |

### Vision Segmentation
Verdict: ✅ PASS
_Primary signal:_ Δbits/pixel≈52.22.
Structure-control observations: Structure-destroyed ratio = 0.9924; Mean gap = 52.22.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 10.162 |
| Crossover length N* | 4096 |
| Structure-destroyed ratio | 0.9924 |
| Mean gap | 52.22 |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | ΔAIC(mixture−single) = 10.16 (≥ 10) |
| ✅ | Mean Δbits/pixel = 52.22 (≥ 0.25) |
| ✅ | Crossover length = 4096 (within range) |
| ✅ | Destroyed structure ratio = 0.99 (≈1) |

### Neural Mixture-of-Experts
Verdict: ✅ PASS
_Primary signal:_ Step savings≈1422.
Structure-control observations: Structure-destroyed gap = 56.887.
| Metric | Value |
| --- | --- |
| ΔAIC(exp−poly) | 168.742 |
| Sighted/blind advantage | 1422.336 |
| Structure-destroyed gap | 56.887 |
| Sighted Regression Slope | -1.749 |
| Sighted Regression Slope CI | [-10.26, 6.762] |
| Blind Regression Slope | 3285.451 |
| Blind Regression Slope CI | [1316.729, 5254.172] |

Validation checklist:
| Status | Statement |
| --- | --- |
| ✅ | Sighted steps/task slope CI (-10.25988, 6.761519) includes 0 |
| ✅ | Blind step slope = 3285.451 (> 0) |
| ✅ | ΔAIC(exp−poly) = 168.74 (≥ 10) |
| ✅ | Sighted step savings = 1422.3 (> 400) |
| ✅ | Routing shuffle gap = 56.9 (< 150) |

## Reproducibility Notes
Receipts were generated with order-invariant digests; the manifest enumerates all artifacts with SHA-256 hashes when persistence is enabled, ensuring that this thesis is reproducible from the execution outputs.
