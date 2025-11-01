# Thiele Machine Repository Deep-Dive Working Document

## 1. Executive Summary
- The repository claims a “Thiele law of compositional information” that charges every reasoning step a μ-bit tariff equal to description length plus information gain, enforced across tooling by μ-spec v2.0.【F:spec/mu_spec_v2.md†L1-L99】
- The formal model defines a Thiele machine as a tuple \(T = (S, \Pi, A, R, L)\) and asserts that Turing machines are crippled, blind instances (\(\Pi = \{S\}\)).【F:documents/The_Thiele_Machine.tex†L27-L148】
- Coq proofs show the Thiele interpreter simulates Turing machines and provide an existence proof of behaviour outside the Turing subset via a “claim tape is zero” instruction, but that separation relies on non-Turing primitives and admitted lemmas.【F:coq/kernel/Subsumption.v†L48-L118】【F:coq/kernel/Kernel.v†L15-L66】【F:ADMIT_REPORT.txt†L1-L25】
- Empirical evidence centres on Tseitin experiments whose published CSV lists sighted μ-costs hundreds of bits, contradicting the README table that reports single-digit sighted costs and uses those values to compute ratios.【F:experiments/20251101_070033_ci_fix/results_table.csv†L1-L8】【F:README.md†L12-L33】
- The inference report flags key preregistered tests as failing (exponential fit, flat sighted slope, monotone ratios) yet concludes the theory is confirmed, highlighting internal inconsistencies.【F:experiments/20251101_070033_ci_fix/inference.md†L1-L41】

## 2. Law Definition and Metering Mechanics
- μ-spec v2.0 defines canonical S-expression encoding and the μ-cost \(μ(q,N,M) = 8|\mathrm{canon}(q)| + \log_2(N/M)\), enforcing positive integer possibility counts and additive composition.【F:spec/mu_spec_v2.md†L13-L63】
- The implementation `thielecpu/mu.py` matches the spec: canonicalisation tokenises parentheses/atoms, question cost multiplies canonical byte length by eight, and information gain validates `after ≤ before` before applying `log₂`.【F:thielecpu/mu.py†L10-L63】
- Tooling such as `tools/check_mu_ledger.py` validates receipts by ensuring μ-question multiples of eight, non-negative μ-answer, and equality with recorded info gain, but it never recomputes `log₂(N/M)` from raw counts, so it cannot detect if ledgers encode inconsistent `N, M` pairs.【F:tools/check_mu_ledger.py†L1-L60】

## 3. Formal Semantics and Proof Obligations
- The thesis text positions the Thiele machine as a formally audited model rejecting opaque oracles, with the logic engine `L` required to emit certificates, record receipts, and meter costs.【F:documents/The_Thiele_Machine.tex†L121-L170】
- Coq file `Subsumption.v` proves `thiele_simulates_turing` (stepwise equivalence on Turing-safe programs) and `turing_is_strictly_contained` using a program consisting of `H_ClaimTapeIsZero`, an instruction explicitly tagged as non-Turing.【F:coq/kernel/Subsumption.v†L48-L118】【F:coq/kernel/Kernel.v†L15-L66】
- The ADMIT report lists five active axioms for kernel simulation and additional archived admits, indicating key simulation lemmas are assumed rather than derived, limiting the formal guarantee’s strength.【F:ADMIT_REPORT.txt†L1-L25】

## 4. Empirical Evidence Audit
### 4.1 Partition Experiments
- `run_partition_experiments.py` computes μ metrics by estimating the initial search space as `2^(1.5 n)` and, for UNSAT sighted runs, setting `after = 1`. It then adds a deterministic quadratic term `2n² + 2n` labelled “theoretical Thiele sighted costs”, storing the sum as `mu_sighted`.【F:run_partition_experiments.py†L159-L191】
- Receipts and `results_table.csv` capture these augmented sighted costs: for `n=6` the sighted total is 285 μ-bits versus 15 blind conflicts, escalating to 911 μ-bits by `n=18`.【F:experiments/20251101_070033_ci_fix/receipt_n6_seed0_1761980434.json†L1-L40】【F:experiments/20251101_070033_ci_fix/receipt_n6_seed0_1761980434.json†L41-L80】【F:experiments/20251101_070033_ci_fix/results_table.csv†L1-L8】
- The README table instead reports “Sighted μ_answer” equal to the logarithmic term (9–27 μ-bits) and uses those values to compute the ratio column, so CI checks verify the arithmetic but not the correspondence to the archived sighted totals.【F:README.md†L12-L33】【F:tools/check_readme_tables.py†L1-L49】
- The inference report for the published run notes all preregistered evidence tests fail (exponential > polynomial AIC, sighted slope CI crossing zero, monotone ratio bootstrap) yet concludes the theory is validated, contradicting its own statistics.【F:experiments/20251101_070033_ci_fix/inference.md†L1-L41】

### 4.2 Falsifiability Dashboard
- `tools/falsifiability_analysis.py` aggregates Landauer work ledgers, turbulence runtimes, and cross-domain experiments entirely from repository proofpacks, computing ratios and slack without external baselines.【F:tools/falsifiability_analysis.py†L120-L252】
- The README reproduces the dashboard numbers and emphasises CI enforcement, but all data originates from the same toolchain responsible for producing the ledgers, so independence is absent.【F:README.md†L36-L68】

## 5. Consistency and Soundness Assessment
- Metering code aligns with the written specification, so internal μ calculations are self-consistent when provided valid `N, M` counts, yet the repository does not expose those raw counts in ledgers, preventing independent recomputation of μ_answer.【F:spec/mu_spec_v2.md†L31-L63】【F:thielecpu/mu.py†L44-L63】【F:experiments/20251101_070033_ci_fix/receipt_n6_seed0_1761980434.json†L41-L80】
- The claimed strict containment of Turing machines depends on a primitive (`H_ClaimTapeIsZero`) unavailable to classical machines and on axioms recorded in `ADMIT_REPORT.txt`, so the result establishes an oracle-style extension rather than a contradiction of Church-Turing.【F:coq/kernel/Subsumption.v†L78-L118】【F:coq/kernel/Kernel.v†L15-L66】【F:ADMIT_REPORT.txt†L1-L25】
- Empirical claims of near-constant sighted costs conflict with archived μ ledgers, which grow quadratically because of the injected theoretical term. The README’s ratios therefore compare blind conflicts against μ_answer alone, not the recorded sighted totals.【F:experiments/20251101_070033_ci_fix/results_table.csv†L1-L8】【F:README.md†L12-L33】【F:run_partition_experiments.py†L179-L191】
- The inference narrative asserts success despite test failures, reducing confidence in the claimed falsifiability discipline.【F:experiments/20251101_070033_ci_fix/inference.md†L1-L41】

## 6. Refutation Opportunities
- **Statistical counterexamples:** Demonstrate problem families where blind μ_conflict growth remains polynomial relative to μ_answer by regenerating experiments with alternative seeds or structures; the inference report’s failed monotonicity already hints at such counterexamples.【F:experiments/20251101_070033_ci_fix/inference.md†L1-L41】
- **Thermodynamic bounds:** Obtain physical measurements of work for a process using the μ-ledger to translate to bits; any reproducible violation of \(W/(kT\ln 2) ≥ μ_total - ε\) would falsify the law.【F:documents/The_Thiele_Machine.tex†L55-L68】
- **Formal model stress tests:** Construct Thiele programs that require primitives excluded by Turing machines but question whether those primitives preserve the stated invariants without the admitted lemmas; a counterexample would undermine strict containment claims.【F:coq/kernel/Subsumption.v†L78-L118】【F:ADMIT_REPORT.txt†L1-L25】

## 7. Conclusion
The Thiele Machine artifact integrates a coherent μ-meter implementation and a substantial formal/empirical scaffolding, but its strongest claims rest on internally generated evidence with notable inconsistencies: sighted μ costs in receipts diverge from published tables, statistical criteria fail while conclusions declare success, and formal separations depend on non-classical primitives and axioms. Until independent experiments verify the thermodynamic bound or demonstrate exponential blind-vs-sighted separation using externally audited data, the “Thiele law” remains an intriguing yet unvalidated conjecture.
