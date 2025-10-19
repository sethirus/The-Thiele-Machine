# Shor-on-Thiele Demonstration – Empirical Analysis

## Overview
`scripts/shor_on_thiele_demo.py` stages a reproducible three-act
factorisation of \(N = 21\) with base \(a = 2\). Act I performs blind
trial division, Act II invokes the Thiele-native period oracle, and
Act III summarises the contrasting cost ledgers. Each run refreshes the
receipts under `shor_demo_output/`, including the per-act summaries,
solver reasoning log, and consolidated `analysis_report.json` for
auditors.【F:scripts/shor_on_thiele_demo.py†L1-L189】【F:shor_demo_output/analysis_report.json†L1-L39】

The period oracle backs the demonstration. `thielecpu/shor_oracle.py`
implements `find_period_with_claims`, which encodes Shor’s order
conditions in Z3, iteratively issues claims about the order’s parity and
bounds, and records both the μ-bit cost and the solver trail. The oracle
currently supports the \(N = 21, a = 2\) showcase but is designed to be
extended to richer claim strategies in future milestones.【F:thielecpu/shor_oracle.py†L1-L239】

## Act-by-Act Results

| Act | Strategy | Arithmetic Work | μ-cost | Notable Artefacts |
| --- | --- | --- | --- | --- |
| I | Sequential trial division up to \(\sqrt{21}\) | 2 divisor checks | 0.0 | `act_i/division_trace.json` records the checked divisors in order.【F:shor_demo_output/act_i/summary.json†L1-L9】【F:shor_demo_output/act_i/division_trace.json†L1-L12】 |
| II | Paid period reasoning via oracle claims | 0 divisor checks | 7.0 | `act_ii/reasoning_summary.json` details seven claims (evenness, bounds, divisibility) culminating in period \(r = 6\).【F:shor_demo_output/act_ii/summary.json†L1-L15】【F:shor_demo_output/act_ii/reasoning_summary.json†L1-L120】 |
| III | Comparative verdict | Aggregates | Aggregates | `analysis_report.json` collates the ledgers and arithmetic call counts.【F:shor_demo_output/analysis_report.json†L1-L39】 |

Both Act I and Act II land on the same factor pair \((3, 7)\). The
contrasting ledgers emphasise the core thesis: the Thiele run expends
no classical divisor checks after purchasing the order witness with
seven μ-bits.

## Relation to the Formal Proof

Milestone 4 discharges the admitted `shor_reduction` theorem in
`coq/shor_primitives/PeriodFinding.v`, showing that once an even period
\(r\) is obtained, the Euclidean GCD of \(a^{r/2} - 1\) and \(N\)
produces a non-trivial divisor. The empirical Act II receipts provide
the concrete witness (period 6), while the proof formalises the
reduction from the period to the factor.【F:coq/shor_primitives/PeriodFinding.v†L26-L47】

## Interpretation

1. **Measured trade-off.** The demo captures the advertised substitution
   of reasoning for arithmetic: two divisor checks collapse to zero once
   the oracle spends seven μ-bits.
2. **Oracle dependency.** The speed-up relies on the hosted Z3 oracle
   reconstructing the period; no hardware-level geometric reasoning is
   implemented yet.
3. **Auditability.** The receipts and reasoning log provide a
   tamper-evident trail, and the formally proven `shor_reduction`
   validates that the recorded period suffices to deliver a divisor.

The experiment therefore complements the graph-colouring laboratory by
showing the same μ-bit versus arithmetic trade-off on a period-finding
problem, while acknowledging that the heavy lifting currently occurs in
host-side reasoning rather than native Thiele hardware.
