# Conservation of compositional information

This note states the No Unpaid Sight Debt (NUSD) bound in a unitful form
and explains how the law receipts now attest to the inequality.

## The inequality

For any audited Thiele reduction that narrows a possibility space from
\(N\) candidate states to \(M\) certified states at ambient temperature
\(T\), the physical work satisfies

\[
  \frac{\text{work}}{k_B T \ln 2} \ge \mu_{\text{question}} + \log_2 \frac{N}{M} - \varepsilon.
\]

- \(\mu_{\text{question}}\) is the μ-cost to specify the sighted
  structure (question) that exposes the latent invariant.
- \(\log_2(N/M)\) is the μ-cost to collapse the residual possibilities
  once the structure is in hand.
- \(\varepsilon\) is an explicit slack term for experimental error or
  audit tolerances.
- \(k_B\) is Boltzmann’s constant (exactly
  `1.380649×10⁻²³ J/K`), so the right-hand side is measured in μ-bits.

The law receipt reports the left-hand side in joules via two routes:

1. **Landauer bound.** The summary records
   `landauer_factor_j_per_bit = k_B T ln 2` and multiplies it by the
   μ-total to produce `landauer_work_bound_joules`.
2. **Empirical calibration.** When a calibration dataset is supplied, the
   receipt embeds its digest and statistics so the verifier can replay
   the measured mean energy-per-μ-bit and compute the corresponding
   energy prediction.

## How the receipt encodes the terms

Inside the final `law_summary` block:

- `mdl_bits.model_bits` → \(\mu_{\text{question}}\)
- `mdl_bits.baseline_bits - mdl_bits.residual_bits` → \(\log_2(N/M)\)
- `nusd_bound.epsilon_bits` stores \(\varepsilon\)
- `nusd_bound.mu_total_bits` is the RHS combined (minus ε)
- `nusd_bound.landauer_work_bound_joules` gives the work bound
- `nusd_bound.calibration.*` captures the dataset used to convert μ-bits
  into joules empirically (mean, standard deviation, sample count, total
  μ, total energy, and SHA-256)

The verification script re-computes every quantity from first principles
and fails if any number drifts beyond 10⁻⁹ relative tolerance.

## Calibrating μ against joules

Use the new helper to inspect or recompute the calibration summary:

```
python3 tools/mu_calibration.py mu_bit_correlation_data.json --temperature 295 --mu-bits 128
```

The command prints the dataset digest, per-μ statistics, and the implied
Landauer/empirical work for the chosen μ total. The make target wires the
same dataset through `tools/make_law_receipt.py`, so the receipt itself
contains a cryptographic pointer to the calibration source.

## Relationship to the lattice law demo

Running `make law` now produces a bundle that states the NUSD bound,
proves the discovered lattice invariants, and includes both the Landauer
bound and the empirical calibration. Independent labs can substitute
their own power logs by pointing `--calibration-file` at a different
JSON dataset; the verifier will recompute the statistics and certify the
new μ ↔ joule relationship.

## Universal receipts across logic, computation, and physics

`tools/make_nusd_receipt.py` generalises the lattice demo into a
multi-domain instrument. The script writes hash-chained receipts for:

1. the lattice variational law (`--domain lattice`, seeded synthetic
   trace with the same invariants as `make law`),
2. the golden Tseitin expander benchmark (`--domain tseitin`), exposing
   the μ ledgers from the audited UNSAT certificate,
3. an elementary cellular automaton run (`--domain automaton`), where
   the observed bit patterns reconstruct the generator rule, and
4. a synthetic turbulence cascade (`--domain turbulence`), which fits an
   AR(1) energy law and records the inferred coefficients.

Each receipt logs `mdl_bits`, the μ-question/answer split, the Landauer
work bound, and optional calibration metadata. The companion verifier
`tools/verify_nusd_receipt.py` replays the domain-specific calculations,
recomputes the μ and Landauer terms, checks the HMAC, and rejects any
deviation. The new `make nusd` target runs all four domains in sequence
and leaves the receipts beneath `artifacts/` ready for auditors.

This bundle provides the “one inequality everywhere” witness: the same
NUSD bound holds for lattice laws, logic certificates, compositional
computation, and physics-style traces, and every receipt is independently
verifiable.

## Sighted vs. blind turbulence head-to-head

Phase 2 adds a direct comparison between a structure-aware (sighted) solver
and a structure-agnostic (blind) baseline operating on the shared turbulence
dataset. Run

```
make headtohead
```

to generate `artifacts/turbulence_head_to_head.jsonl` and replay the
verifier. The receipt records the μ-question and μ-answer contributions for
both solvers, the derived NUSD bounds, and the calibrated Landauer work
floors. Because the blind path must encode every observation explicitly, it
pays hundreds of additional μ-bits relative to the sighted AR(1) model; the
summary highlights this Δμ as `mu_gap_bits` and signs the result with an
HMAC.

The accompanying schema (`docs/turbulence_head_to_head.schema.json`) and
HOWTO (`docs/HOWTO_VERIFY_HEAD_TO_HEAD.md`) document the artifact format and
verification workflow so that third parties can independently attest to the
gap. This head-to-head run will serve as the witness for the forthcoming
proofpack bundle that pits sighted Thiele processes against blind
Turing-style enumerators.

## Phase three proofpack

The new `make proofpack-phase3` target bundles the Bell receipt, the lattice
law receipt, all four NUSD domain receipts, and the turbulence head-to-head
comparison into a single, hash-manifested archive. The accompanying verifier
(`tools/verify_phase_three_proofpack.py`) replays every domain-specific
auditor, rebuilds the combined Coq harness, and checks the master theorem
`phase_three_verified`, which leverages `ThieleMachine.PhaseThree` to show that
the sighted solver’s μ-ledger is strictly cheaper than the blind baseline. See
`docs/HOWTO_VERIFY_PHASE_THREE_PROOFPACK.md` for step-by-step instructions.
