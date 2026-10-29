# kernel/quantum

CHSH, Tsirelson, and the NPA positive-semidefinite conditions, reached by
polynomial certificates over the rationals and the reals. No Hilbert space is
invoked in the verification step, and no machine is fixed: these files are
mathematics about correlators and trial counts.

## Files

### CHSH

| File | Purpose |
|---|---|
| `ValidCorrelation.v` | Valid correlation boxes (non-negative, normalized, no-signaling) and local boxes as mixtures of deterministic strategies |
| `BoxCHSH.v` | Rational box operations; the deterministic bound and the algebraic bound (`local_S_2_deterministic`, `box_chsh_bound_algebraic`) |
| `MinorConstraints.v` | Factorizable correlation witnesses satisfy the minor constraints and the classical bound (`factorizable_CHSH_classical_bound`, `local_box_CHSH_bound`) |
| `CHSHStatisticalBridge.v` | The CHSH statistic of aggregate trial counts, its algebraic ceiling, and the fact that locally consistent deterministic counts cannot violate it (`chsh_stat_violation_not_local`); no Hoeffding bound or confidence level |
| `CHSHCouplingBridge.v` | Separable couplings and the classical bound (`chsh_violation_rules_out_locally_factorizable_coupling`) |

### Tsirelson

| File | Purpose |
|---|---|
| `TsirelsonGeneral.v` | The Tsirelson bound from row constraints and Cauchy-Schwarz (`tsirelson_from_row_bounds`, `tsirelson_from_column_bounds`), and the CHSH value's invariance under swapping the parties (`semantics_invariant_party_swap`) |
| `TsirelsonFromAlgebra.v` | The non-circular bridge: the bound is reached and tight (`tsirelson_tight`) |

### NPA and PSD

| File | Purpose |
|---|---|
| `NPAMomentMatrix.v` | The level-1 NPA moment matrix for CHSH |
| `ConstructivePSD.v` | PSD facts by quadratic forms, without eigenvalues |
| `CHSHColumnCheck.v` | An integer check on CHSH trial counts that implies the zero-marginal NPA matrix is PSD (`column_contractive_check_witness_npa_psd`), the biconditional `npa_psd_iff_column_contractive`, and the Tsirelson bound from PSD (`npa_psd_implies_tsirelson_bound`) |
| `SmallChshCheck.v` | The integer CHSH check on eight counts, exact for its pinned matrix: it passes if and only if every pair was sampled and the matrix is positive semidefinite (`small_chsh_check_iff`), and a pass gives the Tsirelson bound (`small_chsh_check_tsirelson`) |
| `SmallChshMachine.v` | The check as the CHECK of an earned chain on the small machine of `minimal/EarnedMulti.v`: a raised flag means a passing, Tsirelson-bounded tally was checked and committed (`small_chsh_flag_implies_tsirelson`), with worked tallies that certify and that are refused forever |
| `QuantumPartitionPSD_1AB.v` | Q_{1+AB} matrix certificates for specified correlator and higher-moment slots; soundness only, no completeness for quantum behaviors |
| `GenRealizability.v` | A dimension-polymorphic PSD predicate (`psd_n`) and the 5x5 CHSH PSD as a special case |
| `ElliptopeCompletion.v` | The CHSH correlator quantum set as an existential completion of the zero-marginal NPA matrix (`elliptope_tsirelson`, `deterministic_strategy_elliptope`, `pr_box_not_elliptope`) |
| `ElliptopeGate.v` | A decidable integer membership check for the elliptope, sound into `elliptope_realizable` (`elliptope_check_full_sound`) |

## Load-bearing exports

- `npa_psd_iff_column_contractive`, `column_contractive_check_witness_npa_psd`
- `algebraically_coherent_tsirelson_general` (in [`category/`](../category/))
- `tsirelson_from_row_bounds`, `tsirelson_tight`

## Imports

The Coq standard library (Reals, QArith, Lra, Psatz), and `category/` for the
algebraic bound.
