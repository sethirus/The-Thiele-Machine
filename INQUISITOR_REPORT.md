# INQUISITOR REPORT
Generated: 2026-01-10 07:51:55Z (UTC)
Scanned: 242 Coq files across the repo
## Summary
- HIGH: 0
- MEDIUM: 15
- LOW: 20

## Rules
- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)
- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)
- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)
- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter` (HIGH - unproven assumptions FORBIDDEN)
- `HYPOTHESIS_ASSUME`: `Hypothesis` (HIGH - functionally equivalent to Axiom, FORBIDDEN)
- `CONTEXT_ASSUMPTION`: `Context` with forall/arrow (HIGH - undocumented section-local axiom)
- `CONTEXT_ASSUMPTION_DOCUMENTED`: `Context` with INQUISITOR NOTE (LOW - documented dependency)
- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (MEDIUM - verify instantiation)
- `MODULE_SIGNATURE_DECL`: `Axiom` / `Parameter` inside `Module Type` (informational)
- `COST_IS_LENGTH`: `Definition *cost* := ... length ... .`
- `EMPTY_LIST`: `Definition ... := [].`
- `ZERO_CONST`: `Definition ... := 0.` / `0%Z` / `0%nat`
- `TRUE_CONST`: `Definition ... := True.` or `:= true.`
- `PROP_TAUTOLOGY`: `Theorem ... : True.`
- `IMPLIES_TRUE_STMT`: statement ends with `-> True.`
- `LET_IN_TRUE_STMT`: statement ends with `let ... in True.`
- `EXISTS_TRUE_STMT`: statement ends with `exists ..., True.`
- `CIRCULAR_INTROS_ASSUMPTION`: tautology + `intros; assumption.`
- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof
- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`
- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`
- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat`, `Z.abs`, `Nat.min`, `Nat.max`
- `ASSUMPTION_AUDIT`: unexpected axioms from `Print Assumptions`
- `SYMMETRY_CONTRACT`: missing equivariance lemma for declared symmetry
- `PAPER_MAP_MISSING`: paper ↔ Coq symbol map entry missing/broken
- `MANIFEST_PARSE_ERROR`: failed to parse Inquisitor manifest JSON
- `COMMENT_SMELL`: TODO/FIXME/WIP markers in Coq comments
- `UNUSED_HYPOTHESIS`: introduced hypothesis not used (heuristic)
- `DEFINITIONAL_INVARIANCE`: invariance lemma appears definitional/vacuous
- `Z_TO_NAT_BOUNDARY`: Z.to_nat without nearby nonnegativity guard
- `PHYSICS_ANALOGY_CONTRACT`: physics-analogy theorem lacks invariance or definitional label
- `SUSPICIOUS_SHORT_PROOF`: complex theorem has suspiciously short proof (critical files)
- `MU_COST_ZERO`: μ-cost definition is trivially zero
- `CHSH_BOUND_MISSING`: CHSH bound theorem may not reference proper Tsirelson bound
- `PROBLEMATIC_IMPORT`: import may introduce classical axioms

## Vacuity Ranking (file-level)
Higher score = more likely unfinished/vacuous.

| score | tags | file |
|---:|---|---|
| 65 | const-fun | `coq/thielemachine/coqproofs/SpectralApproximation.v` |

## Findings
### MEDIUM

#### `coq/kernel/NoArbitrage.v`
- L105: **ZERO_CONST** — Definition is a constant zero.
  - `Definition c_initial : CState := 0%nat.`

#### `coq/kernel/ProperSubsumption.v`
- L38: **ZERO_CONST** — Definition is a constant zero.
  - `Definition blank : Symbol := 0.`

#### `coq/kernel/TsirelsonUniqueness.v`
- L25: **SUSPICIOUS_SHORT_PROOF** — Complex theorem \`mu_zero_algebraic_bound\` has very short proof (1 lines) - verify this is not a placeholder.
  - `Theorem mu_zero_algebraic_bound :`

#### `coq/kernel/TsirelsonUpperBound.v`
- L347: **SUSPICIOUS_SHORT_PROOF** — Complex theorem \`tsirelson_bound_lt_algebraic_max\` has very short proof (2 lines) - verify this is not a placeholder.
  - `Lemma tsirelson_bound_lt_algebraic_max : tsirelson_bound < 4%Q.`

#### `coq/thielemachine/coqproofs/MuAlu.v`
- L194: **MU_COST_ZERO** — μ-cost definition \`mu_zero\` is trivially zero - ensure this is intentional.
  - `Definition mu_zero : MuAccumulator := {| mu_value := 0 |}.`

#### `coq/thielemachine/coqproofs/OracleImpossibility.v`
- L92: **PROBLEMATIC_IMPORT** — Import may introduce classical axioms - verify this is documented and necessary.
  - `Require Import Classical.`

#### `coq/thielemachine/verification/Admissibility.v`
- L143: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `trace_admissible s [PDISCOVER (fst m) (Z.to_nat cost)].`
- L143: **Z_TO_NAT_BOUNDARY** — Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).
  - `trace_admissible s [PDISCOVER (fst m) (Z.to_nat cost)].`
- L151: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `exists (fst m), (Z.to_nat cost).`
- L151: **Z_TO_NAT_BOUNDARY** — Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).
  - `exists (fst m), (Z.to_nat cost).`

#### `coq/thielemachine/verification/ObservationInterface.v`
- L179: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `else 1 # (Pos.of_nat (Z.to_nat (1 + Z.abs mu))).`
- L203: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `destruct (Z.to_nat (1 + Z.abs (BlindSighted.mu_total (BlindSighted.ledger s)))) eqn:Hk;`
- L203: **Z_TO_NAT_BOUNDARY** — Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).
  - `destruct (Z.to_nat (1 + Z.abs (BlindSighted.mu_total (BlindSighted.ledger s)))) eqn:Hk;`

#### `coq/thielemachine/verification/PhysicsPillars.v`
- L1: **SYMMETRY_CONTRACT** — Missing symmetry equivariance lemma matching: vm_step.*equiv, trace_run.*equiv|run_vm.*equiv
  - ``

#### `coq/thielemachine/verification/Symmetry.v`
- L1: **SYMMETRY_CONTRACT** — Missing symmetry equivariance lemma matching: vm_step.*equiv, trace_run.*equiv|run_vm.*equiv
  - ``

### LOW

#### `coq/kernel/AlgebraicCoherence.v`
- L205: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`symmetric_coherence_bound\` is documented with INQUISITOR NOTE.
  - `Context (symmetric_coherence_bound : forall e : Q,`
- L212: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
  - `Context (tsirelson_from_algebraic_coherence : forall c : Correlators,`

#### `coq/kernel/BoxCHSH.v`
- L77: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`normalized_E_bound\` is documented with INQUISITOR NOTE.
  - `Context (normalized_E_bound : forall B x y,`
- L95: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`valid_box_S_le_4\` is documented with INQUISITOR NOTE.
  - `Context (valid_box_S_le_4 : forall B,`
- L119: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`local_box_S_le_2\` is documented with INQUISITOR NOTE.
  - `Context (local_box_S_le_2 : forall B,`
- L182: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`normalized_E_bound\` is documented with INQUISITOR NOTE.
  - `Context (normalized_E_bound : forall B x y,`
- L187: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
  - `Context (tsirelson_from_algebraic_coherence : forall c : Correlators,`

#### `coq/kernel/TsirelsonUniqueness.v`
- L59: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
  - `Context (tsirelson_from_algebraic_coherence : forall c : Correlators,`

#### `coq/modular_proofs/EncodingBounds.v`
- L147: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`encode_list\` is documented with INQUISITOR NOTE.
  - `Context (encode_list : list nat -> nat).`
- L148: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`digits_ok\` is documented with INQUISITOR NOTE.
  - `Context (digits_ok : list nat -> Prop).`
- L149: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`encode_list_upper\` is documented with INQUISITOR NOTE.
  - `Context (encode_list_upper : forall xs, digits_ok xs -> encode_list xs < Nat.pow BASE (length xs)).`

#### `coq/thielemachine/coqproofs/BellCheck.v`
- L134: **CHSH_BOUND_MISSING** — CHSH bound theorem \`CHSH_classical_bound\` may not reference proper Tsirelson bound value.
  - `Lemma CHSH_classical_bound :`

#### `coq/thielemachine/coqproofs/BellInequality.v`
- L701: **CHSH_BOUND_MISSING** — CHSH bound theorem \`local_CHSH_bound\` may not reference proper Tsirelson bound value.
  - `Lemma local_CHSH_bound : forall (B : Box), local B -> Qabs (S B) <= 2#1.`
- L839: **CHSH_BOUND_MISSING** — CHSH bound theorem \`tsirelson_gamma_bound\` may not reference proper Tsirelson bound value.
  - `Lemma tsirelson_gamma_bound : -1#1 <= tsirelson_gamma <= 1#1.`
- L1301: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`\` is documented with INQUISITOR NOTE.
  - `Context {Instr State Observation : Type}.`

#### `coq/thielemachine/coqproofs/BellReceiptLocalGeneral.v`
- L291: **CHSH_BOUND_MISSING** — CHSH bound theorem \`local_trials_CHSH_bound\` may not reference proper Tsirelson bound value.
  - `Theorem local_trials_CHSH_bound :`

#### `coq/thielemachine/coqproofs/HyperThiele_Halting.v`
- L32: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`H\` is documented with INQUISITOR NOTE.
  - `Context (H : Oracle) (Halts : nat -> Prop).`

#### `coq/thielemachine/coqproofs/ListHelpers.v`
- L16: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`\` is documented with INQUISITOR NOTE.
  - `Context {A : Type}.`

#### `coq/thielemachine/coqproofs/PhysicsEmbedding.v`
- L22: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`encode_lattice\` is documented with INQUISITOR NOTE.
  - `Context (encode_lattice : Lattice -> VMState)`

#### `coq/thielemachine/coqproofs/WaveEmbedding.v`
- L23: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`encode_wave\` is documented with INQUISITOR NOTE.
  - `Context (encode_wave : WaveState -> VMState)`

