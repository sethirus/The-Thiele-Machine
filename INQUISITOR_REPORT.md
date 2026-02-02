# INQUISITOR REPORT
Generated: 2026-02-02 09:36:52Z (UTC)
Scanned: 272 Coq files across the repo
## Summary
- HIGH: 0
- MEDIUM: 28
- LOW: 106

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
- L31: **SUSPICIOUS_SHORT_PROOF** — Complex theorem \`mu_zero_algebraic_bound\` has very short proof (1 lines) - verify this is not a placeholder.
  - `Theorem mu_zero_algebraic_bound :`

#### `coq/kernel/TsirelsonUpperBound.v`
- L401: **SUSPICIOUS_SHORT_PROOF** — Complex theorem \`classical_bound_lt_algebraic_max\` has very short proof (2 lines) - verify this is not a placeholder.
  - `Lemma classical_bound_lt_algebraic_max : classical_bound_value < 4%Q.`

#### `coq/theory/EvolutionaryForge.v`
- L230: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `exists (crossover s1 s2 (Nat.min (length s1) (length s2) / 2)).`
- L235: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (Hmin_pos: Nat.min (length s1) (length s2) > 0) by lia.`
- L236: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (H: Nat.min (length s1) (length s2) / 2 <= Nat.min (length s1) (length s2)).`
- L240: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (Hmin_pos: Nat.min (length s1) (length s2) > 0) by lia.`
- L241: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (H: Nat.min (length s1) (length s2) / 2 <= Nat.min (length s1) (length s2)).`
- L337: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `exists [crossover s1 s2 (Nat.min (length s1) (length s2) / 2)].`
- L346: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (Hmin_pos: Nat.min (length s1) (length s2) > 0) by lia.`
- L347: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (H: Nat.min (length s1) (length s2) / 2 <= Nat.min (length s1) (length s2)).`
- L351: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (Hmin_pos: Nat.min (length s1) (length s2) > 0) by lia.`
- L352: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `assert (H: Nat.min (length s1) (length s2) / 2 <= Nat.min (length s1) (length s2)).`

#### `coq/theory/Representations.v`
- L46: **MU_COST_ZERO** — μ-cost definition \`qm_mu\` is trivially zero - ensure this is intentional.
  - `Definition qm_mu {A B} (_ : UnitaryOp A B) : nat := 0.`
- L46: **ZERO_CONST** — Definition is a constant zero.
  - `Definition qm_mu {A B} (_ : UnitaryOp A B) : nat := 0.`
- L133: **MU_COST_ZERO** — μ-cost definition \`thermo_mu\` is trivially zero - ensure this is intentional.
  - `Definition thermo_mu {A B} (_ : ThermoOp A B) : nat := 0.`
- L133: **ZERO_CONST** — Definition is a constant zero.
  - `Definition thermo_mu {A B} (_ : ThermoOp A B) : nat := 0.`

#### `coq/theory/Universality.v`
- L19: **PROBLEMATIC_IMPORT** — Import may introduce classical axioms - verify this is documented and necessary.
  - `Require Import Coq.Logic.ProofIrrelevance.`

#### `coq/thielemachine/coqproofs/MuAlu.v`
- L194: **MU_COST_ZERO** — μ-cost definition \`mu_zero\` is trivially zero - ensure this is intentional.
  - `Definition mu_zero : MuAccumulator := {| mu_value := 0 |}.`

#### `coq/thielemachine/coqproofs/OracleImpossibility.v`
- L92: **PROBLEMATIC_IMPORT** — Import may introduce classical axioms - verify this is documented and necessary.
  - `Require Import Classical.`

#### `coq/thielemachine/verification/Admissibility.v`
- L145: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `trace_admissible s [PDISCOVER (fst m) (Z.to_nat cost)].`
- L145: **Z_TO_NAT_BOUNDARY** — Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).
  - `trace_admissible s [PDISCOVER (fst m) (Z.to_nat cost)].`
- L153: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `exists (fst m), (Z.to_nat cost).`
- L153: **Z_TO_NAT_BOUNDARY** — Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).
  - `exists (fst m), (Z.to_nat cost).`

#### `coq/thielemachine/verification/ObservationInterface.v`
- L179: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `else 1 # (Pos.of_nat (Z.to_nat (1 + Z.abs mu))).`
- L203: **CLAMP_OR_TRUNCATION** — Clamp/truncation detected (can break algebraic laws unless domain/partiality is explicit).
  - `destruct (Z.to_nat (1 + Z.abs (BlindSighted.mu_total (BlindSighted.ledger s)))) eqn:Hk;`
- L203: **Z_TO_NAT_BOUNDARY** — Z.to_nat used without nearby nonnegativity guard (potential boundary clamp).
  - `destruct (Z.to_nat (1 + Z.abs (BlindSighted.mu_total (BlindSighted.ledger s)))) eqn:Hk;`

### LOW

#### `coq/kernel/AlgebraicCoherence.v`
- L259: **CHSH_BOUND_MISSING** — CHSH bound theorem \`chsh_weak_bound\` may not reference proper Tsirelson bound value.
  - `Lemma chsh_weak_bound : forall e00 e01 e10 e11 : Q,`
- L296: **CHSH_BOUND_MISSING** — CHSH bound theorem \`chsh_squared_bound_from_correlations\` may not reference proper Tsirelson bound value.
  - `Lemma chsh_squared_bound_from_correlations : forall e00 e01 e10 e11 : Q,`

#### `coq/kernel/BoxCHSH.v`
- L135: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`local_box_S_le_2\` is documented with INQUISITOR NOTE.
  - `Context (local_box_S_le_2 : forall B,`
- L200: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`normalized_E_bound\` is documented with INQUISITOR NOTE.
  - `Context (normalized_E_bound : forall B x y,`
- L203: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
  - `Context (tsirelson_from_algebraic_coherence : forall c : Correlators,`

#### `coq/kernel/ConstantUnification.v`
- L26: **AXIOM_DOCUMENTED** — Found Axiom tau_mu.
  - `Axiom tau_mu : R.`
- L27: **AXIOM_DOCUMENTED** — Found Axiom d_mu.
  - `Axiom d_mu : R.`
- L28: **AXIOM_DOCUMENTED** — Found Axiom k_B.
  - `Axiom k_B : R.`
- L29: **AXIOM_DOCUMENTED** — Found Axiom T.
  - `Axiom T : R.`
- L31: **AXIOM_DOCUMENTED** — Found Axiom tau_mu_pos.
  - `Axiom tau_mu_pos : tau_mu > 0.`
- L32: **AXIOM_DOCUMENTED** — Found Axiom d_mu_pos.
  - `Axiom d_mu_pos : d_mu > 0.`
- L33: **AXIOM_DOCUMENTED** — Found Axiom k_B_pos.
  - `Axiom k_B_pos : k_B > 0.`
- L34: **AXIOM_DOCUMENTED** — Found Axiom T_pos.
  - `Axiom T_pos : T > 0.`

#### `coq/kernel/HardAssumptions.v`
- L47: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`normalized_E_bound\` is documented with INQUISITOR NOTE.
  - `Context (normalized_E_bound : forall B x y,`

#### `coq/kernel/MinorConstraints.v`
- L197: **AXIOM_DOCUMENTED** — Found Axiom Fine_theorem.
  - `Axiom Fine_theorem : forall E00 E01 E10 E11 s t,`
- L260: **CHSH_BOUND_MISSING** — CHSH bound theorem \`minor_constraints_imply_CHSH_bound\` may not reference proper Tsirelson bound value.
  - `Theorem minor_constraints_imply_CHSH_bound : forall E00 E01 E10 E11,`
- L358: **AXIOM_DOCUMENTED** — Found Axiom Gram_PSD.
  - `Axiom Gram_PSD : forall (s e1 e2 : R),`
- L429: **AXIOM_DOCUMENTED** — Found Axiom local_box_satisfies_minors.
  - `Axiom local_box_satisfies_minors : forall B,`

#### `coq/kernel/MuInformationTheoreticBounds.v`
- L39: **AXIOM_DOCUMENTED** — Found Axiom partition_claim_information_bound.
  - `Axiom partition_claim_information_bound : forall (n num_partitions : nat),`
- L61: **AXIOM_DOCUMENTED** — Found Axiom state_space_reduction_bound.
  - `Axiom state_space_reduction_bound : forall (omega omega_prime : nat),`
- L85: **AXIOM_DOCUMENTED** — Found Axiom mu_zero_classical_characterization.
  - `Axiom mu_zero_classical_characterization :`
- L102: **AXIOM_DOCUMENTED** — Found Axiom mu_positive_quantum_characterization.
  - `Axiom mu_positive_quantum_characterization :`

#### `coq/kernel/NPAMomentMatrix.v`
- L216: **AXIOM_DOCUMENTED** — Found Axiom quantum_realizable_implies_normalized.
  - `Axiom quantum_realizable_implies_normalized : forall (npa : NPAMomentMatrix),`

#### `coq/kernel/QuantumBound.v`
- L208: **AXIOM_DOCUMENTED** — Found Axiom quantum_admissible_implies_no_supra_cert.
  - `Axiom quantum_admissible_implies_no_supra_cert :`

#### `coq/kernel/QuantumBoundComplete.v`
- L38: **AXIOM_DOCUMENTED** — Found Axiom VMState.
  - `Axiom VMState : Type.`
- L39: **AXIOM_DOCUMENTED** — Found Axiom vm_instruction.
  - `Axiom vm_instruction : Type.`
- L46: **AXIOM_DOCUMENTED** — Found Axiom Box.
  - `Axiom Box : Type.`
- L47: **AXIOM_DOCUMENTED** — Found Axiom box_apply.
  - `Axiom box_apply : Box -> nat -> nat -> nat -> nat -> Q.`
- L49: **AXIOM_DOCUMENTED** — Found Axiom non_negative.
  - `Axiom non_negative : Box -> Prop.`
- L50: **AXIOM_DOCUMENTED** — Found Axiom normalized.
  - `Axiom normalized : Box -> Prop.`
- L51: **AXIOM_DOCUMENTED** — Found Axiom box_from_trace.
  - `Axiom box_from_trace : nat -> list vm_instruction -> VMState -> Box.`
- L52: **AXIOM_DOCUMENTED** — Found Axiom mu_cost_of_instr.
  - `Axiom mu_cost_of_instr : vm_instruction -> VMState -> nat.`
- L58: **AXIOM_DOCUMENTED** — Found Axiom BoxCHSH_S.
  - `Axiom BoxCHSH_S : Box -> Q.`
- L59: **AXIOM_DOCUMENTED** — Found Axiom BoxCHSH_E.
  - `Axiom BoxCHSH_E : Box -> nat -> nat -> Q.`
- L65: **AXIOM_DOCUMENTED** — Found Axiom is_ljoin.
  - `Axiom is_ljoin : vm_instruction -> Prop.`
- L66: **AXIOM_DOCUMENTED** — Found Axiom is_reveal.
  - `Axiom is_reveal : vm_instruction -> Prop.`
- L67: **AXIOM_DOCUMENTED** — Found Axiom is_lassert.
  - `Axiom is_lassert : vm_instruction -> Prop.`
- L95: **AXIOM_DOCUMENTED** — Found Axiom mu_zero_preserves_factorizable.
  - `Axiom mu_zero_preserves_factorizable : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L111: **AXIOM_DOCUMENTED** — Found Axiom mu_positive_enables_nonfactorizable.
  - `Axiom mu_positive_enables_nonfactorizable : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L149: **AXIOM_DOCUMENTED** — Found Axiom nonfactorizable_is_quantum_realizable.
  - `Axiom nonfactorizable_is_quantum_realizable : forall (B : Box),`
- L170: **AXIOM_DOCUMENTED** — Found Axiom mu_positive_enables_tsirelson.
  - `Axiom mu_positive_enables_tsirelson : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L187: **AXIOM_DOCUMENTED** — Found Axiom mu_zero_classical_bound.
  - `Axiom mu_zero_classical_bound : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L200: **AXIOM_DOCUMENTED** — Found Axiom mu_positive_exceeds_classical.
  - `Axiom mu_positive_exceeds_classical : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`

#### `coq/kernel/SemidefiniteProgramming.v`
- L220: **AXIOM_DOCUMENTED** — Found Axiom PSD_diagonal_nonneg.
  - `Axiom PSD_diagonal_nonneg : forall (n : nat) (M : Matrix n) (i : nat),`
- L285: **AXIOM_DOCUMENTED** — Found Axiom schur_2x2_criterion.
  - `Axiom schur_2x2_criterion : forall (M : Matrix 2),`
- L298: **AXIOM_DOCUMENTED** — Found Axiom PSD_cauchy_schwarz.
  - `Axiom PSD_cauchy_schwarz : forall (n : nat) (M : Matrix n) (i j : nat),`
- L305: **AXIOM_DOCUMENTED** — Found Axiom PSD_principal_minors_nonneg.
  - `Axiom PSD_principal_minors_nonneg : forall (n : nat) (M : Matrix n) (i j k : nat),`
- L319: **AXIOM_DOCUMENTED** — Found Axiom PSD_off_diagonal_bound.
  - `Axiom PSD_off_diagonal_bound : forall (n : nat) (M : Matrix n) (i j : nat),`

#### `coq/kernel/TsirelsonBoundComplete.v`
- L87: **AXIOM_DOCUMENTED** — Found Axiom optimal_satisfies_constraint_axiom.
  - `Axiom optimal_satisfies_constraint_axiom :`
- L190: **AXIOM_DOCUMENTED** — Found Axiom chsh_squared_bound_from_constraint_axiom.
  - `Axiom chsh_squared_bound_from_constraint_axiom : forall (E00 E01 E10 E11 : R),`
- L194: **CHSH_BOUND_MISSING** — CHSH bound theorem \`chsh_squared_bound_from_constraint\` may not reference proper Tsirelson bound value.
  - `Lemma chsh_squared_bound_from_constraint : forall (E00 E01 E10 E11 : R),`

#### `coq/kernel/TsirelsonBoundDirect.v`
- L121: **AXIOM_DOCUMENTED** — Found Axiom quadratic_constraint_minimum.
  - `Axiom quadratic_constraint_minimum : forall (x y b : R),`
- L134: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hminor\` not used in proof body or conclusion (heuristic).
  - `intros x b Hminor Hble1 Hx2.`
- L134: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hble1\` not used in proof body or conclusion (heuristic).
  - `intros x b Hminor Hble1 Hx2.`
- L134: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx2\` not used in proof body or conclusion (heuristic).
  - `intros x b Hminor Hble1 Hx2.`
- L152: **AXIOM_DOCUMENTED** — Found Axiom f_bound_max.
  - `Axiom f_bound_max : forall (x : R),`
- L160: **AXIOM_DOCUMENTED** — Found Axiom tsirelson_bound_symmetric.
  - `Axiom tsirelson_bound_symmetric : forall (npa : NPAMomentMatrix) (x y : R),`
- L167: **AXIOM_DOCUMENTED** — Found Axiom tsirelson_bound_symmetric_lower.
  - `Axiom tsirelson_bound_symmetric_lower : forall (npa : NPAMomentMatrix) (x y : R),`
- L174: **AXIOM_DOCUMENTED** — Found Axiom reduction_to_symmetric_stmt.
  - `Axiom reduction_to_symmetric_stmt : forall (npa : NPAMomentMatrix),`
- L215: **AXIOM_DOCUMENTED** — Found Axiom reduction_to_symmetric.
  - `Axiom reduction_to_symmetric : forall (npa : NPAMomentMatrix),`

#### `coq/kernel/TsirelsonBoundProof.v`
- L39: **AXIOM_DOCUMENTED** — Found Axiom sqrt2.
  - `Axiom sqrt2 : R.`
- L40: **AXIOM_DOCUMENTED** — Found Axiom sqrt2_squared.
  - `Axiom sqrt2_squared : sqrt2 * sqrt2 = 2.`
- L41: **AXIOM_DOCUMENTED** — Found Axiom sqrt2_positive.
  - `Axiom sqrt2_positive : sqrt2 > 0.`
- L42: **AXIOM_DOCUMENTED** — Found Axiom sqrt2_bounds.
  - `Axiom sqrt2_bounds : 1.4 < sqrt2 < 1.5.`
- L72: **AXIOM_DOCUMENTED** — Found Axiom quantum_CHSH_bound.
  - `Axiom quantum_CHSH_bound : forall (npa : NPAMomentMatrix),`
- L110: **AXIOM_DOCUMENTED** — Found Axiom optimal_is_quantum_realizable.
  - `Axiom optimal_is_quantum_realizable :`
- L115: **AXIOM_DOCUMENTED** — Found Axiom optimal_achieves_tsirelson.
  - `Axiom optimal_achieves_tsirelson :`
- L138: **AXIOM_DOCUMENTED** — Found Axiom classical_CHSH_bound.
  - `Axiom classical_CHSH_bound : forall (npa : NPAMomentMatrix),`
- L176: **AXIOM_DOCUMENTED** — Found Axiom grothendieck_constant.
  - `Axiom grothendieck_constant : R.`
- L177: **AXIOM_DOCUMENTED** — Found Axiom grothendieck_value.
  - `Axiom grothendieck_value : 1.7 < grothendieck_constant < 1.8.`
- L178: **AXIOM_DOCUMENTED** — Found Axiom grothendieck_inequality.
  - `Axiom grothendieck_inequality : forall (npa : NPAMomentMatrix),`

#### `coq/kernel/TsirelsonBoundProof2.v`
- L56: **AXIOM_DOCUMENTED** — Found Axiom chsh_bound_from_psd.
  - `Axiom chsh_bound_from_psd : forall (E00 E01 E10 E11 : R),`
- L66: **AXIOM_DOCUMENTED** — Found Axiom chsh_bound_from_psd_axiom.
  - `Axiom chsh_bound_from_psd_axiom : forall (E00 E01 E10 E11 : R),`

#### `coq/kernel/TsirelsonBoundTDD.v`
- L204: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdet\` not used in proof body or conclusion (heuristic).
  - `intros E00 E01 E10 E11 Hdet.`
- L253: **AXIOM_DOCUMENTED** — Found Axiom optimal_is_psd_axiom.
  - `Axiom optimal_is_psd_axiom :`

#### `coq/kernel/TsirelsonBoundVerification.v`
- L76: **AXIOM_DOCUMENTED** — Found Axiom test_config_111_minor3_negative_axiom.
  - `Axiom test_config_111_minor3_negative_axiom :`
- L140: **AXIOM_DOCUMENTED** — Found Axiom config_111_0_not_psd_axiom.
  - `Axiom config_111_0_not_psd_axiom :`

#### `coq/kernel/TsirelsonGeneral.v`
- L83: **CHSH_BOUND_MISSING** — CHSH bound theorem \`tsirelson_from_row_bounds\` may not reference proper Tsirelson bound value.
  - `Theorem tsirelson_from_row_bounds :`
- L90: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrow1\` not used in proof body or conclusion (heuristic).
  - `intros e00 e01 e10 e11 Hrow1 Hrow2.`
- L90: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrow2\` not used in proof body or conclusion (heuristic).
  - `intros e00 e01 e10 e11 Hrow1 Hrow2.`

#### `coq/kernel/TsirelsonUniqueness.v`
- L58: **AXIOM_DOCUMENTED** — Found Axiom mu_zero_classical_bound.
  - `Axiom mu_zero_classical_bound :`
- L72: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
  - `Context (tsirelson_from_algebraic_coherence : forall c : Correlators,`

#### `coq/modular_proofs/EncodingBounds.v`
- L147: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`encode_list\` is documented with INQUISITOR NOTE.
  - `Context (encode_list : list nat -> nat).`
- L148: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`digits_ok\` is documented with INQUISITOR NOTE.
  - `Context (digits_ok : list nat -> Prop).`
- L149: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`encode_list_upper\` is documented with INQUISITOR NOTE.
  - `Context (encode_list_upper : forall xs, digits_ok xs -> encode_list xs < Nat.pow BASE (length xs)).`

#### `coq/physics_exploration/EmergentSpacetime.v`
- L10: **AXIOM_DOCUMENTED** — Found Axiom d_mu.
  - `Axiom d_mu : R.`
- L11: **AXIOM_DOCUMENTED** — Found Axiom d_mu_positive.
  - `Axiom d_mu_positive : d_mu > 0.`

#### `coq/physics_exploration/HolographicGravity.v`
- L9: **AXIOM_DOCUMENTED** — Found Axiom G.
  - `Axiom G : R.`
- L10: **AXIOM_DOCUMENTED** — Found Axiom G_positive.
  - `Axiom G_positive : G > 0.`

#### `coq/physics_exploration/ParticleMasses.v`
- L9: **AXIOM_DOCUMENTED** — Found Axiom m_electron.
  - `Axiom m_electron : R.`
- L10: **AXIOM_DOCUMENTED** — Found Axiom m_muon.
  - `Axiom m_muon : R.`
- L11: **AXIOM_DOCUMENTED** — Found Axiom m_proton.
  - `Axiom m_proton : R.`
- L13: **AXIOM_DOCUMENTED** — Found Axiom masses_positive.
  - `Axiom masses_positive : m_electron > 0 /\ m_muon > 0 /\ m_proton > 0.`

#### `coq/physics_exploration/PlanckDerivation.v`
- L8: **AXIOM_DOCUMENTED** — Found Axiom k_B.
  - `Axiom k_B : R.`
- L9: **AXIOM_DOCUMENTED** — Found Axiom k_B_positive.
  - `Axiom k_B_positive : k_B > 0.`
- L11: **AXIOM_DOCUMENTED** — Found Axiom T.
  - `Axiom T : R.`
- L12: **AXIOM_DOCUMENTED** — Found Axiom T_positive.
  - `Axiom T_positive : T > 0.`

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

