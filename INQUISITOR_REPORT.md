# INQUISITOR REPORT
Generated: 2026-01-12 02:10:20Z (UTC)
Scanned: 243 Coq files across the repo
## Summary
- HIGH: 63
- MEDIUM: 26
- LOW: 16

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
### HIGH

#### `coq/INQUISITOR_ASSUMPTIONS.json`
- L1: **ASSUMPTION_AUDIT** — coqtop not found; cannot run assumption audit.
  - `coqtop`
- L1: **PAPER_MAP_MISSING** — coqtop not found; cannot verify paper symbol map.
  - `coqtop`

#### `coq/kernel/BoxCHSH.v`
- L82: **AXIOM_OR_PARAMETER** — Found Axiom normalized_E_bound.
  - `Axiom normalized_E_bound : forall B x y,`
- L100: **AXIOM_OR_PARAMETER** — Found Axiom valid_box_S_le_4.
  - `Axiom valid_box_S_le_4 : forall B,`

#### `coq/kernel/MinorConstraints.v`
- L108: **AXIOM_OR_PARAMETER** — Found Axiom Fine_theorem.
  - `Axiom Fine_theorem : forall E00 E01 E10 E11 s t,`
- L162: **AXIOM_OR_PARAMETER** — Found Axiom correlation_matrix_bounds.
  - `Axiom correlation_matrix_bounds : forall s e1 e2,`
- L241: **AXIOM_OR_PARAMETER** — Found Axiom Gram_PSD.
  - `Axiom Gram_PSD : forall (s e1 e2 : R),`
- L306: **AXIOM_OR_PARAMETER** — Found Axiom local_box_satisfies_minors.
  - `Axiom local_box_satisfies_minors : forall B,`
- L324: **AXIOM_OR_PARAMETER** — Found Axiom Q2R_abs_bound.
  - `Axiom Q2R_abs_bound : forall q,`
- L328: **AXIOM_OR_PARAMETER** — Found Axiom Q2R_plus_ax.
  - `Axiom Q2R_plus_ax : forall q1 q2, Q2R (q1 + q2)%Q = Q2R q1 + Q2R q2.`
- L329: **AXIOM_OR_PARAMETER** — Found Axiom Q2R_minus_ax.
  - `Axiom Q2R_minus_ax : forall q1 q2, Q2R (q1 - q2)%Q = Q2R q1 - Q2R q2.`
- L364: **AXIOM_OR_PARAMETER** — Found Axiom local_box_CHSH_bound.
  - `Axiom local_box_CHSH_bound : forall B,`

#### `coq/kernel/NPAMomentMatrix.v`
- L185: **AXIOM_OR_PARAMETER** — Found Axiom quantum_realizable_implies_normalized.
  - `Axiom quantum_realizable_implies_normalized : forall (npa : NPAMomentMatrix),`

#### `coq/kernel/NoArbitrage.v`
- L165: **AXIOM_OR_PARAMETER** — Found Axiom asymmetric_cost_pos.
  - `Axiom asymmetric_cost_pos : forall t, 0 <= asymmetric_cost t.`
- L198: **AXIOM_OR_PARAMETER** — Found Axiom asymmetric_bounded_by_phi.
  - `Axiom asymmetric_bounded_by_phi : forall t s,`

#### `coq/kernel/QuantumBound.v`
- L204: **AXIOM_OR_PARAMETER** — Found Axiom quantum_admissible_implies_no_supra_cert.
  - `Axiom quantum_admissible_implies_no_supra_cert :`

#### `coq/kernel/QuantumBoundComplete.v`
- L30: **AXIOM_OR_PARAMETER** — Found Axiom VMState.
  - `Axiom VMState : Type.`
- L31: **AXIOM_OR_PARAMETER** — Found Axiom vm_instruction.
  - `Axiom vm_instruction : Type.`
- L35: **AXIOM_OR_PARAMETER** — Found Axiom Box.
  - `Axiom Box : Type.`
- L36: **AXIOM_OR_PARAMETER** — Found Axiom box_apply.
  - `Axiom box_apply : Box -> nat -> nat -> nat -> nat -> Q.`
- L38: **AXIOM_OR_PARAMETER** — Found Axiom non_negative.
  - `Axiom non_negative : Box -> Prop.`
- L39: **AXIOM_OR_PARAMETER** — Found Axiom normalized.
  - `Axiom normalized : Box -> Prop.`
- L40: **AXIOM_OR_PARAMETER** — Found Axiom box_from_trace.
  - `Axiom box_from_trace : nat -> list vm_instruction -> VMState -> Box.`
- L41: **AXIOM_OR_PARAMETER** — Found Axiom mu_cost_of_instr.
  - `Axiom mu_cost_of_instr : vm_instruction -> VMState -> nat.`
- L44: **AXIOM_OR_PARAMETER** — Found Axiom BoxCHSH_S.
  - `Axiom BoxCHSH_S : Box -> Q.`
- L45: **AXIOM_OR_PARAMETER** — Found Axiom BoxCHSH_E.
  - `Axiom BoxCHSH_E : Box -> nat -> nat -> Q.`
- L48: **AXIOM_OR_PARAMETER** — Found Axiom is_ljoin.
  - `Axiom is_ljoin : vm_instruction -> Prop.`
- L49: **AXIOM_OR_PARAMETER** — Found Axiom is_reveal.
  - `Axiom is_reveal : vm_instruction -> Prop.`
- L50: **AXIOM_OR_PARAMETER** — Found Axiom is_lassert.
  - `Axiom is_lassert : vm_instruction -> Prop.`
- L73: **AXIOM_OR_PARAMETER** — Found Axiom mu_zero_preserves_factorizable.
  - `Axiom mu_zero_preserves_factorizable : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L86: **AXIOM_OR_PARAMETER** — Found Axiom mu_positive_enables_nonfactorizable.
  - `Axiom mu_positive_enables_nonfactorizable : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L119: **AXIOM_OR_PARAMETER** — Found Axiom nonfactorizable_is_quantum_realizable.
  - `Axiom nonfactorizable_is_quantum_realizable : forall (B : Box),`
- L137: **AXIOM_OR_PARAMETER** — Found Axiom mu_positive_enables_tsirelson.
  - `Axiom mu_positive_enables_tsirelson : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L149: **AXIOM_OR_PARAMETER** — Found Axiom mu_zero_classical_bound.
  - `Axiom mu_zero_classical_bound : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`
- L160: **AXIOM_OR_PARAMETER** — Found Axiom mu_positive_exceeds_classical.
  - `Axiom mu_positive_exceeds_classical : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),`

#### `coq/kernel/SemidefiniteProgramming.v`
- L116: **AXIOM_OR_PARAMETER** — Found Axiom PSD_diagonal_nonneg.
  - `Axiom PSD_diagonal_nonneg : forall (n : nat) (M : Matrix n) (i : nat),`
- L153: **AXIOM_OR_PARAMETER** — Found Axiom schur_2x2_criterion.
  - `Axiom schur_2x2_criterion : forall (M : Matrix 2),`
- L164: **AXIOM_OR_PARAMETER** — Found Axiom PSD_cauchy_schwarz.
  - `Axiom PSD_cauchy_schwarz : forall (n : nat) (M : Matrix n) (i j : nat),`
- L176: **AXIOM_OR_PARAMETER** — Found Axiom PSD_off_diagonal_bound.
  - `Axiom PSD_off_diagonal_bound : forall (n : nat) (M : Matrix n) (i j : nat),`

#### `coq/kernel/TsirelsonBoundProof.v`
- L34: **AXIOM_OR_PARAMETER** — Found Axiom sqrt2.
  - `Axiom sqrt2 : R.`
- L35: **AXIOM_OR_PARAMETER** — Found Axiom sqrt2_squared.
  - `Axiom sqrt2_squared : sqrt2 * sqrt2 = 2.`
- L36: **AXIOM_OR_PARAMETER** — Found Axiom sqrt2_positive.
  - `Axiom sqrt2_positive : sqrt2 > 0.`
- L37: **AXIOM_OR_PARAMETER** — Found Axiom sqrt2_bounds.
  - `Axiom sqrt2_bounds : 1.4 < sqrt2 < 1.5.`
- L56: **AXIOM_OR_PARAMETER** — Found Axiom quantum_CHSH_bound.
  - `Axiom quantum_CHSH_bound : forall (npa : NPAMomentMatrix),`
- L90: **AXIOM_OR_PARAMETER** — Found Axiom optimal_is_quantum_realizable.
  - `Axiom optimal_is_quantum_realizable :`
- L95: **AXIOM_OR_PARAMETER** — Found Axiom optimal_achieves_tsirelson.
  - `Axiom optimal_achieves_tsirelson :`
- L115: **AXIOM_OR_PARAMETER** — Found Axiom classical_CHSH_bound.
  - `Axiom classical_CHSH_bound : forall (npa : NPAMomentMatrix),`
- L121: **AXIOM_OR_PARAMETER** — Found Axiom tsirelson_exceeds_classical.
  - `Axiom tsirelson_exceeds_classical :`
- L138: **AXIOM_OR_PARAMETER** — Found Axiom grothendieck_constant.
  - `Axiom grothendieck_constant : R.`
- L139: **AXIOM_OR_PARAMETER** — Found Axiom grothendieck_value.
  - `Axiom grothendieck_value : 1.7 < grothendieck_constant < 1.8.`
- L140: **AXIOM_OR_PARAMETER** — Found Axiom grothendieck_inequality.
  - `Axiom grothendieck_inequality : forall (npa : NPAMomentMatrix),`
- L146: **AXIOM_OR_PARAMETER** — Found Axiom tsirelson_consistent_with_grothendieck.
  - `Axiom tsirelson_consistent_with_grothendieck :`

#### `coq/kernel/TsirelsonUniqueness.v`
- L55: **AXIOM_OR_PARAMETER** — Found Axiom mu_zero_classical_bound.
  - `Axiom mu_zero_classical_bound :`

#### `coq/shor_primitives/PolylogConjecture.v`
- L77: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`

#### `coq/theory/ArchTheorem.v`
- L164: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L174: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`

#### `coq/theory/EvolutionaryForge.v`
- L137: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L146: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L184: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L199: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L217: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L228: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L243: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`

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

#### `coq/shor_primitives/PolylogConjecture.v`
- L70: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - lia timeout`

#### `coq/theory/ArchTheorem.v`
- L157: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - need to prove 90.51% > reliability_threshold`
- L167: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - need correct Real library lemmas`
- L242: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - pdiscover_computes_signature needs proper type definition`

#### `coq/theory/EvolutionaryForge.v`
- L128: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - requires reasoning about list length preservation`
- L139: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - lia tactics having difficulty with witness`
- L177: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - depends on admitted crossover_preserves_viability`
- L186: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - depends on admitted crossover_preserves_viability`
- L206: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete - lia tactic timeouts`
- L220: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - lia tactics having timeout issues`
- L236: **COMMENT_SMELL** — Comment contains placeholder marker (TODO/FIXME/WIP/etc).
  - `TODO: Complete this proof - incomplete goals`

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

#### `coq/kernel/BoxCHSH.v`
- L124: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`local_box_S_le_2\` is documented with INQUISITOR NOTE.
  - `Context (local_box_S_le_2 : forall B,`
- L189: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
  - `Context (tsirelson_from_algebraic_coherence : forall c : Correlators,`

#### `coq/kernel/MinorConstraints.v`
- L169: **CHSH_BOUND_MISSING** — CHSH bound theorem \`minor_constraints_imply_CHSH_bound\` may not reference proper Tsirelson bound value.
  - `Theorem minor_constraints_imply_CHSH_bound : forall E00 E01 E10 E11,`

#### `coq/kernel/TsirelsonUniqueness.v`
- L69: **CONTEXT_ASSUMPTION_DOCUMENTED** — Context parameter \`tsirelson_from_algebraic_coherence\` is documented with INQUISITOR NOTE.
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

