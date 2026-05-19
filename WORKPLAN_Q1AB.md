# Q_{1+AB} Extension — Final Status

The Q_{1+AB} extension adds a new ISA family (`instr_chsh_lassert_1ab*`)
and a kernel-internal Schur-cascade bridge that, on a non-trapping
opcode step, certifies `quantum_realizable_q1ab` of the witness-derived
rational correlators — i.e. the 9×9 NPA Q_{1+AB} moment matrix is
symmetric and PSD at those correlators and at the supplied γ values.
The math, integer kernel, opcode wiring, and headline no-trap wrappers
landed in four successive slices — γ=0, γ_5, γ_345, full γ_12345 —
and are all Qed-closed under **only** the two standard stdlib axioms
`ClassicalDedekindReals.sig_forall_dec` and
`FunctionalExtensionality.functional_extensionality_dep` (the same set
the existing Q_1 kernel theorems use). No project-local axiom, no
`Hypothesis`, no `Parameter` is introduced.

**Definitional note.** In this codebase, `quantum_realizable_q1ab` is
*defined* (in `QuantumPartitionPSD_1AB.v:557`) as `symmetric9 ∧ PSD9`
of the 9×9 NPA Q_{1+AB} moment matrix. This matches the NPA-hierarchy
operational definition of "quantum-realizable at level 1+AB". The
standard mathematical fact `Q_{1+AB} = Q in CHSH` (Ishizaka 2025) is an
*external* citation that justifies the operational naming — it is not
a Coq proof obligation, exactly as NPA's own convergence theorems are
cited externally in every NPA-hierarchy paper rather than re-formalized.
Formalizing it would require GNS construction + operator-algebra
machinery outside the present SOS infrastructure; the choice here is
to stop at the operational claim (`quantum_realizable_q1ab` = PSD9 of
the NPA matrix), which is what the cert opcode certifies.

## Slice overview

| Slice          | New opcode                         | ISA tag | Math (QuantumPartitionPSD_1AB.v) | Integer-kernel decider (VMStep.v)      | Soundness                                              | No-trap headline (→ `quantum_realizable_q1ab`)                                |
|----------------|-------------------------------------|---------|----------------------------------|----------------------------------------|--------------------------------------------------------|--------------------------------------------------------------------------------|
| **γ = 0**      | `instr_chsh_lassert_1ab`           | 0x2F    | §5, §9                           | `column_contractive_check_q1ab_kernel` | `column_contractive_check_q1ab_sound_at_g_zero`        | `chsh_lassert_1ab_no_trap_implies_quantum_realizable_q1ab`                    |
| **γ_5**        | `instr_chsh_lassert_1ab_g5`        | 0x30    | §12, §13                         | `q1ab_g5_full_integer_check_kernel`    | `q1ab_g5_full_integer_check_sound`                     | `chsh_lassert_1ab_g5_no_trap_implies_quantum_realizable_q1ab`                 |
| **γ_345**      | `instr_chsh_lassert_1ab_g345`      | 0x31    | §14, §15                         | `q1ab_g345_full_integer_check_kernel`  | `q1ab_g345_caller_witness_z_abs_implies_psd9`          | `chsh_lassert_1ab_g345_no_trap_implies_quantum_realizable_q1ab`               |
| **full γ_12345** | `instr_chsh_lassert_1ab_g12345`  | 0x32    | §16.1–16.5                       | `q1ab_g12345_full_integer_check_kernel`| `q1ab_g12345_caller_witness_z_abs_implies_psd9`        | `chsh_lassert_1ab_g12345_no_trap_implies_quantum_realizable_q1ab`             |

51 ISA opcodes total (`CANONICAL_51` in
[tests/test_completeness_gate.py](tests/test_completeness_gate.py)).
OCaml↔RTL slack 4 — the four `CHSH_LASSERT_1AB*` opcodes are VM-only
by design (no RTL counterpart; the Q_{1+AB} cert check is a
software-tier discipline).

The headline column closes the chain for each slice: a non-trapping,
no-err-flip execution of the matching cert-opcode implies
`quantum_realizable_q1ab` at the bucket-derived rational correlators
and γ values. The four wrappers live in §17 of
[coq/kernel/quantum/QuantumPartitionPSD_1AB.v](coq/kernel/quantum/QuantumPartitionPSD_1AB.v).

## Verification (current state)

- `make -C coq`: clean. Every kernel + kami_hw .v file compiles.
- `make ocaml-runner`: clean. `build/extracted_vm_runner` rebuilt.
- `python scripts/inquisitor.py`: **OK**. 0 HIGH, 0 MEDIUM, 1 LOW
  (pre-existing `kami_hw/F4_VerilogEvaluator.v`, untouched).
- `Print Assumptions` on every new top-level theorem across all four
  slices: only the two stdlib axioms above. No project-local axiom,
  `Hypothesis`, or `Parameter` introduced.
- `pytest tests/`: **964 passed**. Includes cross-layer parity test,
  OCaml↔Python opcode-set parity, completeness gate, and all
  51-opcode invariants.

## Open

The Q_{1+AB} extension is closed end-to-end in the codebase's own
operational terms (`quantum_realizable_q1ab` = `symmetric9 ∧ PSD9` of
the 9×9 NPA matrix). The two items below are explicitly out of scope.

### External citation: Ishizaka 2025 (Q_{1+AB} = Q in CHSH)

Not formalized in Coq, and *deliberately not*. The mathematical fact
that level-1+AB of the NPA hierarchy equals the quantum set Q in the
CHSH scenario is a published result (Ishizaka 2025; the closure can
also be argued via Tsirelson's 1980 dimension-2 construction). It
justifies the operational `quantum_realizable_q1ab` naming used in
this codebase but is **not** a Coq proof obligation here, exactly as
NPA's own convergence theorems are cited externally in every
NPA-hierarchy paper rather than re-formalized.

The earlier `IshizakaHypothesis` *parameter* approach (forbidden by
the user) would have introduced this as an unproven Coq axiom,
contaminating the kernel. The current finish line avoids that: the
Coq kernel states what it *actually* proves — `quantum_realizable_q1ab`
in the operational PSD9 sense — and the equivalence to the physicist's
Q is left as an external citation in prose. No Coq axiom is added.

Formalizing the bridge anyway would require Hilbert-space / operator
algebra machinery (GNS construction, level-1+AB rank closure,
CHSH-specific rank calculation) that this codebase does not have. It
is a multi-week project unto itself, independent of the Q_{1+AB}
substrate certification work.

### Pre-existing inquisitor LOW

`coq/kami_hw/F4_VerilogEvaluator.v` — vacuity score 65, tag
`const-fun`. Pre-existing, unrelated to Q_{1+AB} work, untouched by
any of the four slices.

---

## §A — Slice 1: γ = 0 (`instr_chsh_lassert_1ab`, tag 0x2F)

### Math kernel

New file [coq/kernel/quantum/QuantumPartitionPSD_1AB.v](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):

1. **Fin9 / Vec9 / Matrix9 / sum_fin9 / quad9 / PSD9 / symmetric9** —
   9×9 PSD machinery (≈ lines 72–107). Qed-closed.

2. **`q1ab_moment_matrix`** — the 9×9 NPA Q_{1+AB} matrix parametric
   in (E_{00}..E_{11}, γ_1..γ_5) (lines 131–219). Symmetry theorem
   [q1ab_moment_matrix_symmetric](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L271)
   Qed-closed.

3. **`column_contractive_q1ab`** predicate (line 391) and full
   biconditional [q1ab_psd_iff_column_contractive](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L527)
   Qed-closed in both directions via SOS decomposition + variable
   cancellation.

4. **Integer-arithmetic check** in
   [coq/kernel/foundation/VMStep.v](coq/kernel/foundation/VMStep.v):
   `sum_E_sq_check_witness` and `column_contractive_check_q1ab_kernel`
   are pure Z-arithmetic. Re-exported in the new file as
   `column_contractive_check_q1ab`.

5. **Soundness** [column_contractive_check_q1ab_sound_at_g_zero](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L735)
   Qed-closed: integer check → real predicate at γ = 0. Uses an
   explicit 4-D Cauchy-Schwarz SOS identity + existing Q_1 soundness
   machinery.

6. **Diagnostic (§9)**
   [q1ab_check_at_gzero_forces_unit_ball](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L988)
   and [q1ab_check_at_gzero_implies_classical_bound](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L1012)
   Qed-closed. **Verdict**: the γ = 0 check forces
   `E_{00}² + E_{01}² + E_{10}² + E_{11}² ≤ 1`, hence `|S| ≤ 2`. This
   is strictly inside the classical-bound cone L (which is the convex
   hull of 16 ±1 vertices) — PR-box is rejected, and classical
   vertices like `(1, 1, 1, −1)` are also excluded. Full Tsirelson
   saturation (`|S| = 2√2`) is **not** admitted at γ = 0; it requires
   the γ-parameterized extensions in slices B/C/D.

### Kernel bridge

[chsh_lassert_1ab_no_trap_implies_q1ab_psd](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
— a successful step of `instr_chsh_lassert_1ab` forces PSD9 of the
9×9 NPA matrix at γ = 0. The integer check is performed *by the
opcode itself*, so the conclusion has no external hypothesis.
Qed-closed.

Wrapper [chsh_lassert_1ab_no_trap_implies_quantum_realizable_q1ab](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
packages this as a `quantum_realizable_q1ab` (= symmetric9 + PSD9)
conclusion.

### Opcode wiring

- **Constructor** in `vm_instruction` ([VMStep.v:202](coq/kernel/foundation/VMStep.v#L202)).
- **Cost** = `S mu_delta` (cert-setter) in `instruction_cost`.
- **Classification** = cert-setter in `is_cert_setterb`.
- **Step relations** `step_chsh_lassert_1ab_ok` / `_bad` in `vm_step`.
- **`vm_apply` branch** in [SimulationProof.v](coq/kernel/foundation/SimulationProof.v).
- **Binary encoding** at tag 47 (0x2F) in [VMInstructionEncoding.v](coq/kernel/foundation/VMInstructionEncoding.v),
  decoder round-trip restored.
- **Pattern matches** across kernel + kami_hw + hardware bridges:
  Locality, DagRestriction, ClassicalConservativity, MuLedgerConservation,
  LocalInfoLoss, RevelationRequirement, MuShannonQuantitative,
  LandauerDerivation, CHSHExtraction, PythonBisimulation,
  ThreeLayerIsomorphism, Abstraction, EmbedStep, ShadowEmbedStep,
  VerilogRefinement — every pattern updated explicitly (no
  wildcards); every dependent proof re-closed with Qed.

### Extraction + harness + tests

- OCaml: `build/thiele_core.ml` contains `Coq_instr_chsh_lassert_1ab`,
  cost case, `is_cert_setterb` case, `vm_apply` branch.
- `scripts/forge.py` maps `CHSH_LASSERT_1AB → 0x2F`.
- `thielecpu/generated/generated_core.py` regenerated.
- `build/extracted_vm_runner.ml` parses `CHSH_LASSERT_1AB cost`.
- `thielecpu/vm.py` parse arm + dispatch arm + `_CERT_SETTERS` entry.

---

## §B — Slice 2: γ_5 (`instr_chsh_lassert_1ab_g5`, tag 0x30)

### Real-valued caller witness (§12)

[QuantumPartitionPSD_1AB.v §12](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
closes the γ_5-only slice as a real-valued caller check:

1. **Block decomposition** [q1ab_residual_g5_only_decomp](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   at γ_1 = γ_2 = γ_3 = γ_4 = 0 with γ_5 free, `q1ab_residual` splits
   as (top 2×2 in v_{B1}, v_{B2}, identical to γ = 0) + (bottom 4×4
   in v_{ij} carrying the `2γ_5·(v_{11}v_{22} + v_{12}v_{21})` cross
   term). Closed by `ring`.

2. **Weighted 4D Cauchy-Schwarz as a 6-term SOS identity**
   [weighted_4d_CS_SOS_identity](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   for any A, B, α, β, γ, δ, x, y, z, w,
   `(B(α²+γ²) + A(β²+δ²))·(A(x²+z²) + B(y²+w²)) − AB·(αx+βy+γz+δw)²
    = (Bαy−Aβx)² + (Bαw−Aδx)² + (Aβz−Bγy)² + (Bγw−Aδz)² + AB·(αz−γx)²
    + AB·(βw−δy)²`. Closed by `ring`.

3. **Inequality form** [weighted_4d_CS_nonneg](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   immediate from SOS identity + A, B ≥ 0.

4. **Witness predicate** [q1ab_g5_caller_witness](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   `−1 < γ_5 < 1` AND
   `(1−γ_5)·[(e_{00}+e_{11})² + (e_{01}+e_{10})²]
    + (1+γ_5)·[(e_{00}−e_{11})² + (e_{01}−e_{10})²] ≤ 2(1−γ_5²)`. At
   γ_5 = 0 this collapses to the unit ball.

5. **Bottom-block nonneg** [q1ab_bottom_block_g5_nonneg](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   change of variables rotates the cross term into a
   `(1+γ_5)/(1−γ_5)`-weighted diagonal; weighted CS closes via the
   SOS identity, cancelling AB > 0.

6. **Composite caller check → column_contractive_q1ab**
   [q1ab_g5_caller_check_implies_column_contractive](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   `zero_marginal_column_contractive E` + γ_5 witness ⟹
   `column_contractive_q1ab E 0 0 0 0 γ_5`.

7. **Headline PSD9** [q1ab_g5_caller_check_implies_psd9](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   composes with §5's `column_contractive_q1ab_implies_psd9` to give
   `PSD9 (q1ab_moment_matrix E 0 0 0 0 γ_5)`.

8. **Strict-extension diagnostic**
   [q1ab_g5_witness_strict_extension_exists](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   exhibits `(e_{ij} = 3/5, γ_5 = 1/2)` with `||E||² = 36/25 > 1`
   still admitted by the witness — the γ_5 extension genuinely
   enlarges the γ = 0 unit ball.

### Integer-witnessed γ_5 check (§13)

[QuantumPartitionPSD_1AB.v §13](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
lifts §12 to a pure Z-arithmetic decision procedure:

1. **Bridge lemma** [state_bucket_correlation_to_IZR](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   `state_bucket_correlation s d = IZR (chsh_d_z s d) / IZR (chsh_n_z s d)`
   when `chsh_n_z s d > 0`.
2. **Abstract integer check** [q1ab_g5_caller_witness_z_abs](coq/kernel/quantum/QuantumPartitionPSD_1AB.v):
   bool decider on `(D_xy, N_xy, Ng5, Dg5)` enforcing strict N
   positivity, `−Dg5 < Ng5 < Dg5`, and the cleared polynomial
   `Dg5·(Dg5−Ng5)·X_int + Dg5·(Dg5+Ng5)·Y_int ≤ 2·(Dg5²−Ng5²)·Den2`.
3. **Abstract soundness** [q1ab_g5_caller_witness_z_abs_sound](coq/kernel/quantum/QuantumPartitionPSD_1AB.v).
4. **WitnessCounts variant** [q1ab_g5_caller_witness_z](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
   + soundness [q1ab_g5_caller_witness_z_sound](coq/kernel/quantum/QuantumPartitionPSD_1AB.v).
5. **Composite headline check** [q1ab_g5_full_integer_check](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
   = `column_contractive_check_witness` ∧ `q1ab_g5_caller_witness_z`,
   with soundness [q1ab_g5_full_integer_check_sound](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)
   giving `PSD9 (q1ab_moment_matrix E 0 0 0 0 (IZR Ng5 / IZR Dg5))`
   from the bool check.

### Opcode wiring

New constructor [instr_chsh_lassert_1ab_g5 (mu_delta same_g5 diff_g5 : nat)](coq/kernel/foundation/VMStep.v#L211)
carrying a γ_5 nat bucket pair (γ_5 = (same_g5 − diff_g5)/(same_g5 +
diff_g5)). Plumbed through:

- **VMStep.v** — constructor, cost (S mu_delta, cert-setter),
  classification, step relations `_ok` / `_bad`,
  `q1ab_g5_check_z_kernel` + composite kernel
  `q1ab_g5_full_integer_check_kernel`.
- **SimulationProof.v** — `vm_apply` branch.
- **VMInstructionEncoding.v** — tag 48 (0x30) encoder + decoder
  round-trip via `decode_chain`.
- **MuLedgerConservation.v, VMEncoding.v, Locality.v, DagRestriction.v,
  ClassicalConservativity.v, LocalInfoLoss.v, RevelationRequirement.v,
  MuShannonQuantitative.v, LandauerDerivation.v, CHSHExtraction.v,
  PythonBisimulation.v, ThreeLayerIsomorphism.v, Abstraction.v,
  EmbedStep.v, ShadowEmbedStep.v, VerilogRefinement.v** — every
  pattern-match arm updated explicitly.

### Extraction + harness + tests

- `build/thiele_core.ml`: `Coq_instr_chsh_lassert_1ab_g5 of int * int * int`.
- `build/extracted_vm_runner.ml` parses
  `CHSH_LASSERT_1AB_G5 mu_delta same_g5 diff_g5`.
- `scripts/forge.py`: tag 0x30. `scripts/forge_vm.py`: field map.
- `thielecpu/vm.py` + `thielecpu/generated/generated_core.py`
  regenerated.

---

## §C — Slice 3: γ_345 (`instr_chsh_lassert_1ab_g345`, tag 0x31)

### Math kernel (§14)

With γ_1 = γ_2 = 0, all three of γ_3, γ_4, γ_5 free.

- **`q1ab_residual_g345_decomp`** — block decomposition at γ_1 = γ_2 = 0:
  `q1ab_residual = b_part(b1, b2; v) + bot_g5_only(v)`, where
  `b_part` is the (b1, b2)-augmented 2×2 form carrying γ_3, γ_4 as a
  linear part. Closed by `ring`.
- **`augmented_2x2_qf_nonneg`** — the 2-variable Schur-augmented PSD
  lemma. Given strict zero-marginal-column-contractive
  (A > 0, det(M_b) > 0) and the Schur slack
  `det(M_b)·c ≥ Q_adj(L_1, L_2)`, the augmented QF
  `A·b1² + 2B·b1·b2 + C_M·b2² + 2·L_1·b1 + 2·L_2·b2 + c ≥ 0` for all
  (b1, b2). Polynomial identity:
  `A·(A·C_M − B²)·(QF + c) = (A·C_M − B²)·(A·b1 + B·b2 + L_1)²
                            + ((A·C_M − B²)·b2 + (A·L_2 − B·L_1))²
                            + A·((A·C_M − B²)·c − Q_adj)`
  closed by `ring`, then `nra`.
- **`q1ab_g345_caller_witness`** — strict
  zero-marginal-column-contractive + 4-variable universal
  `∀ v ∈ R⁴, det(M_b)·bot_g5_only(v) ≥
   Q_adj(g_3·v_{12} + g_4·v_{22}, g_3·v_{11} + g_4·v_{21})`.
- **`q1ab_g345_caller_check_implies_column_contractive`** — witness
  → `column_contractive_q1ab e_{ij} 0 0 g_3 g_4 g_5`.
- **`q1ab_g345_caller_check_implies_psd9`** — composed corollary.
- **`q1ab_g345_witness_g3g4_zero`** — sanity check: at γ_3 = γ_4 = 0
  the witness reduces to §12's γ_5 closure.

### Lifted to integer + 4×4 Sylvester PD (§15)

Sylvester-PD bool decision over the 4×4 difference matrix
`H_{γ_345} = det_M·M_M − M_N`:

1. **Generic 4×4 LDLT (§15.1)** —
   [sym4_qf, sym4_d1..sym4_d4, sym4_P1, sym4_Q1, sym4_Q2,
    sym4_LDLT_identity, sym4_qf_nonneg_from_pd](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L1855).
   PD interior (4 leading Sylvester minors > 0) ⟹ `sym4_qf` nonneg
   via the explicit LDLT identity (one `ring` call, no `nra` / `field`).
2. **γ_345 H specialization (§15.2)** —
   [q345_A, q345_B, q345_C_M, q345_det_M, q345_H11..q345_H44,
    q345_sym4_qf_equals_diff](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L2000).
   Closed by `ring`.
3. **Real-valued minors witness (§15.3)** —
   [q1ab_g345_minors_witness](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L2072):
   strict column-contractive + 4 strict-PD inequalities.
   [q1ab_g345_minors_witness_implies_caller_witness](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L2123)
   bridges to §14, closing PSD9.
4. **Cleared-Z bridge layer (§15.4)** — 41 Z-helper definitions in
   [coq/kernel/foundation/VMStep.v](coq/kernel/foundation/VMStep.v)
   (`cleared_A_num`, `cleared_C_M_num`, `cleared_B_num`,
   `cleared_det_M_num`, 10× `cleared_HXX_num`, `sym4_d1_Z..sym4_d4_Z`,
   4× `cleared_d_k_num`) plus 14 bridge lemmas proving
   `IZR (numerator) = denominator · real_value`.
5. **Bool integer check + soundness (§15.5)** —
   [q1ab_g345_caller_witness_z_abs](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L2794),
   [q1ab_g345_caller_witness_z_abs_sound](coq/kernel/quantum/QuantumPartitionPSD_1AB.v#L2801):
   integer check passes ⟹ minors witness ⟹ PSD9.

**Refactoring note.** The 41 Z-helpers live in VMStep.v (the
foundation needs them for the kernel-Z check).
`q1ab_g345_caller_witness_z_abs` in the quantum file is a one-line
forwarder to `q1ab_g345_check_z_kernel`.

### Opcode wiring

New constructor
[instr_chsh_lassert_1ab_g345 (mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat)](coq/kernel/foundation/VMStep.v#L233).
Plumbed through the same 14+ kernel/kami_hw files as §B. Cost
discipline = `S mu_delta`, classification = true, tag 0x31 (50th
opcode), binary encoder/decoder round-trip preserved. Step relations
`step_chsh_lassert_1ab_g345_ok` / `_bad`; ok-step triggers
`q1ab_g345_full_integer_check_kernel` over WitnessCounts + (Ng3, Dg3,
Ng4, Dg4, Ng5, Dg5).

**Region diagnostic** — admitted rationals are precisely the strict-PD
interior of §14's caller witness cone: trial-count denominators
N_{ij} > 0, γ-denominators Dg_k > 0, |g_k| < 1 for k = 3, 4, 5,
strict zero-marginal-column-contractive, and strict positivity of the
4 leading principal minors of `H_{γ_345}`.

### Extraction + harness + tests

- `build/thiele_core.ml`:
  `Coq_instr_chsh_lassert_1ab_g345 of int*int*int*int*int*int*int`.
- `build/extracted_vm_runner.ml` parses
  `CHSH_LASSERT_1AB_G345 mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5`.
- `scripts/forge.py`: tag 0x31. `scripts/forge_vm.py`: field map.
- `thielecpu/vm.py` + `thielecpu/generated/generated_core.py`
  regenerated.

---

## §D — Slice 4: full γ_12345 (`instr_chsh_lassert_1ab_g12345`, tag 0x32)

With γ_1, γ_2 free, the b-block / v-block bilinear cross terms
prevent §C's augmented-Schur trick. Instead, we treat the full
6-variable `q1ab_residual` as a single symmetric 6×6 quadratic form
`H_{γ_12345}` and certify PSD via a **compositional Schur cascade**:

```
sym6_qf nonneg
  ⇐ h11 > 0 ∧ sym5_qf(scaled_S_6, ·) nonneg     (sym6 → sym5)
  ⇐ h11 > 0 ∧ sym5_d_1(scaled_S_6) > 0 ∧ sym4_qf(scaled_S_5, ·) nonneg
                                                 (sym5 → sym4)
  ⇐ … ⇐ sym4 PD interior (§15.1 base case)
```

Each Schur step is a single polynomial identity provable by `ring`.

### Math kernel (§16.1–16.4)

- **§16.1** — sym5 Schur reduction
  ([QuantumPartitionPSD_1AB.v ~L2974+](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)).
  10 `sym5_scaled_S_ij` entries (each `h11·h_{ij} − h_{1i}·h_{1j}`),
  `sym5_P1` linear form, `sym5_Schur_identity`
  (`h11·sym5_qf = P1² + sym4_qf(scaled_S, v_{2..5})`, ring),
  `sym5_pd_interior` predicate, `sym5_qf_nonneg_from_pd`.
- **§16.2** — sym6 Schur reduction
  ([QuantumPartitionPSD_1AB.v ~L3170+](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)).
  Same template at 6×6: 15 `sym6_scaled_S_ij`, `sym6_P1`,
  `sym6_Schur_identity` (`h11·sym6_qf = P1² + sym5_qf(...)`, ring),
  `sym6_pd_interior`, `sym6_qf_nonneg_from_pd`.
- **§16.3** — γ_12345 H specialization
  ([QuantumPartitionPSD_1AB.v ~L3550+](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)).
  21 `q12345_HXX` polynomials in `(e_{ij}, γ_1..γ_5)`, and
  `q12345_sym6_qf_equals_residual` proving
  `sym6_qf q12345_H… (vB1, vB2, v11, v12, v21, v22) = q1ab_residual`.
  Closed by `ring`.
- **§16.4** — real-valued minors witness + PSD9 bridge
  ([QuantumPartitionPSD_1AB.v ~L3650+](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)):
  `q1ab_g12345_minors_witness` = `sym6_pd_interior` at q12345 entries;
  `q1ab_g12345_minors_witness_implies_column_contractive`,
  `q1ab_g12345_minors_witness_implies_psd9`; sanity-check
  `q12345_witness_at_g12_zero_reduces_to_g345`.

### Integer-Z kernel (§16.5)

**[VMStep.v](coq/kernel/foundation/VMStep.v) — cleared-Z numerators
+ Schur-step helpers + Z-bool decider:**

- `g12345_COMMON_Z` uniform scaling factor
  `(N00·N01·N10·N11·Dg1·Dg2·Dg3·Dg4·Dg5)²`.
- 21 `cleared_g12345_HXX_Z` numerators — each is
  `g12345_COMMON_Z · q12345_HXX(D/N, ..., Ng/Dg)` cleared to Z.
- `schur_step_Z h11 hij h1i h1j := h11·hij - h1i·h1j` helper.
- 15 `cleared_g12345_S6_IJ_Z` (4×4 Schur of row 1 of cleared sym6).
- 10 `cleared_g12345_S5_IJ_Z` (4×4 Schur of row 1 of cleared 5×5
  scaled_S_6).
- `q1ab_g12345_check_z_kernel` bool decider: positivity of all N's
  and Dg's, `|Ng_k| < Dg_k` bounds for k=1..5, and six Schur-cascade
  PD checks (H11 > 0, S6_22 > 0, sym4_d_k of cleared S5 > 0 for
  k=1..4).
- `q1ab_g12345_full_integer_check_kernel` composite on
  `WitnessCounts` + 5 γ-bucket pairs.

**[QuantumPartitionPSD_1AB.v](coq/kernel/quantum/QuantumPartitionPSD_1AB.v) — 21 H bridges + 15 S6 bridges + 10 S5 bridges + soundness:**

- **21 H-entry bridges** `cleared_g12345_HXX_Z_bridge` for
  XX ∈ {11..16, 22..26, 33..36, 44..46, 55..56, 66}: each proves
  `IZR (cleared_g12345_HXX_Z(...)) = IZR (g12345_COMMON_Z(...))
   · q12345_HXX(IZR D / IZR N, …, IZR Ng / IZR Dg)`
  under denominator-positivity hypotheses. Closed by a uniform
  `g12345_H_bridge` tactic (one-liner proofs).
- **15 S6 cascade bridges** `cleared_g12345_S6_22_Z_bridge` …
  `cleared_g12345_S6_66_Z_bridge`
  ([~L4097–4695](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)):
  each proves `IZR (cleared_g12345_S6_ij_Z(...)) = KZ² ·
  (H11·H_ij − H_1i·H_1j)`. Template:
  `unfold; rewrite schur_step_Z_IZR; rewrite [3-or-4 H bridges by assumption]; ring`.
- **10 S5 cascade bridges** `cleared_g12345_S5_22_Z_bridge` …
  `cleared_g12345_S5_55_Z_bridge`
  ([~L4777–4940](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)):
  each proves `IZR (cleared_g12345_S5_ij_Z(...)) = KZ⁴ ·
  sym5_scaled_S_ij` expanded in 21 `q_kl_R` polynomial atoms.
  Template: `unfold; rewrite schur_step_Z_IZR; rewrite [3-or-4 S6 bridges by assumption]; ring`.
- **4 sym4_d_k cascade** inlined in the soundness theorem:
  1. `apply Z.ltb_lt + apply IZR_lt` lifts integer-Schur PD checks to
     `0 < IZR (sym4_d_k_Z(cleared_S5_*_Z))`.
  2. `rewrite sym4_d_k_Z_IZR` pushes IZR into `sym4_d_k`.
  3. `rewrite cleared_g12345_S5_*_Z_bridge in Hd_k by assumption`
     substitutes `KZ⁴ · S5_*_R` for each of the 10 S5 entries.
  4. `rewrite sym4_d_k_scale` factors `(KZ⁴)^k` out of `sym4_d_k`.
  5. `apply Rmult_lt_reg_l with (KZ^(4·k))` cancels the scaling,
     using `KZ2_pos`, `KZ4_pos`, `KZ8_pos`, `KZ12_pos`, `KZ16_pos`
     to discharge positivity side conditions.
- **Soundness theorem** `q1ab_g12345_caller_witness_z_abs_sound`
  ([~L5050–5125](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)):
  bool integer check passes ⇒ `q1ab_g12345_minors_witness` at the
  IZR-rational correlators and γ values.
- **Headline PSD9 corollary**
  `q1ab_g12345_caller_witness_z_abs_implies_psd9`
  ([~L5130+](coq/kernel/quantum/QuantumPartitionPSD_1AB.v)):
  composes soundness with §16.4's
  `q1ab_g12345_minors_witness_implies_psd9` for a one-step
  bool-check → PSD9 conclusion.

### Opcode wiring

New constructor
[instr_chsh_lassert_1ab_g12345 (mu_delta same_g1 diff_g1 same_g2 diff_g2 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 : nat)](coq/kernel/foundation/VMStep.v)
carrying 11 nat args (1 cost + 5 γ-bucket pairs). Plumbed through:

- **VMStep.v** — constructor + cost (`S mu_delta`, cert-setter) +
  `is_cert_setterb` arm + step relations `_ok` / `_bad`.
- **SimulationProof.v** — `vm_apply` branch + `vm_step_pc_advance`
  PC-trap exemption.
- **MuLedgerConservation.v** — `vm_apply_mu` Schur-cascade arm.
- **VMInstructionEncoding.v** — tag 50 (0x32) encoder + 11-arg
  decoder with `decode_chain` round-trip preserved.
- **VMEncoding.v** — instruction-layout T_Halt arm.
- **Locality.v** — `instr_targets` empty-list arm +
  `states_agree_on_module` arm.
- **DagRestriction.v** — `vm_apply_chsh_lassert_1ab_g12345_pc`
  helper + `dag_instr_advances_pc` arm.
- **ClassicalConservativity.v** — `is_classical_opcode` false arm.
- **LocalInfoLoss.v** — `instr_mu_cost` +
  `other_instr_module_count_unchanged` + `cost_bounds_info_loss` arms.
- **RevelationRequirement.v** — three cert-channel preservation arms.
- **LandauerDerivation.v** — three preservation/cost arms.
- **MuShannonQuantitative.v** — `vm_apply_cert_addr_cases` arm.
- **CHSHExtraction.v** — extended `destruct instr as` pattern for the
  two extractor-validity lemmas.
- **PythonBisimulation.v** — `increments_pc` arm.
- **ThreeLayerIsomorphism.v** — `instruction_exhaustive` arm +
  `increments_pc_by_one` arm.
- **Abstraction.v** (kami_hw) — `kami_apply_instr` Schur-cascade arm.
- **EmbedStep.v** (kami_hw) — `embed_step_compute` Schur-cascade arm.
- **ShadowEmbedStep.v** (kami_hw) — `ShadowSupportedOpcode` exclusion
  + `SupportedOpcode_implies_ShadowSupported` arm.
- **VerilogRefinement.v** (kami_hw) — `verilog_increments_pc` arm.

### Extraction + harness + tests

- `build/thiele_core.ml`:
  `Coq_instr_chsh_lassert_1ab_g12345 of int * int * int * int * int *
   int * int * int * int * int * int` and the
  `q1ab_g12345_full_integer_check_kernel` extracted function.
- `build/extracted_vm_runner.ml` parses
  `CHSH_LASSERT_1AB_G12345 mu_delta same_g1 diff_g1 same_g2 diff_g2
   same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5`.
- `scripts/forge.py`: `CHSH_LASSERT_1AB_G12345 → 0x32`.
- `scripts/forge_vm.py`: `Instr_chsh_lassert_1ab_g12345` field map.
  The `parse_cert_setters` helper was also taught to handle the
  multi-line OCaml emission style that the formatter uses when a
  long arm wraps `-> true` onto the next line.
- `thielecpu/vm.py` regenerated; `_CERT_SETTERS` includes
  `chsh_lassert_1ab_g12345`.
- `thielecpu/generated/generated_core.py` regenerated; tag byte 50 in
  `COQ_TAG_TO_OPCODE_BYTE`, mnemonic `CHSH_LASSERT_1AB_G12345` in
  `COQ_TAG_TO_MNEMONIC`.
- `tests/test_completeness_gate.py`: `CANONICAL_51` +
  `test_vmstep_has_51_constructors` + new `chsh_lassert_1ab_g12345`
  entry in `test_vm_run_all_46_opcodes_accepted`. OCaml↔RTL parity
  slack 3 → 4.

---

## §17 — Headline no-trap wrappers (all slices)

Each Q_{1+AB} cert-opcode in the γ_*-extended family has a headline
wrapper packaging "no-trap step ⇒ `quantum_realizable_q1ab` at the
bucket-derived rationals", paralleling the existing slice-A wrapper
`chsh_lassert_1ab_no_trap_implies_quantum_realizable_q1ab`. The three
new wrappers live in §17 of
[QuantumPartitionPSD_1AB.v](coq/kernel/quantum/QuantumPartitionPSD_1AB.v).

- **Slice B** — `chsh_lassert_1ab_g5_no_trap_implies_quantum_realizable_q1ab`:
  direct application of `q1ab_g5_full_integer_check_sound`, which
  already concludes PSD9 at `state_bucket_correlation`-based
  correlators. No IZR-bridge step needed.
- **Slice C** — `chsh_lassert_1ab_g345_no_trap_implies_quantum_realizable_q1ab`:
  extracts N00..N11 positivity from the bool decider, applies
  `state_bucket_correlation_to_IZR` to bridge each `state_e_xy s` to
  `IZR D / IZR N`, then applies
  `q1ab_g345_caller_witness_z_abs_implies_psd9`.
- **Slice D** — `chsh_lassert_1ab_g12345_no_trap_implies_quantum_realizable_q1ab`:
  same pattern as slice C, with nine N/Dg positivity facts extracted
  (the cascade's first nine conjuncts), then
  `q1ab_g12345_caller_witness_z_abs_implies_psd9` applied with those
  positivities as explicit arguments.

Each wrapper composes the existing soundness theorem with
`q1ab_moment_matrix_symmetric` to deliver the `symmetric9 ∧ PSD9`
packaging. `Print Assumptions` on all three: only the two stdlib
axioms. No project-local axiom introduced.

The headline claim each wrapper makes for its slice:

> A non-trapping, no-err-flip execution of the cert-opcode implies
> `quantum_realizable_q1ab` at the witness-counter-derived rational
> correlators (`state_e00 s`, `state_e01 s`, `state_e10 s`,
> `state_e11 s`) and at the bucket-derived γ rationals
> (`IZR (chsh_d_z same_g_k diff_g_k) / IZR (chsh_n_z same_g_k diff_g_k)`).

i.e. the cert opcode certifies Q_{1+AB} membership (in the codebase's
operational sense: 9×9 NPA moment matrix symmetric and PSD).

---

## Implementation notes (cross-slice)

### Ring vs let bindings

`ring` does **not** reduce `let` bindings in goal statements even
after `cbv zeta`. The cleared-Z bridges in slices C and D therefore
use *explicit* sub-expression forms — write
`IZR D00 / IZR N00` directly in the RHS rather than introducing
`let r00 := …`. This expands the line count per lemma but keeps the
proofs to a one-line `ring` close after rewrites.

### Section structure for the §D cleared-Z bridges

The S5 cascade + KZ helpers + soundness theorem live inside a single
`Section S5_and_minors_bridges` that declares 18 Z-typed `Variables`
(D00, N00, …, Ng5, Dg5) plus 22 `Local Notation`s (KZ + 21
`q_kl_R`). **No** Section `Hypothesis` / `Prop`-typed `Variable` —
the inquisitor flags those as axiom-equivalent. Instead, each lemma
takes the 9 denominator-positivity preconditions explicitly, bound by
`intros HN00 HN01 HN10 HN11 HDg1 HDg2 HDg3 HDg4 HDg5.` in every proof,
and `rewrite ... by assumption` discharges the bridge side conditions.

### Single source of truth for OCaml extraction

Both extraction roots — [coq/Extraction.v](coq/Extraction.v) →
`build/thiele_core.ml` and
[coq/ThieleMachineComplete.v](coq/ThieleMachineComplete.v) →
`build/thiele_core_complete.ml` — produce byte-identical OCaml for
the shared surface, via matching `Extraction Inline` directives on
`Coq.Init.Nat` helpers that intermediate kernel imports would
otherwise pull into the `Nat` module. (Note: `ThieleMachineComplete.v`
ships only the original 47-opcode subset; the four `CHSH_LASSERT_1AB*`
opcodes live exclusively on the modular `Extraction.v` root.)

### Pre-existing report Q&A

- **γ = 0 diagnostic**: γ = 0 admits no supraclassical correlator.
  Formally proved by `q1ab_check_at_gzero_implies_classical_bound`
  (|S| ≤ 2). Strictly stronger: forces `||E||² ≤ 1`.
- **Region admitted by current integer check**: the unit ball at γ = 0;
  the γ_5 cone at slice B; the γ_345 cone at slice C; the full γ_12345
  Schur-cascade cone at slice D. PR-box is rejected at every slice.
  Tsirelson saturation (|S| = 2√2) is admitted from slice C onward
  for the right γ_3, γ_4, γ_5 values.
- **Ishizaka step**: not formalized. The file claims only PSD9
  (= Q_{1+AB} membership), not Q membership.
- **Kami RTL**: the four `CHSH_LASSERT_1AB*` opcodes are
  VM-only — they appear in the Kami snapshot apply (Abstraction.v),
  embed step (EmbedStep.v), shadow embed (ShadowEmbedStep.v), and
  Verilog-PC bookkeeping (VerilogRefinement.v) as trap-discipline
  arms, but they have no concrete RTL counterpart in `ThieleTypes.v`
  (OCaml↔RTL slack 4).

---

## Historical: rank-3 Schur-complement alternative for γ_1, γ_2 (not implemented)

The original planning analysis for closing γ_1, γ_2 envisioned a
**rank-3 Schur-complement characterization** rather than the
compositional sym6 → sym5 → sym4 Schur cascade that was actually used
in §D. This route is preserved here as historical context for the
alternative not taken.

γ_1, γ_2 (the 3-body A-A-B moments `⟨A_1A_2B_1⟩`, `⟨A_1A_2B_2⟩`) enter
the second and third SOS-deducted forms
`(e_{00}vB1 + e_{01}vB2 + γ_1 v_{21} + γ_2 v_{22})²` and
`(e_{10}vB1 + e_{11}vB2 + γ_1 v_{11} + γ_2 v_{12})²`. They couple
b1, b2 to v_{ij} symmetrically, so the augmented Schur trick of §14
doesn't apply — the b-block has bilinear-in-(b, v) cross terms that
interleave with the existing −e_{ij}·b·… structure.

The proposed alternative was: write the residual under any
(γ_1..γ_5) as `||y||² + N_γ(y, y) − ||R^T y||²` where R is the 6×3
matrix whose columns are the gradients of `IP_ee`, `IP_g_1`, `IP_g_2`
(the three deducted squared forms), and N_γ is the bilinear matrix of
the γ_3, γ_4, γ_5 cross terms. The residual is then
`y^T (I_6 − R R^T + N_γ) y`. PSD ⇔ the 6×6 matrix
`I_6 − R R^T + N_γ ≥ 0`. By Schur complement,
`I_6 − R R^T ≥ 0 ⇔ R^T R ≤ I_3`, reducing the test to Sylvester on
the 3×3 Gram matrix `G_{ij} := r_i · r_j`:

- `G_{11} = e_{00}² + e_{01}² + γ_1² + γ_2²`
- `G_{22} = e_{10}² + e_{11}² + γ_1² + γ_2²`
- `G_{33} = ||E||²`
- `G_{12} = e_{00}e_{10} + e_{01}e_{11}`
- `G_{13} = e_{10}γ_1 + e_{11}γ_2`
- `G_{23} = e_{00}γ_1 + e_{01}γ_2`

Sylvester gives 3 polynomial inequalities (degrees 2, 4, 6) on
`I_3 − G`. Encoding the rank-3 Schur-complement equivalence in Coq
would have required either an explicit 6×6 SOS identity expressing
`y^T (I_6 − R R^T) y` as a polynomial-witnessed sum of squared linear
forms in y, or a generic linear-algebra lemma over a generic real
matrix type.

The compositional sym6 → sym5 → sym4 cascade in §D was preferred
because each Schur step is a single `ring` identity at sym4 size, and
the integer kernel composes by reusing the existing `sym4_d_k_Z`
machinery from §15.1.
