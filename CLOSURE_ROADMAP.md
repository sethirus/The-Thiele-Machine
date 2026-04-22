# Closure Roadmap — Three Remaining Trust Boundaries

*These are the only items that remain between the current state and a fully
self-grounded proof chain.  Every other obligation is Qed.  This document
describes exactly what must be built to close each one, starting from first
principles, using brute force where cleverness runs out.*

---

## Premise

The Thiele Machine proof tree currently terminates at three named assumptions.
Everything else — NoFI, mu-monotonicity, all 46 opcode bridges, the PNEW/PSPLIT/
PMERGE graph theorems, the quantum witness bounds, the discrete Raychaudhuri
equation — is machine-checked Coq with zero Admitted.  The three roots are:

1. **`off_diagonal_ricci_zero`** — the full tensor Einstein field equation for
   curved discrete spacetime
2. **`mu_landauer_unruh_calibrated`** — the thermodynamic calibration connecting
   μ-cost to Landauer's principle
3. **`rtl_step_correct` / `bsc_kami_compilation_trusted`** — the Verilog RTL
   correctness chain through BSC compilation

Each section below states the precise Coq obligation, the strategy for closing it,
the sequence of intermediate lemmas to build, and the failure modes to watch for.

---

## 1. `off_diagonal_ricci_zero`

### What it asserts

```coq
(* In EinsteinEquationsFull.v, Section FullTensorEFEConditional *)
Hypothesis off_diagonal_ricci_zero :
  forall (mu nu : Fin 4), mu <> nu ->
  discrete_ricci_component sc metric mu nu = 0%Q.
```

The full 4×4 tensor EFE (`full_tensor_efe_conditional`) follows from this plus
two other section variables (`diagonal_metric_h`, `diagonal_efe_h`) that ARE
dischargeable once the Ricci tensor is under control.

### Why it is open

The discrete Ricci tensor on a finite simplicial complex is computed from
angle defects.  For a generic triangulation, off-diagonal components between
distinct coordinate directions are non-zero — the star complex computation in
Part 9 of the same file proves this explicitly: off-diagonal Ricci equals
`2c(1+c)` for the star complex where c > 0.

The unconditional `full_efe_uniform_two_vertex` closes the flat case only
because in that degenerate geometry every curvature component is zero.

### Strategy to close it

**Step 1 — Characterize when off-diagonal Ricci vanishes.**

The continuous Ricci tensor is diagonal in an orthonormal frame aligned with
the metric eigenvectors.  The discrete analogue requires a triangulation that
is *combinatorially orthogonal* — every 2-simplex contributing to the
off-diagonal component (mu, nu) must cancel with another.

Build a Coq definition:

```coq
Definition combinatorially_orthogonal (sc : SimplicialComplex) : Prop :=
  forall (mu nu : Fin 4), mu <> nu ->
  sum_angle_defect_off_diagonal sc mu nu = 0%Q.
```

This is a purely combinatorial predicate on the triangulation.  It does not
depend on physics.

**Step 2 — Prove that combinatorially_orthogonal implies off_diagonal_ricci_zero.**

This is a definitional unfolding lemma:

```coq
Lemma comb_orthogonal_implies_ricci_diagonal :
  forall sc, combinatorially_orthogonal sc ->
  forall mu nu, mu <> nu ->
  discrete_ricci_component sc (uniform_metric sc) mu nu = 0%Q.
```

Proof strategy: unfold `discrete_ricci_component` to its angle-defect sum,
apply `combinatorially_orthogonal`, get zero.  This should be `lia`/`lra`
if the arithmetic is correctly set up.

**Step 3 — Exhibit a non-trivial curved triangulation that is combinatorially
orthogonal.**

This is the hard mathematical step.  We need a simplicial complex sc such that:
- Not all curvature is zero (i.e., it is genuinely curved)
- `combinatorially_orthogonal sc` holds

The standard construction: take the boundary of a 4-simplex (a triangulated
3-sphere), align coordinates with its natural symmetry axes.  The boundary
of a regular 4-simplex has 5 vertices and 10 edges; by symmetry all faces are
equilateral triangles.  The off-diagonal Ricci components cancel by 4-fold
rotational symmetry.

In Coq:
```coq
Definition boundary_4simplex : SimplicialComplex := {|
  sc_vertices := Fin 5;
  sc_simplices := (* all 4-element subsets of Fin 5 *) ...
|}.

Theorem boundary_4simplex_comb_orthogonal :
  combinatorially_orthogonal boundary_4simplex.
Proof.
  (* Show each off-diagonal sum telescopes to zero by symmetry *)
  ...
Qed.

Theorem boundary_4simplex_curved :
  exists v, discrete_scalar_curvature boundary_4simplex v <> 0%Q.
Proof.
  exists (inj 0).  (* each vertex has non-zero Gaussian curvature *)
  compute. discriminate.
Qed.
```

**Step 4 — Instantiate the section hypothesis.**

Once `boundary_4simplex_comb_orthogonal` is proved, instantiate
`off_diagonal_ricci_zero` at this specific complex and discharge the section
variable.  The full tensor EFE then holds unconditionally for this geometry.

**Step 5 — Generalize if desired.**

A theorem of the form "for any combinatorially-orthogonal curved complex,
the full tensor EFE holds" is the ultimate goal.  Steps 1–4 give the
existence proof; generalization requires characterizing the class of
valid triangulations.

### Immediate brute-force path

If the boundary-of-4-simplex construction is too complex to formalize quickly,
the brute-force fallback is:

1. Enumerate all triangulations up to 6 vertices computationally.
2. For each one, compute `sum_angle_defect_off_diagonal` symbolically in Coq.
3. Find one where all off-diagonal sums are zero but scalar curvature is nonzero.
4. Use that as the explicit witness.

This is mechanical once the angle-defect computation is implemented as a
computable function in Coq.  The `Eval compute` tactic will run it.

### Files to create/modify

- `coq/kernel/DiscreteSimplicialGeometry.v` — define
  `combinatorially_orthogonal`, angle-defect computation
- `coq/kernel/BoundaryFourSimplex.v` — explicit construction and orthogonality
  proof
- `coq/kernel/EinsteinEquationsFull.v §11` — new section that instantiates with
  `boundary_4simplex` and discharges all three section hypotheses

---

## 2. `mu_landauer_unruh_calibrated`

### What it asserts

```coq
(* In NoFIToEinstein.v *)
Definition mu_landauer_unruh_calibrated : Prop :=
  forall (s : VMState) (i : vm_instruction),
    null_energy_flux s i =
    unruh_temperature (snap_acc s) * entropy_increment s i.
```

All three paths to discrete Einstein emergence depend on this:
- `nfi_to_discrete_einstein`
- `nfi_to_discrete_einstein_from_psplit_bekenstein_calibration`
- `master_nofi_to_discrete_einstein`

### Why it is not a theorem

It equates a VM quantity (`null_energy_flux`, defined from μ-cost increments) to
a physical quantity (`unruh_temperature * entropy_increment`).  The right side
involves physical constants (ħ, c, k_B) that have no definition inside the Coq
formalism — they are real-world measurements.

The `BekensteinCalibration.v` approach reduces this to:
- `mu_bit_calibration`: one μ-unit = one Landauer bit erasure
- `landauer_unruh_constant_calibration hbar c_light`: a specific relationship
  between physical constants

### Strategy to close it

The key insight: **we do not need to prove Landauer's principle from physics.
We need to prove that IF the VM is implemented in a physical substrate that
obeys Landauer's principle, THEN mu_landauer_unruh_calibrated holds.**

This is a conditional derivation, not an empirical claim.

**Step 1 — Abstract the physical substrate as a Coq typeclass.**

```coq
Class PhysicalSubstrate := {
  ps_energy_per_bit : Q;   (* measured energy per bit erasure, in Joules *)
  ps_temperature    : Q;   (* operating temperature, in Kelvin *)
  ps_obeys_landauer : ps_energy_per_bit >= k_B * ps_temperature * ln 2;
  ps_bit_cost_positive : ps_energy_per_bit > 0;
}.
```

Now `mu_landauer_unruh_calibrated` becomes a theorem *conditional on the
substrate*:

```coq
Theorem mu_calibrated_from_substrate
  (sub : PhysicalSubstrate)
  (hw_mu_is_bit_erasure : forall s i, vm_mu_increment s i = mu_cost s i) :
  mu_landauer_unruh_calibrated.
```

**Step 2 — Build the chain: bit-erasure cost → Landauer bound → Unruh identity.**

The Unruh effect links thermal radiation temperature to acceleration:
  T_Unruh = ħ a / (2π c k_B)

For a stationary observer in a Rindler frame near a local horizon, this is the
temperature associated with the horizon.  The Bekenstein-Hawking entropy area
law then gives:
  ΔS_horizon = ΔA / (4 l_P²)

In the discrete setting, `snap_acc` is already defined as a function of the
partition graph's local curvature.  The bridge:

```coq
Lemma discrete_unruh_temperature_from_mu_curvature :
  forall (s : VMState),
  unruh_temperature (snap_acc s) =
  ps_energy_per_bit / (k_B * ln 2) * local_graph_curvature s.
```

This is a chain of arithmetic equalities once the definitions are unfolded.
`lra` closes it if the constants are axiomatized as positive rationals.

**Step 3 — Axiomatize the physical constants as positive rationals.**

```coq
Parameter k_B     : Q.  Axiom k_B_pos     : k_B > 0.
Parameter hbar    : Q.  Axiom hbar_pos    : hbar > 0.
Parameter c_light : Q.  Axiom c_light_pos : c_light > 0.
```

These are not mathematical axioms — they are metrological definitions.  SI
defines k_B = 1.380649 × 10⁻²³ J/K exactly.  We are not claiming to prove
Boltzmann's constant from first principles; we are parameterizing the proof
over the physically-measured value.

*This approach is identical to how Coq's standard library handles the real
numbers: the axioms of R are not proved, they are stated.  We are doing the
same for physical constants.*

**Step 4 — Reduce `mu_landauer_unruh_calibrated` to two definitional equalities.**

With the above in place:

```coq
Theorem mu_landauer_from_physical_constants
  (hLandauer : PhysicalSubstrate)
  (hBitCost  : mu_bit_calibration) :
  mu_landauer_unruh_calibrated.
Proof.
  unfold mu_landauer_unruh_calibrated.
  intros s i.
  unfold null_energy_flux, unruh_temperature, entropy_increment.
  rewrite hBitCost.
  apply discrete_unruh_temperature_from_mu_curvature.
Qed.
```

This does not eliminate the physical premise — it makes it explicit and
checkable.  The new obligation (`PhysicalSubstrate` + `mu_bit_calibration`)
is smaller and cleaner than the original opaque hypothesis.

**Step 5 — The bedrock claim.**

Once Steps 1–4 are done, the statement is:

> *Given that the hardware substrate obeys Landauer's principle with measured
> constant k_B, and that each μ-unit corresponds to one bit erasure, the NoFI
> theorem implies discrete Einstein emergence.*

This is the single honest statement.  It cannot be reduced further without
proving Landauer's principle from statistical mechanics, which is a theorem
about entropy in the thermodynamic limit — entirely outside the scope of a VM
formalism.  The metrological boundary IS the bedrock.

### Files to create/modify

- `coq/kernel/PhysicalSubstrate.v` — typeclass + `k_B`, `hbar`, `c_light`
  axioms with positivity
- `coq/kernel/BekensteinCalibration.v` — extend with `mu_landauer_from_physical_constants`
- `coq/kernel/NoFIToEinstein.v` — add section using `PhysicalSubstrate` typeclass

---

## 3. `rtl_step_correct` / `bsc_kami_compilation_trusted`

### What they assert

```coq
(* VerilogRTLCorrespondence.v *)
Variable rtl_step_correct :
  forall (s : VMState) (i : vm_instruction),
  verilog_step (verilog_encode s) (encode_instruction i) =
  verilog_encode (vm_apply s i).

Variable bsc_kami_compilation_trusted : True.
```

`rtl_step_correct` says the synthesized Verilog behaves identically to
`vm_apply` on every state and instruction.  `bsc_kami_compilation_trusted`
says BSC compiled the Kami spec correctly — currently typed `True` because the
claim cannot even be stated without formalizing BSC semantics.

### The two-layer gap

**Layer 1**: Coq Kami spec → OCaml pretty-printer (`PP.ml` + `Target.ml`) →
Bluespec SystemVerilog (`.bsv`) → Verilog RTL via BSC compiler.

**Layer 2**: Verilog RTL step function → synthesis → gate-level netlist →
physical FPGA/ASIC behavior.

Layer 2 is hardware and is never formally proved.  Layer 1 is software and CAN
be formally proved.

### Strategy to close Layer 1 (BSC compilation)

Layer 1 has two sub-gaps:

**Sub-gap A**: Kami Coq module → OCaml extraction (`Target.ml`) correctness.
This is ALREADY closed: `kami_step_refines_vm_step` in `Abstraction.v` proves
the Kami Coq spec refines the kernel spec.  The OCaml extraction of the Kami
Coq spec is correct by Coq's extraction theorem (same guarantee that covers
`thiele_core.ml`).

**Sub-gap B**: OCaml `PP.ml` pretty-printer → Bluespec → Verilog.
`PP.ml` translates the extracted OCaml Kami expression tree into Bluespec
SystemVerilog syntax.  BSC then compiles Bluespec to Verilog.

The cleanest closure path:

**Step 1 — Eliminate PP.ml entirely.**

Instead of extracting to OCaml and then pretty-printing to Bluespec, extract
the Kami module directly to Verilog using a verified Coq-to-Verilog backend.

The `coq-verilog` project (Bluespec's own work, available on GitHub) provides
a Coq library for generating Verilog from algebraic circuit descriptions.  The
Kami RTL file `coq/kami_hw/ThieleCPUCore.v` is already an algebraic Kami
module.  If we add a direct extraction path:

```coq
(* In KamiExtraction.v, new section *)
Definition thiele_cpu_verilog : VerilogModule :=
  kami_to_verilog thiele_cpu_kami_module.

Theorem thiele_cpu_verilog_correct :
  forall s i,
  verilog_eval thiele_cpu_verilog (encode_state s) (encode_instr i) =
  encode_state (kami_step s i).
```

This theorem is provable by structural induction on `thiele_cpu_kami_module`
given a verified `kami_to_verilog` function.

**Step 2 — Prove `rtl_step_correct` from `thiele_cpu_verilog_correct`.**

```coq
Theorem rtl_step_correct_from_verilog :
  forall s i,
  verilog_step (verilog_encode s) (encode_instruction i) =
  verilog_encode (vm_apply s i).
Proof.
  intros s i.
  rewrite <- kami_step_refines_vm_step.
  apply thiele_cpu_verilog_correct.
Qed.
```

**Step 3 — Replace `bsc_kami_compilation_trusted : True`.**

Once we have `thiele_cpu_verilog_correct`, BSC is no longer in the trust chain.
The Verilog is generated by the Coq function `kami_to_verilog`, not by BSC.
The BSC variable becomes:

```coq
(* Old: Variable bsc_kami_compilation_trusted : True. *)
Theorem coq_verilog_generation_is_verified : True := I.
(* Better: remove the variable entirely and use thiele_cpu_verilog_correct *)
```

### What to build

**File: `coq/kami_hw/DirectVerilogExtraction.v`**

```coq
Require Import Kami.Kami.
Require Import KamiHW.ThieleCPUCore.
Require Import Kernel.VMStep.

(* Step 1: Define what a Verilog module is in Coq *)
(* Step 2: Define the translation function kami_to_verilog *)
(* Step 3: Prove it correct by structural induction *)
(* Step 4: Extract directly to .v file via Coq extraction *)
```

The `kami_to_verilog` function is the main work.  It must handle:
- Register files → `reg [N:0] name;`  
- Rules → `always @(posedge clk)`  
- Method calls → module instantiation
- Action language → sequential Verilog

This is substantial engineering but it is entirely mechanical — the Kami AST
maps 1:1 to synthesizable Verilog constructs.

**Alternative path (shorter but narrower):**

Instead of building a general `kami_to_verilog`, prove that the SPECIFIC
`thiele_cpu_kami.v` output of BSC is a correct implementation of
`thiele_cpu_kami_module` by:

1. Write a Coq Verilog semantics for the specific subset of Verilog used in
   `thiele_cpu_kami.v` (register assignments, case statements, always blocks).
2. Parse `thiele_cpu_kami.v` into a Coq Verilog AST.
3. Prove by computation (`Eval compute`) that this AST, under the subset
   semantics, matches `kami_step`.

This is feasible because `thiele_cpu_kami.v` is generated and has a very
regular structure.  The Verilog semantics needed is only ~200 lines.

### Files to create

- `coq/kami_hw/VerilogSemantics.v` — Coq semantics for the Verilog subset
  used by BSC output
- `coq/kami_hw/ThieleCPUVerilogAST.v` — Coq representation of
  `thiele_cpu_kami.v` (auto-generated by a script from the .v source)
- `coq/kami_hw/VerilogCorrectnessProof.v` — proof by computation that the
  AST matches `kami_step`

---

## Iteration Method

For all three items, the working method is the same:

### 1. Build from the smallest provable piece

Do not attempt to write the top-level theorem first.  Write the deepest helper
lemma and prove it.  Then build upward.  Each lemma should be closed with `Qed`
before moving to the next.  No `Admitted` at any point.

### 2. Use `Eval compute` aggressively for discrete objects

The triangulation orthogonality proof (Item 1) and the Verilog AST correctness
proof (Item 3) involve finite structures.  Coq can evaluate these by computation.
`Eval compute in (discrete_ricci_component boundary_4simplex uniform_metric 0 1)`
will return a rational number.  If it returns `0%Q`, the proof is `reflexivity`.

### 3. Parameterize over what cannot be proved, isolate it clean

For Item 2 (Landauer calibration): the physical constants are real measurements.
Parameterize the Coq proof over them using a typeclass.  The theorem then says
"given these measured constants, the chain holds."  This is not giving up — it
is stating exactly what is proved vs. what is assumed, which is the only honest
thing to do for any physical theorem.

### 4. The singular action

Every one of these three derives from the same root:

> **The μ-cost function is the unique measure of irreversible information
> processing under the NoFI constraint.**

- Item 1 (EFE): curvature IS the rate of change of μ-cost per unit area
- Item 2 (Landauer): μ-cost per bit IS thermodynamic work under Landauer's bound
- Item 3 (RTL): the hardware increments μ-cost in exact correspondence with
  `vm_apply`

If this root claim is fully grounded, all three close.  The mu-initiality theorem
(`MuInitiality.v`) already proves the uniqueness.  The three remaining items are
three faces of the same object: that the unique μ-measure is realized in
geometry (EFE), thermodynamics (Landauer), and hardware (RTL).

---

## Priority Order

| Item | Difficulty | Path | What closes it |
|------|-----------|------|----------------|
| RTL (`rtl_step_correct`) | Medium | Build `VerilogSemantics.v` + AST proof | Computational verification of the specific Verilog file |
| Off-diagonal Ricci | Hard | Build `BoundaryFourSimplex.v` + orthogonality | Exhibit one curved combinatorially-orthogonal complex |
| Landauer calibration | Philosophical | Build `PhysicalSubstrate.v` typeclass | Reduce to named physical constants, no further reduction possible |

Start with RTL — it is the most mechanical and has the clearest proof path.
The Verilog file is fixed, regular, generated; proving it by computation is
engineering, not mathematics.

Off-diagonal Ricci next — the boundary-of-4-simplex construction is a finite
calculation that Coq can verify.

Landauer last — not because it is hardest but because it terminates at an
honest metrological boundary that cannot be reduced further without proving
statistical mechanics from scratch.

---

*This roadmap is version-controlled.  Update it as intermediate theorems are
proved.  Each closed lemma brings the obligation into sharper focus.*
