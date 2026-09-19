# Actual dispatch observation proof

The earlier "diagnosis but no theorem" blocker is resolved. This does not close
all of C1/C2, B3/B4, C3 or E; STATUS.md remains the completion authority.

## Checked objects and exact scope

- `ActionObservation.observe_action_write_correct`: for every successful linear
  Kami `SemAction`, the syntax observer equals `M.find` of that key in the actual
  update map. Reads are from the pre-state. The observer is not an enabledness
  test: its skipped assertions and suffix are justified by the successful
  `SemAction` premise. It does not manufacture an execution.
- `DispatchObservation.dispatch_add_actual_execution`: an actual `SemAction`
  and one-rule `Multistep` from the defined loaded-reset state. ISA version 2,
  legacy opcode 0x13, destination 3, sources 1 and 2, charge 5; inputs 7 and 9.
  PC becomes 1, mu becomes 5, err remains false, r3 becomes 16, and every other
  data register is preserved.
- `DispatchAddFamily.dispatch_add_family_actual_execution`: the same actual
  execution contract for **all** `x y : word 32`, with r1=x, r2=y, r3 receiving
  `wplus x y`. This covers wrapped hardware addition. The remaining registers
  start at zero; all other CPU state is reset apart from the loaded imem.
- `DispatchAbstractionBridge.dispatch_add_typed_refinement`: the concrete 7+9
  instance satisfies the actual CPU name/kind schema before and after dispatch;
  the projection of PC, mu, err and all sixteen data registers agrees with
  `kami_step` at both instruction boundaries.
- `dispatch_preserves_register_schema`: every enabled dispatch preserves the
  schema of any pre-state satisfying it, independently of the ADD example.

The source defines all representations and constructs enabledness; no premise
assumes interpreter correctness or the desired result. The concrete snapshot
bridge does **not** claim equality of unobserved memory, structural fields,
CSRs, or scratch/FSM state. The operand-family theorem uses hardware word
arithmetic, not an unproved identification of 32-bit and abstract arithmetic.

## Reduction mechanism and repair

The syntax observer avoids constructing the entire proof-carrying update map.
Once the ADD register expression is isolated, `vm_compute` returns a residual
term containing `evalZeroExtendTrunc_subproof0` under dependent casts, including
at the 4-to-4 source-index conversion. Kami defines those equalities with
`abstract lia` in `vendor/kami/Kami/Semantics.v`, so they remain opaque during
computation. The charge's 8-to-32 conversion has the analogous issue.

`clear_concrete_word_casts` proves each concrete-width equality proof equal to
`eq_refl` using `Eqdep_dec.UIP_dec` and `Nat.eq_dec`. Rewriting these equalities
allows reduction to finish. The register vector equality is then proved by
functional extensionality and checking its sixteen possible indices. No vendor
source, ISA encoding, action semantics, or existing evaluator was modified.

`dispatch_observation/CastProbe.v` isolates the same failure with **no map or
CPU rule**: after `vm_compute`, reflexivity fails on a 4-bit-to-4-bit conversion;
the cast repair makes it close. `cast-probe.log` records the expected failure
and the successful theorem, which is closed under the global context.

This provides a checked working method and identifies an opaque-cast obstruction;
it does not establish that sorted maps alone caused every earlier long run.
The previous FMap-only diagnosis should not be treated as a proved root cause.

## Validation

Run from the repository root:

```
python3 artifacts/review_revision/dispatch_observation/validate.py
```

`dispatch_observation/validation.json` records the first three-module pass;
`dispatch_observation/family-validation.json` records the subsequent universal
operand-family pass and final project-file hash. Both record exact commands,
raw exit codes, elapsed times and checked source hashes. The default command
above now checks all four modules together; `--family-only` reproduces the
additional pass. Individual logs retain compiler timing,
expanded observation definitions, theorem types, and `Print Assumptions` output.
The checker uses dependency-enabled `coqchk -silent -o`, without bypass flags.
All recorded builds, integration checks, probes and both checker runs exit 0.
The bridge checker took 711.44 seconds; the family checker took 300.65 seconds.
Both report no unsafe fixpoints, type-in-type, or assumed positivity.
The native `scripts/reproduce_coq.py` defaults now include both new proof
libraries and the three new probes. Its five existing runner tests pass;
`runner-check.json` and `native-runner-tests.log` retain that result.

Compilation and integration concern these new proof modules; no extraction,
RTL generation, timing measurement, or separate-machine reproduction is claimed.

The per-theorem inherited assumptions are functional extensionality and
`Eq_rect_eq.eq_rect_eq`. The concrete cast repair uses decidable equality of
naturals and adds no axiom. Both broad dependency contexts also list Kami's existing
`CommonTactics.cheat`; it is not among the assumptions printed for the new
top-level theorems. The raw checker reports retain this distinction.

## Recovery and remaining obligations

Pre-edit source snapshot: `/tmp/thiele-before-dispatch-observer.tar.gz` (excludes
compiled products, artifacts, git internals and environment/dependency caches).
The pre-ledger-edit review artifacts are also preserved in
`/tmp/thiele-ledger-before-dispatch-observer.tar.gz`. These local recovery copies
are not an immutable release candidate or independent reproduction.

All-opcode/full-observation retirement refinement, the remaining interpreter
and recurrence contracts, and final local assurance stay open. Independent reproduction/review became
optional under Devon's 2026-09-14 contract amendment. The
current CPU source already contains the seven-fault `mc_phase` guard; the older
investigation's unpatched-source description is historical. No claim about
regenerating the emitted RTL follows from this source observation.
