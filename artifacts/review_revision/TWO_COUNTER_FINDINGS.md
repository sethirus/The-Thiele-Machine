# Two-counter layout investigation

Scope: Gate B2c sufficient independently usable storage, unchanged ISA. This is a bounded candidate investigation, not a universality or nonuniversality theorem.

## Checked candidate

`coq/kernel/foundation/VMTwoCounterAccess.v` defines buckets 00=(u+1,v+1), 01=(a+1,b+1), 10=(1,0), 11=(1,1). The differences u-v and a-b can each be incremented/decremented through actual `record_trial` calls without changing the other buckets.

The source checker is `coq/kernel/foundation/VMStep.v`, lines 678-744. Its exact integer checks prove:

- `first_test`: base checker accepts exactly u=v, independently of a,b.
- `second_test_when_first_zero`: if u=v, the sum-of-squares checker accepts exactly a=b.
- `combined_test`: actual 1AB checker accepts exactly u=v AND a=b.
- `all_extended_guards_reject`: if u<>v, every extended checker rejects, for arbitrary a,b and arbitrary supplied gamma bucket parameters. All four extended definitions explicitly conjoin the base checker (lines 741, 792, 1064, 1597).
- `second_branch_when_first_zero`: the actual unchanged two-step `run_vm` execution of CHSH_LASSERT_1AB followed by the success/trap trampoline jumps to the selected target according to a=b, provided u=v. It returns the same explicit full state transformer as the existing counter branch theorem, including one charge unit, persistent error, and CSR error effects. It is a real VM execution theorem, not an external decoder.

The branch proof relies on the actual `SimulationProof.vm_apply` 1AB clause (line 591 onward). No source or instruction changes are required.

`two_counter_update_correct` additionally proves all four update choices as actual one-step `run_vm` executions, with full-state equality: PC advances by one, charge is zero, and ordinary state and latched error are preserved. All 11 probed results are `Closed under the global context`. `two_counter_report.txt` records their types and assumptions. No `Admitted` or new axioms occur in this source.

## Concrete limitation

The layout exposes an independently updated second signed counter, but not an independently tested second counter. While first is nonzero, choosing any of the existing CHSH guard variants cannot distinguish second-zero from second-nonzero. This remains true even for arbitrary instruction-supplied gamma parameters, because each variant first requires the base guard.

It is possible to drain the first nonnegative difference to zero and then test the second. That changes the represented first value. No internally executable save/restore procedure preserving both logical counters has been established. The already proved one-counter drain is therefore insufficient to turn this into a general two-counter-machine simulation.

This statement is deliberately local: it does not rule out a different layout, a protocol that changes the pinned bucket, graph-based storage, or use of other opcodes. It also does not establish that every state encoding is finite. This candidate should not close Gate B2c.

## Next precise target

Construct an actual instruction-list macro which tests a=b for arbitrary u,v and restores both logical counters (with explicit frame, error, charge and termination effects), or find a different encoding that admits both tests. Any multiple branch sites must also handle the single fixed trap address through an internally executed dispatcher. Merely defining a Coq projection that reads both differences does not supply that macro.

Validation completed: full Coq build, the repository contract probe, and dependency-checking `coqchk -silent -o` passed. Raw reports are `normalization-two-counter-build.log`, `two_counter_report.txt`, and `normalization-two-counter-coqchk.log`. The exact combined checker invocation is in `normalization_two_counter_coqchk_command.json`; no bypass flags were used. The earlier scratch-library checks are superseded by these checks of the integrated repository module.
