# B4 limitative theorem for the unbounded model: contract review, 2026-09-14

This is a local source and theorem-contract review. It is not an independent reviewer report. It is not Gate E closure.

## Construction choice

The B4 contract permits "a different proved construction with its prerequisites discharged" in place of a fixed-point argument. This closure uses that clause. The construction is Rice's theorem by many-one reduction from the complement of pinned MM2 halting. No recursion-theorem field, representability hypothesis or interpreter-correctness premise is assumed.

A fixed-point argument was not used for two checked reasons. First, `Substrate.run` is a total function returning the converged state. `total_run_obstruction` proves that any such function for this model decides termination on input 0, so it already yields the upstream limitative conclusion; the record cannot be instantiated without that consequence. Second, an internal recursion theorem needs a universal program written inside the guest fragment itself. The self-interpreter `U` uses sixteen host registers and interprets a four-register guest, so `U` is not a guest program. No internal universal guest program is claimed. The conditional VM substrate diagonal in `VMSubstrateInstance.v` stays conditional and is not cited as discharged.

## Model and observation

Programs are well-formed guest programs `list GInstr` from B3. Execution is `g_run`, which `g_run_is_run_vm_u` proves equal to `run_vm_u` on `g_program p`. `g_beh_host_iff` proves the observation equals what the fixed host `U` produces from the encoded program and input.

`g_beh p x g mu` states that the guest run from input x (register 0; other registers, pc and ledger 0) terminates with registers g and guest ledger mu. `g_equiv` is equality of this relation on every input. It observes returned registers and the guest ledger. It does not observe the final pc or the step count.

## Proved contracts

| Obligation | Result |
| --- | --- |
| Effective transformer | `rice_prog pm w`: save the input in register 2, load the MM2 inputs, run the compiled MM2 guest relocated to address 4, restore the input and zero the other registers, run `w` relocated after it. Relocation (`reloc`, `reloc_run`) sends in-range targets by the offset and every exit to the block end. `rice_prog_wf` proves the output is in the model. |
| Behaviour on halting instances | `rice_prog_halting`: if the MM2 instance halts, `rice_prog pm w` is `g_equiv` to `w`. The proof takes the least termination index of the compiled guest, uses `qprog_keeps` (register 2 and the ledger are untouched), and `tail_beh`. |
| Behaviour on non-halting instances | `rice_prog_nonhalting`: any terminating behaviour of `rice_prog pm w` implies the MM2 instance halts. The proof uses bounded search, so it is constructive. With `g_bottom_beh`, a non-halting instance makes `rice_prog pm w` equivalent to the never-terminating program. |
| Limitative result | `self_rice`: for every predicate respecting `g_equiv` on well-formed programs, true of some well-formed program and false of `g_bottom`, the predicate restricted to well-formed programs is undecidable. `self_rice_dual` covers the other orientation. Both use the upstream synthetic `undecidable` unchanged, through `MM2_HALTING_compl_undec`, which composes the library's own reductions from `PCPb_compl_undec`. |
| Representable deciders | `g_decides D enc Pr`: guest program `D` terminates on the encoding of every well-formed program with register 0 equal to 1 exactly when `Pr` holds. `g_decides_decidable` turns any such decider into a Boolean decider using constructive ground description on naturals. `self_rice_representable` concludes that such a `D` makes the complement of SBTM halting enumerable. |
| Named predicates | `g_halts_on_zero_undecidable` (termination on input 0) and `g_returns_zero_undecidable` (terminates on 0 and returns 0 in register 0 whenever it terminates). Both witnesses and both extensionality arguments are proved. |
| Bounded versus unbounded | The bounded decidability results are unchanged. These results concern unbounded termination only. |

## Evidence

`rice/validate.py` runs the three module builds, Makefile integration, the contract probe `rice/Contracts.v` and dependency-enabled `coqchk`, each under 900 s and 1.8 GB. All exit 0; the slowest check is `coqchk` at 75 s and 439 MB. All 15 probed results are closed under the global context. `coqchk` reports no axioms, no unsafe (co)fixpoints and no assumed positivity. `Makefile.local` lists the additional vendor objects in its grouped undecidability target, so a clean source-only build has a rule for each import.
