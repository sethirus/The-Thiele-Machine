# The Story of the Safety Proof

## The Goal
The theorem `pc_never_exceeds_program_bounds_thiele` states that the universal Thiele machine never attempts to execute an instruction outside of the program image laid out in memory. Put plainly, every interpreter step respects the bounds of the encoded program so long as the initial configuration is sane and no contradictions arise in the specification.

## The Method
The argument proceeds by induction on `n`, the number of interpreter steps. The base case `n = 0` is immediate: with no execution, the program counter (`pc`) obviously remains within bounds. For the inductive step we assume that every run of length `n` stays within the program image and we must show that a run of length `S n` does the same. This reduces to analysing the single-step transition supplied by `kernel_step` and tracking how the interpreter preserves its invariants.

The proof decomposes the step relation into cases: fetch, decode, rule search, rule application, and halting. Each case is discharged by specialised lemmas that connect the low-level CPU semantics to the abstract Turing machine configuration.

## The Core Challenge
The difficult subcase is the “no matching rule” branch in the universal interpreter. Here the CPU performs the ten-instruction `FindRule` sweep, fails to discover a rule for the current `(state, symbol)` pair, and must fall back to a halting configuration without touching the program image. To complete the inductive step we need to argue that this sweep leaves the encoded configuration untouched so that the inductive hypothesis applies to the resulting state.

## The Key Insights
Several auxiliary results make the inductive proof succeed:

* `utm_no_rule_preserves_mem_length` shows that the ten-step `FindRule` sweep never changes the length of CPU memory. This is the heart of the symbolic-execution argument: every instruction executed in the no-rule branch either reads from memory or rewrites an existing cell without extending the tape buffer.
* `utm_no_rule_preserves_tape_len` translates the memory-level fact into the Turing tape view. Combining the memory-length preservation with the tape-window invariants proves that the extracted tape after the sweep has exactly the same length as before the sweep.
* `utm_no_rule_preserves_cpu_config` lifts the invariants to the full configuration. It states that if no rule matches, then running ten steps of the CPU leaves the `(state, tape, head)` triple unchanged. This lemma plugs directly into the bridge between the CPU semantics and the abstract machine.
* `ThieleMap` furnishes the final connection between the abstract Thiele machine and the universal interpreter. It maps every encoded configuration back to the logical specification, ensuring that the inductive hypothesis about bounded program counters transfers across the encoding/decoding pipeline.

With these ingredients the inductive step closes. The no-rule path yields a halting configuration without touching the program memory, every other path follows the executable semantics that have already been verified, and therefore the program counter always remains within the bounds of the loaded program.
