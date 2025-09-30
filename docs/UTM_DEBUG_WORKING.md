## High-level project purpose
- Produce a completely machine-checked, admit-free Coq formalization of
  the "Thiele Machine" development: the formal model (Constitution), a
  Coq proof of the Subsumption/Separation theorems, and a reproducible
  auditor that compiles the proofs and verifies empirical receipts.
- Make the entire pipeline auditable and reproducible: a one-command
  auditor that builds, runs the sighted Thiele program, and verifies
  receipts for the run.

## Why the encoder and proof-splitting work
- Problem: the original universal machine used a single-word numeric
  packing for instructions (big multiprecision encodings). That caused
  large, arithmetic-heavy proof obligations (division/mod lemmas) which
  blow up peak memory during `coqc` and make the files fragile to local
  resource limits.
- Goal: reduce per-proof peak memory and make proofs mechanizable
  locally (so the CI/auditor can run without exotic hardware).
- Strategy:
  - Replace single-word packing with an explicit multi-word instruction
    layout (opcode + separate operand words). This eliminates the heavy
    division/mod arithmetic in decode lemmas.
  - Replace monolithic admits and single giant simulation lemmas with a
    "Forge Protocol" style: many tiny, focused lemmas that each have
    low peak memory and are easy to check.
  - Keep the program image flattened (a list of nat words) so the
    interpreter proofs pattern-match against nth/skips instead of
    heavy number theory.

## What this change achieves (intended deliverables)
- Smaller, local proof obligations for the decoder and simulation steps
  (encode/decode roundtrip split into per-instruction lemmas).
- A path from the big, admitted simulates_one_step lemma into a chain
  of micro-lemmas that can be checked incrementally and are robust
  against the memory limits of typical CI runners.
- A clear fallback: if the remaining microproofs still exceed local
  runtime limits, the repo contains scripts to run the final build on
  a larger VM or CI runner (32–64 GB recommended).

## Current Status (Updated September 30, 2025)
- **Coq Installation Confirmed**: Coq 8.20 is installed at "C:\Coq-Platform~8.20~2025.01\bin\coqc.exe". Compilation tested with direct coqc commands.
- **Pattern Fixes Applied**: Added IS_* predicate definitions (IS_FetchSymbol, IS_FindRule_Start, IS_ApplyRule_Start, IS_Reset) as equality propositions for PC values. Standardized all destruct patterns for TMConfig tuples from `[[q tape] head]` to `(q, tape, head)` to match the type definition `nat * list nat * nat`. Updated unfold statements to remove InterpreterState references.
- **Compilation Progress**: Previous unification errors resolved. Latest compilation attempt failed at line 218 in `inv_strong_implies_min` with "Expects a conjunctive pattern made of 2 patterns" - likely incorrect destruct for conjunctions in `destruct Hinv as (HQ & HHEAD & HPC & _).`.
- **Remaining Work**: Fix the conjunctive pattern error at line 218. Two `admit` statements in `apply_implies_find_rule_some` lemma need completion for mechanical proofs about rule table memory layout and register loading.

## Minimal, recommended next steps (what to do first)
1. **Fix Conjunctive Pattern Error**: Examine line 218 in `inv_strong_implies_min` and correct the destruct pattern for conjunctions (use nested `[ ]` for conjunctions, not `( )`).
2. Re-run compilation with `coqc -R thieleuniversal/coqproofs ThieleUniversal thieleuniversal/coqproofs/ThieleUniversal.v` to verify the fix.
3. Complete the two `admit` statements in `apply_implies_find_rule_some` incrementally:
   - First admit: Prove existence of rule index `i` where memory cells match loaded register values.
   - Second admit: Use encoding lemmas to rewrite memory accesses to rule components and prove `find_rule` returns the correct triple.
4. If compilation succeeds, run full build with `make -C coq` or equivalent for all files.

## Completion Status
- Main compilation blockers (unification and pattern errors) are being resolved incrementally.
- Coq installation functional and path confirmed.
- Destruct patterns standardized across all affected lemmas.
- IS_* predicates defined for cleaner proofs.
- Remaining issues are well-scoped: one pattern fix and two admits.
- Documentation updated to reflect current state.

## What this change achieves (intended deliverables)
- Smaller, local proof obligations for the decoder and simulation steps
  (encode/decode roundtrip split into per-instruction lemmas).
- A path from the big, admitted simulates_one_step lemma into a chain
  of micro-lemmas that can be checked incrementally and are robust
  against the memory limits of typical CI runners.
- A clear fallback: if the remaining microproofs still exceed local
  runtime limits, the repo contains scripts to run the final build on
  a larger VM or CI runner (32–64 GB recommended).

## Why the tape-window / `inv_init` debug matters now
- The immediate compile break was a syntactic term-shape mismatch when applying a helper lemma that reasons about `pad_to`/`skipn`/`firstn` shapes in the initial state construction (`inv_init`). That mismatch was purely about *term shape* (syntactic form), not a fundamental logical gap.
- **Resolution**: Fixed by unfolding `setup_state` and proving the tape window directly in `inv_init`, ensuring term shapes match without relying on external lemma application.

## Minimal, recommended next steps (what to do first)
1. **Install Coq 8.20**: To test the compilation fix and proceed with development.
2. Re-run the targeted compile for only `ThieleUniversal.v` to verify the `inv_init` fix.
3. Complete the `admit` statements in `apply_implies_find_rule_some` incrementally. The proofs involve showing that the interpreter's register values correspond to an existing rule in the table, using the invariant and memory preservation properties.
4. If any step still needs more RAM/time, run the full build using the provided `scripts/build_on_big_vm.sh` on a 32–64 GB runner.

## Longer-term considerations
- Keep proofs small: whenever a new heavy lemma appears, try to split
  it into N small lemmas that can be checked independently.
- Avoid introducing new numeric packing that re-introduces div/mod
  lemmas. If an optimization requires packing, prefer packing into
  separate words and proving small, local lemmas about the fields.
- Keep the one-click auditor script up to date so the final full build
  is reproducible on CI/VM.

## Quick references
- Files to inspect first:
  - `coq/thieleuniversal/coqproofs/UTM_Encode.v` — encoder + per-instr
    decode lemmas (should be light-weight).
  - `coq/thieleuniversal/coqproofs/UTM_Program.v` — program constants
    (RULES_START_ADDR, TAPE_START_ADDR) and the flattened program
    listing.
  - `coq/thieleuniversal/coqproofs/ThieleUniversal.v` — main interpreter
    and invariants (where `inv_init` currently fails).
- Command to reproduce the current failing build (single-file):

  make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'

If you want, I’ll implement the exact-shape bridging lemma now (it’s a
small, safe edit) and then rerun the local targeted compile. Say
“add bridging lemma” to proceed.

Status and working notes — Thiele Universal / encoder

Purpose


Short summary of what we changed and why
- Problem motivating the edits:
  - The original single-word instruction encoding produced heavy
    div/modarith proof obligations and caused high memory/CPU pressure
    during compilation. Replacing it with a multi-word encoding reduces
    arithmetic in proofs.
- Key edits already made (what to look at):
  - coq/thieleuniversal/coqproofs/UTM_Encode.v
    - New multi-word encoder/decoder: each instruction is 4 words
      (opcode, arg1, arg2, arg3). This removes division/mod operations
      from the decoder and the heavy proofs.
    - Small per-instruction round-trip lemmas (decode_encode_*).
  - coq/thieleuniversal/coqproofs/UTM_Program.v
    - Restored the concrete program listing and introduced
      RULES_START_ADDR and TAPE_START_ADDR here (module UTM_Program).
  - coq/thieleuniversal/coqproofs/ThieleUniversal.v
    - Switched the interpreter to delegate decoding to
      `UTM_Encode.decode_instr_from_mem` (avoids re-proving the
      division-heavy decode lemmas in this file).
    - Set PROGRAM_STEPS := 4 * length program_instrs.
    - Several small local proof edits and a sequence of micro-refactors
      to try to keep proof obligations tractable.

Current failing point (what blocks a full compile)
- **Resolved**: The build previously failed in `ThieleUniversal.v` at the `inv_init` / tape-window lemma due to a term shape mismatch. This has been fixed by unfolding `setup_state` and proving the tape window directly.
- If compilation proceeds, any remaining issues will be in other parts of the proof.

What I tried (short bullets)
- Added IS_* predicate definitions: IS_FetchSymbol pc := pc = 0, IS_FindRule_Start pc := pc = 3, IS_ApplyRule_Start pc := pc = 29, IS_Reset pc := pc = 48.
- Standardized destruct patterns for TMConfig from `[[q tape] head]` to `(q, tape, head)` in all affected lemmas to match type `nat * list nat * nat`.
- Updated unfold statements: changed `unfold IS_FindRule_Start, InterpreterState` to `unfold IS_FindRule_Start`; changed `unfold IS_Reset, InterpreterState` to `unfold IS_Reset`.
- Ran iterative compilations with `coqc -R thieleuniversal/coqproofs ThieleUniversal thieleuniversal/coqproofs/ThieleUniversal.v` to identify and fix pattern errors.
- **Latest Issue**: Compilation fails at line 218 with "Expects a conjunctive pattern made of 2 patterns" in `inv_strong_implies_min`, likely due to incorrect destruct for conjunctions (should use nested `[ ]` not `( )`).

Repro (full local command used repeatedly)
- From the repository root, run the direct Coq compilation:

  cd coq; C:\Coq-Platform~8.20~2025.01\bin\coqc.exe -R thieleuniversal/coqproofs ThieleUniversal thieleuniversal/coqproofs/ThieleUniversal.v

- This compiles ThieleUniversal.v directly using the confirmed Coq installation path.

How I debugged the goal (manual steps that reproduced the goal print)
- Temporarily insert in the proof a failing tactic that prints the
  current goal (this is quick and non-invasive):

  let G := match goal with |- ?G => G end in fail 1 "DEBUG_INV_INIT_GOAL:" G.

  Compilation will fail but the build error output includes the goal
  term (see "Current failing point" above). Remove this printing
  tactic once you capture the goal text.

Suggested minimal fixes to try next (ordered by low risk)
1. Fix the conjunctive pattern error at line 218 in `inv_strong_implies_min` by correcting the destruct pattern for conjunctions (use nested `[ ]` instead of `( )`).
2. Re-run the compilation command above to verify the fix.
3. Complete the two `admit` statements in `apply_implies_find_rule_some` incrementally.

One-line to revert the most-recent local edits (if you want to go
back):
- git checkout -- coq/thieleuniversal/coqproofs/ThieleUniversal.v
- git checkout -- coq/thieleuniversal/coqproofs/UTM_Program.v
- git checkout -- coq/thieleuniversal/coqproofs/UTM_Encode.v

Files changed in this session (for quick reference)
- coq/thieleuniversal/coqproofs/ThieleUniversal.v — Added IS_* definitions, standardized destruct patterns to `(q, tape, head)`, updated unfold statements, iterative fixes for conjunctive pattern errors.

Next immediate action I recommend (pick one)
- Fix the conjunctive pattern error at line 218 in `inv_strong_implies_min`.
- Complete the `admit` statements in `apply_implies_find_rule_some` by implementing the mechanical proofs for rule table indexing and register loading.
- If you want, I can help implement the proofs for the admits or debug further issues.

