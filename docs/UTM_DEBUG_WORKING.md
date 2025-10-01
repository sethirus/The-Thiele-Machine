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
- **Coq Installation Confirmed**: Coq 8.18.0 installed via `apt-get install coq`; `/usr/bin/coqc -v` confirms the toolchain inside this container.
- **Pattern Fixes Applied**: Added IS_* predicate definitions (IS_FetchSymbol, IS_FindRule_Start, IS_ApplyRule_Start, IS_Reset) as equality propositions for PC values. Standardized all destruct patterns for TMConfig tuples to the right-associated form `((q, tape), head)` matching the type definition `nat * (list nat * nat)`. Updated unfold statements to remove InterpreterState references.
- **Structured `inv_init` Proof Landed**: Replaced the monolithic block with a `repeat split` proof that reuses `tape_window_ok_setup_state`, `firstn_app_le`, and `skipn_app_le`, preventing the previous term-expansion blow-up.
- **Remaining Work**: With `inv_init` stable, the next blockers are the two admits in `apply_implies_find_rule_some`; once they are discharged we can run the single-file and full builds.

## Minimal, recommended next steps (what to do first)
1. Replace the monolithic `inv_init` block with the structured proof that uses `tape_window_ok_setup_state`, `firstn_app_le`, and `skipn_app_le`.
2. Re-run `make thieleuniversal/coqproofs/ThieleUniversal.vo` to confirm `inv_init` closes without manual rewrites.
3. Complete the two `admit` statements in `apply_implies_find_rule_some` incrementally:
   - First admit: Prove existence of rule index `i` where memory cells match loaded register values.
   - Second admit: Use encoding lemmas to rewrite memory accesses to rule components and prove `find_rule` returns the correct triple.
4. After the admits are discharged, run the single-file build and then the full `make -C coq` pipeline as a smoke test.

### Active iteration plan (living checklist)
| Status | Task | Notes / Links |
| ------ | ---- | -------------- |
| ✅ | Refactor `inv` to use `tape_window_ok` and add helper lemmas. | Introduced `firstn_app_le`, `skipn_app_le`, and delegated the tape goal to `tape_window_ok` for cleaner subgoals. |
| ✅ | Expose `coqc` in the container image. | Installed distribution package `coq` 8.18.0 (OCaml 4.14.1) so local compilations can run directly. |
| ✅ | Standardize `TMConfig` destructuring patterns. | Replaced all occurrences of `(q, tape, head)` with the right-associated `((q, tape), head)` form in `ThieleUniversal.v`. |
| ✅ | Re-run targeted compile: `make thieleuniversal/coqproofs/ThieleUniversal.vo`. | Latest run (with Coq installed) now reaches the simulation section; build stops in `transition_Fetch_to_FindRule` after relocating `run_n_mem_preserved_if_no_store` below the `run_n` helpers. |
| ✅ | Re-implement `inv_init` with the structured `repeat split` proof. | Proof now closes via `tape_window_ok_setup_state`, `firstn_app_le`, and `skipn_app_le`; the targeted compile proceeds past this point. |
| ✅ | Update simulation lemmas to use `decode_instr`'s state argument. | Rewrote `run1_pc_succ` and the fetch-phase simulation to decode from whole CPU states, introducing `run1_run_n` to keep `run_n` proofs intact. Targeted build now proceeds until the `FindRule` simulation branch needs memory-equality facts. |
| ✅ | Regenerate Coq build scripts for the Linux toolchain. | Replaced the Windows `coq_makefile.exe` path in `coq/Makefile` and `Makefile.conf` with the container’s `coq_makefile` so local builds invoke the installed toolchain. |
| ⬜ | Discharge Admit #1 (`apply_implies_find_rule_some`): show existence of rule index satisfying invariant memory equality. | Supporting work: added `program_instrs_before_apply_not_store` and `decode_instr_before_apply_not_store`, turning the program-prefix equality into a “no `StoreIndirect` before PC 29” fact. Introduced `run_n_mem_preserved_until_apply` to reuse `read_mem_rule_component` once we know every prefix PC stays `<29`. Added `program_instrs_before_apply_jump_target_lt` and its state-level lift `decode_instr_before_apply_jump_target_lt` so pre-apply jumps cannot leave the prefix. **Recent progress:** proved `program_instrs_before_apply_pc_unchanged`, `decode_instr_before_apply_pc_unchanged`, the single-step bound `run1_pc_before_apply_le`, and the companion lemmas `run1_program_prefix_before_apply` and `run_n_program_prefix_before_apply`, ensuring each pre-apply step keeps both the PC ≤ 29 and, under the guarded run, the program prefix intact. Next micro-step is to derive the corresponding multi-step PC guard so `run_n_mem_preserved_until_apply` can be instantiated in the witness construction. Targeted `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'` still fails at the expected `decode_instr_from_mem_ext` frontier. |
| ⬜ | Discharge Admit #2 (`apply_implies_find_rule_some`): prove `find_rule` returns the retrieved triple. | Use the encoder's `decode_encode_find_rule` style lemmas; rewrite through `UTM_Encode.decode_instr_from_mem` and apply the invariant's structural facts about program layout. |
| ⬜ | End-to-end check: `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`. | Ensure the single-file build passes before scaling to the full suite. |
| ⬜ | Full audit pipeline smoke test (`scripts/build_on_big_vm.sh` if needed). | Only necessary once the single file builds locally and CI resources are known. |

### Per-admit micro-proof sketch (use while iterating)
- **Admit #1 context reminder**
  - Goal form: `exists i, load_rule_from_mem mem = Some (rule_at i)` or similar.
  - Use `inv_strong` invariants: they typically include a `rules_are_loaded` fact ensuring each rule's payload is stored contiguously. Combine with previously proven decode lemmas to isolate each memory cell.
  - Tactics: `destruct` the invariant witness, `eexists`, then rewrite via helper lemmas (`nth_error_split`, `firstn_skipn`) to align the addresses.

- **Admit #2 outline**
  - After obtaining the witness, rewrite the interpreter call to `find_rule` using `UTM_Encode.find_rule_correct` (or analogous lemma in `UTM_Encode.v`).
  - Close remaining subgoals with `simpl`/`rewrite` sequences and existing arithmetic lemmas about `RULES_START_ADDR` offsets.
  - Ensure all hypotheses about tape/head remain unchanged; the `find_rule` proof should not require modifying them.

Record quick notes from each iteration directly under this section so future passes start with up-to-date context.

- **2025-09-30 (current container)**: Verified `coqc` 8.18.0 is installed via `apt-get`; ready to re-run targeted builds.
- **2025-09-30 (container refresh)**: Reinstalled Coq 8.18.0 with `sudo apt-get install coq`; confirmed availability via `coqc -v`.
- **2025-09-30 (current container – reinstall)**: Reinstalled Coq 8.18.0 in the refreshed shell with `apt-get install coq` and re-checked `coqc -v` to confirm the toolchain is available for subsequent proof iterations.
- **2025-09-30 (current container – fetch phase)**: Updated the fetch-phase simulation to call `decode_instr` on full states; targeted compile now reaches the `transition_FindRule_to_ApplyRule` branch where rule-table equalities are required.
- **2025-09-30 (current container – toolchain check)**: Reinstalled Coq 8.18.0 via `apt-get install coq` in this shell and confirmed availability with `coqc -v` so upcoming proof work can run.
- **2025-09-30 (current container – toolchain reinstall)**: After container reset, ran `apt-get update` and `apt-get install -y coq`; verified availability with `coqc -v` before proceeding to the admit proofs.
- **2025-09-30 (current container – toolchain refresh)**: Reinstalled Coq 8.18.0 via `sudo apt-get install -y coq` in this shell and confirmed with `coqc -v` so future steps can run proofs locally.
- **2025-09-30 (current container – admit #1 prep)**: Reinstalled Coq 8.18.0, reran `make thieleuniversal/coqproofs/ThieleUniversal.vo`, and confirmed the build now stops in `transition_Fetch_to_FindRule` before reaching the `apply_implies_find_rule_some` admits. Next action is to prove the "no store before PC 29" memory-preservation lemma so that the rule-table witness can be extracted for Admit #1.
- **2025-09-30 (current container – fetch prefix investigation)**: Installed Coq 8.18.0, reran the targeted build (still stops with `program` opaque), and attempted to characterize the first fetch-phase instructions without unfolding `program`. Direct evaluation via `vm_compute` shows that `decode_instr_from_mem program 1` currently yields `Jnz 1000 0`, so we need to reconcile the PC-to-address scaling before introducing the intended prefix lemmas for `transition_Fetch_to_FindRule`.
- **2025-09-30 (current container – memory preservation helper)**: Added `step_mem_preserved_if_no_store` in `ThieleUniversal.v` to capture that a single interpreter step without `StoreIndirect` leaves memory unchanged; the follow-up task is to lift this across `run_n` to propagate rule-table equality into `apply_implies_find_rule_some`.
- **2025-09-30 (current container – run_n memory preservation)**: Proved `run_n_mem_preserved_if_no_store` so multi-step prefixes without stores keep memory fixed. Targeted `make thieleuniversal/coqproofs/ThieleUniversal.vo` still fails early because the generated Makefile calls the Windows `coq_makefile.exe`; need to regenerate it to use `/usr/bin/coq_makefile` before the next compile attempt.
- **2025-09-30 (current container – lemma ordering fix)**: Reinstalled Coq 8.18.0, moved `run_n_mem_preserved_if_no_store` after the `run_n` helper lemmas, and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`; build now reaches `transition_Fetch_to_FindRule` (as expected) while Admit #1 remains open.
- **2025-09-30 (current container – toolchain verified again)**: Ran `apt-get update` followed by `apt-get install -y coq` in this shell and confirmed availability with `coqc -v` prior to resuming Admit #1 work.
- **2025-09-30 (current container – compile check)**: Reinstalled Coq 8.18.0 (`apt-get install coq`) and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`; the build fails in `transition_Fetch_to_FindRule` because the proof still has the `run_n st (S (S (S (read_reg REG_PC st))))` vs `run_n st 3` goal, so Admit #1 remains blocked until that mismatch is addressed.
- **2025-09-30 (current container – fetch decoding)**: Installed Coq 8.18.0, reran the targeted build, and patched `transition_Fetch_to_FindRule` to instantiate the post-fetch state with an explicit step count so the `run_n st (S (S (S (read_reg REG_PC st))))` vs `run_n st 3` mismatch disappears. The build now fails later in the same lemma because `program` is opaque when specialising `Hmem_prog`; need small prefix lemmas instead of raw `unfold program`.
- **2025-09-30 (current container – toolchain + rebuild)**: Reinstalled Coq 8.18.0 (`apt-get install -y coq`), confirmed `coqc -v`, and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`; compilation still stops with "program is opaque" in `transition_Fetch_to_FindRule`, confirming the next action is to expose the required program prefix via helper lemmas.
- **2025-09-30 (current container – toolchain refresh + compile check)**: Ran `apt-get update` followed by `apt-get install -y coq`, verified availability with `coqc -v`, and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`; build again halts with "program is opaque" at line 526 of `transition_Fetch_to_FindRule`. Next micro-step: introduce prefix lemmas that expose the fetch-phase program words without unfolding `program`.
- **2025-09-30 (current container – fetch prefix still opaque)**: Reinstalled Coq 8.18.0, confirmed with `coqc -v`, and reran the single-file build; compilation still fails with "program is opaque" inside `transition_Fetch_to_FindRule`. Enumerated the `program_instrs` indices to verify that PC 1 should decode to `AddReg REG_ADDR REG_TEMP1 REG_HEAD`, so we need a helper lemma exposing `nth` of the flattened `program` to align the decoder with the program counter.
- **2025-09-30 (current container – program prefix lemmas)**: Added `program_word_0`–`program_word_5` and `program_length_gt_5` in `ThieleUniversal.v` so `transition_Fetch_to_FindRule` can use the concrete fetch prefix without unfolding the opaque `program`. Compile still fails with the same "program is opaque" error until the proof is refactored to use these lemmas.
- **2025-09-30 (current container – fetch prefix rewrite attempt)**: Installed Coq 8.18.0, rewrote the fetch-phase proof to reuse `program_word_*` instead of `unfold program`, and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`; build still stops in `transition_Fetch_to_FindRule` with a `rewrite` mismatch on `nth 1 (mem st) 0` (chunk `6a4cfc`). Next pass should encapsulate the decoded prefix in a dedicated lemma so the goal exposes the expected `nth` pattern.
- **2025-09-30 (current container – fetch PC scaling)**: Introduced the `4 * PC` address calculation in `decode_instr`, added `program_word_6`–`program_word_11` plus `program_length_gt_11`, and rewired `transition_Fetch_to_FindRule` to use the expanded lemmas. The targeted build now reaches `transition_FindRule_to_ApplyRule`, which fails because the remaining simulation proof still assumes the old (word-indexed) program counter (chunk `fbf73d`).
- **2025-09-30 (current container – find-rule scaling follow-up)**: Reinstalled Coq 8.18.0, updated the fetch-phase proof to use the scaled program counter, and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`; the build now stops in `transition_FindRule_to_ApplyRule`, which still decodes at `pc` instead of `4 * pc` (chunk `184b0f`). Next pass should propagate the scaled-address rewrites through that lemma.
- **2025-09-30 (current container – move register encoding)**: Updated `transition_FindRule_to_ApplyRule` to conclude with `read_reg REG_MOVE st' = encode_z move`, resolving the nat/Z type clash. The targeted `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'` run now stops earlier in `transition_Fetch_to_FindRule` on the pending `nth 1 (mem st) 0` rewrite (`31c638`).
- **2025-09-30 (current container – find-rule scaling attempt)**: Installed Coq 8.18.0 in this shell and reran the targeted build. The compilation still stops in `transition_FindRule_to_ApplyRule`; attempting to reuse the old nested tuple destructs now fails because the final component is the 3-branch `Z` move encoding. Next pass should restructure the symbolic-execution proof to fetch instructions via the scaled prefix lemmas instead of `cbv`-ing through the tuple destruct chain.
- **2025-09-30 (current container – find-rule refactor WIP)**: Reinstalled Coq 8.18.0, reran the targeted build, and updated `transition_FindRule_to_ApplyRule` to destruct TM rules using the right-associated tuple pattern while case-splitting on `m_next : Z`. The compile still fails with `Expects a disjunctive pattern with 3 branches` at the same lemma, so the symbolic execution block still needs to be rewritten around the scaled address decoder.
- **2025-09-30 (current container – find-rule tuple symmetry)**: After reinstalling Coq 8.18.0, rewrote `transition_FindRule_to_ApplyRule` with the right-associated tuple destruct and symmetric rule-table equality. The branch now advances past the prior pattern error but fails with `Cannot find witness` when instantiating the `0 < length (tm_rules tm)` hypothesis (line 777), indicating the matching-case simulation still needs to reconcile the tuple shape with the rule-table helper lemmas.
- **2025-09-30 (current container – find-rule witness WIP)**: Installed Coq 8.18.0 in the fresh shell and reran `make thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`. The build still stops at line 777 with “Cannot find witness”; next step is to refactor the matching-rule branch to construct the run witness using `read_mem_rule_component` and the scaled PC helper lemmas instead of the legacy `cbv` script.
- **2025-09-30 (current container – witness preservation plan)**: Reinstalled Coq 8.18.0, reran the targeted single-file build, and confirmed the remaining obstacle is constructing the rule-table witness at line 777. Next step is to prove a preservation lemma that no `StoreIndirect` executes before PC 29, allowing `read_mem_rule_component` to be applied to the apply-start state.
- **2025-09-30 (current container – store-free prefix lemma)**: Proved `decode_instr_before_apply_not_store`, turning the invariant’s program-prefix equality into a direct "no `StoreIndirect`" fact for every state with PC < 29. This sets up `run_n_mem_preserved_if_no_store` to keep the rule table intact up to the apply-start state.
- **2025-09-30 (current container – admit #1 memory preservation)**: Reinstalled Coq 8.18.0 via `apt-get`, confirmed availability with `coqc -v`, and sketched the forthcoming lemma that the run up to `IS_ApplyRule_Start` executes only PC < 29 instructions. This will feed `run_n_mem_preserved_if_no_store`, allowing us to carry the original `read_mem_rule_component` facts forward in the witness proof.
- **2025-09-30 (current container – apply-start memory lemma)**: Installed Coq 8.18.0, introduced `run_n_mem_preserved_until_apply` to combine the PC<29 guard with the program-prefix equality, and reran `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`. Build still fails earlier (`decode_instr_from_mem_ext` term-shape mismatch); next step is to use the new lemma inside `apply_implies_find_rule_some` to complete the witness.
- **2025-09-30 (current container – apply-start PC guard TODO)**: Tried to instantiate `run_n_mem_preserved_until_apply` inside `apply_implies_find_rule_some`, but the proof currently lacks a lemma showing that every prefix state before hitting `PC = 29` stays below the apply-phase threshold. Need to formalize the “first time the PC reaches 29” guard so the preservation lemma can transfer the rule-table equalities to the apply-start state.
- **2025-09-30 (current container – PC guard attempt)**: Spent this pass trying to encode the “PC < 29 for every prefix” lemma, but `decode_instr_from_mem_ext` doesn’t mesh cleanly with the scaled `4 * pc` decoder yet. Reverted the partial patch; next pass still needs a PC-bound lemma that cooperates with the scaled addressing.
- **2025-09-30 (current container – PC guard attempt #2)**: Installed Coq 8.18.0 in the refreshed shell and explored lifting `run1_pc_before_apply_le` across multi-step executions. Found that proving a first-hit-of-29 guard needs a simultaneous argument about memory preservation (to keep the program prefix available for each step), leaving the lemma unfinished. Next iteration should set up a combined induction that tracks both PC bounds and the prefix equality before applying `run_n_mem_preserved_until_apply`.
- **2025-09-30 (current container – branch-target helper)**: Added `program_instrs_before_apply_jump_target_lt` to record that every `Jz`/`Jnz` instruction before PC 29 jumps to a target `< 29`, providing the final data point needed to restate the PC-prefix guard with the scaled decoder.
- **2025-09-30 (current container – branch-target state lift)**: Installed Coq 8.18.0 via `apt-get install -y coq`, confirmed with `coqc -v`, and proved `decode_instr_before_apply_jump_target_lt` to transport the `< 29` jump-target fact to decoded states. Re-running `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'` still stops at the expected `decode_instr_from_mem_ext` mismatch (chunk `480a6a`).
- **2025-09-30 (current container – build script refresh)**: Installed Coq 8.18.0 and rewired `coq/Makefile` plus `Makefile.conf` to call the local `coq_makefile`, so future `make` runs no longer depend on the Windows toolchain path.
- **2025-09-30 (current container – PC step bound)**: Reinstalled Coq 8.18.0 (`coqc -v` confirmed) and proved the helper lemmas `program_instrs_before_apply_pc_unchanged`, `decode_instr_before_apply_pc_unchanged`, and `run1_pc_before_apply_le`, establishing that any pre-apply step keeps the next PC at most 29. Targeted `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'` still stops at the known `decode_instr_from_mem_ext` guard (chunk `de45aa`).
- **2025-09-30 (current container – single-step prefix preservation)**: Installed Coq 8.18.0 (`coqc -v` confirmed) and proved `run1_program_prefix_before_apply`, showing every pre-apply step leaves the flattened program prefix unchanged. The next pass will fold this memory fact together with `run1_pc_before_apply_le` to derive the sought first-hit-of-29 guard. Targeted `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'` still stops at the known `decode_instr_from_mem_ext` guard (chunk `263df4`).
- **2025-09-30 (current container – prefix guard lift)**: Reinstalled Coq 8.18.0 (`coqc -v` confirmed), proved `run_n_program_prefix_before_apply` so the program prefix equality propagates across any guarded multi-step run, and reran `make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'`, which still stops at the `decode_instr_from_mem_ext` mismatch (chunk `cfe23e`). Next step is to establish the matching multi-step PC bound to pair with the new prefix lemma.

## Completion Status
- Main compilation blockers (unification and pattern errors) are being resolved incrementally.
- Coq installation functional and path confirmed.
- Destruct patterns standardized across all affected lemmas.
- IS_* predicates defined for cleaner proofs.
- Remaining issues are well-scoped: local `coqc` install plus two admits in `apply_implies_find_rule_some`.
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
- **Current Status**: `inv` now calls `tape_window_ok`; the remaining work is to rewrite `inv_init` so each conjunct uses the staged helper lemmas instead of a monolithic `cbn` block that explodes the goal.

## Minimal, recommended next steps (what to do first)
1. **Install/Expose Coq**: Add `coqc` to the container PATH (or reuse the Windows toolchain via WSL path) so the single-file compile can run locally.
2. Re-run the targeted compile for only `ThieleUniversal.v` to verify the reorganized `inv_init` proof.
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

  cd coq; coqc -R thieleuniversal/coqproofs ThieleUniversal thieleuniversal/coqproofs/ThieleUniversal.v

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

