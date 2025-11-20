# ThieleUniversalBridge proof bottleneck notes

## Timed build snapshot
- `make -C coq bridge-timed BRIDGE_TIMEOUT=120` still times out on `ThieleUniversalBridge.v`, confirming the bridge file remains the blocking artifact even after the core tier succeeds. The timeout fires while `coqc` is processing the bridge file before the dependent `ThieleUniversal.vo` target starts.【778028†L1-L7】
- A synchronous 120s run of `timeout --foreground 120s make -C coq thielemachine/verification/ThieleUniversalBridge.vo COQFLAGS='-time -async-proofs off'` still stalls inside the bridge file after reaching `transition_FindRule_Next`; the job needed a manual interrupt after hanging in the guarded replay despite `read_mem` being opaque.【64e5b2†L147-L213】【08300a†L1-L4】

## Iteration notes
- Replaced the Fetch→FindRule direct proof's `step_n 3` replay with a register-level PC increment argument, chaining the existing `step_*` lemmas instead of unfolding `run_n`. This removes the first stall point reported by the timed run instrumentation and keeps the fetch trace entirely algebraic.
- Reverted the FindRule loop lemmas to short `step_n` replays and blocked the expensive memory unfolding with `Local Opaque CPU.read_mem`, so the 6- and 4-instruction traces execute symbolically without expanding the padded tape. The guard is rewritten to the known Boolean before stepping to keep the branch deterministic.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1313-L1382】

## Progress toward completion
- The setup-state invariant and tape/rule window facts stabilised and have not regressed across the last iterations, so the front matter of the bridge proof is effectively complete.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L536-L619】
- The Fetch→FindRule handoff now bypasses long `run_n` replays, using chained step lemmas to reach PC=3 directly; timed runs no longer stall in this phase.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1238-L1259】
- The loop proofs start from the cached entry state and replay the 6- and 4-instruction slices symbolically with `step_n`, relying on the opaque `read_mem` to avoid expanding the padded program while the guard is resolved up front. The bridge file still exhausts the 120s timeout during batch compilation, but the stall is confined to the FindRule section.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1313-L1382】【897c7a†L1-L4】

## Remaining effort estimate
- **Validate the opaque-step replay**: the 6- and 4-step blocks now run with `CPU.read_mem` opaque and a pre-resolved guard. Confirm in the next timed run whether the timeout still triggers at the bridge file or whether `coqc` advances beyond the FindRule lemmas.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1313-L1382】【897c7a†L1-L4】
- **Cache loop state shapes**: introduce definitions for the post-iteration register/memory slices (after `run_n cpu 6` and `run_n cpu 4`) so subsequent lemmas re-use equalities instead of recomputing them, reducing proof search around the loop helper facts.
- **Time-box the rule-table reasoning**: keep the existing checkpoints and add `Time` wrappers to the list-centric lemmas (`find_rule_index`, `rules_before_dont_match`) to confirm they stay negligible. If they remain fast, the remaining effort is confined to the single non-match replay.
- **Reconfirm with a longer timeout**: once the `transition_FindRule_Next` replay is computational, re-run `make -C coq bridge-timed BRIDGE_TIMEOUT=300` to verify the bridge file clears the FindRule loop. If it passes, the bridge proof should be within striking distance of completing the archived trace.

## Where the proof load concentrates
- **State setup invariant**: `inv_setup_state` closes cleanly with padding and prefix lemmas (lines 539–578), so the front matter is not the source of the hang.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L539-L579】
- **Fetch→FindRule entry**: The direct and wrapper lemmas around the Fetch/FindRule handoff sit in the 1132–1183 range and rely on small-step `step_n` reasoning over concrete prefixes.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1132-L1183】 These sections complete quickly when replayed interactively, suggesting the slowdown occurs later.
- **FindRule loop scaffolding**: The loop-entry facts and `transition_FindRule_*` lemmas sit in the 1224–1380 range and replay `run_n` on partially symbolic states. With `read_mem` opaque, the `step_n` scripts stay bounded, but this is still where the compiler spends its time during bridge builds.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1224-L1382】
- **Guarded non-match replay**: `transition_FindRule_Next` rewrites the `Jz` guard to `false` immediately, leaves `read_mem` opaque, and steps six instructions symbolically, so the loop replay avoids unfolding the padded tape while advancing PC and ADDR.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L1313-L1365】

## Latest timed run
- The current 120s timed build (`timeout --foreground 120s make -C coq thielemachine/verification/ThieleUniversalBridge.vo COQFLAGS='-time -async-proofs off'`) still hangs while replaying `transition_FindRule_Next`; `read_mem` remains opaque, but the proof script does not complete and required manual interruption.【64e5b2†L147-L213】【08300a†L1-L4】

### 2025-XX-XX update
- Added a tiny `step_n` replay on the FindRule non-match path that no longer depends on the fetch block’s memory prefix; the helper lemmas that tried to show the prefix was preserved were dropped in favour of the leaner replay.
- A 60s timed run (`timeout --foreground 60s make -C coq thielemachine/verification/ThieleUniversalBridge.vo COQFLAGS='-time -async-proofs off'`) still stalls while replaying `transition_FindRule_Next`; the early fetch lemmas complete quickly, so the hang remains confined to the 6-step loop replay.

### New instrumentation for timed runs
- Added `[bridge]` checkpoints plus `Time` wrappers on the Fetch→FindRule and FindRule loop lemmas so `make -C coq bridge-timed ...` prints the last completed milestone before a timeout. Look for messages like `[bridge] transition_FindRule_to_ApplyRule` in the build log to pinpoint the stall.
- The `step_fast` helper now prefers explicit decoder hypotheses over unfolding `decode_program_at_pc`, avoiding the expensive `calc_bounds` path when a lemma already provides concrete instruction decodes.【F:coq/thielemachine/verification/ThieleUniversalBridge.v†L636-L650】

## Suggested incremental work modules
1. **Instrument loop checkpoints**
   - Drop `idtac`/`Time` markers around `transition_FindRule_Next` and `transition_FindRule_Found` so a timed build reports whether we exit the entry lemmas before hanging.
   - If markers print, move them downward until the timeout reappears; this binary search will isolate the slowest proof script without altering semantics.
2. **Confirm opacity boundaries**
   - Keep `CPU.read_mem` opaque inside the FindRule lemmas and ensure no downstream facts re-open it; if further slowdowns appear, consider temporarily hiding other memory helpers (e.g., `pad_to`) during the 6- and 4-step traces.
3. **Cache per-iteration state shapes**
   - Add helper definitions for the loop-carried CPU state (register/memory slices after `loop_steps i`) so `loop_iteration_no_match` can reuse computed shapes instead of recomputing `run_n` chains. Proving equality once per helper should shrink subsequent goals.
4. **Break out rule-table scans**
   - Move the pure list reasoning (`find_rule_index`, `rules_before_dont_match`) into a separate section or module with their own timing markers. Confirm they are not the bottleneck; if they are fast, the slowdown is confined to the CPU-step side.

Documenting each checkpoint with timing output will let the next pass resume directly at the slowest lemma rather than re-running the full symbolic trace.
