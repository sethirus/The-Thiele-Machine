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

## Why the tape-window / `inv_init` debug matters now
- The immediate compile break is not about large arithmetic; it is a
  syntactic term-shape mismatch when applying a helper lemma that
  reasons about `pad_to`/`skipn`/`firstn` shapes in the initial state
  construction (`inv_init`). That mismatch is purely about *term
  shape* (syntactic form), not a fundamental logical gap.
- Fixing it is low-risk: we can either (a) add a tiny bridging lemma
  whose shape precisely matches the goal, or (b) reorder a couple of
  `unfold`/`subst` steps so the helper lemma's LHS occurs literally in
  the goal. Either route keeps the main design intact.

## Minimal, recommended next steps (what to do first)
1. Add a tiny, exact-shape bridging lemma (low risk) that says
   `firstn (length rest) (skipn n (pad_to n l ++ rest)) = rest` when
   `length l <= n`. That ensures the helper rewrite will match the
   goal without touching the large infrastructure.
2. Re-run the targeted compile for only `ThieleUniversal.v` and close
   remaining tiny micro-lemmas incrementally.
3. If any step still needs more RAM/time, run the full build using the
   provided `scripts/build_on_big_vm.sh` on a 32–64 GB runner.

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
- The build fails in `ThieleUniversal.v` at the `inv_init` / tape-window
  lemma (inv_init uses tape_window_ok_setup_state). The exact error
  message (reproducible with the single-file make shown below):

  Error: Unable to unify "tape" with
    "firstn (length tape)
       (skipn TAPE_START_ADDR
           (pad_to TAPE_START_ADDR
              (pad_to RULES_START_ADDR program ++ encode_rules (tm_rules tm)) ++ tape))".

- In short: a rewrite or apply using the helper lemma
  `skipn_pad_to_app`/`tape_window_ok_setup_state` fails because the
  subterm shape in the actual goal does not match the LHS shape expected
  by the helper lemma.

What I tried (short bullets)
- Moved decoding to the new multi-word decoder (no div/mod in the
  main file). UTM_Encode compiles.
- Restored and rationalized where the concrete program lives so there
  is exactly one `program_instrs` (avoids duplicate defs).
- Tried applying the helper lemma in different ways:
  - `apply tape_window_ok_setup_state` (original form)
  - `eapply` / `apply with explicit args` (delay or force matching)
  - Inline the helper proof body (copy the small reasoning into the
    call site) and attempt to `rewrite`.
  - Toggle opacity of `pad_to` / `skipn` to help rewrite matching.
  - Inserted lightweight debug tactics that let the compiler show the
    current goal shape (the goal printed above came from these runs).
- None of the above made the goal and the helper LHS syntactically
  compatible in this environment yet.

Repro (full local command used repeatedly)
- From the repository root (this repository is in branch
  `public-release`), run the single-file targeted build:

  make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo -j1 COQEXTRAFLAGS='-native-compiler no'

- This builds the encoder and the program parts first and stops on the
  failing universal file. The -native-compiler=no option is used to keep
  memory pressure lower.

How I debugged the goal (manual steps that reproduced the goal print)
- Temporarily insert in the proof a failing tactic that prints the
  current goal (this is quick and non-invasive):

  let G := match goal with |- ?G => G end in fail 1 "DEBUG_INV_INIT_GOAL:" G.

  Compilation will fail but the build error output includes the goal
  term (see "Current failing point" above). Remove this printing
  tactic once you capture the goal text.

Suggested minimal fixes to try next (ordered by low risk)
1. Exact-shape bridging lemma
   - Add a tiny lemma that matches the *actual* goal shape reported above
     and reduces it to the helper lemma. Example pattern:

       Lemma skipn_pad_to_app_variant l n rest :
         length l <= n ->
         firstn (length rest) (skipn n (pad_to n l ++ rest)) = rest.
       Proof. (* short proof using existing helpers *) Qed.

   - Use this variant at the invocation site to guarantee an exact
     syntactic match. This is the safest change: it does not alter the
     existing helper or the program encoding, it only adds a tiny
     matching lemma to adapt term shapes.

2. Avoid extra reductions/unfolds before applying lemma
   - Re-order `unfold`/`subst` so the goal displays `pad_to ... ++ rest`
     in exactly the same arrangement as the helper expects. Coq's
     matching is syntactic; small differences in parentheses or in the
     order of `pad_to` occurrences (e.g. double `pad_to`) prevent the
     rewrite from firing.

3. Import/Module shape sanity check (if 1 and 2 fail)
   - Ensure that there is exactly one `program_instrs` and that any
     `RULES_START_ADDR`/`TAPE_START_ADDR` live in the same module or
     have been `Import`ed at top-level before they are used in
     definitions. Duplicate definitions / different module paths can
     cause subtle term shapes.

4. If the environment keeps killing coqc or the remaining proof is
   still too heavy: run the full compile on a larger VM (32–64 GB) via
   scripts/build_on_big_vm.sh included in the repo.

One-line to revert the most-recent local edits (if you want to go
back):
- git checkout -- coq/thieleuniversal/coqproofs/ThieleUniversal.v
- git checkout -- coq/thieleuniversal/coqproofs/UTM_Program.v
- git checkout -- coq/thieleuniversal/coqproofs/UTM_Encode.v

Files changed in this session (for quick reference)
- coq/thieleuniversal/coqproofs/UTM_Encode.v — multi-word encoder + small lemmas
- coq/thieleuniversal/coqproofs/UTM_Program.v — concrete program + addresses
- coq/thieleuniversal/coqproofs/ThieleUniversal.v — delegate decode to encoder,
  adjust PROGRAM_STEPS, and small proof edits while debugging.

Next immediate action I recommend (pick one)
- Add the bridging lemma (fast, low risk). I will do it now if you
  want — I already have the exact failing shape. This will probably
  fix the exact rewrite mismatch and allow compilation to proceed.
- Or: I can open an interactive Coq session (coqtop/VS Code) and step
  through the `inv_init` proof with you — useful if you want to
  inspect proofs live.
- Or: prepare and run the larger VM build if the final steps still
  produce high-memory proof obligations.

